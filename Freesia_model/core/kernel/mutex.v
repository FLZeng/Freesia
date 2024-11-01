Require Import ZArith.
From iris.base_logic.lib Require Import invariants.
From iris.heap_lang Require Import proofmode notation.

From lib Require Import basic_types.
From core.kernel Require Import spinlock.
From core.kernel Require Import wait_queue.

Definition mutex_init_inner : val :=
  λ: "lk" "state" "wq",
    "state" <- #0;;
    "wq" <- NONEV;;
    cpu_spin_init "lk".

Definition mutex_init (mutex : Mutex) : expr :=
  let lk := mutex.(m_lk) in
  let state := mutex.(m_state) in
  let wq := mutex.(m_wq) in
    mutex_init_inner #lk #state #wq.

Definition mutex_destroy_inner : val :=
  λ: "lk" "state" "wq",
    cpu_spin_lock "lk";;
    (
    if: ((!"state" = #0) && (!"wq" = NONEV)) then
      cpu_spin_unlock "lk"
    else
      #()
    ).

Definition mutex_destroy (mutex : Mutex) : expr :=
  let lk := mutex.(m_lk) in
  let state := mutex.(m_state) in
  let wq := mutex.(m_wq) in
    mutex_destroy_inner #lk #state #wq.

Definition mutex_read_trylock_inner : val :=
  λ: "lk" "state" "wq",
    cpu_spin_lock "lk";;
    if: #(-1) < (!"state") then
      "state" <- !"state" + #1;;
      cpu_spin_unlock "lk";;
      #true
    else
      cpu_spin_unlock "lk";;
      #false.

Definition mutex_read_trylock (mutex : Mutex) :=
  let lk := mutex.(m_lk) in
  let state := mutex.(m_state) in
  let wq := mutex.(m_wq) in
    mutex_read_trylock_inner #lk #state #wq.

Definition mutex_trylock_inner : val :=
  λ: "lk" "state" "wq",
  cpu_spin_lock "lk";;
  (
  if: (!"state") = #0 then
    "state" <- #(-1);;
    cpu_spin_unlock "lk";;
    #true
  else
    cpu_spin_unlock "lk";;
    #false
  ).

Definition mutex_trylock (mutex : Mutex) :=
  let lk := mutex.(m_lk) in
  let state := mutex.(m_state) in
  let wq := mutex.(m_wq) in
    mutex_trylock_inner #lk #state #wq.

Definition mutex_read_lock_inner : val :=
  rec: "mutex_read_lock_inner" "lk" "state" "wq" :=
    let: "wqe" := mk_wait_queue_elem #() in

    cpu_spin_lock "lk";;

    let: "can_lock" := (#(-1) < (!"state")) in
    (if: "can_lock" then
      "state" <- !"state" + #1   (* read_locked *)
    else
      (* Someone else is holding the lock, add self to
         the wait queue *)
      wq_wait_init "wq" "wqe" #true (* wait_read*)
    );;   

    cpu_spin_unlock "lk";;

    if: "can_lock" then
      #()
    else
      (* Someone else is holding the lock, wait for 
         the lock to become available.
      *)
      wq_wait_final "wq" "wqe";;
      (* Waken up by someone, start a new try for the lock *)
      "mutex_read_lock_inner" "lk" "state" "wq".

Definition mutex_read_lock (mutex : Mutex) :=
  let lk := mutex.(m_lk) in
  let state := mutex.(m_state) in
  let wq := mutex.(m_wq) in
    mutex_read_lock_inner #lk #state #wq.

Definition mutex_lock_inner : val :=
  rec: "mutex_lock_inner" "lk" "state" "wq" :=
    let: "wqe" := mk_wait_queue_elem #() in

    cpu_spin_lock "lk";;

    (* let: "state_val" := !"state" in *)
    let: "can_lock" := (!"state" = #(0)) in
    (
    if: "can_lock" then
      "state" <- #(-1)   (* write locked *)
    else
      (* Someone else is holding the lock, add self to
         the wait queue *)
      wq_wait_init "wq" "wqe" #false (* wait_write*)
    );;

    cpu_spin_unlock "lk";;

    if: "can_lock" then
      #()
    else
      (* Someone else is holding the lock, wait for 
         the lock to become available.
      *)
      wq_wait_final "wq" "wqe";;
      (* Waken up by someone, start a new try for the lock *)
      "mutex_lock_inner" "lk" "state" "wq".

Definition mutex_lock (mutex : Mutex) :=
  let lk := mutex.(m_lk) in
  let state := mutex.(m_state) in
  let wq := mutex.(m_wq) in
    mutex_lock_inner #lk #state #wq.

Definition mutex_read_unlock_inner : val :=
  λ: "lk" "state" "wq",
    cpu_spin_lock "lk";;
    if: (!"state") ≤ #0 then
      (* No one is holding the lock *)
      cpu_spin_unlock "lk";;
      #()
    else
      "state" <- !"state" - #1;;
      cpu_spin_unlock "lk";;
      wq_wake_next "wq".

Definition mutex_read_unlock (mutex : Mutex) :=
  let lk := mutex.(m_lk) in
  let state := mutex.(m_state) in
  let wq := mutex.(m_wq) in
    mutex_read_unlock_inner #lk #state #wq.

Definition mutex_unlock_inner : val :=
  λ: "lk" "state" "wq",
    cpu_spin_lock "lk";;
    if: (!"state") = #(0) then
      (* No one is holding the lock *)
      cpu_spin_unlock "lk";;
      #()
    else
      "state" <- #0;;
      cpu_spin_unlock "lk";;
      wq_wake_next "wq".

Definition mutex_unlock (mutex : Mutex) :=
  let lk := mutex.(m_lk) in
  let state := mutex.(m_state) in
  let wq := mutex.(m_wq) in
    mutex_unlock_inner #lk #state #wq.


Section proof.

Context `{!heapGS Σ}.

Definition is_pointer (l : loc) : iProp Σ :=
  ∃ v : val, l ↦ v.

Definition is_pointer_z (l : loc) : iProp Σ :=
  ∃ v : Z, l ↦ #v.

Definition is_pointer_b (l : loc) : iProp Σ :=
  ∃ v : bool, l ↦ #v.

Definition is_valid_mutex (mutex : Mutex) : iProp Σ :=
  is_pointer mutex.(m_lk) ∗
  is_pointer mutex.(m_state) ∗
  is_pointer mutex.(m_wq).

Definition mutex_inv (lst: loc) (lwq: loc) (R : iProp Σ) : iProp Σ :=
  ∃ (state : Z) (wq : val),
    lst ↦ #state ∗
    lwq ↦ wq ∗
    if (Z.eqb state 0) then R else True.

Definition is_mutex (mutex : Mutex) (R : iProp Σ) : iProp Σ :=
  (is_spinlock #(mutex.(m_lk)) (mutex_inv mutex.(m_state) mutex.(m_wq) R)).

Lemma neq_imp_neqb (a b : Z) :
  (a ≠ b)%Z → ((a =? b)%Z = false).
Proof.
  intros Hneq.
  apply Z.eqb_neq.
  done.
Qed.

Lemma lt_imp_ltb (a b : Z) :
  (a < b)%Z → ((a <? b)%Z = true).
Proof.
  intros Hlt.
  apply Z.ltb_lt.
  done.
Qed.

Lemma neq_trans (a b : Z) :
  (a ≠ b)%Z -> ((a + 1 =? b + 1)%Z = false).
Proof.
  intros Hneq.
  lia.
Qed.

Lemma lt_trans (a b : Z) :
  (a < b)%Z -> ((a <? b + 1)%Z = true).
Proof.
  intros Hlt.
  lia.
Qed.

Lemma lt_trans2 (a b : Z) :
  (a < b)%Z -> ((a - 1 <? b - 1)%Z = true).
Proof.
  intros Hlt.
  lia.
Qed.

Lemma mutex_init_spec (mutex : Mutex) (R : iProp Σ):
  {{{
      is_valid_mutex mutex ∗
      R
  }}}
    mutex_init mutex
  {{{ RET #(); is_mutex mutex R }}}.
Proof.
  iIntros (Φ) "[Hm HR] HΦ".
  iDestruct "Hm" as "(Hlk & Hstate & Hwq)".
  iDestruct "Hlk" as (v1) "Hlk".
  iDestruct "Hstate" as (v2) "Hstate".
  iDestruct "Hwq" as (v3) "Hwq".
  unfold mutex_init.
  unfold mutex_init_inner.
  wp_lam. wp_let. wp_let.
  wp_store. wp_store.
  wp_bind (cpu_spin_init _).
  wp_apply (cpu_spin_init_spec (m_lk mutex) (mutex_inv (m_state mutex) (m_wq mutex) R) with "[Hlk Hstate Hwq HR]").
  - iFrame.
    iExact "HR".
  - iIntros "#Hsp".
    iDestruct "Hsp" as (lsp) "[%Heq #Hinv_spin]".
    iApply "HΦ".
    unfold is_mutex.
    iExists lsp.
    iSplit; eauto.
Qed.

Lemma mutex_destroy_spec mutex R :
  {{{ is_mutex mutex R ∗ R }}}
    mutex_destroy mutex
  {{{ RET #(); True }}}.
Proof.
  iIntros (Φ) "[#Hm HR] HΦ".
  unfold mutex_destroy.
  wp_lam. wp_let. wp_let.
  wp_bind (cpu_spin_lock _).
  wp_apply (cpu_spin_lock_spec with "Hm").
  iIntros "[Hinv_spin HR_mutex]".
  wp_seq.
  iDestruct "HR_mutex" as (state wq) "(Hlst & Hlwq & HR_mutex)".
  wp_load.
  destruct (decide (state = 0%Z)) as [->|Hneq].
  - wp_pure. wp_if. wp_load.
    destruct (decide (wq = NONEV)) as [->|Hwq_neq].
    + wp_pure. wp_if.
      wp_bind (cpu_spin_unlock _).
      wp_apply (cpu_spin_unlock_spec with "[$Hinv_spin Hlst Hlwq HR]").
      * iExists 0%Z, NONEV.
        iFrame.
      * iIntros "_".
        iApply "HΦ".
        done.
    + wp_pure.
      case_bool_decide; [simplify_eq |].
      wp_if.
      iApply "HΦ".
      done.
  - wp_pure.
    case_bool_decide; [simplify_eq |].
    do 2 wp_if.
    iApply "HΦ".
    done.
Qed.

Lemma mutex_trylock_spec mutex R :
  {{{ is_mutex mutex R }}}
    mutex_trylock mutex
  {{{ b, RET #b; if b is true then R else True }}}.
Proof.
  iIntros (Φ) "#Hm HΦ".
  unfold mutex_trylock.
  wp_rec. wp_let. wp_let.
  wp_bind (cpu_spin_lock _).
  wp_apply (cpu_spin_lock_spec with "Hm").
  iIntros "[Hinv_spin HR]".
  wp_pure credit:"Hcred".
  wp_lam.
  wp_bind (! _)%E.
  iDestruct "Hm" as (lsp2->) "Hinv_mutex".
  iInv "Hinv_mutex" as (sp) "[Hlsp HR_mutex]" "Hclose".
  iApply fupd_wp.
  iApply (lc_fupd_add_later with "Hcred").
  iIntros "!>!>".
  iDestruct "HR" as (state wq) "(Hlst & Hlwq & HR)".
  wp_load.
  destruct (decide (state = 0)) as [->|Hneq].
  - iMod ("Hclose" with "[Hlsp HR_mutex]") as "_".
    + iNext. iExists sp. iFrame.
    + iModIntro.
      wp_pure. wp_if. wp_store.
      wp_bind (cpu_spin_unlock _).
      wp_apply (cpu_spin_unlock_spec with "[$Hinv_spin Hlst Hlwq]").
      * iExists (-1)%Z, wq.
        iFrame.
      * iIntros "_".
        wp_seq.
        iApply ("HΦ" $! true).
        done.
  - iMod ("Hclose" with "[Hlsp HR_mutex]") as "_".
    + iNext. iExists sp. iFrame.
    + iModIntro.
      wp_pure.
      case_bool_decide; [simplify_eq |].
      wp_if.
      wp_bind (cpu_spin_unlock _).
      wp_apply (cpu_spin_unlock_spec with "[$Hinv_spin Hlst Hlwq]").
      * iExists state, wq.
        iFrame.
        apply neq_imp_neqb in Hneq.
        rewrite Hneq.
        done.
      * iIntros "_".
        wp_seq.
        iApply ("HΦ" $! false).
        done.
Qed.

Lemma mutex_lock_spec mutex R :
  {{{ is_mutex mutex R }}}
    mutex_lock mutex
  {{{ RET #(); is_mutex mutex R ∗ R }}}.
Proof.
  iIntros (Φ) "#Hm HΦ".
  unfold mutex_lock.
  iLöb as "IH".
  wp_rec. wp_let. wp_let.
  unfold mk_wait_queue_elem; wp_alloc wqe as "Hwqe".
  wp_let.
  wp_bind (cpu_spin_lock _).
  wp_apply (cpu_spin_lock_spec with "Hm").
  iIntros "[Hinv_spin HR]".
  wp_seq.
  iDestruct "HR" as (state wq) "(Hlst & Hlwq & HR)".
  wp_load.
  destruct (decide (state = 0%Z)) as [->|Hneq].
  - wp_pure. wp_let. wp_if.
    wp_store.
    wp_bind (cpu_spin_unlock _).
    wp_apply (cpu_spin_unlock_spec with "[$Hinv_spin Hlst Hlwq]").
    + iExists (-1)%Z, wq.
      iFrame.
    + iIntros "_".
      wp_seq. wp_if.
      iApply ("HΦ").
      iFrame.
      iModIntro.
      iExact "Hm".
  - wp_pure. wp_let.
    case_bool_decide; [simplify_eq |].
    wp_if.
    wp_bind (wq_wait_init _ _ _).
    wp_apply (wq_wait_init_spec with "HR").
    iIntros "HR".
    wp_seq.
    wp_bind (cpu_spin_unlock _).
    wp_apply (cpu_spin_unlock_spec with "[$Hinv_spin Hlst Hlwq]").
    + iExists state, wq.
      iFrame.
      apply neq_imp_neqb in Hneq.
      rewrite Hneq.
      done.
    + iIntros "_".
      wp_seq. wp_if.
      wp_apply (wq_wait_final_spec with "HR").
      iIntros "HR".
      wp_seq.
      wp_apply ("IH" with "HΦ").
Qed.

Lemma mutex_unlock_spec mutex R :
  {{{ is_mutex mutex R ∗ R }}}
    mutex_unlock mutex
  {{{ RET #(); True }}}.
Proof.
  iIntros (Φ) "[#Hm HR] HΦ".
  unfold mutex_unlock.
  wp_lam. wp_let. wp_let.
  wp_bind (cpu_spin_lock _).
  wp_apply (cpu_spin_lock_spec with "Hm").
  iIntros "[Hinv_spin HR_mutex]".
  wp_seq.
  iDestruct "HR_mutex" as (state wq) "(Hlst & Hlwq & HR_mutex)".
  wp_load.
  destruct (decide (state = 0%Z)) as [->|Hneq].
  - wp_pure. wp_if.
    wp_bind (cpu_spin_unlock _).
    wp_apply (cpu_spin_unlock_spec with "[$Hinv_spin Hlst Hlwq HR]").
    + iExists 0%Z, wq.
      iFrame.
    + iIntros "_".
      wp_seq.
      iApply "HΦ".
      done.
  - wp_pure.
    case_bool_decide; [simplify_eq |].
    wp_if. wp_store.
    wp_bind (cpu_spin_unlock _).
    wp_apply (cpu_spin_unlock_spec with "[$Hinv_spin Hlst Hlwq HR]").
    + iExists 0%Z, wq.
      iFrame.
    + iIntros "_".
      wp_seq.
      wp_apply (wq_wake_next_spec with "HR_mutex").
      iIntros "_".
      iApply "HΦ".
      done.
Qed.

End proof.
