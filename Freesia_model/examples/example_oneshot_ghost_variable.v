From iris.proofmode Require Import tactics.
From iris.heap_lang Require Export lang.
From iris.heap_lang Require Import assert proofmode notation adequacy.
From iris.heap_lang.lib Require Import par.

From lib Require Import oneshot.
From core.kernel Require Import spinlock.

Context `{!heapGS Σ, !oneshotG Σ, !spawnG Σ}.

(** Concurrent increment with spinlock using oneshot ghost variables *)
Definition incr_inner : val := λ: "ℓ" "flag",
  (* Attempt to acquire flag and increment ℓ if successful *)
  if: !"flag" = #false then
    "flag" <- #true;;          (* Set flag to mark critical section *)
    FAA "ℓ" #1;;              (* Atomic increment *)
    #()
  else
    #().                      (* Already locked, no-op *)

(** Main increment operation with spinlock protection *)
Definition incr : val := λ: "lk" "ℓ" "flag",
  cpu_spin_lock "lk";;         (* Acquire spinlock *)
  incr_inner "ℓ" "flag";;      (* Perform actual increment *)
  cpu_spin_unlock "lk".        (* Release spinlock *)

(** Parallel execution of two increment operations *)
Definition parallel_incr : val := λ: "lk" "ℓ" "flag",
  (* Fork two threads *)
  (incr "lk" "ℓ" "flag") ||| (incr "lk" "ℓ" "flag");;
  ! "ℓ".                      (* Return final value *)

(** Invariant combining physical state and ghost state:
    - flag: physical variable status
    - ℓ: shared counter
    - γ: oneshot ghost variable tracking completion *)
Definition incr_inv (ℓ : loc) (flag : loc) (γ : gname) (n : Z) : iProp Σ :=
    (flag ↦ #false ∗ ℓ ↦ #n ∗ (Pending γ (1/2)%Qp)     (* pending state *)
  ∨ flag ↦ #true ∗ ℓ ↦ #(n+1) ∗ (Shot γ #(n+1)))%I.     (* shot state *)

(** Verification of successful incr execution *)
Lemma incr_succ_spec (lk : loc) (ℓ : loc) (flag : loc) (n : Z) (γ : gname):
  {{{ flag ↦ #false ∗
      (Pending γ (1/2)%Qp) ∗
      is_spinlock #lk (incr_inv ℓ flag γ n) }}}
    incr #lk #ℓ #flag
  {{{ RET #(); (Shot γ #(n+1)) }}}.
Proof.
  iIntros "%Φ [Hflag [Hγ1 #Hsp]] HΦ /=".
  wp_lam. wp_let. wp_let.

  (* 1. Acquire spinlock and open invariant *)
  wp_bind (cpu_spin_lock _).
  wp_apply (cpu_spin_lock_spec with "Hsp").
  iIntros "[Hinv_sp Hinv_incr]".
  wp_seq. wp_lam. wp_let.

  (* 2. Case analysis on current state *)
  wp_bind (! _)%E.
  iDestruct "Hinv_incr" as "[[_ [Hl Hγ2]]|[_ [Hl Hγ2]]]".
  - (* Case 1: pending state *)
    wp_load. wp_pures. wp_store.

    (* 3. Split and shoot oneshot *)
    iDestruct (pending_split with "[$Hγ1 $Hγ2]") as "Hγ".
    iMod (pending_shoot _ #(n+1) with "Hγ") as "Hγ".
    iAssert ((Shot γ #(n+1)) ∗ (Shot γ #(n+1)))%I with "[Hγ]" as "[Hγ1 Hγ2]".
    { by iApply shot_idemp. }

    (* 4. Perform atomic increment *)
    wp_faa. wp_seq. wp_seq.

    (* 5. Release lock with updated state *)
    wp_apply (cpu_spin_unlock_spec with "[Hinv_sp Hflag Hl Hγ1]").
    * iFrame. iRight. iFrame.
    * iIntros "_". iApply "HΦ". iApply "Hγ2".
  - (* Case 2: shot state (already completed)  *)
    by iCombine "Hγ1 Hγ2" gives %?.
Qed.

(** Verification of failed incr execution *)
Lemma incr_failed_spec (lk : loc) (ℓ : loc) (flag : loc) (n : Z) (γ : gname):
  {{{ flag ↦ #true ∗
      is_spinlock #lk (incr_inv ℓ flag γ n) }}}
    incr #lk #ℓ #flag
  {{{ RET #(); (Shot γ #(n+1)) }}}.
Proof.
  iIntros "%Φ [Hflag #Hsp] HΦ /=".
  wp_lam. wp_let. wp_let.

  (* 1. Acquire spinlock and open invariant *)
  wp_bind (cpu_spin_lock _).
  wp_apply (cpu_spin_lock_spec with "Hsp").
  iIntros "[Hinv_sp Hinv_incr]".
  wp_seq. wp_lam. wp_let.

  (* 2. Case analysis on current state *)
  wp_bind (! _)%E.
  iDestruct "Hinv_incr" as "[[H [Hl Hγ2]]|[_ [Hl Hγ2]]]".
  - (* Case 1: pending state *)
    iAssert (False)%I with "[H Hflag]" as %[].    (* exfalso situation *)
    { iApply (pointsto_exclusive flag). iFrame. }
  - (* Case 2: shot state *)
    wp_load. wp_pures.

    (* 3. shot idempotent *)
    iAssert ((Shot γ #(n+1)) ∗ (Shot γ #(n+1)))%I with "[Hγ2]" as "[Hγ1 Hγ2]".
    { by iApply shot_idemp. }

    (* 4. Release lock with Nop *)
    wp_apply (cpu_spin_unlock_spec with "[Hinv_sp Hflag Hl Hγ1]").
    * iFrame. iRight. iFrame.
    * iIntros "_". iApply "HΦ". iApply "Hγ2".
Qed.

(** Verification of successful inner incr operation *)
Lemma incr_inner_succ_spec (ℓ : loc) (flag : loc) (n : Z) (γ : gname):
  {{{ flag ↦ #false ∗             (* Physical flag in unlocked state *)
      ℓ ↦ #n ∗                    (* Shared counter value *)
      (Pending γ 1%Qp) }}}        (* Full pending ghost state *)
    incr_inner #ℓ #flag
  {{{ RET #(); (Shot γ #(n+1)) ∗ incr_inv ℓ flag γ n }}}.
Proof.
  iIntros "%Φ [Hflag [Hl Hγ]] HΦ /=".
  wp_lam. wp_let.
  wp_bind (! _)%E.
  wp_load. wp_pures. wp_store.

  (* Ghost state transition *)
  iMod (pending_shoot _ #(n+1) with "Hγ") as "Hγ".
  (* Idempotency of shot *)
  iAssert ((Shot γ #(n+1)) ∗ (Shot γ #(n+1)))%I with "[Hγ]" as "[Hγ1 Hγ2]".
    { by iApply shot_idemp. }

  wp_faa. wp_seq.
  iModIntro. iApply "HΦ".
  
  (* construct invariant *)
  iFrame. iRight. iFrame.
Qed.

(** Verification of failed inner incr operation *)
Lemma incr_inner_failed_spec (ℓ : loc) (flag : loc) (n : Z) (γ : gname):
  {{{ flag ↦ #true ∗            (* Physical flag already locked *)
      ℓ ↦ #(n+1) ∗              (* Pre-incremented counter *)
      (Shot γ #(n+1)) }}}       (* Existing shot ghost state *)
    incr_inner #ℓ #flag
  {{{ RET #(); (Shot γ #(n+1)) ∗ incr_inv ℓ flag γ n }}}.
Proof.
  iIntros "%Φ [Hflag [Hl Hγ]] HΦ /=".

  (* Leverage shot idempotency *)
  iAssert ((Shot γ #(n+1)) ∗ (Shot γ #(n+1)))%I with "[Hγ]" as "[Hγ1 Hγ2]".
    { by iApply shot_idemp. }

  wp_lam. wp_let.
  wp_bind (! _)%E.
  wp_load. wp_pures.
  iModIntro. iApply "HΦ".

  (* construct invariant *)
  iFrame. iRight. iFrame.
Qed.

(** Structural decomposition lemma for pending state *)
Lemma incr_inv_pending (ℓ : loc) (flag : loc) (n : Z) (γ : gname):
  incr_inv ℓ flag γ n ∗ (Pending γ (1/2)%Qp) -∗
  flag ↦ #false ∗ ℓ ↦ #n ∗ (Pending γ (1/2)%Qp).
Proof.
  iIntros "[Hinv_incr Hγ1]".
  (* Case analysis *)
  iDestruct "Hinv_incr" as "[[Hflag [Hl Hγ2]]|[Hflag [Hl Hγ2]]]".
  - iFrame.                           (* Left case: pending state *)
  - by iCombine "Hγ1 Hγ2" gives %?.   (* Right case: contradiction *)
Qed.

(** Structural decomposition lemma for shot state *)
Lemma incr_inv_shot (ℓ : loc) (flag : loc) (n : Z) (γ : gname):
  incr_inv ℓ flag γ n ∗ (Shot γ #(n+1)) -∗
  flag ↦ #true ∗ ℓ ↦ #(n+1) ∗ (Shot γ #(n+1)).
Proof.
  iIntros "[Hinv_incr Hγ1]".
  (* Case analysis *)
  iDestruct "Hinv_incr" as "[[Hflag [Hl Hγ2]]|[Hflag [Hl Hγ2]]]".
  - by iCombine "Hγ1 Hγ2" gives %?.   (* Left case: contradiction *)
  - iFrame.                           (* Right case: shot state *)
Qed.

(** Full initialization and increment specification *)
Lemma incr_spec1 (lk : loc) (ℓ : loc) (flag : loc) (n : Z) (γ : gname):
  {{{ flag ↦ #false ∗                    (* Physical flag in unlocked state *)
      ℓ ↦ #n ∗                           (* Shared counter initial value *)
      lk ↦ #false ∗                      (* Spinlock in unlocked state *)
      (Pending γ 1%Qp) }}}               (* Full pending ghost resource *)
    incr #lk #ℓ #flag
  {{{ RET #(); (Shot γ #(n+1)) }}}.      (* Postcondition: shot state *)
Proof.
  iIntros "%Φ [Hflag [Hl [Hlk Hγ]]] HΦ /=".
  wp_lam.
  wp_let. wp_let.

  (* 1. Split pending ghost resource *)
  iDestruct (pending_split with "Hγ") as "[Hγ1 Hγ2]".

  (* 2. Establish increment invariant *)
  iAssert (incr_inv ℓ flag γ n)%I with "[Hflag Hl Hγ2]" as "Hinv_incr".
  { iLeft. by iFrame. }     (* Left disjunct: pending state *)

  (* 3. Create spinlock invariant *)
  iMod (inv_alloc basic_types.lockN _ (spinlock_inv lk ((incr_inv ℓ flag γ n))) with "[Hlk Hinv_incr]") as "#Hinv_sp".
  { iNext. iExists false. iFrame. }       (* Initial lock state: unlocked *)

  (* 4. Cast to spinlock interface *)
  iAssert (is_spinlock #lk ((incr_inv ℓ flag γ n))) with "[Hinv_sp]" as "#Hinv".
  { iExists lk. iSplit; first eauto. iExact "Hinv_sp". }

  (* 5. Main lock-protected increment *)
  wp_bind (cpu_spin_lock _).
  wp_apply (cpu_spin_lock_spec with "Hinv").
  iIntros "[Hinv1 Hinv_incr]".
  wp_seq.
  wp_bind (incr_inner _ _).

  (* 6. Case analysis on shared state *)
  iDestruct "Hinv_incr" as "[[Hflag [Hl Hγ2]]|[Hflag [Hl Hγ2]]]".
  - (* Case: pending state *)
    iDestruct (pending_split with "[$Hγ1 $Hγ2]") as "Hγ".
    wp_apply (incr_inner_succ_spec ℓ flag n γ with "[Hflag Hl Hγ]").
    { iFrame. }
    iIntros "[Hγ Hinv_incr]".
    wp_seq.
    (* 7. Release spinlock *)
    wp_apply (cpu_spin_unlock_spec with "[Hinv1 Hinv_incr]").
    + iFrame. iApply "Hinv_incr".     (* Reconstruct lock invariant *)
    + iIntros "_". iApply "HΦ". iApply "Hγ".
  - (* Case: shot state *)
    by iCombine "Hγ1 Hγ2" gives %?.   (* pending + shot contradiction *)
Qed.

(** General increment specification with existing lock *)
Lemma incr_spec (lk : loc) (ℓ : loc) (flag : loc) (n : Z) (γ : gname):
  {{{ is_spinlock #lk (incr_inv ℓ flag γ n) ∗  (* Existing lock invariant *)
      (Pending γ (1/2)%Qp) }}}                 (* Half pending ghost resource *)
    incr #lk #ℓ #flag
  {{{ RET #(); (Shot γ #(n+1)) }}}.
Proof.
  iIntros "%Φ [#Hinv Hγ1] HΦ /=".
  wp_lam. wp_let. wp_let.

  (* 1. Acquire spinlock *)
  wp_bind (cpu_spin_lock _).
  wp_apply (cpu_spin_lock_spec with "Hinv").
  iIntros "[Hinv1 Hinv_incr]".
  wp_seq.
  wp_bind (incr_inner _ _).

  (* 2. State decomposition *)
  iDestruct "Hinv_incr" as "[[Hflag [Hl Hγ2]]|[Hflag [Hl Hγ2]]]".
  - (* Case: pending state *)
    iDestruct (pending_split with "[$Hγ1 $Hγ2]") as "Hγ".
    wp_apply (incr_inner_succ_spec ℓ flag n γ with "[Hflag Hl Hγ]").
    { iFrame. }
    iIntros "[Hγ Hinv_incr]".
    wp_seq.
    (* 3. Release spinlock *)
    wp_apply (cpu_spin_unlock_spec with "[Hinv1 Hinv_incr]").
    + iFrame. iApply "Hinv_incr".     (* Reconstruct lock invariant *)
    + iIntros "_". iApply "HΦ". iApply "Hγ".
  - (* Case: shot state *)
    by iCombine "Hγ1 Hγ2" gives %?.       (* Resource contradiction *)
Qed.

(** Parallel increment verification *)
Lemma parallel_incr_spec (lk : loc) (ℓ : loc) (flag : loc) (n : Z) (γ : gname):
  {{{ is_spinlock #lk (incr_inv ℓ flag γ n) ∗  (* Lock invariant *)
      incr_inv ℓ flag γ n ∗                    (* Current shared state *)
      (Pending γ 1%Qp) }}}                     (* Full pending ghost resource *)
    parallel_incr #lk #ℓ #flag
  {{{ RET #(n+1); True }}}.
Proof.
  iIntros "%Φ [#Hinv [Hinv_incr Hγ]] HΦ /=".

  (* 1. Split ghost resource for parallel threads *)
  iDestruct (pending_split with "Hγ") as "[Hγ1 Hγ2]".
  wp_lam. wp_let. wp_let.

  (* 2. Parallel execution *)
  wp_smart_apply (wp_par 
    (λ _, Shot γ #(n+1))                 (* Left thread postcondition *)
    (λ _, Shot γ #(n+1))                 (* Right thread postcondition *)
    with "[Hγ1] [Hγ2]").
  - (* Left thread *)
    wp_apply (incr_spec with "[Hinv Hγ1]").
    + iFrame. iApply "Hinv".
    + iIntros "Hγ". iApply "Hγ".
  - (* Right thread *)
    wp_apply (incr_spec with "[Hinv Hγ2]").
    + iFrame. iApply "Hinv".
    + iIntros "Hγ". iApply "Hγ".
  - (* Post-parallel join *)
    iIntros (v1 v2) "[Hγ1 Hγ2]".
    iModIntro. wp_seq.

    (* 3. Verify final state *)
    iAssert (flag ↦ #true ∗ ℓ ↦ #(n+1) ∗ (Shot γ #(n+1)))%I with "[Hinv_incr Hγ1]" as "[Hflag [Hl Hγ3]]".
    { iApply incr_inv_shot. iFrame. }
    wp_load. iModIntro. iApply "HΦ". done.
Qed.
