From iris.algebra Require Import frac agree csum.
From iris.proofmode Require Import tactics.
From iris.program_logic Require Export weakestpre.
From iris.heap_lang Require Export lang.
From iris.heap_lang Require Import assert proofmode notation adequacy.
From iris.heap_lang.lib Require Import par.
From iris.prelude Require Import options.

From lib Require Import basic_types.
From lib Require Import oneshot.
From core.kernel Require Import spinlock.

Context `{!heapGS Σ, !oneshotG Σ, !spawnG Σ}.

Definition incr_inner : val := λ: "ℓ" "flag",
  if: !"flag" = #false then
    "flag" <- #true;;
    FAA "ℓ" #1;;
    #()
  else
    #().

Definition incr : val := λ: "lk" "ℓ" "flag",
  cpu_spin_lock "lk";;
  incr_inner "ℓ" "flag";;
  cpu_spin_unlock "lk".

Definition parallel_incr : val := λ: "lk" "ℓ" "flag",
  (incr "lk" "ℓ" "flag") ||| (incr "lk" "ℓ" "flag");;
  ! "ℓ".

Definition incr_inv (ℓ : loc) (flag : loc) (γ : gname) (n : Z) : iProp Σ :=
    (flag ↦ #false ∗ ℓ ↦ #n ∗ (Pending γ (1/2)%Qp)
  ∨ flag ↦ #true ∗ ℓ ↦ #(n+1) ∗ (Shot γ #(n+1)))%I.


Lemma incr_succ_spec (lk : loc) (ℓ : loc) (flag : loc) (n : Z) (γ : gname):
  {{{ flag ↦ #false ∗
      (Pending γ (1/2)%Qp) ∗
      is_spinlock #lk (incr_inv ℓ flag γ n) }}}
    incr #lk #ℓ #flag
  {{{ RET #(); (Shot γ #(n+1)) }}}.
Proof.
  iIntros "%Φ [Hflag [Hγ1 #Hsp]] HΦ /=".
  wp_lam. wp_let. wp_let.
  wp_bind (cpu_spin_lock _).
  wp_apply (cpu_spin_lock_spec with "Hsp").
  iIntros "[Hinv_sp Hinv_incr]".
  wp_seq. wp_lam. wp_let.
  wp_bind (! _)%E.
  iDestruct "Hinv_incr" as "[[_ [Hl Hγ2]]|[_ [Hl Hγ2]]]".
  - (* Case 1: flag ↦ #false ∗ ℓ ↦ #n *)
    wp_load. wp_pures. wp_store.
    iDestruct (pending_split with "[$Hγ1 $Hγ2]") as "Hγ".
    iMod (pending_shoot _ #(n+1) with "Hγ") as "Hγ".
    iAssert ((Shot γ #(n+1)) ∗ (Shot γ #(n+1)))%I with "[Hγ]" as "[Hγ1 Hγ2]".
    { by iApply shot_idemp. }
    wp_faa. wp_seq. wp_seq.
    wp_apply (cpu_spin_unlock_spec with "[Hinv_sp Hflag Hl Hγ1]").
    * iFrame. iRight. iFrame.
    * iIntros "_". iApply "HΦ". iApply "Hγ2".
  - (* Case 2: flag ↦ #true ∗ ℓ ↦ #(n+1) *)
    by iCombine "Hγ1 Hγ2" gives %?.
Qed.

Lemma incr_failed_spec (lk : loc) (ℓ : loc) (flag : loc) (n : Z) (γ : gname):
  {{{ flag ↦ #true ∗
      is_spinlock #lk (incr_inv ℓ flag γ n) }}}
    incr #lk #ℓ #flag
  {{{ RET #(); (Shot γ #(n+1)) }}}.
Proof.
  iIntros "%Φ [Hflag #Hsp] HΦ /=".
  wp_lam. wp_let. wp_let.
  wp_bind (cpu_spin_lock _).
  wp_apply (cpu_spin_lock_spec with "Hsp").
  iIntros "[Hinv_sp Hinv_incr]".
  wp_seq. wp_lam. wp_let.
  wp_bind (! _)%E.
  iDestruct "Hinv_incr" as "[[H [Hl Hγ2]]|[_ [Hl Hγ2]]]".
  - (* Case 1: flag ↦ #false ∗ ℓ ↦ #n *)
    iAssert (False)%I with "[H Hflag]" as %[].
    { iApply (pointsto_exclusive flag). iFrame. }
  - (* Case 2: flag ↦ #true ∗ ℓ ↦ #(n+1) *)
    wp_load. wp_pures.
    iAssert ((Shot γ #(n+1)) ∗ (Shot γ #(n+1)))%I with "[Hγ2]" as "[Hγ1 Hγ2]".
    { by iApply shot_idemp. }
    wp_apply (cpu_spin_unlock_spec with "[Hinv_sp Hflag Hl Hγ1]").
    * iFrame. iRight. iFrame.
    * iIntros "_". iApply "HΦ". iApply "Hγ2".
Qed.


Lemma incr_inner_succ_spec (ℓ : loc) (flag : loc) (n : Z) (γ : gname):
  {{{ flag ↦ #false ∗
      ℓ ↦ #n ∗
      (Pending γ 1%Qp) }}}
    incr_inner #ℓ #flag
  {{{ RET #(); (Shot γ #(n+1)) ∗ incr_inv ℓ flag γ n }}}.
Proof.
  iIntros "%Φ [Hflag [Hl Hγ]] HΦ /=".
  wp_lam. wp_let.
  wp_bind (! _)%E.
  wp_load. wp_pures. wp_store.
  iMod (pending_shoot _ #(n+1) with "Hγ") as "Hγ".
  iAssert ((Shot γ #(n+1)) ∗ (Shot γ #(n+1)))%I with "[Hγ]" as "[Hγ1 Hγ2]".
    { by iApply shot_idemp. }
  wp_faa. wp_seq.
  iModIntro. iApply "HΦ".
  iFrame. iRight. iFrame.
Qed.

Lemma incr_inner_failed_spec (ℓ : loc) (flag : loc) (n : Z) (γ : gname):
  {{{ flag ↦ #true ∗
      ℓ ↦ #(n+1) ∗
      (Shot γ #(n+1)) }}}
    incr_inner #ℓ #flag
  {{{ RET #(); (Shot γ #(n+1)) ∗ incr_inv ℓ flag γ n }}}.
Proof.
  iIntros "%Φ [Hflag [Hl Hγ]] HΦ /=".
  iAssert ((Shot γ #(n+1)) ∗ (Shot γ #(n+1)))%I with "[Hγ]" as "[Hγ1 Hγ2]".
    { by iApply shot_idemp. }
  wp_lam. wp_let.
  wp_bind (! _)%E.
  wp_load. wp_pures.
  iModIntro. iApply "HΦ".
  iFrame. iRight. iFrame.
Qed.


Lemma incr_inv_pending (ℓ : loc) (flag : loc) (n : Z) (γ : gname):
  incr_inv ℓ flag γ n ∗ (Pending γ (1/2)%Qp) -∗
  flag ↦ #false ∗ ℓ ↦ #n ∗ (Pending γ (1/2)%Qp).
Proof.
  iIntros "[Hinv_incr Hγ1]".
  iDestruct "Hinv_incr" as "[[Hflag [Hl Hγ2]]|[Hflag [Hl Hγ2]]]".
  - iFrame.
  - by iCombine "Hγ1 Hγ2" gives %?.
Qed.

Lemma incr_inv_shot (ℓ : loc) (flag : loc) (n : Z) (γ : gname):
  incr_inv ℓ flag γ n ∗ (Shot γ #(n+1)) -∗
  flag ↦ #true ∗ ℓ ↦ #(n+1) ∗ (Shot γ #(n+1)).
Proof.
  iIntros "[Hinv_incr Hγ1]".
  iDestruct "Hinv_incr" as "[[Hflag [Hl Hγ2]]|[Hflag [Hl Hγ2]]]".
  - by iCombine "Hγ1 Hγ2" gives %?.
  - iFrame.
Qed.

Lemma incr_spec1 (lk : loc) (ℓ : loc) (flag : loc) (n : Z) (γ : gname):
  {{{ flag ↦ #false ∗ ℓ ↦ #n ∗ lk ↦ #false ∗
      (Pending γ 1%Qp) }}}
    incr #lk #ℓ #flag
  {{{ RET #(); (Shot γ #(n+1)) }}}.
Proof.
  iIntros "%Φ [Hflag [Hl [Hlk Hγ]]] HΦ /=".
  wp_lam.
  wp_let. wp_let.
  (* iMod (own_alloc (Pending 1%Qp)) as (γ) "Hγ"; first done. *)
  iDestruct (pending_split with "Hγ") as "[Hγ1 Hγ2]".
  (* iMod (inv_alloc N _ (incr_inv ℓ flag γ n) with "[Hflag Hl Hγ2]") as "#Hinv_incr".
  { iLeft. by iFrame. } *)
  iAssert (incr_inv ℓ flag γ n)%I with "[Hflag Hl Hγ2]" as "Hinv_incr".
  { iLeft. by iFrame. }
  iMod (inv_alloc basic_types.lockN _ (spinlock_inv lk ((incr_inv ℓ flag γ n))) with "[Hlk Hinv_incr]") as "#Hinv_sp".
  { iNext. iExists false. iFrame. }
  (* iMod (inv_alloc N _ (is_spinlock #lk (inv N (incr_inv ℓ flag γ n))) with "[Hinv]") as "#HN".
  { iNext. iExists lk. iSplit; first eauto. iExact "Hinv". } *)
  iAssert (is_spinlock #lk ((incr_inv ℓ flag γ n))) with "[Hinv_sp]" as "#Hinv".
  { iExists lk. iSplit; first eauto. iExact "Hinv_sp". }
  wp_bind (cpu_spin_lock _).
  wp_apply (cpu_spin_lock_spec with "Hinv").
  iIntros "[Hinv1 Hinv_incr]".
  wp_seq.
  wp_bind (incr_inner _ _).
  iDestruct "Hinv_incr" as "[[Hflag [Hl Hγ2]]|[Hflag [Hl Hγ2]]]".
  - iDestruct (pending_split with "[$Hγ1 $Hγ2]") as "Hγ".
    (* iApply incr_inner_succ_spec. *)
    wp_apply (incr_inner_succ_spec ℓ flag n γ with "[Hflag Hl Hγ]").
    { iFrame. }
    iIntros "[Hγ Hinv_incr]".
    wp_seq.
    wp_apply (cpu_spin_unlock_spec with "[Hinv1 Hinv_incr]").
    + iFrame. iApply "Hinv_incr".
    + iIntros "_". iApply "HΦ". iApply "Hγ".
  - by iCombine "Hγ1 Hγ2" gives %?.
Qed.

Lemma incr_spec (lk : loc) (ℓ : loc) (flag : loc) (n : Z) (γ : gname):
  {{{ is_spinlock #lk (incr_inv ℓ flag γ n) ∗
      (Pending γ (1/2)%Qp) }}}
    incr #lk #ℓ #flag
  {{{ RET #(); (Shot γ #(n+1)) }}}.
Proof.
  iIntros "%Φ [#Hinv Hγ1] HΦ /=".
  wp_lam.
  wp_let. wp_let.
  wp_bind (cpu_spin_lock _).
  wp_apply (cpu_spin_lock_spec with "Hinv").
  iIntros "[Hinv1 Hinv_incr]".
  wp_seq.
  wp_bind (incr_inner _ _).
  iDestruct "Hinv_incr" as "[[Hflag [Hl Hγ2]]|[Hflag [Hl Hγ2]]]".
  - iDestruct (pending_split with "[$Hγ1 $Hγ2]") as "Hγ".
    (* iApply incr_inner_succ_spec. *)
    wp_apply (incr_inner_succ_spec ℓ flag n γ with "[Hflag Hl Hγ]").
    { iFrame. }
    iIntros "[Hγ Hinv_incr]".
    wp_seq.
    wp_apply (cpu_spin_unlock_spec with "[Hinv1 Hinv_incr]").
    + iFrame. iApply "Hinv_incr".
    + iIntros "_". iApply "HΦ". iApply "Hγ".
  - by iCombine "Hγ1 Hγ2" gives %?.
Qed.

Lemma parallel_incr_spec (lk : loc) (ℓ : loc) (flag : loc) (n : Z) (γ : gname):
  {{{ is_spinlock #lk (incr_inv ℓ flag γ n) ∗
      incr_inv ℓ flag γ n ∗
      (Pending γ 1%Qp) }}}
    parallel_incr #lk #ℓ #flag
  {{{ RET #(n+1); True }}}.
Proof.
  iIntros "%Φ [#Hinv [Hinv_incr Hγ]] HΦ /=".
  iDestruct (pending_split with "Hγ") as "[Hγ1 Hγ2]".
  wp_lam. wp_let. wp_let.
  wp_smart_apply (wp_par (λ _ , (Shot γ #(n+1))) (λ _ , (Shot γ #(n+1))) with "[Hγ1] [Hγ2]").
  - wp_apply (incr_spec with "[Hinv Hγ1]").
    + iFrame. iApply "Hinv".
    + iIntros "Hγ". iApply "Hγ".
  - wp_apply (incr_spec with "[Hinv Hγ2]").
    + iFrame. iApply "Hinv".
    + iIntros "Hγ". iApply "Hγ".
  - iIntros (v1 v2) "[Hγ1 Hγ2]".
    iModIntro. wp_seq.
    iAssert (flag ↦ #true ∗ ℓ ↦ #(n+1) ∗ (Shot γ #(n+1)))%I with "[Hinv_incr Hγ1]" as "[Hflag [Hl Hγ3]]".
    { iApply incr_inv_shot. iFrame. }
    wp_load. iModIntro. iApply "HΦ". done.
Qed.

