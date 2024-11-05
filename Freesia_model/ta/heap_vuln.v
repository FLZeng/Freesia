From iris.algebra Require Import excl_auth frac_auth numbers.
From iris.base_logic.lib Require Import invariants.
From iris.heap_lang Require Import lib.par proofmode notation.

From lib Require Import basic_types.
From lib Require Import oneshot.
From core.kernel Require Import spinlock.
From core.kernel Require Import mutex.

Context `{!heapGS Σ, !oneshotG Σ, !spawnG Σ}.

Record User := mkUser {
  username : loc;
  password : loc;
  is_valid : loc;
}.

Definition user_exit_inner : val :=
  λ: "flag" "username",
  if: !"flag" then
    Free "username";;
    "flag" <- #false
  else
    #().

Definition user_exit (user : User) (s : System_State) : expr :=
  let username := user.(username) in
  let mutex := s.(g_mutex) in
  let is_valid := user.(is_valid) in
    mutex_lock mutex;;
    user_exit_inner #is_valid #username;;
    mutex_unlock mutex.

Definition user_exit_par (user : User) (s : System_State): expr :=
  (user_exit user s)
  |||
  (user_exit user s).


Section User_Exit_Spec.

Definition valid_user_inv (γ : gname) (flag : loc) (username : loc) (v : val) : iProp Σ :=
    (flag ↦ #true ∗ username ↦ v ∗ (Pending γ (1/2)%Qp)
  ∨ flag ↦ #false ∗ (Shot γ #0))%I.

Lemma valid_user_inv_pending (γ : gname) (flag : loc) (username : loc) (v : val):
  valid_user_inv γ flag username v ∗ (Pending γ (1/2)%Qp) -∗
  flag ↦ #true ∗ username ↦ v ∗ (Pending γ (1/2)%Qp).
Proof.
  iIntros "[Hinv_name Hγ1]".
  iDestruct "Hinv_name" as "[[Hflag [Hl Hγ2]]|[Hflag Hγ2]]".
  - iFrame.
  - by iCombine "Hγ1 Hγ2" gives %?.
Qed.

Lemma valid_user_inv_shot (γ : gname) (flag : loc) (username : loc) (v : val):
  valid_user_inv γ flag username v ∗ (Shot γ #0) -∗
  flag ↦ #false ∗ (Shot γ #0).
Proof.
  iIntros "[Hinv_name Hγ1]".
  iDestruct "Hinv_name" as "[[Hflag [Hl Hγ2]]|[Hflag Hγ2]]".
  - by iCombine "Hγ1 Hγ2" gives %?.
  - iFrame.
Qed.

Lemma user_exit_inner_succ_spec γ (flag : loc) (username : loc) (v : val):
  {{{ flag ↦ #true ∗ username ↦ v ∗ Pending γ 1%Qp }}}
    user_exit_inner #flag #username
  {{{ RET #(); Shot γ #0 ∗ valid_user_inv γ flag username v }}}.
Proof.
  iIntros "%Φ [Hflag [Hname Hγ]] HΦ /=".
  wp_lam. wp_let.
  wp_bind (! _)%E.
  wp_load. wp_pures. wp_free.
  iMod (pending_shoot _ #0 with "Hγ") as "Hγ".
  iAssert ((Shot γ #0) ∗ (Shot γ #0))%I with "[Hγ]" as "[Hγ1 Hγ2]".
  { by iApply shot_idemp. }
  wp_seq. wp_store.
  iModIntro. iApply "HΦ".
  iFrame. iRight. iFrame.
Qed.

Lemma user_exit_inner_failed_spec γ (flag : loc) (username : loc) (v : val):
  {{{ flag ↦ #false ∗ Shot γ #0 }}}
    user_exit_inner #flag #username
  {{{ RET #(); Shot γ #0 ∗ valid_user_inv γ flag username v }}}.
Proof.
  iIntros "%Φ [Hflag Hγ] HΦ /=".
  wp_lam. wp_let.
  wp_bind (! _)%E.
  wp_load. wp_pures.
  iAssert ((Shot γ #0) ∗ (Shot γ #0))%I with "[Hγ]" as "[Hγ1 Hγ2]".
  { by iApply shot_idemp. }
  iModIntro. iApply "HΦ".
  iFrame. iRight. iFrame.
Qed.

Lemma user_exit_succ_spec γ user s (v : val):
  {{{
      is_mutex (g_mutex s) (valid_user_inv γ user.(is_valid) user.(username) v) ∗
      user.(is_valid) ↦ #true ∗
      Pending γ (1/2)%Qp
  }}}
    user_exit user s
  {{{
      RET #();
      Shot γ #0
  }}}.
Proof.
  iIntros (Φ) "[#Hmutex [Hflag Hγ1]] Post".
  unfold user_exit.
  wp_bind (mutex_lock _).
  wp_smart_apply (mutex_lock_spec with "Hmutex").
  iIntros "[_ Hinv_name]".
  wp_seq.
  iDestruct "Hinv_name" as "[[H [Hname Hγ2]]|[_ Hγ2]]".
  - iDestruct (pending_split with "[$Hγ1 $Hγ2]") as "Hγ".
    wp_bind (user_exit_inner _ _).
    wp_apply (user_exit_inner_succ_spec γ with "[Hflag Hname Hγ]").
    { iFrame. }
    iIntros "[Hγ Hinv_name]".
    wp_seq.
    wp_smart_apply (mutex_unlock_spec (g_mutex s) (valid_user_inv γ user.(is_valid) user.(username) v) with "[Hinv_name]"); [auto|].
    iIntros "_".
    iApply "Post".
    iFrame.
  - by iCombine "Hγ1 Hγ2" gives %?.
Qed.

Lemma user_exit_failed_spec γ user s (v : val):
  {{{
      is_mutex (g_mutex s) (valid_user_inv γ user.(is_valid) user.(username) v) ∗
      user.(is_valid) ↦ #false
  }}}
    user_exit user s
  {{{
      RET #();
      Shot γ #0
  }}}.
Proof.
  iIntros (Φ) "[#Hmutex Hflag] Post".
  unfold user_exit.
  wp_bind (mutex_lock _).
  wp_smart_apply (mutex_lock_spec with "Hmutex").
  iIntros "[_ Hinv_name]".
  wp_seq.
  iDestruct "Hinv_name" as "[[H [Hname Hγ2]]|[_ Hγ2]]".
  - iAssert (False)%I with "[H Hflag]" as %[].
    { iApply (pointsto_exclusive (user.(is_valid))). iFrame. }
  - wp_bind (user_exit_inner _ _).
    wp_apply (user_exit_inner_failed_spec with "[Hflag Hγ2]").
    { iFrame. }
    iIntros "[Hγ Hinv_name]".
    wp_seq.
    wp_bind (mutex_unlock _).
    wp_smart_apply (mutex_unlock_spec (g_mutex s) (valid_user_inv γ user.(is_valid) user.(username) v) with "[Hinv_name]"); [auto|].
    iIntros "_".
    iApply "Post".
    iFrame.
Qed.

Lemma user_exit_spec γ user s v:
  {{{
      is_mutex (g_mutex s) (valid_user_inv γ user.(is_valid) user.(username) v) ∗
      (Pending γ (1/2)%Qp)
  }}}
    user_exit user s
  {{{ RET #(); (Shot γ #0) }}}.
Proof.
  iIntros "%Φ [#Hmutex Hγ1] Post /=".
  unfold user_exit.
  wp_bind (mutex_lock _).
  wp_smart_apply (mutex_lock_spec with "Hmutex").
  iIntros "[_ Hinv_name]".
  wp_seq.
  iDestruct "Hinv_name" as "[[Hflag [Hname Hγ2]]|[Hflag Hγ2]]".
  - iDestruct (pending_split with "[$Hγ1 $Hγ2]") as "Hγ".
    wp_bind (user_exit_inner _ _).
    wp_apply (user_exit_inner_succ_spec γ with "[Hflag Hname Hγ]").
    { iFrame. }
    iIntros "[Hγ Hinv_name]".
    wp_seq.
    wp_smart_apply (mutex_unlock_spec (g_mutex s) (valid_user_inv γ user.(is_valid) user.(username) v) with "[Hinv_name]"); [auto|].
    iIntros "_".
    iApply "Post".
    iFrame.
  - wp_bind (user_exit_inner _ _).
    wp_apply (user_exit_inner_failed_spec with "[Hflag Hγ2]").
    { iFrame. }
    iIntros "[Hγ Hinv_name]".
    wp_seq.
    wp_smart_apply (mutex_unlock_spec (g_mutex s) (valid_user_inv γ user.(is_valid) user.(username) v) with "[Hinv_name]"); [auto|].
    iIntros "_". iApply "Post". iFrame.
Qed.

Lemma user_exit_par_spec γ user s v:
  {{{
      is_mutex (g_mutex s) (valid_user_inv γ user.(is_valid) user.(username) v) ∗
      valid_user_inv γ user.(is_valid) user.(username) v ∗
      Pending γ 1%Qp
  }}}
    user_exit_par user s
  {{{ w, RET w; True }}}.
Proof.
  iIntros "%Φ [#Hinv [Hinv_name Hγ]] HΦ /=".
  iDestruct (pending_split with "Hγ") as "[Hγ1 Hγ2]".
  unfold user_exit_par.
  wp_smart_apply (wp_par (λ _ , (Shot γ #0)) (λ _ , (Shot γ #0)) with "[Hγ1] [Hγ2]").
  - wp_apply (user_exit_spec with "[Hinv Hγ1]").
    + iFrame. iApply "Hinv".
    + iIntros "Hγ". iApply "Hγ".
  - wp_apply (user_exit_spec with "[Hinv Hγ2]").
    + iFrame. iApply "Hinv".
    + iIntros "Hγ". iApply "Hγ".
  - iIntros (v1 v2) "[Hγ1 Hγ2]".
    iNext. iApply "HΦ". done.
Qed.

End User_Exit_Spec.