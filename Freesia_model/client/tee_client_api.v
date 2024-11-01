From iris.algebra Require Import excl_auth frac_auth numbers.
From iris.base_logic.lib Require Import invariants.
From iris.heap_lang Require Import lib.par proofmode notation.

From lib Require Import basic_types.
From lib Require Import oneshot.
From core.kernel Require Import spinlock.
From core.kernel Require Import mutex.

Context `{!heapGS Σ, !oneshotG Σ, !spawnG Σ}.

Definition is_valid_state (state : System_State) : iProp Σ :=
  is_pointer state.(g_fd) ∗
  is_valid_mutex state.(g_mutex).

Definition is_valid_ctx (ctx : TEEC_Context) : iProp Σ :=
  is_pointer ctx.(ctx_imp).(ctx_fd) ∗
  is_pointer_b ctx.(ctx_imp).(is_initialized).

Parameter is_eq : Prop -> Prop -> Prop.
Parameter is_eq_dec : forall x y, { is_eq x y } + { ~ is_eq x y }.

Definition teec_open_dev : val :=
  λ: "fd", FAA "fd" #1.

Definition close : val :=
  λ: "fd", CAS "fd" !"fd" #0.

Definition TEEC_InitializeContext_inner : val :=
  λ: "flag" "fd" "ctx_fd",
  if: !"flag" then
    #()
  else
    teec_open_dev "fd";;
    "ctx_fd" = ref (!"fd");;
    "flag" <- #true.

Definition TEEC_InitializeContext (ctx : TEEC_Context) (s : System_State) : expr :=
  let fd := s.(g_fd) in
  let mutex := s.(g_mutex) in
  let ctx_fd := ctx.(ctx_imp).(ctx_fd) in
  let is_initialized := ctx.(ctx_imp).(is_initialized) in
    mutex_lock mutex;;
    TEEC_InitializeContext_inner #is_initialized #fd #ctx_fd;;
    mutex_unlock mutex.

Definition TEEC_InitializeContext_par (ctx : TEEC_Context) (s : System_State): expr :=
  let fd := s.(g_fd) in
  ( TEEC_InitializeContext ctx s)
  |||
  ( TEEC_InitializeContext ctx s)
  ;;
  ! (#fd).

Definition TEEC_FinalizeContext_inner : val :=
  λ: "flag" "fd",
  if: !"flag" then
    close "fd";;
    "flag" <- #false
  else
    #().

Definition TEEC_FinalizeContext (ctx : TEEC_Context) (s : System_State) : expr :=
  let fd := ctx.(ctx_imp).(ctx_fd) in
  let mutex := s.(g_mutex) in
  let is_initialized := ctx.(ctx_imp).(is_initialized) in
    (* mutex_lock mutex;; *)
    mutex_lock mutex;;
    TEEC_FinalizeContext_inner #is_initialized #fd;;
    mutex_unlock mutex.

Definition TEEC_FinalizeContext_par (ctx : TEEC_Context) (s : System_State): expr :=
  let fd := ctx.(ctx_imp).(ctx_fd) in
  ( TEEC_FinalizeContext ctx s)
  |||
  ( TEEC_FinalizeContext ctx s)
  ;;
  ! (#fd).


Section TEEC_InitializeContext_Spec.

Definition initialize_ctx_inv (γ : gname) (flag : loc) (fd : loc) (n : Z) : iProp Σ :=
    (flag ↦ #false ∗ fd ↦ #n ∗ (Pending γ (1/2)%Qp)
  ∨ flag ↦ #true ∗ fd ↦ #(n+1) ∗ (Shot γ #(n+1)))%I.

Lemma initialize_ctx_inv_pending (γ : gname) (flag : loc) (fd : loc) (n : Z):
  initialize_ctx_inv γ flag fd n ∗ (Pending γ (1/2)%Qp) -∗
  flag ↦ #false ∗ fd ↦ #n ∗ (Pending γ (1/2)%Qp).
Proof.
  iIntros "[Hinv_fd Hγ1]".
  iDestruct "Hinv_fd" as "[[Hflag [Hl Hγ2]]|[Hflag [Hl Hγ2]]]".
  - iFrame.
  - by iCombine "Hγ1 Hγ2" gives %?.
Qed.

Lemma initialize_ctx_inv_shot (γ : gname) (flag : loc) (fd : loc) (n : Z):
  initialize_ctx_inv γ flag fd n ∗ (Shot γ #(n+1)) -∗
  flag ↦ #true ∗ fd ↦ #(n+1) ∗ (Shot γ #(n+1)).
Proof.
  iIntros "[Hinv_fd Hγ1]".
  iDestruct "Hinv_fd" as "[[Hflag [Hl Hγ2]]|[Hflag [Hl Hγ2]]]".
  - by iCombine "Hγ1 Hγ2" gives %?.
  - iFrame.
Qed.

Lemma TEEC_InitializeContext_inner_succ_spec γ (flag : loc) (fd : loc) (ctx_fd : loc) (n : Z):
  {{{ flag ↦ #false ∗ fd ↦ #n ∗ Pending γ 1%Qp }}}
    TEEC_InitializeContext_inner #flag #fd #ctx_fd
  {{{ RET #(); Shot γ #(n+1) ∗ initialize_ctx_inv γ flag fd n }}}.
Proof.
  iIntros "%Φ [Hflag [Hfd Hγ]] HΦ /=".
  wp_lam. wp_let. wp_let.
  wp_bind (! _)%E.
  wp_load. wp_pures. wp_lam. wp_faa.
  iMod (pending_shoot _ #(n+1) with "Hγ") as "Hγ".
  iAssert ((Shot γ #(n+1)) ∗ (Shot γ #(n+1)))%I with "[Hγ]" as "[Hγ1 Hγ2]".
  { by iApply shot_idemp. }
  wp_seq.
  wp_bind (! _)%E.
  wp_load.
  wp_bind (ref _)%E.
  wp_alloc cfd as "Hcfd".
  wp_pures. wp_store.
  iModIntro. iApply "HΦ".
  iFrame. iRight. iFrame.
Qed.

Lemma TEEC_InitializeContext_inner_failed_spec γ (flag : loc) (fd : loc) (ctx_fd : loc) (n : Z):
  {{{ flag ↦ #true ∗ fd ↦ #(n+1) ∗ Shot γ #(n+1) }}}
    TEEC_InitializeContext_inner #flag #fd #ctx_fd
  {{{ RET #(); Shot γ #(n+1) ∗ initialize_ctx_inv γ flag fd n }}}.
Proof.
  iIntros "%Φ [Hflag [Hfd Hγ]] HΦ /=".
  wp_lam. wp_let. wp_let.
  wp_bind (! _)%E.
  wp_load. wp_pures.
  iAssert ((Shot γ #(n+1)) ∗ (Shot γ #(n+1)))%I with "[Hγ]" as "[Hγ1 Hγ2]".
  { by iApply shot_idemp. }
  iModIntro. iApply "HΦ".
  iFrame. iRight. iFrame.
Qed.

Lemma TEEC_InitializeContext_succ_spec γ ctx s (n:Z):
  {{{
      is_mutex (g_mutex s) (initialize_ctx_inv γ ctx.(ctx_imp).(is_initialized) (g_fd s) n) ∗
      ctx.(ctx_imp).(is_initialized) ↦ #false ∗
      Pending γ (1/2)%Qp
  }}}
    TEEC_InitializeContext ctx s
  {{{
      RET #();
      Shot γ #(n+1)
  }}}.
Proof.
  iIntros (Φ) "[#Hmutex [Hflag Hγ1]] Post".
  unfold TEEC_InitializeContext.
  wp_bind (mutex_lock _).
  wp_smart_apply (mutex_lock_spec with "Hmutex").
  iIntros "[_ Hinv_fd]".
  wp_seq.
  iDestruct "Hinv_fd" as "[[H [Hfd Hγ2]]|[_ [Hfd Hγ2]]]".
  - iDestruct (pending_split with "[$Hγ1 $Hγ2]") as "Hγ".
    wp_bind (TEEC_InitializeContext_inner _ _ _).
    wp_apply (TEEC_InitializeContext_inner_succ_spec γ with "[Hflag Hfd Hγ]").
    { iFrame. }
    iIntros "[Hγ Hinv_fd]".
    wp_seq.
    wp_smart_apply (mutex_unlock_spec (g_mutex s) (initialize_ctx_inv γ ctx.(ctx_imp).(is_initialized) (g_fd s) n) with "[Hinv_fd]"); [auto|].
    iIntros "_".
    iApply "Post".
    iFrame.
  - by iCombine "Hγ1 Hγ2" gives %?.
Qed.

Lemma TEEC_InitializeContext_failed_spec γ ctx s n:
  {{{
      is_mutex (g_mutex s) (initialize_ctx_inv γ ctx.(ctx_imp).(is_initialized) (g_fd s) n) ∗
      ctx.(ctx_imp).(is_initialized) ↦ #true
  }}}
    TEEC_InitializeContext ctx s
  {{{
      RET #();
      Shot γ #(n+1)
  }}}.
Proof.
  iIntros (Φ) "[#Hmutex Hflag] Post".
  unfold TEEC_InitializeContext.
  wp_bind (mutex_lock _).
  wp_smart_apply (mutex_lock_spec with "Hmutex").
  iIntros "[_ Hinv_fd]".
  wp_seq.
  iDestruct "Hinv_fd" as "[[H [Hfd Hγ2]]|[_ [Hfd Hγ2]]]".
  - iAssert (False)%I with "[H Hflag]" as %[].
    { iApply (pointsto_exclusive (is_initialized (ctx_imp ctx))). iFrame. }
  - wp_bind (TEEC_InitializeContext_inner _ _ _).
    wp_apply (TEEC_InitializeContext_inner_failed_spec with "[Hflag Hfd Hγ2]").
    { iFrame. }
    iIntros "[Hγ Hinv_fd]".
    wp_seq.
    wp_bind (mutex_unlock _).
    wp_smart_apply (mutex_unlock_spec (g_mutex s) (initialize_ctx_inv γ ctx.(ctx_imp).(is_initialized) (g_fd s) n) with "[Hinv_fd]"); [auto|].
    iIntros "_".
    iApply "Post".
    iFrame.
Qed.

Lemma TEEC_InitializeContext_spec γ ctx s n:
  {{{ 
      is_mutex (g_mutex s) (initialize_ctx_inv γ ctx.(ctx_imp).(is_initialized) (g_fd s) n) ∗
      (Pending γ (1/2)%Qp)
  }}}
    TEEC_InitializeContext ctx s
  {{{ RET #(); (Shot γ #(n+1)) }}}.
Proof.
  iIntros "%Φ [#Hmutex Hγ1] Post /=".
  unfold TEEC_InitializeContext.
  wp_bind (mutex_lock _).
  wp_smart_apply (mutex_lock_spec with "Hmutex").
  iIntros "[_ Hinv_fd]".
  wp_seq.
  iDestruct "Hinv_fd" as "[[Hflag [Hfd Hγ2]]|[Hflag [Hfd Hγ2]]]".
  - iDestruct (pending_split with "[$Hγ1 $Hγ2]") as "Hγ".
    wp_bind (TEEC_InitializeContext_inner _ _ _).
    wp_apply (TEEC_InitializeContext_inner_succ_spec γ with "[Hflag Hfd Hγ]").
    { iFrame. }
    iIntros "[Hγ Hinv_fd]".
    wp_seq.
    wp_smart_apply (mutex_unlock_spec (g_mutex s) (initialize_ctx_inv γ ctx.(ctx_imp).(is_initialized) (g_fd s) n) with "[Hinv_fd]"); [auto|].
    iIntros "_".
    iApply "Post".
    iFrame.
  - wp_bind (TEEC_InitializeContext_inner _ _ _).
    wp_apply (TEEC_InitializeContext_inner_failed_spec γ with "[Hflag Hfd Hγ2]").
    { iFrame. }
    iIntros "[Hγ Hinv_fd]".
    wp_seq.
    wp_smart_apply (mutex_unlock_spec (g_mutex s) (initialize_ctx_inv γ ctx.(ctx_imp).(is_initialized) (g_fd s) n) with "[Hinv_fd]"); [auto|].
    iIntros "_". iApply "Post". iFrame.
Qed.

Lemma TEEC_InitializeContext_par_spec γ ctx s n:
  {{{
      is_mutex (g_mutex s) (initialize_ctx_inv γ ctx.(ctx_imp).(is_initialized) (g_fd s) n) ∗
      initialize_ctx_inv γ ctx.(ctx_imp).(is_initialized) (g_fd s) n ∗
      Pending γ 1%Qp
  }}}
    TEEC_InitializeContext_par ctx s
  {{{ RET #(n+1); True }}}.
Proof.
  iIntros "%Φ [#Hinv [Hinv_fd Hγ]] HΦ /=".
  iDestruct (pending_split with "Hγ") as "[Hγ1 Hγ2]".
  unfold TEEC_InitializeContext_par.
  wp_smart_apply (wp_par (λ _ , (Shot γ #(n+1))) (λ _ , (Shot γ #(n+1))) with "[Hγ1] [Hγ2]").
  - wp_apply (TEEC_InitializeContext_spec with "[Hinv Hγ1]").
    + iFrame. iApply "Hinv".
    + iIntros "Hγ". iApply "Hγ".
  - wp_apply (TEEC_InitializeContext_spec with "[Hinv Hγ2]").
    + iFrame. iApply "Hinv".
    + iIntros "Hγ". iApply "Hγ".
  - iIntros (v1 v2) "[Hγ1 Hγ2]".
    iNext. wp_seq.
    iAssert ((is_initialized (ctx_imp ctx)) ↦ #true ∗ (g_fd s) ↦ #(n+1) ∗ (Shot γ #(n+1)))%I with "[Hinv_fd Hγ1]" as "[Hflag [Hfd Hγ3]]".
    { iApply initialize_ctx_inv_shot. iFrame. }
    wp_load. iModIntro. iApply "HΦ". done.
Qed.

End TEEC_InitializeContext_Spec.


Section TEEC_FinalizeContext_Spec.

Definition finalize_ctx_inv (γ : gname) (flag : loc) (fd : loc) (n : Z) : iProp Σ :=
    (flag ↦ #true ∗ fd ↦ #n ∗ (Pending γ (1/2)%Qp)
  ∨ flag ↦ #false ∗ fd ↦ #0 ∗ (Shot γ #0))%I.

Lemma finalize_ctx_inv_pending (γ : gname) (flag : loc) (fd : loc) (n : Z):
  finalize_ctx_inv γ flag fd n ∗ (Pending γ (1/2)%Qp) -∗
  flag ↦ #true ∗ fd ↦ #n ∗ (Pending γ (1/2)%Qp).
Proof.
  iIntros "[Hinv_fd Hγ1]".
  iDestruct "Hinv_fd" as "[[Hflag [Hl Hγ2]]|[Hflag [Hl Hγ2]]]".
  - iFrame.
  - by iCombine "Hγ1 Hγ2" gives %?.
Qed.

Lemma finalize_ctx_inv_shot (γ : gname) (flag : loc) (fd : loc) (n : Z):
  finalize_ctx_inv γ flag fd n ∗ (Shot γ #0) -∗
  flag ↦ #false ∗ fd ↦ #0 ∗ (Shot γ #0).
Proof.
  iIntros "[Hinv_fd Hγ1]".
  iDestruct "Hinv_fd" as "[[Hflag [Hl Hγ2]]|[Hflag [Hl Hγ2]]]".
  - by iCombine "Hγ1 Hγ2" gives %?.
  - iFrame.
Qed.

Lemma TEEC_FinalizeContext_inner_succ_spec γ (flag : loc) (fd : loc) (n : Z):
  {{{ flag ↦ #true ∗ fd ↦ #n ∗ Pending γ 1%Qp }}}
    TEEC_FinalizeContext_inner #flag #fd
  {{{ RET #(); Shot γ #0 ∗ finalize_ctx_inv γ flag fd n }}}.
Proof.
  iIntros "%Φ [Hflag [Hfd Hγ]] HΦ /=".
  wp_lam. wp_let.
  wp_bind (! _)%E. wp_load.
  wp_pures. wp_lam.
  wp_bind (! _)%E. wp_load.
  wp_bind (CmpXchg _ _ _).
  wp_cmpxchg_suc. wp_pures. wp_store.
  iMod (pending_shoot _ #0 with "Hγ") as "Hγ".
  iAssert ((Shot γ #0) ∗ (Shot γ #0))%I with "[Hγ]" as "[Hγ1 Hγ2]".
  { by iApply shot_idemp. }
  iModIntro. iApply "HΦ".
  iFrame. iRight. iFrame.
Qed.

Lemma TEEC_FinalizeContext_inner_failed_spec γ (flag : loc) (fd : loc) (n : Z):
  {{{ flag ↦ #false ∗ fd ↦ #0 ∗ Shot γ #0 }}}
    TEEC_FinalizeContext_inner #flag #fd
  {{{ RET #(); Shot γ #0 ∗ finalize_ctx_inv γ flag fd n }}}.
Proof.
  iIntros "%Φ [Hflag [Hfd Hγ]] HΦ /=".
  wp_lam. wp_let.
  wp_bind (! _)%E.
  wp_load. wp_pures.
  iAssert ((Shot γ #0) ∗ (Shot γ #0))%I with "[Hγ]" as "[Hγ1 Hγ2]".
  { by iApply shot_idemp. }
  iModIntro. iApply "HΦ".
  iFrame. iRight. iFrame.
Qed.

Lemma TEEC_FinalizeContext_succ_spec γ ctx s (n:Z):
  {{{
      is_mutex (g_mutex s) (finalize_ctx_inv γ ctx.(ctx_imp).(is_initialized) (ctx_fd (ctx_imp ctx)) n) ∗
      ctx.(ctx_imp).(is_initialized) ↦ #true ∗
      Pending γ (1/2)%Qp
  }}}
    TEEC_FinalizeContext ctx s
  {{{
      RET #();
      Shot γ #0
  }}}.
Proof.
  iIntros (Φ) "[#Hmutex [Hflag Hγ1]] Post".
  unfold TEEC_FinalizeContext.
  wp_bind (mutex_lock _).
  wp_smart_apply (mutex_lock_spec with "Hmutex").
  iIntros "[_ Hinv_fd]".
  wp_seq.
  iDestruct "Hinv_fd" as "[[H [Hfd Hγ2]]|[_ [Hfd Hγ2]]]".
  - iDestruct (pending_split with "[$Hγ1 $Hγ2]") as "Hγ".
    wp_bind (TEEC_FinalizeContext_inner _ _).
    wp_apply (TEEC_FinalizeContext_inner_succ_spec γ with "[Hflag Hfd Hγ]").
    { iFrame. }
    iIntros "[Hγ Hinv_fd]".
    wp_seq.
    wp_smart_apply (mutex_unlock_spec (g_mutex s) (finalize_ctx_inv γ ctx.(ctx_imp).(is_initialized) (ctx_fd (ctx_imp ctx)) n) with "[Hinv_fd]"); [auto|].
    iIntros "_".
    iApply "Post".
    iFrame.
  - by iCombine "Hγ1 Hγ2" gives %?.
Qed.

Lemma TEEC_FinalizeContext_failed_spec γ ctx s n:
  {{{
      is_mutex (g_mutex s) (finalize_ctx_inv γ ctx.(ctx_imp).(is_initialized) (ctx_fd (ctx_imp ctx)) n) ∗
      ctx.(ctx_imp).(is_initialized) ↦ #false
  }}}
    TEEC_FinalizeContext ctx s
  {{{
      RET #();
      Shot γ #0
  }}}.
Proof.
  iIntros (Φ) "[#Hmutex Hflag] Post".
  unfold TEEC_FinalizeContext.
  wp_bind (mutex_lock _).
  wp_smart_apply (mutex_lock_spec with "Hmutex").
  iIntros "[_ Hinv_fd]".
  wp_seq.
  iDestruct "Hinv_fd" as "[[H [Hfd Hγ2]]|[_ [Hfd Hγ2]]]".
  - iAssert (False)%I with "[H Hflag]" as %[].
    { iApply (pointsto_exclusive (is_initialized (ctx_imp ctx))). iFrame. }
  - wp_bind (TEEC_FinalizeContext_inner _ _).
    wp_apply (TEEC_FinalizeContext_inner_failed_spec with "[Hflag Hfd Hγ2]").
    { iFrame. }
    iIntros "[Hγ Hinv_fd]".
    wp_seq.
    wp_bind (mutex_unlock _).
    wp_smart_apply (mutex_unlock_spec (g_mutex s) (finalize_ctx_inv γ ctx.(ctx_imp).(is_initialized) (ctx_fd (ctx_imp ctx)) n) with "[Hinv_fd]"); [auto|].
    iIntros "_".
    iApply "Post".
    iFrame.
Qed.

Lemma TEEC_FinalizeContext_spec γ ctx s n:
  {{{ 
      is_mutex (g_mutex s) (finalize_ctx_inv γ ctx.(ctx_imp).(is_initialized) (ctx_fd (ctx_imp ctx)) n) ∗
      (Pending γ (1/2)%Qp)
  }}}
    TEEC_FinalizeContext ctx s
  {{{ RET #(); (Shot γ #0) }}}.
Proof.
  iIntros "%Φ [#Hmutex Hγ1] Post /=".
  unfold TEEC_FinalizeContext.
  wp_bind (mutex_lock _).
  wp_smart_apply (mutex_lock_spec with "Hmutex").
  iIntros "[_ Hinv_fd]".
  wp_seq.
  iDestruct "Hinv_fd" as "[[Hflag [Hfd Hγ2]]|[Hflag [Hfd Hγ2]]]".
  - iDestruct (pending_split with "[$Hγ1 $Hγ2]") as "Hγ".
    wp_bind (TEEC_FinalizeContext_inner _ _).
    wp_apply (TEEC_FinalizeContext_inner_succ_spec γ with "[Hflag Hfd Hγ]").
    { iFrame. }
    iIntros "[Hγ Hinv_fd]".
    wp_seq.
    wp_smart_apply (mutex_unlock_spec (g_mutex s) (finalize_ctx_inv γ ctx.(ctx_imp).(is_initialized) (ctx_fd (ctx_imp ctx)) n) with "[Hinv_fd]"); [auto|].
    iIntros "_". iApply "Post". iFrame.
  - wp_bind (TEEC_FinalizeContext_inner _ _).
    wp_apply (TEEC_FinalizeContext_inner_failed_spec γ with "[Hflag Hfd Hγ2]").
    { iFrame. }
    iIntros "[Hγ Hinv_fd]".
    wp_seq.
    wp_smart_apply (mutex_unlock_spec (g_mutex s) (finalize_ctx_inv γ ctx.(ctx_imp).(is_initialized) (ctx_fd (ctx_imp ctx)) n) with "[Hinv_fd]"); [auto|].
    iIntros "_". iApply "Post". iFrame.
Qed.

Lemma TEEC_FinalizeContext_par_spec γ ctx s n:
  {{{
      is_mutex (g_mutex s) (finalize_ctx_inv γ ctx.(ctx_imp).(is_initialized) (ctx_fd (ctx_imp ctx)) n) ∗
      finalize_ctx_inv γ ctx.(ctx_imp).(is_initialized) (ctx_fd (ctx_imp ctx)) n ∗
      Pending γ 1%Qp
  }}}
    TEEC_FinalizeContext_par ctx s
  {{{ RET #0; True }}}.
Proof.
  iIntros "%Φ [#Hinv [Hinv_fd Hγ]] HΦ /=".
  iDestruct (pending_split with "Hγ") as "[Hγ1 Hγ2]".
  unfold TEEC_FinalizeContext_par.
  wp_smart_apply (wp_par (λ _ , (Shot γ #0)) (λ _ , (Shot γ #0)) with "[Hγ1] [Hγ2]").
  - wp_apply (TEEC_FinalizeContext_spec with "[Hinv Hγ1]").
    + iFrame. iApply "Hinv".
    + iIntros "Hγ". iApply "Hγ".
  - wp_apply (TEEC_FinalizeContext_spec with "[Hinv Hγ2]").
    + iFrame. iApply "Hinv".
    + iIntros "Hγ". iApply "Hγ".
  - iIntros (v1 v2) "[Hγ1 Hγ2]".
    iNext. wp_pures.
    iAssert ((is_initialized (ctx_imp ctx)) ↦ #false ∗ (ctx_fd (ctx_imp ctx)) ↦ #0 ∗ (Shot γ #0))%I with "[Hinv_fd Hγ1]" as "[Hflag [Hfd Hγ3]]".
    { iApply finalize_ctx_inv_shot. iFrame. }
    wp_load. iModIntro. iApply "HΦ". done.
Qed.

End TEEC_FinalizeContext_Spec.
