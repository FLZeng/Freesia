From iris.base_logic.lib Require Import invariants.
From iris.heap_lang Require Import proofmode notation.

From lib Require Import basic_types.

Definition cpu_spin_init : val := λ: "l",
  (* ref #SPINLOCK_UNLOCK. *)
  "l" <- #false.

Definition cpu_spin_trylock : val := λ: "l",
  (* CAS "l" #SPINLOCK_UNLOCK #SPINLOCK_LOCK. *)
  CAS "l" #false #true.

Definition cpu_spin_lock : val :=
  rec: "cpu_spin_lock" "l" :=
    if: cpu_spin_trylock "l" then
      #()
    else
      "cpu_spin_lock" "l".

Definition cpu_spin_unlock : val := λ: "l",
  (* "l" <- #SPINLOCK_UNLOCK. *)
  (* CmpXchg "l" #true #false;;
  #(). *)
  "l" <- #false.


Section proof.

Context `{!heapGS Σ}.

Definition is_pointer (l : loc) : iProp Σ :=
  ∃ v : val, l ↦ v.

Definition spinlock_inv (l : loc) (R : iProp Σ) : iProp Σ :=
  ∃ b : bool, l ↦ #b ∗ if b then True else R.

Definition is_spinlock (lk : val) (R : iProp Σ) : iProp Σ :=
  ∃ l: loc, ⌜ lk = #l ⌝ ∧ inv lockN (spinlock_inv l R).

Lemma cpu_spin_init_spec (l : loc) (R : iProp Σ):
  {{{ is_pointer l ∗ R }}}
    cpu_spin_init #l
  {{{ RET #(); is_spinlock #l R }}}.
Proof.
  iIntros (Φ) "[Hl HR] HΦ".
  iDestruct "Hl" as (v) "Hl".
  iApply wp_fupd.
  wp_lam.
  wp_store.
  iMod (inv_alloc lockN _ (spinlock_inv l R) with "[HR Hl]") as "#Hinv".
  - iNext.
    iExists false.
    iFrame.
  - iModIntro.
    iApply "HΦ".
    iExists l.
    eauto.
Qed.

Lemma cpu_spin_trylock_spec lk R :
  {{{ is_spinlock lk R }}}
    cpu_spin_trylock lk
  {{{ b, RET #b; if b is true then R else True }}}.
Proof.
  iIntros (Φ) "#Hl HΦ".
  iDestruct "Hl" as (l ->) "#Hinv".
  wp_rec.
  wp_bind (CmpXchg _ _ _).
  iInv lockN as (b) "[Hl HR]" "Hclose".
  destruct b.
  - wp_cmpxchg_fail.
    iMod ("Hclose" with "[Hl]") as "_".
    + iNext.
      iExists true.
      iFrame.
    + iModIntro.
      wp_proj.
      iApply ("HΦ" $! false).
      done.
  - wp_cmpxchg_suc.
    iMod ("Hclose" with "[Hl]") as "_".
    + iNext.
      iExists true.
      iFrame.
    + iModIntro.
      wp_proj.
      iApply ("HΦ" $! true with "HR").
Qed.

Lemma cpu_spin_lock_spec lk R :
  {{{ is_spinlock lk R }}}
    cpu_spin_lock lk
  {{{ RET #(); is_spinlock lk R ∗ R }}}.
Proof.
  iIntros (Φ) "#Hl HΦ".
  iLöb as "IH".
  wp_rec.
  wp_apply (cpu_spin_trylock_spec with "Hl").
  iIntros ([]).
  - iIntros "HR".
    wp_if.
    iApply ("HΦ").
    iFrame.
    done.
  - iIntros "_".
    wp_if.
    iApply ("IH" with "HΦ").
Qed.

Lemma cpu_spin_unlock_spec lk R :
  {{{ is_spinlock lk R ∗ R }}}
    cpu_spin_unlock lk
  {{{ RET #(); True }}}.
Proof.
  iIntros (Φ) "[Hlock HR] HΦ".
  iDestruct "Hlock" as (l ->) "#Hinv /=".
  wp_lam.
  iInv "Hinv" as (b) "[Hl Hb]" "Hclose".
  wp_store.
  iApply "HΦ".
  iApply "Hclose".
  iNext.
  iExists false.
  iFrame.
Qed.
End proof.