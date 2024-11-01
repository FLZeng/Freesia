From iris.algebra Require Import frac agree csum.
From iris.proofmode Require Import tactics.
From iris.program_logic Require Export weakestpre.
From iris.heap_lang Require Export lang.
From iris.heap_lang Require Import assert proofmode notation adequacy.
From iris.heap_lang.lib Require Import par.
From iris.prelude Require Import options.


Definition oneshotR := csumR fracR (agreeR valO).
Class oneshotG Σ := { oneshot_inG : inG Σ oneshotR }.
Definition oneshotΣ : gFunctors := #[GFunctor oneshotR].
Global Instance subG_oneshotΣ {Σ} : subG oneshotΣ Σ → oneshotG Σ.
Proof. solve_inG. Qed.
Global Existing Instance oneshot_inG.

Definition Pending `{oneshotG Σ} γ (q : Qp) :=
  own γ (Cinl q).
Definition Shot `{oneshotG Σ} γ (v : val) :=
  own γ (Cinr (to_agree v)).

Lemma new_pending `{oneshotG Σ} :
  ⊢ |==> ∃ γ, Pending γ 1%Qp.
Proof.
  by apply own_alloc.
Qed.

Lemma pending_split `{oneshotG Σ} γ q :
  (Pending γ q) ⊣⊢ (Pending γ (q/2)) ∗ (Pending γ (q/2)).
Proof.
  rewrite /Pending. rewrite -own_op -Cinl_op. rewrite frac_op Qp.div_2 //.
Qed.

Lemma pending_shoot `{oneshotG Σ} γ n :
  (Pending γ 1%Qp) ==∗ (Shot γ n).
Proof.
  iIntros "Hγ". iMod (own_update with "Hγ") as "$"; last done.
  by apply cmra_update_exclusive.
Qed.

Lemma shot_not_pending `{oneshotG Σ} γ v q :
  Shot γ v -∗ Pending γ q -∗ False.
Proof.
  iIntros "Hs Hp".
  iCombine "Hs Hp" gives %[].
Qed.

Lemma shot_idemp `{oneshotG Σ} γ n :
  (Shot γ n) ⊣⊢ (Shot γ n) ∗ (Shot γ n).
Proof.
  rewrite /Shot.
  rewrite -own_op -Cinr_op.
  rewrite agree_idemp.
  eauto.
Qed.

Lemma shot_agree `{oneshotG Σ} γ (v w: val) :
  Shot γ v -∗ Shot γ w -∗ ⌜v = w⌝.
Proof.
  iIntros "Hs1 Hs2".
  iCombine "Hs1 Hs2" gives %Hfoo.
  iPureIntro. by apply to_agree_op_inv_L.
Qed.

Lemma pointsto_exclusive `{heapGS Σ} (ℓ : loc) :
  ℓ ↦ #true ∗ ℓ ↦ #false -∗ False.
Proof.
  iIntros "[H1 H2]".
  iDestruct (pointsto_valid_2 with "H1 H2") as %Hvalid.
  destruct Hvalid as [_ Hf].
  done.
Qed.
