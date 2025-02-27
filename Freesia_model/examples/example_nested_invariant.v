From iris.proofmode Require Import tactics.
From iris.heap_lang Require Export lang.
From iris.heap_lang Require Import assert proofmode notation adequacy.
From iris.base_logic Require Import invariants ghost_var.

Context `{!heapGS Σ}.

(* Declare namespaces *)
Definition outer_ns := nroot .@ "outer".
Definition inner_ns := nroot .@ "inner".

(* Inner invariant: enforces that integer n is even *)
Definition inner_inv (n : Z) : iProp Σ :=
  ⌜Zeven n⌝.

(* Outer invariant: maintains x ↦ n and nests the inner invariant 
   Note: inner_ns should be declared as a distinct namespace *)
Definition outer_inv (x : loc) : iProp Σ :=
  ∃ n:Z, x ↦ #n ∗ inv inner_ns (inner_inv n).

(* Global specification: establishes outer invariant as persistent assertion *)
Definition is_even (x : loc) : iProp Σ :=
  inv outer_ns (outer_inv x).

Lemma even_spec (x : loc) :
  {{{ is_even x }}}
    #x <- !#x + #2
  {{{ RET #(); True }}}.
Proof.
  iIntros (Φ) "#Hinv_outer Hpost".
  wp_bind (! _)%E.

  (* Step 1: Open outer invariant to access x's value *)
  iInv outer_ns as (n) "[Hx #Hinv_inner]" "Hclose".
  wp_load.  (* Load current value of x *)

  (* Step 2: Verify inner invariant (n must be even) *)
  iInv "Hinv_inner" as "> %Heven".  (* > indicates later modality *)
  iModIntro. iSplitR.
  { iPureIntro. auto. }  (* Re-establish inner invariant unchanged *)

  (* Step 3: Reconstruct outer invariant with original value *)
  iMod ("Hclose" with "[Hx Hinv_inner]") as "_".
  { iNext. iFrame. eauto. }  (* Frame unchanged resources *)
  iModIntro.

  (* Step 4: Prepare new inner invariant for n+2 *)
  iMod (inv_alloc inner_ns _ (inner_inv (n+2)) 
    with "[Hinv_inner]") as "#Hinv_inner2".
  { iNext. iPureIntro. by apply Zeven_plus_Zeven. }  (* n+2 preserves evenness *)

  (* Step 5: Atomic update of x's value *)
  wp_pure credit:"Hcred".  (* Got a credit *)
  iInv outer_ns as (n') "[Hx _]" "Hclose".
  iMod (lc_fupd_elim_later with "Hcred Hx") as "Hx".  (* Eliminate later modality *)
  wp_store.  (* Store n+2 to x *)

  (* Step 6: Re-establish outer invariant with updated value *)
  iMod ("Hclose" with "[Hx Hinv_inner]") as "_".
  { iNext. iExists (n+2)%Z. iFrame. eauto. }  (* Update outer invariant *)

  iModIntro. iApply "Hpost". done.
Qed.