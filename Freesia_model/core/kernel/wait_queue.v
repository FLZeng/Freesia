From iris.base_logic.lib Require Import invariants.
From iris.heap_lang Require Import proofmode notation.

From lib Require Import basic_types.
From core.kernel Require Import spinlock.

Definition wq_spin_lock := cpu_spin_init #().


Check wq_spin_lock.

Definition wq_remove_elm : val :=
  rec: "wq_remove_elm" "wq" "wqe" :=
    match: !"wq" with
      NONE => #()
    | SOME "p" =>
      let: "wqe2" := Fst !"p" in
      let: "wq2" := Snd !"p" in
      if: "wqe" = "wqe2" then
        "wq" <- "wq2"
      else
        "wq_remove_elm" "wq2" "wqe"
    end.

Definition wq_wait_init : val := λ: "wq" "wqe" "wait_read",
  let: "l" := wq_spin_lock in
  "wqe" <- (#false, "wait_read");;
  cpu_spin_lock "l";;
  "wq" <- ("wqe", "wq");;
  cpu_spin_unlock "l".

Definition wq_wait_final : val := 
  rec: "wq_wait_final" "wq" "wqe" :=
  let: "l" := wq_spin_lock in
  cpu_spin_lock "l";;
  let: "done" := Fst !"wqe" in
  if "done" then
    (* remove "wqe" from "wq";; *)
    wq_remove_elm "wq" "wqe";;
    cpu_spin_unlock "l"
  else
    cpu_spin_unlock "l";;
    "wq_wait_final" "wq" "wqe".

Definition wq_wake_iter : val :=
  rec: "wq_wake_iter" "wq" "do_wakeup" "wake_read" "wake_type_assigned" :=
    match: !"wq" with
      NONE => #()
    | SOME "p" =>
      let: "wqe" := Fst !"p" in
      let: "wq2" := Snd !"p" in
      let: "done" := Fst !"wqe" in
      let: "wait_read" := Snd !"wqe" in
      if: "done" then
        "wq_wake_iter" "wq2" "do_wakeup" "wake_read" "wake_type_assigned"
      else
        if: ~ !"wake_type_assigned" then
          "wake_read" <- "wait_read";;
          "wake_type_assigned" <- #true
        else
          #();;
      
        if: "wait_read" = !"wake_read" then
          "wqe" <- (#true, "wait_read");;
          "do_wakeup" <- #true
        else
          "wq_wake_iter" "wq2" "do_wakeup" "wake_read" "wake_type_assigned"
    end.

Definition wq_wake_next : val :=
  rec: "wq_wake_next" "wq" :=
  let: "l" := wq_spin_lock in
  let: "do_wakeup" := ref #false in
  let: "wake_read" := ref #false in
  let: "wake_type_assigned" := ref #false in

  cpu_spin_lock "l";;
  wq_wake_iter "wq" "do_wakeup" "wake_read" "wake_type_assigned"
  cpu_spin_unlock "l";;

  match (!"do_wakeup", !"wake_read") with
    (#true, #true) => "wq_wake_next" "wq" "wake_type_assigned"
  | _ => #()
  end.


Section proof.

Context `{!heapGS Σ}.

Lemma wq_wait_init_spec wq wqe wait_read (R : iProp Σ):
  {{{ R }}}
    wq_wait_init wq wqe wait_read
  {{{ RET #(); R }}}.
Proof.
  admit.
Admitted.

Lemma wq_wait_final_spec wq wqe (R : iProp Σ):
  {{{ R }}}
    wq_wait_final wq wqe
  {{{ RET #(); R }}}.
Proof.
  admit.
Admitted.

Lemma wq_wake_next_spec wq (R : iProp Σ):
  {{{ R }}}
    wq_wake_next wq
  {{{ RET #(); R }}}.
Proof.
  admit.
Admitted.

End proof.