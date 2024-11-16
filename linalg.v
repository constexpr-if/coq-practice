Require Import Nat List.

Lemma length_hd_elim:
  forall (X: Type) (v v' w w': list X) (a b: X),
  v = a::v' -> w = b::w' -> length v = length w -> length v' = length w'.
Proof. intros. rewrite H, H0 in H1. injection H1. trivial. Qed.

Fixpoint dot_prod {X: Type} (prod add: X -> X -> X) (acc: X) (v w: list X) (H: length v = length w): X :=
  match v as v0, w as w0 return v = v0 -> w = w0 -> X with
  | a::v', b::w' => fun Hv Hw =>
    let LEN := length_hd_elim X v v' w w' a b in
    dot_prod prod add (add acc (prod a b)) v' w' (LEN Hv Hw H)
  | _, _ => fun _ _ => acc
  end eq_refl eq_refl.


