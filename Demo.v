Require Import SMT.
Add LoadPath "~/smt4coq".
Require Import compcert.lib.Integers.

Lemma xx : forall x y, (Int64.ltu x y = false) -> Int64.ltu x y = true \/ x = y.
Proof.
intros. print z3. Admitted.

Require Import ZArith.

Lemma int64_prop2 :
  forall i0 i,
    Int64.ltu i0 i = false ->
    Int64.unsigned 
    (Int64.add (Int64.divu (Int64.sub i0 i) (Int64.repr 2)) i) 
    = Z.div (Z.add (Int64.unsigned i) (Int64.unsigned i0)) 2.
Proof.
intros.
print z3.
Admitted.

Lemma Y: forall x, Int64.zero = x -> x = Int64.repr 0.
intros.
print z3.
Admitted.

Lemma X: forall ix, (Int64.shru
                (Int64.and
                   (Int64.or (Int64.shl (Int64.repr 1) (Int64.repr 56))
                      (Int64.and ix (Int64.not (Int64.shl (Int64.repr 255) (Int64.repr 56)))))
                   (Int64.shl (Int64.repr 281474976710655) (Int64.repr 8))) 
                (Int64.repr 8))
      = 

      (Int64.shru (Int64.and ix (Int64.repr 72057594037927935)) (Int64.repr 8)).
Proof.
intros.
print z3.
smt4coq.
Qed.