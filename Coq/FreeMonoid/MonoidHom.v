Require Import FreeMonoid.StructMonoid. Export FreeMonoid.StructMonoid.

Section MonoidHomomorphisms.

Class MonoidHomomorphism {A B : Type} `{Monoid A} `{Monoid B} (f : A -> B) := {
  homo_preserves_op : forall x y : A, f (m_op x y) = m_op (f x) (f y);
  homo_preserves_id : f (mn_id) = mn_id;
}.

End MonoidHomomorphisms.
