Require Import Coq.Reals.Reals.
Require Import Coq.Logic.FunctionalExtensionality.
Open Scope R_scope.

(** * Superposition Principle for Linear Operators in Calculus

    The superposition principle states that linear operators preserve
    linear combinations. This fundamental principle applies to:
    - Differentiation
    - Integration
    - Linear differential equations

    This file proves the superposition principle for both differentiation
    and integration operators.
*)

(** ** Superposition Principle for Differentiation *)

(** The superposition principle for differentiation states that
    the derivative of a linear combination equals the linear combination
    of derivatives: D(af + bg) = aD(f) + bD(g) *)

Theorem differentiation_superposition_principle :
  forall (D : (R -> R) -> (R -> R)),
  forall (D_additive : forall (f g : R -> R),
    D (fun x => f x + g x) = fun x => D f x + D g x),
  forall (D_homog : forall (f : R -> R) (s : R),
    D (fun x => s * f x) = fun x => s * D f x),
  forall (f g : R -> R) (a b : R),
    D (fun x => a * f x + b * g x) = fun x => a * D f x + b * D g x.
Proof.
  intros D D_additive D_homog f g a b.

  (* Rewrite using additivity *)
  rewrite D_additive.

  (* Apply homogeneity to each term *)
  rewrite D_homog.
  rewrite D_homog.

  (* The result follows by reflexivity *)
  reflexivity.
Qed.

(** ** Corollaries of the Differentiation Superposition Principle *)

(** Special case: derivative of a sum (when a = b = 1) *)
Corollary differentiation_sum :
  forall (D : (R -> R) -> (R -> R)),
  forall (D_additive : forall (f g : R -> R),
    D (fun x => f x + g x) = fun x => D f x + D g x),
  forall (f g : R -> R),
    D (fun x => f x + g x) = fun x => D f x + D g x.
Proof.
  intros D D_additive f g.
  apply D_additive.
Qed.

(** Special case: derivative of a scalar multiple *)
Corollary differentiation_scalar_mult :
  forall (D : (R -> R) -> (R -> R)),
  forall (D_homog : forall (f : R -> R) (s : R),
    D (fun x => s * f x) = fun x => s * D f x),
  forall (f : R -> R) (a : R),
    D (fun x => a * f x) = fun x => a * D f x.
Proof.
  intros D D_homog f a.
  apply D_homog.
Qed.

(** Derivative of a difference *)
Corollary differentiation_difference :
  forall (D : (R -> R) -> (R -> R)),
  forall (D_additive : forall (f g : R -> R),
    D (fun x => f x + g x) = fun x => D f x + D g x),
  forall (D_homog : forall (f : R -> R) (s : R),
    D (fun x => s * f x) = fun x => s * D f x),
  forall (f g : R -> R),
    D (fun x => f x - g x) = fun x => D f x - D g x.
Proof.
  intros D D_additive D_homog f g.
  unfold Rminus.
  replace (fun x : R => f x + - g x) with (fun x : R => 1 * f x + (-1) * g x).
  - rewrite (differentiation_superposition_principle D D_additive D_homog f g 1 (-1)).
    apply functional_extensionality. intros. ring.
  - apply functional_extensionality. intros. ring.
Qed.

(** ** Superposition Principle for Integration *)

(** The superposition principle for integration states that
    the integral of a linear combination equals the linear combination
    of integrals: ∫(af + bg) = a∫f + b∫g *)

Theorem integration_superposition_principle :
  forall (I : (R -> R) -> (R -> R)),
  forall (I_additive : forall (f g : R -> R),
    I (fun x => f x + g x) = fun x => I f x + I g x),
  forall (I_homog : forall (f : R -> R) (s : R),
    I (fun x => s * f x) = fun x => s * I f x),
  forall (f g : R -> R) (a b : R),
    I (fun x => a * f x + b * g x) = fun x => a * I f x + b * I g x.
Proof.
  intros I I_additive I_homog f g a b.

  (* Rewrite using additivity *)
  rewrite I_additive.

  (* Apply homogeneity to each term *)
  rewrite I_homog.
  rewrite I_homog.

  (* The result follows by reflexivity *)
  reflexivity.
Qed.

(** ** Corollaries of the Integration Superposition Principle *)

(** Integral of a sum *)
Corollary integration_sum :
  forall (I : (R -> R) -> (R -> R)),
  forall (I_additive : forall (f g : R -> R),
    I (fun x => f x + g x) = fun x => I f x + I g x),
  forall (f g : R -> R),
    I (fun x => f x + g x) = fun x => I f x + I g x.
Proof.
  intros I I_additive f g.
  apply I_additive.
Qed.

(** Integral of a scalar multiple *)
Corollary integration_scalar_mult :
  forall (I : (R -> R) -> (R -> R)),
  forall (I_homog : forall (f : R -> R) (s : R),
    I (fun x => s * f x) = fun x => s * I f x),
  forall (f : R -> R) (a : R),
    I (fun x => a * f x) = fun x => a * I f x.
Proof.
  intros I I_homog f a.
  apply I_homog.
Qed.

(** Integral of a difference *)
Corollary integration_difference :
  forall (I : (R -> R) -> (R -> R)),
  forall (I_additive : forall (f g : R -> R),
    I (fun x => f x + g x) = fun x => I f x + I g x),
  forall (I_homog : forall (f : R -> R) (s : R),
    I (fun x => s * f x) = fun x => s * I f x),
  forall (f g : R -> R),
    I (fun x => f x - g x) = fun x => I f x - I g x.
Proof.
  intros I I_additive I_homog f g.
  unfold Rminus.
  replace (fun x : R => f x + - g x) with (fun x : R => 1 * f x + (-1) * g x).
  - rewrite (integration_superposition_principle I I_additive I_homog f g 1 (-1)).
    apply functional_extensionality. intros. ring.
  - apply functional_extensionality. intros. ring.
Qed.

(** ** General Linear Operator Superposition Principle *)

(** The superposition principle applies to any linear operator,
    not just differentiation and integration. *)

Theorem linear_operator_superposition :
  forall (L : (R -> R) -> (R -> R)),
  forall (L_additive : forall (f g : R -> R),
    L (fun x => f x + g x) = fun x => L f x + L g x),
  forall (L_homog : forall (f : R -> R) (s : R),
    L (fun x => s * f x) = fun x => s * L f x),
  forall (f g : R -> R) (a b : R),
    L (fun x => a * f x + b * g x) = fun x => a * L f x + b * L g x.
Proof.
  intros L L_additive L_homog f g a b.
  rewrite L_additive.
  rewrite L_homog.
  rewrite L_homog.
  reflexivity.
Qed.

(** ** Extended Superposition Principle for Three Functions *)

(** The superposition principle extends to three or more functions *)

Theorem linear_operator_superposition_three :
  forall (L : (R -> R) -> (R -> R)),
  forall (L_additive : forall (f g : R -> R),
    L (fun x => f x + g x) = fun x => L f x + L g x),
  forall (L_homog : forall (f : R -> R) (s : R),
    L (fun x => s * f x) = fun x => s * L f x),
  forall (f g h : R -> R) (a b c : R),
    L (fun x => a * f x + b * g x + c * h x) =
    fun x => a * L f x + b * L g x + c * L h x.
Proof.
  intros L L_additive L_homog f g h a b c.

  (* Rewrite as (af + bg) + ch *)
  replace (fun x => a * f x + b * g x + c * h x) with
          (fun x => (a * f x + b * g x) + c * h x) by
    (apply functional_extensionality; intros; ring).

  (* Apply superposition to the outer sum *)
  rewrite L_additive.
  rewrite L_homog.

  (* Apply superposition to the inner sum *)
  rewrite (linear_operator_superposition L L_additive L_homog f g a b).

  reflexivity.
Qed.

(** ** Application to Homogeneous Linear Differential Equations *)

(** If f and g are solutions to a homogeneous linear differential equation
    L(y) = 0, then any linear combination af + bg is also a solution. *)

Theorem homogeneous_linear_DE_superposition :
  forall (L : (R -> R) -> (R -> R)),
  forall (L_additive : forall (f g : R -> R),
    L (fun x => f x + g x) = fun x => L f x + L g x),
  forall (L_homog : forall (f : R -> R) (s : R),
    L (fun x => s * f x) = fun x => s * L f x),
  forall (f g : R -> R) (a b : R),
  (* If f and g are solutions *)
  (forall x, L f x = 0) ->
  (forall x, L g x = 0) ->
  (* Then af + bg is also a solution *)
  (forall x, L (fun y => a * f y + b * g y) x = 0).
Proof.
  intros L L_additive L_homog f g a b Hf Hg x.

  (* Apply the superposition principle *)
  assert (H := linear_operator_superposition L L_additive L_homog f g a b).

  (* H is a function equality, so we can apply it to x *)
  assert (Hx : L (fun y : R => a * f y + b * g y) x = (fun x => a * L f x + b * L g x) x).
  { rewrite H. reflexivity. }

  (* Rewrite using Hx and simplify *)
  rewrite Hx.
  simpl.
  rewrite (Hf x).
  rewrite (Hg x).
  ring.
Qed.

(** ** Zero Function is in the Kernel *)

(** The zero function is always a solution to L(y) = 0 *)

Lemma zero_in_kernel :
  forall (L : (R -> R) -> (R -> R)),
  forall (L_homog : forall (f : R -> R) (s : R),
    L (fun x => s * f x) = fun x => s * L f x),
  forall x, L (fun _ => 0) x = 0.
Proof.
  intros L L_homog x.
  replace (L (fun _ : R => 0) x) with (L (fun y : R => 0 * (fun _ : R => 1) y) x) by
    (f_equal; apply functional_extensionality; intros; ring).
  rewrite L_homog.
  ring.
Qed.

(** ** Scalar Multiple of a Solution *)

(** If f is a solution to L(y) = 0, then so is any scalar multiple of f *)

Theorem scalar_multiple_of_solution :
  forall (L : (R -> R) -> (R -> R)),
  forall (L_homog : forall (f : R -> R) (s : R),
    L (fun x => s * f x) = fun x => s * L f x),
  forall (f : R -> R) (a : R),
  (forall x, L f x = 0) ->
  (forall x, L (fun y => a * f y) x = 0).
Proof.
  intros L L_homog f a Hf x.
  rewrite L_homog.
  specialize (Hf x).
  rewrite Hf.
  ring.
Qed.

(** ** Sum of Solutions *)

(** If f and g are solutions to L(y) = 0, then so is f + g *)

Theorem sum_of_solutions :
  forall (L : (R -> R) -> (R -> R)),
  forall (L_additive : forall (f g : R -> R),
    L (fun x => f x + g x) = fun x => L f x + L g x),
  forall (f g : R -> R),
  (forall x, L f x = 0) ->
  (forall x, L g x = 0) ->
  (forall x, L (fun y => f y + g y) x = 0).
Proof.
  intros L L_additive f g Hf Hg x.
  rewrite L_additive.
  specialize (Hf x).
  specialize (Hg x).
  rewrite Hf.
  rewrite Hg.
  ring.
Qed.
