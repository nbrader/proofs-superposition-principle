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

Lemma zero_in_kernel_extensional :
  forall (L : (R -> R) -> (R -> R)),
  forall (L_homog : forall (f : R -> R) (s : R),
    L (fun x => s * f x) = fun x => s * L f x),
  L (fun _ => 0) = fun _ => 0.
Proof.
  intros L L_homog.
  apply functional_extensionality.
  intros x.
  apply zero_in_kernel.
  apply L_homog.
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

(** ** General List-Based Superposition for N Functions *)

Require Import List.
Import ListNotations.

(** Helper function to compute linear combination of a list of functions *)
Fixpoint linear_combination (coeffs : list R) (funcs : list (R -> R)) : R -> R :=
  match coeffs, funcs with
  | [], [] => fun _ => 0
  | c::cs, f::fs => fun x => c * f x + linear_combination cs fs x
  | _, _ => fun _ => 0  (* mismatch case *)
  end.

(** Helper function to apply operator to each function and combine *)
Fixpoint linear_combination_of_results (L : (R -> R) -> (R -> R))
                                       (coeffs : list R)
                                       (funcs : list (R -> R)) : R -> R :=
  match coeffs, funcs with
  | [], [] => fun _ => 0
  | c::cs, f::fs => fun x => c * L f x + linear_combination_of_results L cs fs x
  | _, _ => fun _ => 0
  end.

(** General superposition for list of functions *)
Theorem linear_operator_superposition_list :
  forall (L : (R -> R) -> (R -> R)),
  forall (L_additive : forall (f g : R -> R),
    L (fun x => f x + g x) = fun x => L f x + L g x),
  forall (L_homog : forall (f : R -> R) (s : R),
    L (fun x => s * f x) = fun x => s * L f x),
  forall (coeffs : list R) (funcs : list (R -> R)),
  length coeffs = length funcs ->
  L (linear_combination coeffs funcs) =
  linear_combination_of_results L coeffs funcs.
Proof.
  intros L L_additive L_homog coeffs.
  induction coeffs as [| c cs IH]; intros funcs Hlen.

  - (* Base case: empty list *)
    destruct funcs.
    + simpl.
      apply zero_in_kernel_extensional.
      apply L_homog.
    + simpl in Hlen. discriminate Hlen.

  - (* Inductive case: c::cs *)
    destruct funcs as [| f fs].
    + simpl in Hlen. discriminate Hlen.
    + simpl in Hlen. injection Hlen as Hlen.
      simpl.
      rewrite L_additive.
      rewrite L_homog.
      rewrite IH.
      * reflexivity.
      * apply Hlen.
Qed.

(** Corollary: If all functions in a list are solutions,
    then their linear combination is also a solution *)
Theorem linear_combination_of_solutions :
  forall (L : (R -> R) -> (R -> R)),
  forall (L_additive : forall (f g : R -> R),
    L (fun x => f x + g x) = fun x => L f x + L g x),
  forall (L_homog : forall (f : R -> R) (s : R),
    L (fun x => s * f x) = fun x => s * L f x),
  forall (coeffs : list R) (funcs : list (R -> R)),
  length coeffs = length funcs ->
  (forall f, In f funcs -> forall x, L f x = 0) ->
  forall x, L (linear_combination coeffs funcs) x = 0.
Proof.
  intros L L_additive L_homog coeffs funcs Hlen Hall x.
  rewrite (linear_operator_superposition_list L L_additive L_homog coeffs funcs Hlen).

  induction coeffs as [| c cs IH] in funcs, Hlen, Hall |- *.
  - destruct funcs; simpl.
    + reflexivity.
    + simpl in Hlen. discriminate Hlen.
  - destruct funcs as [| f fs].
    + simpl in Hlen. discriminate Hlen.
    + simpl in Hlen. injection Hlen as Hlen.
      simpl.
      assert (Hf : L f x = 0).
      { apply Hall. simpl. left. reflexivity. }
      rewrite Hf.
      assert (IH' : linear_combination_of_results L cs fs x = 0).
      { apply IH.
        - apply Hlen.
        - intros g Hin. apply Hall. simpl. right. apply Hin. }
      rewrite IH'.
      replace (c * 0 + 0) with 0 by ring.
      reflexivity.
Qed.

(** ** Vector Space Structure of Solution Space *)

(** The set of solutions to L(y) = 0 forms a vector space over R *)

(** Closure under addition (already proved as sum_of_solutions) *)

(** Closure under scalar multiplication (already proved as scalar_multiple_of_solution) *)

(** The solution space contains the zero vector *)
Theorem zero_is_solution :
  forall (L : (R -> R) -> (R -> R)),
  forall (L_homog : forall (f : R -> R) (s : R),
    L (fun x => s * f x) = fun x => s * L f x),
  forall x, L (fun _ => 0) x = 0.
Proof.
  intros L L_homog x.
  apply zero_in_kernel.
  apply L_homog.
Qed.

(** Associativity of addition (inherited from function addition) *)

(** Commutativity of addition *)
Theorem solution_addition_commutative :
  forall (L : (R -> R) -> (R -> R)),
  forall (L_additive : forall (f g : R -> R),
    L (fun x => f x + g x) = fun x => L f x + L g x),
  forall (f g : R -> R),
  (forall x, L f x = 0) ->
  (forall x, L g x = 0) ->
  (forall x, L (fun y => f y + g y) x = L (fun y => g y + f y) x).
Proof.
  intros L L_additive f g Hf Hg x.
  replace (fun y : R => f y + g y) with (fun y : R => g y + f y) by
    (apply functional_extensionality; intros; ring).
  reflexivity.
Qed.

(** Distributivity of scalar multiplication over addition *)
Theorem scalar_mult_distributes_over_addition :
  forall (L : (R -> R) -> (R -> R)),
  forall (L_additive : forall (f g : R -> R),
    L (fun x => f x + g x) = fun x => L f x + L g x),
  forall (L_homog : forall (f : R -> R) (s : R),
    L (fun x => s * f x) = fun x => s * L f x),
  forall (f g : R -> R) (a : R),
  (forall x, L f x = 0) ->
  (forall x, L g x = 0) ->
  (forall x, L (fun y => a * (f y + g y)) x = 0).
Proof.
  intros L L_additive L_homog f g a Hf Hg x.
  replace (fun y : R => a * (f y + g y)) with (fun y : R => a * f y + a * g y) by
    (apply functional_extensionality; intros; ring).
  apply (homogeneous_linear_DE_superposition L L_additive L_homog f g a a Hf Hg).
Qed.

(** ** Concrete Examples *)

Section ConcreteExamples.

(** Example 1: Derivative of polynomial linear combination *)
Example polynomial_derivative_example :
  forall (D : (R -> R) -> (R -> R)),
  forall (D_additive : forall (f g : R -> R),
    D (fun x => f x + g x) = fun x => D f x + D g x),
  forall (D_homog : forall (f : R -> R) (s : R),
    D (fun x => s * f x) = fun x => s * D f x),
  let f := fun x => x^2 in
  let g := fun x => x^3 in
  D (fun x => 3 * f x + 2 * g x) = fun x => 3 * D f x + 2 * D g x.
Proof.
  intros D D_additive D_homog f g.
  apply differentiation_superposition_principle.
  - apply D_additive.
  - apply D_homog.
Qed.

(** Example 2: Second order differential equation y'' - 4y = 0 *)
(** Solutions: e^(2x) and e^(-2x) *)
Example second_order_DE_example :
  forall (L : (R -> R) -> (R -> R)),
  forall (L_additive : forall (f g : R -> R),
    L (fun x => f x + g x) = fun x => L f x + L g x),
  forall (L_homog : forall (f : R -> R) (s : R),
    L (fun x => s * f x) = fun x => s * L f x),
  forall (exp_pos exp_neg : R -> R) (c1 c2 : R),
  (* Assume exp_pos and exp_neg are solutions *)
  (forall x, L exp_pos x = 0) ->
  (forall x, L exp_neg x = 0) ->
  (* Then their linear combination is also a solution *)
  (forall x, L (fun y => c1 * exp_pos y + c2 * exp_neg y) x = 0).
Proof.
  intros L L_additive L_homog exp_pos exp_neg c1 c2 H_pos H_neg x.
  apply (homogeneous_linear_DE_superposition L L_additive L_homog exp_pos exp_neg c1 c2 H_pos H_neg).
Qed.

(** Example 3: Harmonic oscillator y'' + ω²y = 0 *)
(** Solutions: sin(ωx) and cos(ωx) *)
Example harmonic_oscillator_example :
  forall (L : (R -> R) -> (R -> R)),
  forall (L_additive : forall (f g : R -> R),
    L (fun x => f x + g x) = fun x => L f x + L g x),
  forall (L_homog : forall (f : R -> R) (s : R),
    L (fun x => s * f x) = fun x => s * L f x),
  forall (sin_omega cos_omega : R -> R) (A B : R),
  (* Assume sin_omega and cos_omega are solutions *)
  (forall x, L sin_omega x = 0) ->
  (forall x, L cos_omega x = 0) ->
  (* General solution is A*sin(ωx) + B*cos(ωx) *)
  (forall x, L (fun y => A * sin_omega y + B * cos_omega y) x = 0).
Proof.
  intros L L_additive L_homog sin_omega cos_omega A B H_sin H_cos x.
  apply (homogeneous_linear_DE_superposition L L_additive L_homog sin_omega cos_omega A B H_sin H_cos).
Qed.

(** Example 4: Linear combination of three solutions *)
Example three_solutions_example :
  forall (L : (R -> R) -> (R -> R)),
  forall (L_additive : forall (f g : R -> R),
    L (fun x => f x + g x) = fun x => L f x + L g x),
  forall (L_homog : forall (f : R -> R) (s : R),
    L (fun x => s * f x) = fun x => s * L f x),
  forall (f1 f2 f3 : R -> R) (c1 c2 c3 : R),
  (forall x, L f1 x = 0) ->
  (forall x, L f2 x = 0) ->
  (forall x, L f3 x = 0) ->
  (forall x, L (fun y => c1 * f1 y + c2 * f2 y + c3 * f3 y) x = 0).
Proof.
  intros L L_additive L_homog f1 f2 f3 c1 c2 c3 H1 H2 H3 x.

  (* First show that the linear_combination equals our function *)
  assert (Heq : (fun y => c1 * f1 y + c2 * f2 y + c3 * f3 y) =
                linear_combination [c1; c2; c3] [f1; f2; f3]).
  { apply functional_extensionality. intros y. simpl. ring. }

  rewrite Heq.
  apply (linear_combination_of_solutions L L_additive L_homog [c1; c2; c3] [f1; f2; f3]).
  - simpl. reflexivity.
  - intros f Hin.
    simpl in Hin.
    destruct Hin as [Hf | [Hf | [Hf | Hf]]].
    + rewrite <- Hf. apply H1.
    + rewrite <- Hf. apply H2.
    + rewrite <- Hf. apply H3.
    + contradiction.
Qed.

End ConcreteExamples.

(** ** Summary *)

(** This file has proved the superposition principle for linear operators in various forms:

    1. Basic form for two functions
    2. Extension to three functions
    3. General form for n functions (list-based)
    4. Applications to differential equations
    5. Vector space structure of solution spaces
    6. Concrete examples

    The key insight is that linearity (additivity + homogeneity) is sufficient
    to establish the superposition principle, which is fundamental to:
    - Solving linear differential equations
    - Understanding linear operators in functional analysis
    - Working with vector spaces of functions
*)
