import GaloisForLFunctions.HTGeometry.DifferentialSubringCollapse
import GaloisForLFunctions.HTGeometry.DifferentialGaloisSeparation

/-!
# Isomonodromy from a differential-algebraic constraint on the Galois monoid

The isomonodromy endgame consumes a monic linear relation among the jets of every scalar whose
multiple of the identity lies in the span of the Galois monoid.  A differential-algebraic
constraint supplies that relation in its strongest form: the scalar stabiliser of the span is a
subring, so one nonzero differential polynomial vanishing on it makes every one of its elements a
constant, and the monic relation is then `δ x = 0`.

* `deriv_eq_zero_of_scalarSpan_of_zeroSet` — the collapse of the scalar stabiliser;
* `isomonodromy_of_no_riccati_of_zeroSet` — the endgame with the differential constraint replaced by
  a single nonzero differential polynomial vanishing on the scalar stabiliser.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open scoped TensorProduct Differential
open GaloisForLFunctions

section Scalars

variable {C : Type*} [Field C] [CharZero C] [Differential C]
  [IsAlgClosed (differentialConstants C)]

/-- **A differential-algebraic constraint collapses the scalar stabiliser.**  The scalars whose
multiple of the identity lies in the span of a multiplicative set of matrices form a subring, so a
nonzero differential polynomial vanishing on them makes them constants. -/
theorem deriv_eq_zero_of_scalarSpan_of_zeroSet
    (G : Set (Matrix (Fin 2) (Fin 2) C))
    (hone : (1 : Matrix (Fin 2) (Fin 2) C) ∈ G)
    (hmulG : ∀ g ∈ G, ∀ h ∈ G, g * h ∈ G)
    {P : DifferentialPolynomial Unit C} (hP : P ≠ 0)
    (hPV : ∀ v : C, v • (1 : Matrix (Fin 2) (Fin 2) C) ∈
        Submodule.span (differentialConstants C) G →
      differentialPolynomialEvalOver (K := C) (fun _ : Unit => v) P = 0) :
    ∀ x : C, x • (1 : Matrix (Fin 2) (Fin 2) C) ∈
        Submodule.span (differentialConstants C) G → Differential.deriv x = 0 := by
  have honeA : (1 : Matrix (Fin 2) (Fin 2) C) ∈
      Submodule.span (differentialConstants C) G := Submodule.subset_span hone
  have hmulA : ∀ a ∈ Submodule.span (differentialConstants C) G,
      ∀ b ∈ Submodule.span (differentialConstants C) G,
      a * b ∈ Submodule.span (differentialConstants C) G :=
    mul_mem_span_of_mul_mem (C := differentialConstants C) G hmulG
  have honeV : (1 : C) ∈ scalarStabilizer (Submodule.span (differentialConstants C) G) := by
    show (1 : C) • (1 : Matrix (Fin 2) (Fin 2) C) ∈ Submodule.span (differentialConstants C) G
    rwa [one_smul]
  have hmulV : ∀ x ∈ scalarStabilizer (Submodule.span (differentialConstants C) G),
      ∀ y ∈ scalarStabilizer (Submodule.span (differentialConstants C) G),
      x * y ∈ scalarStabilizer (Submodule.span (differentialConstants C) G) := by
    intro x hx y hy
    show (x * y) • (1 : Matrix (Fin 2) (Fin 2) C) ∈ Submodule.span (differentialConstants C) G
    have hprod := hmulA _ hx _ hy
    rwa [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul] at hprod
  exact deriv_eq_zero_of_subring_of_zeroSet
    (scalarStabilizer (Submodule.span (differentialConstants C) G)) honeV hmulV hP hPV

/-- The collapse, in the monic jet shape the classification consumes. -/
theorem jet_relation_of_scalarSpan_of_zeroSet
    (G : Set (Matrix (Fin 2) (Fin 2) C))
    (hone : (1 : Matrix (Fin 2) (Fin 2) C) ∈ G)
    (hmulG : ∀ g ∈ G, ∀ h ∈ G, g * h ∈ G)
    {P : DifferentialPolynomial Unit C} (hP : P ≠ 0)
    (hPV : ∀ v : C, v • (1 : Matrix (Fin 2) (Fin 2) C) ∈
        Submodule.span (differentialConstants C) G →
      differentialPolynomialEvalOver (K := C) (fun _ : Unit => v) P = 0) :
    ∀ x : C, x • (1 : Matrix (Fin 2) (Fin 2) C) ∈
        Submodule.span (differentialConstants C) G →
      differentialJet 1 x = ∑ i : Fin 1, (0 : Fin 1 → C) i * differentialJet (i : ℕ) x := by
  intro x hx
  have hd := deriv_eq_zero_of_scalarSpan_of_zeroSet G hone hmulG hP hPV x hx
  simp [hd]

end Scalars

section Linear

variable {C : Type*} [Field C] [CharZero C] [Differential C]

omit [CharZero C] in
/-- A constant factor passes through every jet. -/
theorem differentialJet_mul_of_deriv_eq_zero {c : C} (hc : c′ = 0) (x : C) (n : ℕ) :
    differentialJet n (c * x) = c * differentialJet n x := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [differentialJet_succ, ih, Derivation.leibniz, hc, smul_zero, add_zero, smul_eq_mul,
        differentialJet_succ]

omit [CharZero C] in
/-- The solution set of a scalar linear differential operator is a subspace over the constants. -/
def linearJetSolutions (n : ℕ) (L : ℕ → C) : Submodule (differentialConstants C) C where
  carrier := {x : C | ∑ i ∈ Finset.range (n + 1), L i * differentialJet i x = 0}
  zero_mem' := by
    show ∑ i ∈ Finset.range (n + 1), L i * differentialJet i (0 : C) = 0
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [differentialJet_apply_zero, mul_zero]
  add_mem' := by
    intro x y hx hy
    show ∑ i ∈ Finset.range (n + 1), L i * differentialJet i (x + y) = 0
    have hsplit : ∀ i ∈ Finset.range (n + 1),
        L i * differentialJet i (x + y)
          = L i * differentialJet i x + L i * differentialJet i y := by
      intro i _
      rw [differentialJet_add_apply, mul_add]
    rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, hx, hy, add_zero]
  smul_mem' := by
    intro c x hx
    show ∑ i ∈ Finset.range (n + 1), L i * differentialJet i ((c : C) * x) = 0
    have hc : (c : C)′ = 0 := c.2
    have hsplit : ∀ i ∈ Finset.range (n + 1),
        L i * differentialJet i ((c : C) * x) = (c : C) * (L i * differentialJet i x) := by
      intro i _
      rw [differentialJet_mul_of_deriv_eq_zero hc]
      ring
    rw [Finset.sum_congr rfl hsplit, ← Finset.mul_sum, hx, mul_zero]

omit [CharZero C] in
@[simp] theorem mem_linearJetSolutions {n : ℕ} {L : ℕ → C} {x : C} :
    x ∈ linearJetSolutions n L ↔ ∑ i ∈ Finset.range (n + 1), L i * differentialJet i x = 0 :=
  Iff.rfl

omit [CharZero C] in
/-- The matrices all of whose entries solve the operator. -/
def matrixLinearJetSolutions (n : ℕ) (L : ℕ → C) :
    Submodule (differentialConstants C) (Matrix (Fin 2) (Fin 2) C) where
  carrier := {M | ∀ i j, M i j ∈ linearJetSolutions n L}
  zero_mem' := fun _ _ => (linearJetSolutions n L).zero_mem
  add_mem' := fun hM hN i j => (linearJetSolutions n L).add_mem (hM i j) (hN i j)
  smul_mem' := fun c _ hM i j => (linearJetSolutions n L).smul_mem c (hM i j)

omit [CharZero C] in
/-- The differential polynomial of a scalar linear operator. -/
def linearJetPolynomial (n : ℕ) (L : ℕ → C) : DifferentialPolynomial Unit C :=
  ∑ i ∈ Finset.range (n + 1),
    MvPolynomial.C (L i) * MvPolynomial.X (((), i) : Unit × ℕ)

omit [CharZero C] in
theorem differentialPolynomialEvalOver_linearJetPolynomial (n : ℕ) (L : ℕ → C) (v : C) :
    differentialPolynomialEvalOver (K := C) (fun _ : Unit => v) (linearJetPolynomial n L)
      = ∑ i ∈ Finset.range (n + 1), L i * differentialJet i v := by
  rw [linearJetPolynomial, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, differentialPolynomialEvalOver_C, differentialPolynomialEvalOver_X]
  simp

omit [CharZero C] [Differential C] in
theorem linearJetPolynomial_ne_zero {n : ℕ} {L : ℕ → C} {i₀ : ℕ} (hi₀ : i₀ ∈ Finset.range (n + 1))
    (hL : L i₀ ≠ 0) : linearJetPolynomial n L ≠ 0 := by
  classical
  intro h
  have hcoeff : MvPolynomial.coeff (Finsupp.single (((), i₀) : Unit × ℕ) 1)
      (linearJetPolynomial n L) = L i₀ := by
    rw [linearJetPolynomial, MvPolynomial.coeff_sum]
    rw [Finset.sum_eq_single i₀]
    · rw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X, if_pos rfl, mul_one]
    · intro j _ hj
      rw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X, if_neg, mul_zero]
      intro hcon
      exact hj (congrArg Prod.snd (Finsupp.single_left_injective (b := (1 : ℕ)) one_ne_zero hcon))
    · intro hcon
      exact absurd hi₀ hcon
  rw [h, MvPolynomial.coeff_zero] at hcoeff
  exact hL hcoeff.symm

omit [CharZero C] in
/-- Every scalar of the stabiliser solves the operator: the solution set is a subspace over the
constants, so the whole span of the group has its entries there. -/
theorem eval_linearJetPolynomial_eq_zero_of_scalarSpan
    (G : Set (Matrix (Fin 2) (Fin 2) C)) {n : ℕ} {L : ℕ → C}
    (hGL : ∀ g ∈ G, ∀ i j, g i j ∈ linearJetSolutions n L) :
    ∀ v : C, v • (1 : Matrix (Fin 2) (Fin 2) C) ∈ Submodule.span (differentialConstants C) G →
      differentialPolynomialEvalOver (K := C) (fun _ : Unit => v) (linearJetPolynomial n L) = 0 := by
  have hspan : Submodule.span (differentialConstants C) G ≤ matrixLinearJetSolutions n L :=
    Submodule.span_le.mpr fun g hg => hGL g hg
  intro v hv
  rw [differentialPolynomialEvalOver_linearJetPolynomial]
  have hmem : (v • (1 : Matrix (Fin 2) (Fin 2) C)) 0 0 ∈ linearJetSolutions n L :=
    hspan hv 0 0
  have hval : (v • (1 : Matrix (Fin 2) (Fin 2) C)) 0 0 = v := by simp
  rwa [hval, mem_linearJetSolutions] at hmem

variable [IsAlgClosed (differentialConstants C)]

/-- **A linear differential relation on a matrix group collapses its scalar stabiliser.**  The
solution set of a scalar linear operator is a subspace over the constants, so the whole span of the
group has its entries there, and in particular every scalar of the stabiliser does. -/
theorem deriv_eq_zero_of_scalarSpan_of_linear
    (G : Set (Matrix (Fin 2) (Fin 2) C))
    (hone : (1 : Matrix (Fin 2) (Fin 2) C) ∈ G)
    (hmulG : ∀ g ∈ G, ∀ h ∈ G, g * h ∈ G)
    {n : ℕ} {L : ℕ → C} {i₀ : ℕ} (hi₀ : i₀ ∈ Finset.range (n + 1)) (hL : L i₀ ≠ 0)
    (hGL : ∀ g ∈ G, ∀ i j, g i j ∈ linearJetSolutions n L) :
    ∀ x : C, x • (1 : Matrix (Fin 2) (Fin 2) C) ∈
        Submodule.span (differentialConstants C) G → x′ = 0 := by
  exact deriv_eq_zero_of_scalarSpan_of_zeroSet G hone hmulG
    (linearJetPolynomial_ne_zero hi₀ hL)
    (eval_linearJetPolynomial_eq_zero_of_scalarSpan G hGL)

end Linear

universe u

variable {K R C : Type u} [Field K] [CommRing R] [Nontrivial R] [Algebra K R]
  [Field C] [Algebra C K] [Algebra C R] [IsScalarTower C K R]
  [Differential K] [Differential R] [DifferentialAlgebra K R]
  [Differential C] [DifferentialAlgebra C R]

/-- **Isomonodromy from differential algebraicity.**  A second-order difference equation without a
base Riccati solution, the scalar stabiliser of whose Galois monoid lies in the zero set of one
nonzero differential polynomial, carries a connection over the base. -/
theorem isomonodromy_of_no_riccati_of_zeroSet
    [IsAlgClosed C] [CharZero C] [IsAlgClosed (differentialConstants C)]
    [Algebra ℚ C] [IsDifferentiallyClosed C]
    (E : Subalgebra C (R ⊗[K] R)) (hEδ : ∀ e ∈ E, tensorSquareDerivation (K := K) e ∈ E)
    [IsReduced E] [Algebra.FiniteType C E]
    {ι : Type*} (b : Module.Basis ι C E)
    (hgen : Algebra.adjoin C
      (Set.range (algebraMap R (R ⊗[K] R)) ∪ (E : Set (R ⊗[K] R))) = ⊤)
    (hindep : LinearIndependent R (fun i => ((b i : E) : R ⊗[K] R)))
    {σK : K ≃+* K} {σR : R ≃+* R}
    (hcompat : ∀ x : K, σR (algebraMap K R x) = algebraMap K R (σK x))
    (hconstC : ∀ x : C, σR (algebraMap C R x) = algebraMap C R x)
    (hσδ : ∀ x : R, σR (Differential.deriv x) = Differential.deriv (σR x))
    (hsimple : IsSigmaSimple σR)
    {a₁ a₀ : K} (hric : ∀ r : K, σK r * r ≠ a₁ * r + a₀)
    (A : Matrix (Fin 2) (Fin 2) K)
    (Y : Matrix (Fin 2) (Fin 2) R) [Invertible Y]
    (hsys : Y.map ((σR : R ≃+* R) : R →+* R) = (A.map (algebraMap K R)) * Y)
    (hY1 : ∀ j, Y 1 j = σR (Y 0 j))
    (hYrec : ∀ j, σR (Y 1 j) = algebraMap K R a₁ * Y 1 j + algebraMap K R a₀ * Y 0 j)
    (Z : Matrix (Fin 2) (Fin 2) (R ⊗[K] R)) (hZE : ∀ i j, Z i j ∈ E)
    (hZ : leftFundamental K Y * Z = rightFundamental K Y)
    {P : DifferentialPolynomial Unit C} (hP : P ≠ 0)
    (hPV : ∀ v : C, v • (1 : Matrix (Fin 2) (Fin 2) C) ∈
        Submodule.span (differentialConstants C)
          (galoisMonoid E Z hZE (tensorDifferentialPoints E hEδ)) →
      differentialPolynomialEvalOver (K := C) (fun _ : Unit => v) P = 0) :
    ∃ B : Matrix (Fin 2) (Fin 2) K,
      B.map ((σK : K ≃+* K) : K →+* K) * A = matrixDeriv A + A * B := by
  refine isomonodromy_of_no_riccati_of_differentiallyClosed E hEδ b hgen hindep hcompat hconstC
    hσδ hsimple hric A Y hsys hY1 hYrec Z hZE hZ (m := 1) (aa := (0 : Fin 1 → C)) ?_
  exact jet_relation_of_scalarSpan_of_zeroSet
    (galoisMonoid E Z hZE (tensorDifferentialPoints E hEδ))
    ((Submonoid.closure _).one_mem)
    (fun g hg h hh => (Submonoid.closure _).mul_mem hg hh) hP hPV

/-- **Isomonodromy from a linear differential relation on the Galois matrices.**  This is the shape
in which the classification of differential algebraic subgroups delivers its conclusion: the entries
of the Galois matrices solve one scalar linear differential operator, so they lie in a subspace over
the differential constants, and the scalar stabiliser of the span of the monoid lies there too. -/
theorem isomonodromy_of_no_riccati_of_linearRelation
    [IsAlgClosed C] [CharZero C] [IsAlgClosed (differentialConstants C)]
    [Algebra ℚ C] [IsDifferentiallyClosed C]
    (E : Subalgebra C (R ⊗[K] R)) (hEδ : ∀ e ∈ E, tensorSquareDerivation (K := K) e ∈ E)
    [IsReduced E] [Algebra.FiniteType C E]
    {ι : Type*} (b : Module.Basis ι C E)
    (hgen : Algebra.adjoin C
      (Set.range (algebraMap R (R ⊗[K] R)) ∪ (E : Set (R ⊗[K] R))) = ⊤)
    (hindep : LinearIndependent R (fun i => ((b i : E) : R ⊗[K] R)))
    {σK : K ≃+* K} {σR : R ≃+* R}
    (hcompat : ∀ x : K, σR (algebraMap K R x) = algebraMap K R (σK x))
    (hconstC : ∀ x : C, σR (algebraMap C R x) = algebraMap C R x)
    (hσδ : ∀ x : R, σR (Differential.deriv x) = Differential.deriv (σR x))
    (hsimple : IsSigmaSimple σR)
    {a₁ a₀ : K} (hric : ∀ r : K, σK r * r ≠ a₁ * r + a₀)
    (A : Matrix (Fin 2) (Fin 2) K)
    (Y : Matrix (Fin 2) (Fin 2) R) [Invertible Y]
    (hsys : Y.map ((σR : R ≃+* R) : R →+* R) = (A.map (algebraMap K R)) * Y)
    (hY1 : ∀ j, Y 1 j = σR (Y 0 j))
    (hYrec : ∀ j, σR (Y 1 j) = algebraMap K R a₁ * Y 1 j + algebraMap K R a₀ * Y 0 j)
    (Z : Matrix (Fin 2) (Fin 2) (R ⊗[K] R)) (hZE : ∀ i j, Z i j ∈ E)
    (hZ : leftFundamental K Y * Z = rightFundamental K Y)
    {n : ℕ} {L : ℕ → C} {i₀ : ℕ} (hi₀ : i₀ ∈ Finset.range (n + 1)) (hL : L i₀ ≠ 0)
    (hGL : ∀ g ∈ galoisMonoid E Z hZE (tensorDifferentialPoints E hEδ), ∀ i j,
      g i j ∈ linearJetSolutions n L) :
    ∃ B : Matrix (Fin 2) (Fin 2) K,
      B.map ((σK : K ≃+* K) : K →+* K) * A = matrixDeriv A + A * B :=
  isomonodromy_of_no_riccati_of_zeroSet E hEδ b hgen hindep hcompat hconstC hσδ hsimple hric A Y
    hsys hY1 hYrec Z hZE hZ (linearJetPolynomial_ne_zero hi₀ hL)
    (eval_linearJetPolynomial_eq_zero_of_scalarSpan
      (galoisMonoid E Z hZE (tensorDifferentialPoints E hEδ)) hGL)

end

end GaloisForLFunctions.HTGeometry
