import GaloisForLFunctions.DifferenceDifferential
import Mathlib.Algebra.MvPolynomial.Derivation
import Mathlib.Tactic

/-!
# Differential polynomial relations and their additive Hopf structure

The differential polynomial ring in a family `xᵢ` is implemented as the ordinary multivariate
polynomial ring on formal jets `X_(i,n)`. Its derivation shifts the jet order. This file connects
jet evaluation to `DifferentialIndependent`, proves that relation ideals are differential ideals,
and defines the additive comultiplication `X_(i,n) ↦ X_(i,n)^L + X_(i,n)^R`.

This is the algebraic foundation for the special additive differential-algebraic subgroup theorem
needed by simultaneous telescoping.
-/

open scoped Differential

namespace GaloisForLFunctions

noncomputable section

/-- Constant-coefficient differential polynomials in a family indexed by `ι`. -/
abbrev DifferentialPolynomial (ι C : Type*) [CommSemiring C] := MvPolynomial (ι × ℕ) C

/-- The jet-shift derivation `D X_(i,n) = X_(i,n+1)`. -/
def differentialPolynomialDerivation (ι C : Type*) [CommRing C] :
    Derivation C (DifferentialPolynomial ι C) (DifferentialPolynomial ι C) :=
  MvPolynomial.mkDerivation C fun p : ι × ℕ => MvPolynomial.X (p.1, p.2 + 1)

@[simp]
theorem differentialPolynomialDerivation_X
    {ι C : Type*} [CommRing C] (i : ι) (n : ℕ) :
    differentialPolynomialDerivation ι C (MvPolynomial.X (i, n)) =
      MvPolynomial.X (i, n + 1) := by
  simp [differentialPolynomialDerivation]

/-- The formal jet-shift derivation as a `Differential` instance. -/
noncomputable instance differentialPolynomial.instDifferential
    (ι C : Type*) [CommRing C] : Differential (DifferentialPolynomial ι C) where
  deriv := (differentialPolynomialDerivation ι C).restrictScalars ℤ

@[simp]
theorem differentialPolynomial_deriv_X
    {ι C : Type*} [CommRing C] (i : ι) (n : ℕ) :
    (MvPolynomial.X (i, n) : DifferentialPolynomial ι C)′ =
      MvPolynomial.X (i, n + 1) := by
  exact differentialPolynomialDerivation_X i n

@[simp]
theorem differentialJet_differentialPolynomial_X
    {ι C : Type*} [CommRing C] (i : ι) (n : ℕ) :
    differentialJet n (MvPolynomial.X (i, 0) : DifferentialPolynomial ι C) =
      MvPolynomial.X (i, n) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [differentialJet_succ, ih, differentialPolynomial_deriv_X]

theorem differentialJet_add_apply
    {K : Type*} [CommRing K] [Differential K] (n : ℕ) (x y : K) :
    differentialJet n (x + y) = differentialJet n x + differentialJet n y := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [differentialJet_succ, differentialJet_succ, differentialJet_succ, ih, map_add]

@[simp]
theorem differentialPolynomial_deriv_C
    {ι C : Type*} [CommRing C] (c : C) :
    (MvPolynomial.C c : DifferentialPolynomial ι C)′ = 0 := by
  change differentialPolynomialDerivation ι C (MvPolynomial.C c) = 0
  simp [differentialPolynomialDerivation]

/-- Evaluate a differential polynomial by sending `X_(i,n)` to the `n`th jet of `xᵢ`. -/
def differentialPolynomialEval
    {ι C K : Type*} [CommRing C] [CommRing K] [Algebra C K] [Differential K]
    (x : ι → K) : DifferentialPolynomial ι C →ₐ[C] K :=
  MvPolynomial.aeval fun p : ι × ℕ => differentialJet p.2 (x p.1)

@[simp]
theorem differentialPolynomialEval_X
    {ι C K : Type*} [CommRing C] [CommRing K] [Algebra C K] [Differential K]
    (x : ι → K) (i : ι) (n : ℕ) :
    differentialPolynomialEval (C := C) x (MvPolynomial.X (i, n)) = differentialJet n (x i) := by
  simp [differentialPolynomialEval]

/-- Jet evaluation commutes with the derivation when the coefficient field maps to constants. -/
theorem differentialPolynomialEval_derivation
    {ι C K : Type*} [CommRing C] [CommRing K] [Algebra C K] [Differential K]
    (x : ι → K) (hconst : ∀ c : C, (algebraMap C K c)′ = 0)
    (P : DifferentialPolynomial ι C) :
    differentialPolynomialEval (C := C) x (differentialPolynomialDerivation ι C P) =
      (differentialPolynomialEval (C := C) x P)′ := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [differentialPolynomialDerivation, differentialPolynomialEval, hconst]
  | add P Q hP hQ =>
      rw [map_add, map_add, map_add, hP, hQ, map_add]
  | mul_X P p hP =>
      rcases p with ⟨i, n⟩
      rw [Derivation.leibniz]
      simp only [smul_eq_mul]
      rw [map_add, map_mul, map_mul, hP]
      simp only [differentialPolynomialDerivation_X, differentialPolynomialEval_X, map_mul]
      rw [differentialJet_succ]
      rw [Derivation.leibniz]
      ring

/-- The ideal of all constant-coefficient differential polynomial relations of a family. -/
def differentialRelationIdeal
    {ι C K : Type*} [CommRing C] [CommRing K] [Algebra C K] [Differential K]
    (x : ι → K) : Ideal (DifferentialPolynomial ι C) :=
  RingHom.ker (differentialPolynomialEval (C := C) x).toRingHom

@[simp]
theorem mem_differentialRelationIdeal_iff
    {ι C K : Type*} [CommRing C] [CommRing K] [Algebra C K] [Differential K]
    (x : ι → K) (P : DifferentialPolynomial ι C) :
    P ∈ differentialRelationIdeal x ↔ differentialPolynomialEval (C := C) x P = 0 := by
  rfl

/-- Relation ideals are stable under the jet-shift derivation. -/
theorem differentialPolynomialDerivation_mem_relationIdeal
    {ι C K : Type*} [CommRing C] [CommRing K] [Algebra C K] [Differential K]
    (x : ι → K) (hconst : ∀ c : C, (algebraMap C K c)′ = 0)
    {P : DifferentialPolynomial ι C} (hP : P ∈ differentialRelationIdeal x) :
    differentialPolynomialDerivation ι C P ∈ differentialRelationIdeal x := by
  rw [mem_differentialRelationIdeal_iff, differentialPolynomialEval_derivation x hconst P]
  rw [mem_differentialRelationIdeal_iff] at hP
  rw [hP, map_zero]

/-- Differential independence is exactly triviality of the differential relation ideal. -/
theorem differentialIndependent_iff_relationIdeal_eq_bot
    {ι C K : Type*} [CommRing C] [CommRing K] [Algebra C K] [Differential K]
    (x : ι → K) :
    DifferentialIndependent C x ↔ differentialRelationIdeal (C := C) x = ⊥ := by
  unfold DifferentialIndependent differentialRelationIdeal differentialPolynomialEval
  exact algebraicIndependent_iff_ker_eq_bot

/-- The differential polynomial represented by a finite family of operators `Lᵢ ∈ C[D]`. -/
def differentialLinearPolynomial
    {ι C : Type*} [CommRing C] (A : Finset ι) (L : ι → Polynomial C) :
    DifferentialPolynomial ι C :=
  ∑ i ∈ A, (L i).sum fun n c => MvPolynomial.C c * MvPolynomial.X (i, n)

/-- Evaluation of a differential-linear polynomial is the corresponding operator sum. -/
theorem differentialPolynomialEval_differentialLinearPolynomial
    {ι C K : Type*} [Field C] [Field K] [Algebra C K] [Differential K]
    (x : ι → K) (A : Finset ι) (L : ι → Polynomial C) :
    differentialPolynomialEval (C := C) x (differentialLinearPolynomial A L) =
      ∑ i ∈ A, differentialOperatorApply (L i) (x i) := by
  classical
  unfold differentialLinearPolynomial differentialOperatorApply
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Polynomial.sum_def]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro n hn
  simp [differentialPolynomialEval]

/-- Embed differential polynomials into the left variables of a doubled jet ring. -/
def differentialPolynomialLeft
    {ι κ C : Type*} [CommRing C] :
    DifferentialPolynomial ι C →ₐ[C] DifferentialPolynomial (Sum ι κ) C :=
  MvPolynomial.rename fun p => (Sum.inl p.1, p.2)

/-- Embed differential polynomials into the right variables of a doubled jet ring. -/
def differentialPolynomialRight
    {ι κ C : Type*} [CommRing C] :
    DifferentialPolynomial κ C →ₐ[C] DifferentialPolynomial (Sum ι κ) C :=
  MvPolynomial.rename fun p => (Sum.inr p.1, p.2)

@[simp]
theorem differentialPolynomialLeft_X
    {ι κ C : Type*} [CommRing C] (i : ι) (n : ℕ) :
    differentialPolynomialLeft (κ := κ) (C := C) (MvPolynomial.X (i, n)) =
      MvPolynomial.X (Sum.inl i, n) := by
  simp [differentialPolynomialLeft]

@[simp]
theorem differentialPolynomialRight_X
    {ι κ C : Type*} [CommRing C] (i : κ) (n : ℕ) :
    differentialPolynomialRight (ι := ι) (C := C) (MvPolynomial.X (i, n)) =
      MvPolynomial.X (Sum.inr i, n) := by
  simp [differentialPolynomialRight]

@[simp]
theorem differentialPolynomialLeft_C
    {ι κ C : Type*} [CommRing C] (c : C) :
    differentialPolynomialLeft (ι := ι) (κ := κ) (MvPolynomial.C c) = MvPolynomial.C c := by
  simp [differentialPolynomialLeft]

@[simp]
theorem differentialPolynomialRight_C
    {ι κ C : Type*} [CommRing C] (c : C) :
    differentialPolynomialRight (ι := ι) (κ := κ) (MvPolynomial.C c) = MvPolynomial.C c := by
  simp [differentialPolynomialRight]

/-- Additive comultiplication on jets: `X_(i,n) ↦ X_(i,n)^L + X_(i,n)^R`. -/
def differentialAddComultiplication
    {ι C : Type*} [CommRing C] :
    DifferentialPolynomial ι C →ₐ[C] DifferentialPolynomial (Sum ι ι) C :=
  differentialPolynomialEval (C := C) fun i =>
    MvPolynomial.X (Sum.inl i, 0) + MvPolynomial.X (Sum.inr i, 0)

@[simp]
theorem differentialAddComultiplication_X
    {ι C : Type*} [CommRing C] (i : ι) (n : ℕ) :
    differentialAddComultiplication (C := C) (MvPolynomial.X (i, n)) =
      MvPolynomial.X (Sum.inl i, n) + MvPolynomial.X (Sum.inr i, n) := by
  simp [differentialAddComultiplication, differentialPolynomialEval,
    differentialJet_add_apply, differentialJet_differentialPolynomial_X]

@[simp]
theorem differentialAddComultiplication_C
    {ι C : Type*} [CommRing C] (c : C) :
    differentialAddComultiplication (ι := ι) (MvPolynomial.C c) = MvPolynomial.C c := by
  simp [differentialAddComultiplication, differentialPolynomialEval]

/-- Additive comultiplication commutes with the jet-shift derivation. -/
theorem differentialAddComultiplication_derivation
    {ι C : Type*} [CommRing C] (P : DifferentialPolynomial ι C) :
    differentialAddComultiplication (C := C) (differentialPolynomialDerivation ι C P) =
      differentialPolynomialDerivation (Sum ι ι) C
        (differentialAddComultiplication (C := C) P) := by
  exact differentialPolynomialEval_derivation
    (fun i => MvPolynomial.X (Sum.inl i, 0) + MvPolynomial.X (Sum.inr i, 0))
    (fun c => by simp) P

/-- A primitive differential polynomial satisfies `P(X+Y)=P(X)+P(Y)`. -/
def IsPrimitiveDifferentialPolynomial
    {ι C : Type*} [CommRing C] (P : DifferentialPolynomial ι C) : Prop :=
  differentialAddComultiplication (C := C) P =
    differentialPolynomialLeft (κ := ι) P + differentialPolynomialRight (ι := ι) P

/-- Every constant-coefficient differential-linear polynomial is primitive. -/
theorem differentialLinearPolynomial_isPrimitive
    {ι C : Type*} [CommRing C] (A : Finset ι) (L : ι → Polynomial C) :
    IsPrimitiveDifferentialPolynomial (differentialLinearPolynomial A L) := by
  classical
  unfold IsPrimitiveDifferentialPolynomial differentialLinearPolynomial
  simp only [map_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Polynomial.sum_def]
  simp only [map_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  simp only [map_mul, differentialAddComultiplication_C, differentialPolynomialLeft_C,
    differentialPolynomialRight_C, differentialAddComultiplication_X,
    differentialPolynomialLeft_X, differentialPolynomialRight_X]
  ring

/-- Scale every formal jet variable by the same scalar. -/
def differentialPolynomialScale
    {ι C : Type*} [CommRing C] (a : C) :
    DifferentialPolynomial ι C →ₐ[C] DifferentialPolynomial ι C :=
  MvPolynomial.aeval fun p => MvPolynomial.C a * MvPolynomial.X p

@[simp]
theorem differentialPolynomialScale_X
    {ι C : Type*} [CommRing C] (a : C) (i : ι) (n : ℕ) :
    differentialPolynomialScale a (MvPolynomial.X (i, n)) =
      MvPolynomial.C a * MvPolynomial.X (i, n) := by
  simp [differentialPolynomialScale]

/-- Fold the left and right copies of the doubled jet ring onto the same variables. -/
def differentialPolynomialFold
    {ι C : Type*} [CommRing C] :
    DifferentialPolynomial (Sum ι ι) C →ₐ[C] DifferentialPolynomial ι C :=
  MvPolynomial.aeval fun p => MvPolynomial.X (Sum.elim id id p.1, p.2)

@[simp]
theorem differentialPolynomialFold_X_left
    {ι C : Type*} [CommRing C] (i : ι) (n : ℕ) :
    differentialPolynomialFold (C := C) (MvPolynomial.X (Sum.inl i, n)) =
      MvPolynomial.X (i, n) := by
  simp [differentialPolynomialFold]

@[simp]
theorem differentialPolynomialFold_X_right
    {ι C : Type*} [CommRing C] (i : ι) (n : ℕ) :
    differentialPolynomialFold (C := C) (MvPolynomial.X (Sum.inr i, n)) =
      MvPolynomial.X (i, n) := by
  simp [differentialPolynomialFold]

theorem differentialPolynomialFold_left
    {ι C : Type*} [CommRing C] (P : DifferentialPolynomial ι C) :
    differentialPolynomialFold (C := C) (differentialPolynomialLeft (κ := ι) P) = P := by
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add P Q hP hQ => simpa using congrArg₂ (· + ·) hP hQ
  | mul_X P p hP =>
      rcases p with ⟨i, n⟩
      simp [hP]

theorem differentialPolynomialFold_right
    {ι C : Type*} [CommRing C] (P : DifferentialPolynomial ι C) :
    differentialPolynomialFold (C := C) (differentialPolynomialRight (ι := ι) P) = P := by
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add P Q hP hQ => simpa using congrArg₂ (· + ·) hP hQ
  | mul_X P p hP =>
      rcases p with ⟨i, n⟩
      simp [hP]

/-- Folding the additive comultiplication is uniform scaling by two. -/
theorem differentialPolynomialFold_comultiplication
    {ι C : Type*} [CommRing C] (P : DifferentialPolynomial ι C) :
    differentialPolynomialFold (C := C) (differentialAddComultiplication P) =
      differentialPolynomialScale (2 : C) P := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [differentialPolynomialScale, differentialPolynomialFold]
  | add P Q hP hQ => simpa using congrArg₂ (· + ·) hP hQ
  | mul_X P p hP =>
      rcases p with ⟨i, n⟩
      simp only [map_mul, hP, differentialAddComultiplication_X, map_add,
        differentialPolynomialFold_X_left, differentialPolynomialFold_X_right,
        differentialPolynomialScale_X]
      rw [map_ofNat]
      ring

/-- Every primitive polynomial satisfies the characteristic-zero rigidity equation
`P(2X) = 2 P(X)`. -/
theorem primitive_scale_two
    {ι C : Type*} [CommRing C] {P : DifferentialPolynomial ι C}
    (hP : IsPrimitiveDifferentialPolynomial P) :
    differentialPolynomialScale (2 : C) P = 2 * P := by
  rw [← differentialPolynomialFold_comultiplication P, hP, map_add,
    differentialPolynomialFold_left, differentialPolynomialFold_right]
  ring

theorem differentialPolynomialScale_monomial
    {ι C : Type*} [CommRing C] (a c : C) (s : (ι × ℕ) →₀ ℕ) :
    differentialPolynomialScale a (MvPolynomial.monomial s c) =
      MvPolynomial.monomial s (c * a ^ (s.sum fun _ n => n)) := by
  rw [differentialPolynomialScale, MvPolynomial.aeval_monomial]
  rw [show (algebraMap C (DifferentialPolynomial ι C)) c = MvPolynomial.C c by rfl]
  rw [show s.prod (fun i k => (MvPolynomial.C a * MvPolynomial.X i) ^ k) =
      MvPolynomial.C (a ^ (s.sum fun _ n => n)) *
        s.prod (fun i k => MvPolynomial.X i ^ k) by
    simp only [Finsupp.prod]
    simp_rw [mul_pow]
    rw [Finset.prod_mul_distrib]
    simp_rw [← MvPolynomial.C_pow]
    rw [← map_prod, Finset.prod_pow_eq_pow_sum]
    rfl]
  rw [MvPolynomial.monomial_eq]
  rw [map_mul]
  ring

theorem coeff_differentialPolynomialScale
    {ι C : Type*} [CommRing C] (a : C) (P : DifferentialPolynomial ι C)
    (s : (ι × ℕ) →₀ ℕ) :
    MvPolynomial.coeff s (differentialPolynomialScale a P) =
      MvPolynomial.coeff s P * a ^ (s.sum fun _ n => n) := by
  classical
  rw [P.as_sum, map_sum]
  simp_rw [differentialPolynomialScale_monomial]
  rw [MvPolynomial.coeff_sum]
  by_cases h : MvPolynomial.coeff s P = 0 <;> simp [h]

/-- In characteristic zero, every monomial occurring in a primitive differential polynomial has
total jet-degree exactly one. Thus additive differential polynomials have no constant or nonlinear
terms. -/
theorem primitive_support_degree_eq_one
    {ι C : Type*} [Field C] [CharZero C] {P : DifferentialPolynomial ι C}
    (hP : IsPrimitiveDifferentialPolynomial P) {s : (ι × ℕ) →₀ ℕ}
    (hs : s ∈ P.support) : s.sum (fun _ n => n) = 1 := by
  have hc : MvPolynomial.coeff s P ≠ 0 := MvPolynomial.mem_support_iff.mp hs
  have heq := congrArg (MvPolynomial.coeff s) (primitive_scale_two hP)
  rw [coeff_differentialPolynomialScale] at heq
  rw [show (2 : DifferentialPolynomial ι C) = MvPolynomial.C (2 : C) by
    exact (map_ofNat MvPolynomial.C 2).symm] at heq
  rw [MvPolynomial.coeff_C_mul] at heq
  have hpow : (2 : C) ^ (s.sum fun _ n => n) = 2 := by
    exact mul_left_cancel₀ hc (heq.trans (mul_comm _ _))
  have hnat : 2 ^ (s.sum fun _ n => n) = 2 ^ 1 := by
    apply Nat.cast_injective (R := C)
    simpa using hpow
  exact Nat.pow_right_injective (by omega : 1 < 2) hnat

/-- A primitive differential polynomial over a characteristic-zero field is literally a finite
constant-coefficient linear combination of formal jets. The finite index type is its support, so
the representation carries no global finiteness assumption on the original family. -/
theorem primitive_eq_finite_jet_linear_sum
    {ι C : Type*} [Field C] [CharZero C] {P : DifferentialPolynomial ι C}
    (hP : IsPrimitiveDifferentialPolynomial P) :
    ∃ j : (↥P.support) → (ι × ℕ),
      P = ∑ s ∈ (Finset.univ : Finset ↥P.support),
        MvPolynomial.C (MvPolynomial.coeff s.1 P) * MvPolynomial.X (j s) := by
  classical
  have hdeg : ∀ s : ↥P.support, s.1.sum (fun _ n => n) = 1 :=
    fun s => primitive_support_degree_eq_one hP s.2
  let j : (↥P.support) → (ι × ℕ) := fun s =>
    Classical.choose ((Finsupp.sum_eq_one_iff s.1).mp (hdeg s))
  have hj : ∀ s : ↥P.support, s.1 = Finsupp.single (j s) 1 := fun s =>
    Classical.choose_spec ((Finsupp.sum_eq_one_iff s.1).mp (hdeg s))
  refine ⟨j, ?_⟩
  calc
    P = ∑ s ∈ P.support, MvPolynomial.monomial s (MvPolynomial.coeff s P) := P.as_sum
    _ = ∑ s ∈ P.support.attach,
        MvPolynomial.monomial s.1 (MvPolynomial.coeff s.1 P) := by
      exact (Finset.sum_attach P.support fun s =>
        MvPolynomial.monomial s (MvPolynomial.coeff s P)).symm
    _ = ∑ s ∈ (Finset.univ : Finset ↥P.support),
        MvPolynomial.C (MvPolynomial.coeff s.1 P) * MvPolynomial.X (j s) := by
      rw [Finset.univ_eq_attach]
      apply Finset.sum_congr rfl
      intro s hs
      rw [hj s]
      simp [MvPolynomial.monomial_eq]

end

end GaloisForLFunctions
