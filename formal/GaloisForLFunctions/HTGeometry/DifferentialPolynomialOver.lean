import GaloisForLFunctions.HTGeometry.DifferentialPolynomial

/-!
# Differential polynomials over a differential coefficient field

The constant-coefficient jet derivation in `DifferentialPolynomial` is not the derivation required
for parameterized Picard--Vessiot relation ideals over a differential base field. This module
constructs the total derivation: differentiate coefficients and shift formal jets. It proves that
jet evaluation into a differential algebra intertwines this total derivation, hence that the full
relation ideal over the base field is derivation-stable.
-/

open scoped Differential

namespace GaloisForLFunctions
noncomputable section

def differentialPolynomialMapCoeffsLinear
    (ι K : Type*) [CommRing K] [Differential K] :
    DifferentialPolynomial ι K →ₗ[ℤ] DifferentialPolynomial ι K :=
  (Finsupp.mapRange.linearMap Differential.deriv.toLinearMap :
    DifferentialPolynomial ι K →ₗ[ℤ] DifferentialPolynomial ι K)

@[simp] theorem differentialPolynomialMapCoeffsLinear_monomial
    {ι K : Type*} [CommRing K] [Differential K]
    (s : (ι × ℕ) →₀ ℕ) (a : K) :
    differentialPolynomialMapCoeffsLinear ι K (MvPolynomial.monomial s a) =
      MvPolynomial.monomial s a′ := by
  change (Finsupp.mapRange.linearMap Differential.deriv.toLinearMap)
    (Finsupp.single s a) = Finsupp.single s a′
  dsimp only [Finsupp.mapRange.linearMap_apply]
  simp

def differentialPolynomialCoeffDerivation
    (ι K : Type*) [CommRing K] [Differential K] :
    Derivation ℤ (DifferentialPolynomial ι K) (DifferentialPolynomial ι K) where
  toLinearMap :=
    differentialPolynomialMapCoeffsLinear ι K
  map_one_eq_zero' := by
    change (Finsupp.single 0 (1 : K)).mapRange (fun x => x′) (map_zero _) = 0
    simp
  leibniz' P Q := by
    induction P using MvPolynomial.induction_on' with
    | add P₁ P₂ hP₁ hP₂ =>
        simp only [add_mul, map_add, add_smul, smul_add, hP₁, hP₂]
        abel
    | monomial s a =>
        induction Q using MvPolynomial.induction_on' with
        | add Q₁ Q₂ hQ₁ hQ₂ =>
            simp only [mul_add, map_add, add_smul, smul_add, hQ₁, hQ₂]
            abel
        | monomial t b =>
            rw [MvPolynomial.monomial_mul]
            change differentialPolynomialMapCoeffsLinear ι K
                (MvPolynomial.monomial (s + t) (a * b)) = _
            have ht := differentialPolynomialMapCoeffsLinear_monomial (ι := ι) t b
            have hs := differentialPolynomialMapCoeffsLinear_monomial (ι := ι) s a
            calc
              differentialPolynomialMapCoeffsLinear ι K
                  (MvPolynomial.monomial (s + t) (a * b)) =
                  MvPolynomial.monomial (s + t) (a * b)′ :=
                differentialPolynomialMapCoeffsLinear_monomial _ _
              _ = MvPolynomial.monomial (s + t) (a * b′) +
                  MvPolynomial.monomial (s + t) (b * a′) := by
                rw [Derivation.leibniz, map_add]
                simp only [smul_eq_mul]
              _ = MvPolynomial.monomial s a * MvPolynomial.monomial t b′ +
                  MvPolynomial.monomial t b * MvPolynomial.monomial s a′ := by
                rw [MvPolynomial.monomial_mul, MvPolynomial.monomial_mul]
                rw [add_comm t s]
              _ = MvPolynomial.monomial s a *
                    differentialPolynomialMapCoeffsLinear ι K (MvPolynomial.monomial t b) +
                  MvPolynomial.monomial t b *
                    differentialPolynomialMapCoeffsLinear ι K (MvPolynomial.monomial s a) := by
                exact congrArg₂ (· + ·)
                  (congrArg (MvPolynomial.monomial s a * ·) ht.symm)
                  (congrArg (MvPolynomial.monomial t b * ·) hs.symm)

@[simp] theorem differentialPolynomialCoeffDerivation_monomial
    {ι K : Type*} [CommRing K] [Differential K]
    (s : (ι × ℕ) →₀ ℕ) (a : K) :
    differentialPolynomialCoeffDerivation ι K (MvPolynomial.monomial s a) =
      MvPolynomial.monomial s a′ := by
  exact differentialPolynomialMapCoeffsLinear_monomial s a

@[simp] theorem differentialPolynomialCoeffDerivation_C
    {ι K : Type*} [CommRing K] [Differential K] (a : K) :
    differentialPolynomialCoeffDerivation ι K (MvPolynomial.C a) = MvPolynomial.C a′ := by
  rw [MvPolynomial.C_apply, differentialPolynomialCoeffDerivation_monomial,
    MvPolynomial.C_apply]

@[simp] theorem differentialPolynomialCoeffDerivation_X
    {ι K : Type*} [CommRing K] [Differential K] (i : ι) (n : ℕ) :
    differentialPolynomialCoeffDerivation ι K (MvPolynomial.X (i,n)) = 0 := by
  rw [MvPolynomial.X]
  simp

def differentialPolynomialOverDerivation
    (ι K : Type*) [CommRing K] [Differential K] :
    Derivation ℤ (DifferentialPolynomial ι K) (DifferentialPolynomial ι K) :=
  differentialPolynomialCoeffDerivation ι K +
    (differentialPolynomialDerivation ι K).restrictScalars ℤ

@[simp] theorem differentialPolynomialOverDerivation_C
    {ι K : Type*} [CommRing K] [Differential K] (a : K) :
    differentialPolynomialOverDerivation ι K (MvPolynomial.C a) = MvPolynomial.C a′ := by
  simp [differentialPolynomialOverDerivation]

@[simp] theorem differentialPolynomialOverDerivation_X
    {ι K : Type*} [CommRing K] [Differential K] (i : ι) (n : ℕ) :
    differentialPolynomialOverDerivation ι K (MvPolynomial.X (i,n)) =
      MvPolynomial.X (i,n+1) := by
  simp [differentialPolynomialOverDerivation]

/-- Evaluate a differential polynomial with coefficients in the differential base field `K`. -/
def differentialPolynomialEvalOver
    {ι K L : Type*} [CommRing K] [CommRing L] [Algebra K L] [Differential L]
    (x : ι → L) : DifferentialPolynomial ι K →ₐ[K] L :=
  MvPolynomial.aeval fun p : ι × ℕ => differentialJet p.2 (x p.1)

@[simp] theorem differentialPolynomialEvalOver_X
    {ι K L : Type*} [CommRing K] [CommRing L] [Algebra K L] [Differential L]
    (x : ι → L) (i : ι) (n : ℕ) :
    differentialPolynomialEvalOver (K := K) x (MvPolynomial.X (i,n)) =
      differentialJet n (x i) := by
  simp [differentialPolynomialEvalOver]

@[simp] theorem differentialPolynomialEvalOver_C
    {ι K L : Type*} [CommRing K] [CommRing L] [Algebra K L] [Differential L]
    (x : ι → L) (a : K) :
    differentialPolynomialEvalOver (K := K) x (MvPolynomial.C a) = algebraMap K L a := by
  simp [differentialPolynomialEvalOver]

theorem differentialPolynomialEvalOver_derivation
    {ι K L : Type*} [CommRing K] [CommRing L] [Algebra K L]
    [Differential K] [Differential L] [DifferentialAlgebra K L]
    (x : ι → L) (P : DifferentialPolynomial ι K) :
    differentialPolynomialEvalOver (K := K) x (differentialPolynomialOverDerivation ι K P) =
      (differentialPolynomialEvalOver (K := K) x P)′ := by
  induction P using MvPolynomial.induction_on with
  | C c =>
      simp only [differentialPolynomialOverDerivation_C, differentialPolynomialEvalOver_C]
      exact (DifferentialAlgebra.deriv_algebraMap c).symm
  | add P Q hP hQ =>
      simp only [map_add, hP, hQ]
  | mul_X P p hP =>
      rcases p with ⟨i,n⟩
      rw [Derivation.leibniz]
      simp only [smul_eq_mul, map_add, map_mul, hP,
        differentialPolynomialEvalOver_X]
      rw [differentialPolynomialOverDerivation_X, differentialPolynomialEvalOver_X,
        differentialJet_succ]
      rw [Derivation.leibniz]
      simp only [smul_eq_mul]

/-- The ideal of differential-polynomial relations over the differential base field. -/
def differentialRelationIdealOver
    {ι K L : Type*} [CommRing K] [CommRing L] [Algebra K L] [Differential L]
    (x : ι → L) : Ideal (DifferentialPolynomial ι K) :=
  RingHom.ker (differentialPolynomialEvalOver (K := K) x).toRingHom

@[simp] theorem mem_differentialRelationIdealOver_iff
    {ι K L : Type*} [CommRing K] [CommRing L] [Algebra K L] [Differential L]
    (x : ι → L) (P : DifferentialPolynomial ι K) :
    P ∈ differentialRelationIdealOver x ↔ differentialPolynomialEvalOver (K := K) x P = 0 :=
  Iff.rfl

theorem differentialPolynomialOverDerivation_mem_relationIdeal
    {ι K L : Type*} [CommRing K] [CommRing L] [Algebra K L]
    [Differential K] [Differential L] [DifferentialAlgebra K L]
    (x : ι → L) {P : DifferentialPolynomial ι K}
    (hP : P ∈ differentialRelationIdealOver x) :
    differentialPolynomialOverDerivation ι K P ∈ differentialRelationIdealOver x := by
  rw [mem_differentialRelationIdealOver_iff,
    differentialPolynomialEvalOver_derivation]
  rw [mem_differentialRelationIdealOver_iff] at hP
  rw [hP, map_zero]

/-- Differential independence over a differential base field is exactly triviality of the full
differential-polynomial relation ideal over that field. -/
theorem differentialIndependent_iff_relationIdealOver_eq_bot
    {ι K L : Type*} [CommRing K] [CommRing L] [Algebra K L] [Differential L]
    (x : ι → L) :
    DifferentialIndependent K x ↔ differentialRelationIdealOver (K := K) x = ⊥ := by
  unfold DifferentialIndependent differentialRelationIdealOver differentialPolynomialEvalOver
  exact algebraicIndependent_iff_ker_eq_bot

end
end GaloisForLFunctions
