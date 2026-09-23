import GaloisForLFunctions.HTGeometry.HLSPhysicalAssumptions

/-!
# Algebraic core of arXiv:2607.09738

This file applies the paper's nondegenerate Dirac mechanism to the corpus's concrete
Weyl-basis HLS gamma matrices.  It formalizes the antisymmetric derivative cancellation,
the two-parameter bivector deformation, its chiral factor, and the exact exceptional
locus of the chiral inverse.  These are algebraic statements; no field equation,
equations of motion, or extra axiom is introduced.
-/

open Complex Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Dirac bivector generator `σ^{μν} = (i/2)[γ^μ,γ^ν]` in the corpus's HLS basis. -/
def hlsDiracBivector (μ ν : Fin 4) :
    Matrix HLSDiracSpinor HLSDiracSpinor ℂ :=
  (Complex.I / (2 : ℂ)) •
    (hlsWeylGamma μ * hlsWeylGamma ν - hlsWeylGamma ν * hlsWeylGamma μ)

theorem hlsDiracBivector_antisymmetric (μ ν : Fin 4) :
    hlsDiracBivector ν μ = -hlsDiracBivector μ ν := by
  simp [hlsDiracBivector, sub_eq_add_neg]

@[simp] theorem hlsDiracBivector_self (μ : Fin 4) :
    hlsDiracBivector μ μ = 0 := by
  simp [hlsDiracBivector]

/-- Chirality commutes with every Dirac bivector, obtained by applying gamma-five
anticommutation twice. -/
theorem hlsWeylGammaFive_commutes_bivector (μ ν : Fin 4) :
    hlsWeylGammaFive * hlsDiracBivector μ ν =
      hlsDiracBivector μ ν * hlsWeylGammaFive := by
  have hμ := hlsWeylGammaFive_anticommutes μ
  have hν := hlsWeylGammaFive_anticommutes ν
  have hμ' := eq_neg_of_add_eq_zero_left hμ
  have hν' := eq_neg_of_add_eq_zero_left hν
  have hμν :
      hlsWeylGammaFive * (hlsWeylGamma μ * hlsWeylGamma ν) =
        (hlsWeylGamma μ * hlsWeylGamma ν) * hlsWeylGammaFive := by
    calc
      hlsWeylGammaFive * (hlsWeylGamma μ * hlsWeylGamma ν) =
          (hlsWeylGammaFive * hlsWeylGamma μ) * hlsWeylGamma ν := by
            rw [Matrix.mul_assoc]
      _ = (-(hlsWeylGamma μ * hlsWeylGammaFive)) * hlsWeylGamma ν := by rw [hμ']
      _ = hlsWeylGamma μ * (hlsWeylGamma ν * hlsWeylGammaFive) := by
            rw [Matrix.neg_mul, Matrix.mul_assoc, hν', Matrix.mul_neg, neg_neg]
      _ = (hlsWeylGamma μ * hlsWeylGamma ν) * hlsWeylGammaFive := by
            rw [Matrix.mul_assoc]
  have hνμ :
      hlsWeylGammaFive * (hlsWeylGamma ν * hlsWeylGamma μ) =
        (hlsWeylGamma ν * hlsWeylGamma μ) * hlsWeylGammaFive := by
    calc
      hlsWeylGammaFive * (hlsWeylGamma ν * hlsWeylGamma μ) =
          (hlsWeylGammaFive * hlsWeylGamma ν) * hlsWeylGamma μ := by
            rw [Matrix.mul_assoc]
      _ = (-(hlsWeylGamma ν * hlsWeylGammaFive)) * hlsWeylGamma μ := by rw [hν']
      _ = hlsWeylGamma ν * (hlsWeylGamma μ * hlsWeylGammaFive) := by
            rw [Matrix.neg_mul, Matrix.mul_assoc, hμ', Matrix.mul_neg, neg_neg]
      _ = (hlsWeylGamma ν * hlsWeylGamma μ) * hlsWeylGammaFive := by
            rw [Matrix.mul_assoc]
  simp only [hlsDiracBivector, Matrix.mul_smul, Matrix.smul_mul]
  congr 1
  rw [mul_sub, sub_mul, hμν, hνμ]

/-- Hodge-dual bivector in the convention `⋆σ = -i σ γ⁵` used by the paper. -/
def hlsDiracDualBivector (μ ν : Fin 4) :
    Matrix HLSDiracSpinor HLSDiracSpinor ℂ :=
  (-Complex.I) • (hlsDiracBivector μ ν * hlsWeylGammaFive)

theorem hlsDiracDualBivector_antisymmetric (μ ν : Fin 4) :
    hlsDiracDualBivector ν μ = -hlsDiracDualBivector μ ν := by
  rw [hlsDiracDualBivector, hlsDiracDualBivector,
    hlsDiracBivector_antisymmetric]
  simp

/-- The paper's most general two-parameter bivector deformation. -/
def hlsNondegenerateDiracBivector
    (ell ellFive : ℝ) (μ ν : Fin 4) :
    Matrix HLSDiracSpinor HLSDiracSpinor ℂ :=
  (ell : ℂ) • hlsDiracBivector μ ν +
    (ellFive : ℂ) • hlsDiracDualBivector μ ν

theorem hlsNondegenerateDiracBivector_antisymmetric
    (ell ellFive : ℝ) (μ ν : Fin 4) :
    hlsNondegenerateDiracBivector ell ellFive ν μ =
      -hlsNondegenerateDiracBivector ell ellFive μ ν := by
  rw [hlsNondegenerateDiracBivector, hlsNondegenerateDiracBivector,
    hlsDiracBivector_antisymmetric, hlsDiracDualBivector_antisymmetric]
  module

/-- Chiral factor multiplying the ordinary bivector in the two-parameter deformation. -/
def hlsDiracChiralCoefficient (ell ellFive : ℝ) :
    Matrix HLSDiracSpinor HLSDiracSpinor ℂ :=
  (ell : ℂ) • 1 - (Complex.I * (ellFive : ℂ)) • hlsWeylGammaFive

/-- Sign-conjugate chiral factor. -/
def hlsDiracChiralConjugate (ell ellFive : ℝ) :
    Matrix HLSDiracSpinor HLSDiracSpinor ℂ :=
  (ell : ℂ) • 1 + (Complex.I * (ellFive : ℂ)) • hlsWeylGammaFive

/-- Proposition 2's two couplings factor through one chiral coefficient. -/
theorem hlsNondegenerateDiracBivector_factor
    (ell ellFive : ℝ) (μ ν : Fin 4) :
    hlsNondegenerateDiracBivector ell ellFive μ ν =
      hlsDiracChiralCoefficient ell ellFive * hlsDiracBivector μ ν := by
  rw [hlsNondegenerateDiracBivector, hlsDiracDualBivector,
    hlsDiracChiralCoefficient]
  have hcomm := hlsWeylGammaFive_commutes_bivector μ ν
  simp only [sub_mul, Matrix.smul_mul, one_mul, smul_smul]
  rw [hcomm]
  have hc : (ellFive : ℂ) * (-Complex.I) =
      -(Complex.I * (ellFive : ℂ)) := by ring
  rw [hc]
  simp [sub_eq_add_neg]

private theorem hlsGammaFive_chiral_product (a b : ℂ) :
    (a • 1 - b • hlsWeylGammaFive) *
        (a • 1 + b • hlsWeylGammaFive) =
      (a * a - b * b) • 1 := by
  simp only [sub_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul,
    one_mul, mul_one, smul_smul]
  rw [hlsWeylGammaFive_squared]
  module

private theorem hlsGammaFive_chiral_product_reverse (a b : ℂ) :
    (a • 1 + b • hlsWeylGammaFive) *
        (a • 1 - b • hlsWeylGammaFive) =
      (a * a - b * b) • 1 := by
  simp only [add_mul, mul_sub, Matrix.smul_mul, Matrix.mul_smul,
    one_mul, mul_one, smul_smul]
  rw [hlsWeylGammaFive_squared]
  module

private theorem complex_chiral_denominator (ell ellFive : ℝ) :
    (ell : ℂ) * (ell : ℂ) -
        (Complex.I * (ellFive : ℂ)) * (Complex.I * (ellFive : ℂ)) =
      ((ell ^ (2 : ℕ) + ellFive ^ (2 : ℕ) : ℝ) : ℂ) := by
  calc
    (ell : ℂ) * (ell : ℂ) -
        (Complex.I * (ellFive : ℂ)) * (Complex.I * (ellFive : ℂ)) =
      (ell : ℂ) ^ (2 : ℕ) - Complex.I ^ (2 : ℕ) * (ellFive : ℂ) ^ (2 : ℕ) := by ring
    _ = ((ell ^ (2 : ℕ) + ellFive ^ (2 : ℕ) : ℝ) : ℂ) := by
      rw [Complex.I_sq]
      push_cast
      ring

/-- Both chiral factors multiply to the scalar denominator `ell² + ellFive²`. -/
theorem hlsDiracChiralCoefficient_mul_conjugate (ell ellFive : ℝ) :
    hlsDiracChiralCoefficient ell ellFive *
        hlsDiracChiralConjugate ell ellFive =
      ((ell ^ (2 : ℕ) + ellFive ^ (2 : ℕ) : ℝ) : ℂ) • 1 := by
  rw [hlsDiracChiralCoefficient, hlsDiracChiralConjugate,
    hlsGammaFive_chiral_product,
    complex_chiral_denominator]

theorem hlsDiracChiralConjugate_mul_coefficient (ell ellFive : ℝ) :
    hlsDiracChiralConjugate ell ellFive *
        hlsDiracChiralCoefficient ell ellFive =
      ((ell ^ (2 : ℕ) + ellFive ^ (2 : ℕ) : ℝ) : ℂ) • 1 := by
  rw [hlsDiracChiralCoefficient, hlsDiracChiralConjugate,
    hlsGammaFive_chiral_product_reverse,
    complex_chiral_denominator]

/-- The real denominator vanishes at exactly one coupling pair. -/
theorem hlsDiracChiralDenominator_eq_zero_iff (ell ellFive : ℝ) :
    ell ^ (2 : ℕ) + ellFive ^ (2 : ℕ) = 0 ↔ ell = 0 ∧ ellFive = 0 := by
  constructor
  · intro h
    constructor <;> nlinarith [sq_nonneg ell, sq_nonneg ellFive]
  · rintro ⟨rfl, rfl⟩
    norm_num

/-- Totalized inverse: it is the true two-sided inverse off the unique degenerate pair
and is zero at that pair. -/
def hlsDiracChiralInverse (ell ellFive : ℝ) :
    Matrix HLSDiracSpinor HLSDiracSpinor ℂ :=
  (((ell ^ (2 : ℕ) + ellFive ^ (2 : ℕ))⁻¹ : ℝ) : ℂ) •
    hlsDiracChiralConjugate ell ellFive

theorem hlsDiracChiralCoefficient_mul_inverse (ell ellFive : ℝ) :
    hlsDiracChiralCoefficient ell ellFive *
        hlsDiracChiralInverse ell ellFive =
      if ell = 0 ∧ ellFive = 0 then 0 else 1 := by
  by_cases h : ell = 0 ∧ ellFive = 0
  · rcases h with ⟨rfl, rfl⟩
    simp [hlsDiracChiralCoefficient, hlsDiracChiralInverse,
      hlsDiracChiralConjugate]
  · have hden : ell ^ (2 : ℕ) + ellFive ^ (2 : ℕ) ≠ 0 := by
      intro hzero
      exact h ((hlsDiracChiralDenominator_eq_zero_iff ell ellFive).mp hzero)
    have hinv :
        (((ell ^ (2 : ℕ) + ellFive ^ (2 : ℕ))⁻¹ : ℝ) : ℂ) *
          ((ell ^ (2 : ℕ) + ellFive ^ (2 : ℕ) : ℝ) : ℂ) = 1 := by
      have hdenC : (ell : ℂ) ^ (2 : ℕ) + (ellFive : ℂ) ^ (2 : ℕ) ≠ 0 := by
        exact_mod_cast hden
      push_cast
      exact inv_mul_cancel₀ hdenC
    rw [if_neg h, hlsDiracChiralInverse, Matrix.mul_smul,
      hlsDiracChiralCoefficient_mul_conjugate]
    simp only [smul_smul, hinv, one_smul]

theorem hlsDiracChiralInverse_mul_coefficient (ell ellFive : ℝ) :
    hlsDiracChiralInverse ell ellFive *
        hlsDiracChiralCoefficient ell ellFive =
      if ell = 0 ∧ ellFive = 0 then 0 else 1 := by
  by_cases h : ell = 0 ∧ ellFive = 0
  · rcases h with ⟨rfl, rfl⟩
    simp [hlsDiracChiralCoefficient, hlsDiracChiralInverse,
      hlsDiracChiralConjugate]
  · have hden : ell ^ (2 : ℕ) + ellFive ^ (2 : ℕ) ≠ 0 := by
      intro hzero
      exact h ((hlsDiracChiralDenominator_eq_zero_iff ell ellFive).mp hzero)
    have hinv :
        (((ell ^ (2 : ℕ) + ellFive ^ (2 : ℕ))⁻¹ : ℝ) : ℂ) *
          ((ell ^ (2 : ℕ) + ellFive ^ (2 : ℕ) : ℝ) : ℂ) = 1 := by
      have hdenC : (ell : ℂ) ^ (2 : ℕ) + (ellFive : ℂ) ^ (2 : ℕ) ≠ 0 := by
        exact_mod_cast hden
      push_cast
      exact inv_mul_cancel₀ hdenC
    rw [if_neg h, hlsDiracChiralInverse, Matrix.smul_mul,
      hlsDiracChiralConjugate_mul_coefficient]
    simp only [smul_smul, hinv, one_smul]

/-- Purely algebraic form of Proposition 1: a symmetric second-derivative tensor
contracts to zero against an antisymmetrized coefficient, without equations of motion. -/
theorem symmetricDerivative_antisymmetricCoefficient_contraction_zero
    {ι V : Type*} [Fintype ι] [DecidableEq ι]
    [AddCommGroup V] [Module ℂ V]
    (K : ι → ι → ℂ) (B : ι → ι → V) :
    ∑ i, ∑ j, (K i j + K j i) • (B i j - B j i) = 0 := by
  let X := ∑ i, ∑ j, (K i j + K j i) • (B i j - B j i)
  have hswap : X = ∑ i, ∑ j, (K j i + K i j) • (B j i - B i j) := by
    simpa [X] using
      (Finset.sum_comm :
        (∑ i, ∑ j, (K i j + K j i) • (B i j - B j i)) =
          ∑ j, ∑ i, (K i j + K j i) • (B i j - B j i))
  have hneg : X = -X := by
    calc
      X = ∑ i, ∑ j, (K j i + K i j) • (B j i - B i j) := hswap
      _ = ∑ i, ∑ j, -((K i j + K j i) • (B i j - B j i)) := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        rw [add_comm (K j i)]
        have hsub : B j i - B i j = -(B i j - B j i) := by abel
        rw [hsub, smul_neg]
      _ = -X := by simp [X]
  have htwo : (2 : ℂ) • X = 0 := by
    rw [two_smul]
    nth_rw 2 [hneg]
    exact add_neg_cancel X
  have hunscale := congrArg (fun Y : V => ((2 : ℂ)⁻¹) • Y) htwo
  simpa [smul_smul] using hunscale

/-- Corpus-level Dirac instance of the off-shell antisymmetric-superpotential
cancellation: symmetric derivative data annihilates the gamma commutator. -/
theorem hlsDirac_symmetricDerivative_commutator_contraction_zero
    (K : Fin 4 → Fin 4 → ℂ) :
    ∑ μ, ∑ ν, (K μ ν + K ν μ) •
      (hlsWeylGamma μ * hlsWeylGamma ν -
        hlsWeylGamma ν * hlsWeylGamma μ) = 0 :=
  symmetricDerivative_antisymmetricCoefficient_contraction_zero K
    (fun μ ν => hlsWeylGamma μ * hlsWeylGamma ν)

end

end GaloisForLFunctions.HTGeometry
