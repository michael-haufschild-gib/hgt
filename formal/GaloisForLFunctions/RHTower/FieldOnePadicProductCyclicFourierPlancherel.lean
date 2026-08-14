import GaloisForLFunctions.RHTower.FieldOnePadicProductCyclicHaarQuadrature

/-!
# Exact Fourier--Plancherel theory on product p-adic residue quotients

This file identifies the literal product Haar-integral Fourier coefficients
with the probability-normalized DFT on `∏ᵢ ZMod (pᵢ ^ nᵢ)` and proves exact
Plancherel.  Every cardinality and Haar factor is explicit.
-/

namespace GaloisForLFunctions.RHTower

noncomputable section

open MeasureTheory TopologicalSpace
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (p : ι → ℕ) [∀ i, Fact (p i).Prime]

/-- Probability-normalized DFT on the simultaneous residue quotient. -/
def fieldOnePadicIntProductCyclicFourier (n : ι → ℕ)
    (f : FieldOnePadicIntProduct p → ℂ) :
    FieldOneFiniteCyclicProduct (fun i => p i ^ n i) → ℂ :=
  fun k => (((∏ i, p i ^ n i : ℕ) : ℂ)⁻¹) *
    fieldOneFiniteCyclicProductDFT (fun i => p i ^ n i)
      (fun r => f (fieldOnePadicIntProductResidueRep p n r)) k

/-- Exact finite-level Plancherel identity on `∏ᵢ ℤ_{pᵢ}`. -/
theorem fieldOnePadicIntProductCyclicFourier_plancherel (n : ι → ℕ)
    (f : FieldOnePadicIntProduct p → ℂ)
    (hf2 : Integrable (fun x => (Complex.normSq (f x) : ℂ))
      (fieldOnePadicIntProductNormalizedHaar p))
    (hperiod : ∀ x z : FieldOnePadicIntProduct p,
      f (x + fieldOnePadicIntProductLatticePoint p n z) = f x) :
    ∑ k : FieldOneFiniteCyclicProduct (fun i => p i ^ n i),
        Complex.normSq (fieldOnePadicIntProductCyclicFourier p n f k) =
      ∫ x, Complex.normSq (f x)
        ∂fieldOnePadicIntProductNormalizedHaar p := by
  letI (i : ι) : NeZero (p i ^ n i) :=
    ⟨pow_ne_zero (n i) (Fact.out : Nat.Prime (p i)).ne_zero⟩
  have hperiod2 : ∀ x z : FieldOnePadicIntProduct p,
      (Complex.normSq
        (f (x + fieldOnePadicIntProductLatticePoint p n z)) : ℂ) =
        (Complex.normSq (f x) : ℂ) := by
    intro x z
    rw [hperiod]
  have hquad :=
    fieldOnePadicIntProduct_sampleSum_eq_nsmul_integral p n
      (fun x => (Complex.normSq (f x) : ℂ)) hf2 hperiod2
  rw [integral_complex_ofReal] at hquad
  have hquadR :
      ∑ r : FieldOneFiniteCyclicProduct (fun i => p i ^ n i),
          Complex.normSq
            (f (fieldOnePadicIntProductResidueRep p n r)) =
        ((∏ i, p i ^ n i : ℕ) : ℝ) *
          ∫ x, Complex.normSq (f x)
            ∂fieldOnePadicIntProductNormalizedHaar p := by
    apply Complex.ofReal_injective
    push_cast
    simpa [nsmul_eq_mul] using hquad
  change ∑ k : FieldOneFiniteCyclicProduct (fun i => p i ^ n i),
      Complex.normSq
        ((((∏ i, p i ^ n i : ℕ) : ℂ)⁻¹) *
          fieldOneFiniteCyclicProductDFT (fun i => p i ^ n i)
            (fun r => f (fieldOnePadicIntProductResidueRep p n r)) k) = _
  rw [fieldOneFiniteCyclicProductFourier_normalized_parseval]
  rw [hquadR]
  have hM : ((∏ i, p i ^ n i : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast Finset.prod_ne_zero_iff.mpr fun i _ =>
      pow_ne_zero (n i) (Fact.out : Nat.Prime (p i)).ne_zero
  rw [← mul_assoc, inv_mul_cancel₀ hM, one_mul]

/-- Literal Haar-integral product Fourier coefficient. -/
def fieldOnePadicIntProductCyclicFourierIntegral (n : ι → ℕ)
    (f : FieldOnePadicIntProduct p → ℂ)
    (k : FieldOneFiniteCyclicProduct (fun i => p i ^ n i)) : ℂ :=
  ∫ x,
      fieldOneFiniteCyclicProductCharacter (fun i => p i ^ n i)
        (fieldOnePadicIntProductToFiniteQuotient p n x) k * f x
    ∂fieldOnePadicIntProductNormalizedHaar p

omit [Fintype ι] [DecidableEq ι] in
/-- Coordinatewise residue reduction is continuous. -/
theorem fieldOnePadicIntProductToFiniteQuotient_continuous (n : ι → ℕ) :
    Continuous (fieldOnePadicIntProductToFiniteQuotient p n) := by
  apply continuous_pi
  intro i
  exact (fieldOnePadicInt_toZModPow_continuous (p i) (n i)).comp
    (continuous_apply i)

/-- Literal Haar coefficients equal the normalized product DFT exactly. -/
theorem fieldOnePadicIntProductCyclicFourierIntegral_eq (n : ι → ℕ)
    (f : FieldOnePadicIntProduct p → ℂ)
    (hf : Integrable f (fieldOnePadicIntProductNormalizedHaar p))
    (hperiod : ∀ x z : FieldOnePadicIntProduct p,
      f (x + fieldOnePadicIntProductLatticePoint p n z) = f x)
    (k : FieldOneFiniteCyclicProduct (fun i => p i ^ n i)) :
    fieldOnePadicIntProductCyclicFourierIntegral p n f k =
      fieldOnePadicIntProductCyclicFourier p n f k := by
  letI (i : ι) : NeZero (p i ^ n i) :=
    ⟨pow_ne_zero (n i) (Fact.out : Nat.Prime (p i)).ne_zero⟩
  let g : FieldOnePadicIntProduct p → ℂ := fun x =>
    fieldOneFiniteCyclicProductCharacter (fun i => p i ^ n i)
      (fieldOnePadicIntProductToFiniteQuotient p n x) k * f x
  have hchar : Continuous (fun x : FieldOnePadicIntProduct p =>
      fieldOneFiniteCyclicProductCharacter (fun i => p i ^ n i)
        (fieldOnePadicIntProductToFiniteQuotient p n x) k) := by
    exact (continuous_of_discreteTopology : Continuous
      (fun r : FieldOneFiniteCyclicProduct (fun i => p i ^ n i) =>
        fieldOneFiniteCyclicProductCharacter (fun i => p i ^ n i) r k)).comp
      (fieldOnePadicIntProductToFiniteQuotient_continuous p n)
  have hg : Integrable g (fieldOnePadicIntProductNormalizedHaar p) := by
    exact hf.bdd_mul (c := 1) hchar.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by
        simp [fieldOneFiniteCyclicProductCharacter])
  have hfclass : ∀ {x y : FieldOnePadicIntProduct p},
      fieldOnePadicIntProductToFiniteQuotient p n x =
          fieldOnePadicIntProductToFiniteQuotient p n y → f x = f y :=
    fieldOnePadicIntProduct_classInvariant_of_primePowerInvariant
      p n f hperiod
  have hgclass : ∀ {x y : FieldOnePadicIntProduct p},
      fieldOnePadicIntProductToFiniteQuotient p n x =
          fieldOnePadicIntProductToFiniteQuotient p n y →
        g x = g y := by
    intro x y hxy
    simp only [g]
    rw [hxy, hfclass hxy]
  have hquad := fieldOneFiniteQuotient_sampleSum_eq_nsmul_integral
    (fieldOnePadicIntProductNormalizedHaar p)
    (fieldOnePadicIntProductNormalizedHaar_univ p)
    (fieldOnePadicIntProductToFiniteQuotient p n)
    (fieldOnePadicIntProductToFiniteQuotient_surjective p n)
    (fieldOnePadicIntProductResidueRep p n)
    (fieldOnePadicIntProductResidueRep_spec p n) g hg hgclass
  have hsum :
      ∑ r : FieldOneFiniteCyclicProduct (fun i => p i ^ n i),
          g (fieldOnePadicIntProductResidueRep p n r) =
        fieldOneFiniteCyclicProductDFT (fun i => p i ^ n i)
          (fun r => f (fieldOnePadicIntProductResidueRep p n r)) k := by
    apply Finset.sum_congr rfl
    intro r _
    simp only [g, fieldOnePadicIntProductResidueRep_spec]
  rw [hsum] at hquad
  have hquad' :
      fieldOneFiniteCyclicProductDFT (fun i => p i ^ n i)
          (fun r => f (fieldOnePadicIntProductResidueRep p n r)) k =
        (∏ i, p i ^ n i) •
          (∫ x, g x ∂fieldOnePadicIntProductNormalizedHaar p) := by
    simpa [FieldOneFiniteCyclicProduct] using hquad
  change (∫ x, g x ∂fieldOnePadicIntProductNormalizedHaar p) =
    (((∏ i, p i ^ n i : ℕ) : ℂ)⁻¹) *
      fieldOneFiniteCyclicProductDFT (fun i => p i ^ n i)
        (fun r => f (fieldOnePadicIntProductResidueRep p n r)) k
  rw [hquad']
  have hM : (((∏ i, p i ^ n i : ℕ) : ℂ)) ≠ 0 := by
    exact_mod_cast Finset.prod_ne_zero_iff.mpr fun i _ =>
      pow_ne_zero (n i) (Fact.out : Nat.Prime (p i)).ne_zero
  simp only [nsmul_eq_mul]
  rw [← mul_assoc, inv_mul_cancel₀ hM, one_mul]

/-- Exact Haar-integral Plancherel identity on every simultaneous finite
residue quotient. -/
theorem fieldOnePadicIntProductCyclicFourierIntegral_plancherel
    (n : ι → ℕ) (f : FieldOnePadicIntProduct p → ℂ)
    (hf : Integrable f (fieldOnePadicIntProductNormalizedHaar p))
    (hf2 : Integrable (fun x => (Complex.normSq (f x) : ℂ))
      (fieldOnePadicIntProductNormalizedHaar p))
    (hperiod : ∀ x z : FieldOnePadicIntProduct p,
      f (x + fieldOnePadicIntProductLatticePoint p n z) = f x) :
    ∑ k : FieldOneFiniteCyclicProduct (fun i => p i ^ n i),
        Complex.normSq
          (fieldOnePadicIntProductCyclicFourierIntegral p n f k) =
      ∫ x, Complex.normSq (f x)
        ∂fieldOnePadicIntProductNormalizedHaar p := by
  simp_rw [fieldOnePadicIntProductCyclicFourierIntegral_eq
    p n f hf hperiod]
  exact fieldOnePadicIntProductCyclicFourier_plancherel
    p n f hf2 hperiod

end

end GaloisForLFunctions.RHTower
