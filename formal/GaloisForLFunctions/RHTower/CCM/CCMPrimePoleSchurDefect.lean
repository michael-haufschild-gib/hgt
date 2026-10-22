import GaloisForLFunctions.RHTower.CCM.CCMPrimePoleSchurEdge
import GaloisForLFunctions.HTGeometry.L2PairingEnergy

/-!
# Actual-prime phase control by the pole-profile Schur defect

Every actual prime-power edge contributes its full complex squared difference.
The sum of these nonnegative energies is the row potential minus the actual
prime Rayleigh pairing. Consequently Schur near-saturation controls all edges
simultaneously, and the source lower bound retains this energy instead of
discarding it in the Schur estimate.
-/

open Complex MeasureTheory Set Filter
open scoped ENNReal InnerProduct BigOperators
noncomputable section
namespace RHTower

def ccmPrimePoleSchurEnergy (a : SuzukiPositiveAperture) (f : SoninL2) : ℝ :=
  ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2*a.1)⌋₊,
    (ArithmeticFunction.vonMangoldt n / Real.sqrt n) * ccmPrimePoleEdgeEnergy a (Real.log n) f

def ccmPrimePoleRowPotential (a : SuzukiPositiveAperture) (f : SoninL2) : ℝ :=
  ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2*a.1)⌋₊,
    (ArithmeticFunction.vonMangoldt n / Real.sqrt n) *
      ((∫ x : ℝ, ccmPrimePoleRowDensity a (Real.log n) f x) +
        (∫ x : ℝ, ccmPrimePoleRowDensity a (-Real.log n) f x))

def ccmPrimePoleSchurEnvelope (a : SuzukiPositiveAperture) : ℝ :=
  Real.log 4 * Real.exp a.1 + 4*a.1 * Real.exp (a.1/2) + 2*a.1 + (Real.log 4 + 4)

theorem ccmPrimePoleSchurEnergy_nonneg (a : SuzukiPositiveAperture) (f : SoninL2) :
    0 ≤ ccmPrimePoleSchurEnergy a f :=
  Finset.sum_nonneg fun n _ => mul_nonneg
    (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _))
    (ccmPrimePoleEdgeEnergy_nonneg a (Real.log n) f)

private theorem negative_shift_pair (h : ℝ) (f : SoninL2) :
    (inner ℂ (logTranslationCLM (-h) f) f).re =
      (inner ℂ (logTranslationCLM h f) f).re := by
  rw [inner_logTranslationCLM, neg_neg]
  exact inner_re_symm (𝕜 := ℂ) _ _

/-- The exact complex phase loss in the literal finite-prime Schur estimate. -/
theorem ccmPrimePoleSchurEnergy_add_prime_eq_rowPotential
    (a : SuzukiPositiveAperture) (f : suzukiApertureHilbert a) :
    ccmPrimePoleSchurEnergy a f.1 + (inner ℂ (ccmFinitePrimeOperator a f) f).re =
      ccmPrimePoleRowPotential a f.1 := by
  rw [inner_ccmFinitePrimeOperator, Complex.re_sum]
  unfold ccmPrimePoleSchurEnergy ccmPrimePoleRowPotential
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n _
  rw [inner_ccmPrimeTransportOperator, ccmPrimePoleEdgeEnergy_eq_rows_sub_pair]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero, Complex.add_re, negative_shift_pair]
  ring

theorem ccmPrimePoleRowPotential_eq_integral (a : SuzukiPositiveAperture) (f : SoninL2) :
    ccmPrimePoleRowPotential a f =
      ∫ x : ℝ, ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2*a.1)⌋₊,
        (ArithmeticFunction.vonMangoldt n / Real.sqrt n) *
          (ccmPrimePoleRowDensity a (Real.log n) f x +
            ccmPrimePoleRowDensity a (-Real.log n) f x) := by
  unfold ccmPrimePoleRowPotential
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro n _
    rw [integral_const_mul, integral_add (integrable_ccmPrimePoleRowDensity a _ f)
      (integrable_ccmPrimePoleRowDensity a _ f)]
  · intro n _
    exact ((integrable_ccmPrimePoleRowDensity a _ f).add
      (integrable_ccmPrimePoleRowDensity a _ f)).const_mul _

private theorem actual_row_le (a : SuzukiPositiveAperture)
    {x : ℝ} (hx : x ∈ centralInterval a.1) :
    (∑ n ∈ Finset.Icc 2 ⌊Real.exp (2*a.1)⌋₊,
      (ArithmeticFunction.vonMangoldt n / Real.sqrt n) *
        ((centralInterval a.1).indicator primePoleProfile (x-Real.log n) +
          (centralInterval a.1).indicator primePoleProfile (x+Real.log n))) ≤
      ccmPrimePoleSchurEnvelope a * primePoleProfile x := by
  have h := primePoleRow_le a (Real.log 4) (4*a.1) 0 (Real.log 4+4)
    (by linarith [a.property])
    (fun X hX hXa => by
      have hp := Chebyshev.psi_le hX
      have hlog : Real.log X ≤ 2*a.1 := by
        rw [← Real.log_exp (2*a.1)]
        exact Real.log_le_log (by linarith) hXa
      nlinarith [Real.sqrt_nonneg X, Real.log_nonneg hX])
    (fun X hX _ => ccmReciprocalMangoldtCumulative_le_log_add X hX) hx
  simpa only [ccmPrimePoleSchurEnvelope, zero_add, add_zero] using h

theorem ccmPrimePoleRowPotential_le_of_row
    (a : SuzukiPositiveAperture) (f : suzukiApertureHilbert a) (L : ℝ)
    (hrow : ∀ x ∈ centralInterval a.1,
      (∑ n ∈ Finset.Icc 2 ⌊Real.exp (2*a.1)⌋₊,
        (ArithmeticFunction.vonMangoldt n / Real.sqrt n) *
          ((centralInterval a.1).indicator primePoleProfile (x-Real.log n) +
            (centralInterval a.1).indicator primePoleProfile (x+Real.log n))) ≤
        L * primePoleProfile x) :
    ccmPrimePoleRowPotential a f.1 ≤ L * ‖f‖ ^ 2 := by
  have hnorm : Integrable (fun x : ℝ => ‖f.1 x‖ ^ 2) :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable f.1)).mp (Lp.memLp f.1)
  have hsum : Integrable (fun x : ℝ => ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2*a.1)⌋₊,
      (ArithmeticFunction.vonMangoldt n / Real.sqrt n) *
        (ccmPrimePoleRowDensity a (Real.log n) f.1 x +
          ccmPrimePoleRowDensity a (-Real.log n) f.1 x)) := by
    exact integrable_finsetSum _ fun n _ =>
      ((integrable_ccmPrimePoleRowDensity a _ f.1).add
        (integrable_ccmPrimePoleRowDensity a _ f.1)).const_mul _
  have hf := indicatorCutoff_ae (centralInterval a.1) (measurableSet_centralInterval a.1) f.1
  rw [indicatorCutoff_suzukiApertureHilbert] at hf
  rw [ccmPrimePoleRowPotential_eq_integral,
    show ‖f‖ ^ 2 = ∫ x : ℝ, ‖f.1 x‖ ^ 2 from
      HTGeometry.norm_l2_sq_eq_integral_norm_sq volume f.1, ← integral_const_mul]
  apply integral_mono_ae hsum (hnorm.const_mul _)
  filter_upwards [hf] with x hf
  by_cases hx : x ∈ centralInterval a.1
  · have hfactor : (∑ n ∈ Finset.Icc 2 ⌊Real.exp (2*a.1)⌋₊,
        (ArithmeticFunction.vonMangoldt n / Real.sqrt n) *
          (ccmPrimePoleRowDensity a (Real.log n) f.1 x +
            ccmPrimePoleRowDensity a (-Real.log n) f.1 x)) =
        ((∑ n ∈ Finset.Icc 2 ⌊Real.exp (2*a.1)⌋₊,
          (ArithmeticFunction.vonMangoldt n / Real.sqrt n) *
            ((centralInterval a.1).indicator primePoleProfile (x-Real.log n) +
              (centralInterval a.1).indicator primePoleProfile (x+Real.log n))) /
            primePoleProfile x) * ‖f.1 x‖ ^ 2 := by
      rw [Finset.sum_div, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro n _
      unfold ccmPrimePoleRowDensity
      rw [sub_eq_add_neg]
      ring
    rw [hfactor]
    exact mul_le_mul_of_nonneg_right
      ((div_le_iff₀ (primePoleProfile_pos x)).mpr (hrow x hx)) (sq_nonneg _)
  · have hz : f.1 x = 0 := by rw [hf, indicator_of_notMem hx]
    simp only [ccmPrimePoleRowDensity, hz, norm_zero, zero_pow two_ne_zero,
      mul_zero, zero_add, Finset.sum_const_zero, le_refl]

theorem ccmPrimePoleRowPotential_le_envelope
    (a : SuzukiPositiveAperture) (f : suzukiApertureHilbert a) :
    ccmPrimePoleRowPotential a f.1 ≤ ccmPrimePoleSchurEnvelope a * ‖f‖ ^ 2 :=
  ccmPrimePoleRowPotential_le_of_row a f _ fun _ hx => actual_row_le a hx

/-- Coefficient-uniform inverse estimate: every actual edge is charged to one common deficit. -/
theorem ccmPrimePoleSchurEnergy_le_deficit
    (a : SuzukiPositiveAperture) (f : suzukiApertureHilbert a) :
    ccmPrimePoleSchurEnergy a f.1 ≤ ccmPrimePoleSchurEnvelope a * ‖f‖ ^ 2 -
      (inner ℂ (ccmFinitePrimeOperator a f) f).re := by
  have h := ccmPrimePoleSchurEnergy_add_prime_eq_rowPotential a f
  have hb := ccmPrimePoleRowPotential_le_envelope a f
  linarith

/-- The full signed source keeps both pole cross terms and all prime edge energy. -/
theorem ccmRestrictedWeilSourceQuadratic_ge_schurEdgeEnergy
    (a : SuzukiPositiveAperture) (u : CCMArchimedeanFormDomain a) :
    let f := ccmArchimedeanFormToAperture a u
    ‖u.1‖ ^ 2 + (2 * gammaHardyPhaseRate 0 - 1 - ccmPrimePoleSchurEnvelope a) * ‖f‖ ^ 2 +
      (inner ℂ (ccmPolarOperator a f) f).re + ccmPrimePoleSchurEnergy a f.1 ≤
        ccmRestrictedWeilSourceQuadratic a u := by
  let f := ccmArchimedeanFormToAperture a u
  have he := ccmPrimePoleSchurEnergy_le_deficit a f
  rw [ccmRestrictedWeilSourceQuadratic_eq_formNorm_sq_add_boundedDiagonal]
  unfold ccmRestrictedWeilBoundedDiagonal
  rw [inner_ccmRestrictedWeilBoundedRemainder, Complex.sub_re, Complex.add_re]
  have hself : (ccmArchimedeanRemainderScalar * inner ℂ f f).re =
      (2 * gammaHardyPhaseRate 0 - 1) * ‖f‖ ^ 2 := by
    have hff : inner ℂ f f = ((‖f‖ ^ 2 : ℝ) : ℂ) := by
      rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ) f]
      norm_cast
    unfold ccmArchimedeanRemainderScalar
    rw [hff, ← Complex.ofReal_mul, Complex.ofReal_re]
  dsimp only
  change _ ≤ ‖u.1‖ ^ 2 +
    ((ccmArchimedeanRemainderScalar * inner ℂ f f).re +
      (inner ℂ (ccmPolarOperator a f) f).re -
      (inner ℂ (ccmFinitePrimeOperator a f) f).re)
  rw [hself]
  nlinarith

end RHTower
