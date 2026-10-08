import GaloisForLFunctions.RHTower.WeilWorkHigherDenominatorInversionConstant

/-!
# Actual inverted Maass logarithmic trace

The original cubic coefficients supply both polynomial growth and summable
inverse-square mass. No regularity of a boundary representative is assumed.
-/

noncomputable section

open Complex MeasureTheory Set Filter Topology
open RHTower.MaassBesselSeries
open scoped ContDiff

namespace RHTower.WeilHigherDenominator

def inversionMaassLogPairing (q : ℕ → ℂ) (A B : ℂ) (φ : ℝ → ℂ) (a b y : ℝ) : ℂ :=
  ∫ x in a..b, φ x * maassFun q A B (inversionBoundaryPoint y x) /
    ((y ^ (1 / 2 : ℝ) * Real.log y : ℝ) : ℂ)

def inversionFourierBoundaryPairing (q : ℕ → ℂ) (A : ℂ) (φ : ℝ → ℂ) (a b : ℝ) : ℂ :=
  A * (∫ x in a..b, φ x * (x⁻¹ : ℝ)) -
    4 * ∑' n : ℕ, q (n + 1) * inversionCosineBoundaryPairing φ a b (n + 1)

theorem continuous_cosSeries_inversion {q : ℕ → ℂ} (hq : PolyGrowth q)
    {y : ℝ} (hy : 0 < y) : Continuous (fun x => cosSeries q (inversionBoundaryPoint y x)) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  exact (hasFDerivAt_besselSeries_tsum hq (1 / 2) 0 0 false
    (inversionBoundaryPoint_im_pos hy x)).continuousAt.comp
      (continuous_inversionBoundaryPoint hy).continuousAt

theorem continuous_constTerm_inversion (A B : ℂ) {y : ℝ} (hy : 0 < y) :
    Continuous (fun x => constTerm A B (inversionBoundaryPoint y x)) := by
  have hi := Complex.continuous_im.comp (continuous_inversionBoundaryPoint hy)
  have hn : ∀ x : ℝ, (inversionBoundaryPoint y x).im ≠ 0 :=
    fun x => (inversionBoundaryPoint_im_pos hy x).ne'
  have hp := Complex.continuous_ofReal.comp (hi.rpow_const (p := (1 / 2 : ℝ))
    fun x => Or.inl (hn x))
  have hl := Complex.continuous_ofReal.comp (hi.log hn)
  convert (continuous_const (y := B) |>.mul hp).add
    (continuous_const (y := A) |>.mul (hp.mul hl)) using 1
  ext x
  simp only [constTerm, MaassBesselSeries.sqrtPart, MaassBesselSeries.sqrtLogPart,
    ofReal_mul, Function.comp_def, Pi.add_apply, Pi.mul_apply]

/-- Identify the actual inverted spatial integral, retaining the complete constant term. -/
theorem inversionMaassLogPairing_eq {q : ℕ → ℂ} (hq : PolyGrowth q) (A B : ℂ)
    {φ : ℝ → ℂ} (hφ : Continuous φ) (a b : ℝ) {y : ℝ} (hy : 0 < y) :
    inversionMaassLogPairing q A B φ a b y =
      (∫ x in a..b, φ x * constTerm A B (inversionBoundaryPoint y x) /
        ((y ^ (1 / 2 : ℝ) * Real.log y : ℝ) : ℂ)) +
      4 * (∫ x in a..b, φ x * cosSeries q (inversionBoundaryPoint y x) /
        ((y ^ (1 / 2 : ℝ) * Real.log y : ℝ) : ℂ)) := by
  have hC := ((hφ.mul (continuous_constTerm_inversion A B hy)).intervalIntegrable (μ := volume) a b).div_const
    (((y ^ (1 / 2 : ℝ) * Real.log y : ℝ) : ℂ))
  have hS := ((hφ.mul (continuous_cosSeries_inversion hq hy)).intervalIntegrable (μ := volume) a b).div_const
    (((y ^ (1 / 2 : ℝ) * Real.log y : ℝ) : ℂ))
  simp only [Pi.mul_apply] at hC hS
  unfold inversionMaassLogPairing
  calc
    _ = ∫ x in a..b, φ x * constTerm A B (inversionBoundaryPoint y x) /
          ((y ^ (1 / 2 : ℝ) * Real.log y : ℝ) : ℂ) +
        4 * (φ x * cosSeries q (inversionBoundaryPoint y x) /
          ((y ^ (1 / 2 : ℝ) * Real.log y : ℝ) : ℂ)) := by
      apply intervalIntegral.integral_congr
      intro x _
      dsimp only [maassFun]
      ring
    _ = _ := by
      rw [intervalIntegral.integral_add hC (hS.const_mul 4), intervalIntegral.integral_const_mul]

/-- The full logarithmic boundary limit of the actual inverted Maass function. -/
theorem tendsto_inversionMaassLogPairing {q : ℕ → ℂ} (hq : PolyGrowth q)
    (hsum : Summable fun n : ℕ => ‖q (n + 1)‖ / ((n + 1 : ℕ) : ℝ) ^ 2)
    (A B : ℂ) {φ : ℝ → ℂ} (hφ : ContDiff ℝ ∞ φ) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hs : tsupport φ ⊆ Ioo a b) :
    Tendsto (inversionMaassLogPairing q A B φ a b) (𝓝[>] 0)
      (𝓝 (inversionFourierBoundaryPairing q A φ a b)) := by
  have hC := tendsto_constTerm_inversion_integral A B hφ.continuous ha hab
  have hS := tendsto_cosSeries_inversion_integral hq hsum hφ ha hab hs
  have ht := hC.add (hS.const_mul 4)
  simp only [mul_neg, ← sub_eq_add_neg] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with y hy
  exact (inversionMaassLogPairing_eq hq A B hφ.continuous a b hy).symm

/-- Original cubic data discharge every coefficient premise of the actual inversion trace. -/
theorem degreeTwoQuotient_tendsto_inversionMaassLogPairing {g : ℕ → ℂ} {E : ℂ → ℂ}
    (hD : WeilZetaPower.ZetaPowerDatum 3 g E) (A B : ℂ) {φ : ℝ → ℂ}
    (hφ : ContDiff ℝ ∞ φ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hs : tsupport φ ⊆ Ioo a b) :
    Tendsto (inversionMaassLogPairing (degreeTwoQuotientCoeff g) A B φ a b) (𝓝[>] 0)
      (𝓝 (inversionFourierBoundaryPairing (degreeTwoQuotientCoeff g) A φ a b)) :=
  tendsto_inversionMaassLogPairing
    (MaassConverseLevelOne.polyGrowth_of_summable fun _ hσ =>
      degreeTwoQuotientCoeff_weighted_summable hD hσ)
    (degreeTwoQuotientCoeff_summable_shift_square hD) A B hφ ha hab hs

end RHTower.WeilHigherDenominator
