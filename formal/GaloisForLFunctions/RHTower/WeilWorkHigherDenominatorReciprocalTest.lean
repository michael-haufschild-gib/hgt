import GaloisForLFunctions.RHTower.WeilWorkHigherDenominatorInversionTrace
import GaloisForLFunctions.RHTower.BurnolCoPoissonHeadConstant

/-!
# Reciprocal test transport for the actual inverted trace

The existing co-Poisson reciprocal seed is the weight-one test transformation.
Its positive compact support removes the apparent singularity at zero.
-/

noncomputable section

open Complex MeasureTheory Set Filter Topology
open scoped ContDiff

namespace RHTower.WeilHigherDenominator

theorem support_coPoissonReciprocalSeed_Ioo {φ : ℝ → ℂ} {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hs : Function.support φ ⊆ Ioo a b) :
    Function.support (coPoissonReciprocalSeed φ) ⊆ Ioo b⁻¹ a⁻¹ := by
  intro t ht
  have hn : φ t⁻¹ ≠ 0 := by
    intro hz
    exact ht (by simp only [coPoissonReciprocalSeed, hz, mul_zero])
  have hx := hs hn
  have hi : 0 < t⁻¹ := ha.trans hx.1
  constructor
  · simpa only [inv_inv] using (inv_lt_inv₀ (ha.trans_le hab) hi).mpr hx.2
  · simpa only [inv_inv] using (inv_lt_inv₀ hi ha).mpr hx.1

theorem hasCompactSupport_coPoissonReciprocalSeed_Ioo {φ : ℝ → ℂ} {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hs : Function.support φ ⊆ Ioo a b) :
    HasCompactSupport (coPoissonReciprocalSeed φ) :=
  HasCompactSupport.of_support_subset_isCompact isCompact_Icc
    ((support_coPoissonReciprocalSeed_Ioo ha hab hs).trans Ioo_subset_Icc_self)

/-- The reciprocal transformation preserves smooth tests supported away from zero. -/
theorem contDiff_coPoissonReciprocalSeed_Ioo {φ : ℝ → ℂ} (hφ : ContDiff ℝ ∞ φ)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hs : Function.support φ ⊆ Ioo a b) :
    ContDiff ℝ ∞ (coPoissonReciprocalSeed φ) := by
  apply contDiff_iff_contDiffAt.mpr
  intro t
  rcases eq_or_ne t 0 with rfl | ht
  · apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds (inv_pos.mpr (ha.trans_le hab))] with t ht
    by_contra hn
    have hm := support_coPoissonReciprocalSeed_Ioo ha hab hs hn
    exact (not_lt_of_ge hm.1.le) ht
  · exact (Complex.ofRealCLM.contDiff.contDiffAt.inv (Complex.ofReal_ne_zero.mpr ht)).mul
      (hφ.contDiffAt.comp t (contDiffAt_id.inv ht))

/-- The reciprocal Jacobian and weight give exact transport on a positive interval. -/
theorem reciprocal_test_integral {φ F : ℝ → ℂ} (hφ : Continuous φ) (hF : Continuous F)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ x in a..b, (φ x * (x⁻¹ : ℝ)) * F x⁻¹) =
      ∫ t in b⁻¹..a⁻¹, coPoissonReciprocalSeed φ t * F t := by
  have hx0 (x : ℝ) (hx : x ∈ uIcc a b) : 0 < x :=
    ha.trans_le (uIcc_of_le hab ▸ hx).1
  have hder : ∀ x ∈ uIcc a b, HasDerivAt (fun t : ℝ => t⁻¹) (-(x ^ 2)⁻¹) x :=
    fun x hx => hasDerivAt_inv (hx0 x hx).ne'
  have hdc : ContinuousOn (fun x : ℝ => -(x ^ 2)⁻¹) (uIcc a b) :=
    ((continuousOn_id.pow 2).inv₀ fun x hx => pow_ne_zero 2 (hx0 x hx).ne').neg
  have hn : ∀ t ∈ (Inv.inv : ℝ → ℝ) '' uIcc a b, t ≠ 0 := by
    rintro t ⟨x, hx, rfl⟩
    exact inv_ne_zero (hx0 x hx).ne'
  have hi : ContinuousOn (fun t : ℝ => t⁻¹) ((Inv.inv : ℝ → ℝ) '' uIcc a b) :=
    continuousOn_id.inv₀ hn
  have hg : ContinuousOn (fun t => coPoissonReciprocalSeed φ t * F t)
      ((Inv.inv : ℝ → ℝ) '' uIcc a b) := by
    convert ((Complex.continuous_ofReal.comp_continuousOn hi).mul
      (hφ.comp_continuousOn hi)).mul hF.continuousOn using 1
    ext t
    simp only [coPoissonReciprocalSeed, ofReal_inv, Function.comp_def, Pi.mul_apply]
  have ht := intervalIntegral.integral_deriv_smul_comp' hder hdc hg
  have he : (∫ x in a..b, (-(x ^ 2)⁻¹) •
      ((fun t => coPoissonReciprocalSeed φ t * F t) ∘ Inv.inv) x) =
      -(∫ x in a..b, (φ x * (x⁻¹ : ℝ)) * F x⁻¹) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro x hx
    have hxc : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hx0 x hx).ne'
    simp only [Function.comp_def, coPoissonReciprocalSeed, inv_inv, Complex.real_smul]
    push_cast
    field_simp [hxc]
  rw [he, intervalIntegral.integral_symm b⁻¹ a⁻¹] at ht
  exact neg_injective ht

theorem inversionWeightedTestIntegral_eq_reciprocal {φ : ℝ → ℂ} (hφ : Continuous φ)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hs : Function.support φ ⊆ Ioo a b) :
    (∫ x in a..b, φ x * (x⁻¹ : ℝ)) = ∫ t : ℝ, coPoissonReciprocalSeed φ t := by
  have ht := reciprocal_test_integral (F := fun _ => 1) hφ continuous_const ha hab
  simpa only [mul_one, intervalIntegral.integral_eq_integral_of_support_subset
    ((support_coPoissonReciprocalSeed_Ioo ha hab hs).trans Ioo_subset_Ioc_self)] using ht

theorem inversionCosineBoundaryPairing_eq_cosineTestCoefficient {φ : ℝ → ℂ}
    (hφ : ContDiff ℝ ∞ φ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hs : Function.support φ ⊆ Ioo a b) (k : ℝ) :
    inversionCosineBoundaryPairing φ a b k = cosineTestCoefficient (coPoissonReciprocalSeed φ) k := by
  have hS := contDiff_coPoissonReciprocalSeed_Ioo hφ ha hab hs
  have hK := hasCompactSupport_coPoissonReciprocalSeed_Ioo ha hab hs
  have ht := reciprocal_test_integral (F := fun t => (Real.cos (2 * Real.pi * k * t) : ℂ))
    hφ.continuous (by fun_prop) ha hab
  rw [cosineTestCoefficient_eq_integral hS.continuous hK]
  rw [intervalIntegral.integral_eq_integral_of_support_subset
    (((Function.support_mul_subset_left _ _).trans (support_coPoissonReciprocalSeed_Ioo ha hab hs)).trans
      Ioo_subset_Ioc_self)] at ht
  simpa only [inversionCosineBoundaryPairing, mul_comm] using ht

/-- The actual inverted trace is the existing arithmetic distribution on its reciprocal test. -/
theorem inversionFourierBoundaryPairing_eq_fourierBoundaryPairing (q : ℕ → ℂ) (A : ℂ)
    {φ : ℝ → ℂ} (hφ : ContDiff ℝ ∞ φ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hs : Function.support φ ⊆ Ioo a b) :
    inversionFourierBoundaryPairing q A φ a b = fourierBoundaryPairing q A (coPoissonReciprocalSeed φ) := by
  simp only [inversionFourierBoundaryPairing, fourierBoundaryPairing,
    inversionWeightedTestIntegral_eq_reciprocal hφ.continuous ha hab hs,
    inversionCosineBoundaryPairing_eq_cosineTestCoefficient hφ ha hab hs]

/-- Reciprocal distributional trace, with all analytic estimates paid by the original datum. -/
theorem degreeTwoQuotient_tendsto_inversion_reciprocal {g : ℕ → ℂ} {E : ℂ → ℂ}
    (hD : WeilZetaPower.ZetaPowerDatum 3 g E) (A B : ℂ) {φ : ℝ → ℂ}
    (hφ : ContDiff ℝ ∞ φ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hs : tsupport φ ⊆ Ioo a b) :
    Tendsto (inversionMaassLogPairing (degreeTwoQuotientCoeff g) A B φ a b) (𝓝[>] 0)
      (𝓝 (fourierBoundaryPairing (degreeTwoQuotientCoeff g) A (coPoissonReciprocalSeed φ))) := by
  rw [← inversionFourierBoundaryPairing_eq_fourierBoundaryPairing _ A hφ ha hab
    ((subset_tsupport φ).trans hs)]
  exact degreeTwoQuotient_tendsto_inversionMaassLogPairing hD A B hφ ha hab hs

end RHTower.WeilHigherDenominator
