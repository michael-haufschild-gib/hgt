import GaloisForLFunctions.RHTower.WeilWorkHigherDenominatorCutoffOverlap
import GaloisForLFunctions.RHTower.WeilWorkHigherDenominatorCutoffJets

/-!
# Actual positive compact tests for the primitive Mellin head

The lower cutoff tests are smooth and compactly supported away from zero.
Their Fourier boundary pairing is exactly the positive-half-line integral
against the primitive normalized at zero. No boundary regularity is assumed.
-/

noncomputable section
open Complex MeasureTheory Set Filter Topology Asymptotics
open scoped ContDiff
namespace RHTower.WeilHigherDenominator

/-- Positive dilation preserves both smooth cutoff buffers. -/
theorem IsMellinTailCutoff.dilate {ψ : ℝ → ℂ} (hψ : IsMellinTailCutoff ψ)
    {R : ℝ} (hR : 0 < R) : IsMellinTailCutoff (fun x => ψ (R * x)) := by
  refine ⟨hψ.smooth.comp (contDiff_const.mul contDiff_id), ?_, ?_⟩
  · obtain ⟨a, ha, h0⟩ := hψ.zero_near_origin
    refine ⟨a / R, div_pos ha hR, fun x hx => h0 (R * x) ?_⟩
    simpa only [mul_comm] using (lt_div_iff₀ hR).mp hx
  · obtain ⟨b, hb⟩ := hψ.one_near_infinity
    refine ⟨b / R, fun x hx => hb (R * x) ?_⟩
    simpa only [mul_comm] using (div_lt_iff₀ hR).mp hx

/-- Actual compact Mellin tests used to approach the lower endpoint. -/
def mellinHeadTest (ψ : ℝ → ℂ) (s : ℂ) (R x : ℝ) : ℂ :=
  (1 - ψ x) * (ψ (R * x) * (x : ℂ) ^ (s - 1))

/-- Each positive-scale test is smooth, compactly supported and buffered away from zero. -/
theorem mellinHeadTest_admissible {ψ : ℝ → ℂ} (hψ : IsMellinTailCutoff ψ)
    (s : ℂ) {R : ℝ} (hR : 0 < R) :
    ContDiff ℝ ∞ (mellinHeadTest ψ s R) ∧ HasCompactSupport (mellinHeadTest ψ s R) ∧
      ∃ a : ℝ, 0 < a ∧ ∀ x < a, mellinHeadTest ψ s R x = 0 := by
  obtain ⟨a, ha, h0⟩ := (hψ.dilate hR).zero_near_origin
  obtain ⟨b, hb⟩ := hψ.one_near_infinity
  refine ⟨(contDiff_const.sub hψ.smooth).mul ((hψ.dilate hR).contDiff_mul_cpow (s - 1)), ?_,
    ⟨a, ha, fun x hx => by simp [mellinHeadTest, h0 x hx]⟩⟩
  apply HasCompactSupport.of_support_subset_isCompact (K := Icc a b) isCompact_Icc
  intro x hx
  constructor
  · by_contra h
    exact hx (by simp [mellinHeadTest, h0 x (lt_of_not_ge h)])
  · by_contra h
    exact hx (by simp [mellinHeadTest, hb x (lt_of_not_ge h)])

/-- The second derivative of a smooth compact test has integral zero. -/
theorem integral_iteratedDeriv_two_compact {φ : ℝ → ℂ}
    (hφ : ContDiff ℝ ∞ φ) (hs : HasCompactSupport φ) :
    (∫ x : ℝ, iteratedDeriv 2 φ x) = 0 := by
  have hd := (contDiff_infty_iff_deriv.mp hφ).2
  have hdd := (contDiff_infty_iff_deriv.mp hd).2
  have H := cosineTestCoefficient_deriv_two hφ hs 0
  rw [cosineTestCoefficient_eq_integral hdd.continuous hs.deriv.deriv] at H
  simpa only [mul_zero, zero_mul, Real.cos_zero, Complex.ofReal_one, Complex.ofReal_zero,
    mul_one, zero_pow (by decide : (2 : ℕ) ≠ 0), neg_zero,
    show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one, iteratedDeriv_zero] using H

/-- An origin buffer identifies the full integral with its positive-half-line integral. -/
theorem integral_Ioi_eq_integral_of_zero_near_origin {φ : ℝ → ℂ}
    (h0 : ∃ a : ℝ, 0 < a ∧ ∀ x < a, φ x = 0) :
    (∫ x : ℝ in Ioi 0, φ x) = ∫ x : ℝ, φ x := by
  obtain ⟨a, ha, h0⟩ := h0
  exact setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx =>
    h0 x ((le_of_not_gt hx).trans_lt ha)

/-- A compact positive test pairs equally with a primitive or its normalization at zero. -/
theorem integral_primitive_compact_pos {F φ : ℝ → ℂ} (hF : Continuous F)
    (hφ : ContDiff ℝ ∞ φ) (hs : HasCompactSupport φ)
    (h0 : ∃ a : ℝ, 0 < a ∧ ∀ x < a, φ x = 0) :
    (∫ x : ℝ, deriv (deriv φ) x * F x) =
      ∫ x : ℝ in Ioi 0, (F x - F 0) * iteratedDeriv 2 φ x := by
  have htwo : iteratedDeriv 2 φ = deriv (deriv φ) := by
    simp only [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_zero]
  have hd := (contDiff_infty_iff_deriv.mp hφ).2
  have hdd := (contDiff_infty_iff_deriv.mp hd).2
  have hD : Continuous (iteratedDeriv 2 φ) := by rw [htwo]; exact hdd.continuous
  have hsD : HasCompactSupport (iteratedDeriv 2 φ) := by rw [htwo]; exact hs.deriv.deriv
  have hiD : Integrable (iteratedDeriv 2 φ) := hD.integrable_of_hasCompactSupport hsD
  have hiFD : Integrable (fun x => F x * iteratedDeriv 2 φ x) :=
    (hF.mul hD).integrable_of_hasCompactSupport (hsD.mul_left (f := F))
  have hshift : (∫ x : ℝ, (F x - F 0) * iteratedDeriv 2 φ x) =
      ∫ x : ℝ, F x * iteratedDeriv 2 φ x := by
    simp only [sub_mul]
    rw [integral_sub hiFD (hiD.const_mul (F 0)), integral_const_mul,
      integral_iteratedDeriv_two_compact hφ hs, mul_zero, sub_zero]
  obtain ⟨a, ha, h0⟩ := h0
  have hz : ∀ x < a, iteratedDeriv 2 φ x = 0 := by
    intro x hx
    have he : φ =ᶠ[𝓝 x] fun _ => (0 : ℂ) := by
      filter_upwards [Iio_mem_nhds hx] with y hy
      exact h0 y hy
    simpa using he.iteratedDeriv_eq 2
  have hposD : (∫ x : ℝ in Ioi 0, (F x - F 0) * iteratedDeriv 2 φ x) =
      ∫ x : ℝ, (F x - F 0) * iteratedDeriv 2 φ x := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    rw [hz x ((le_of_not_gt hx).trans_lt ha), mul_zero]
  rw [hposD, hshift]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [htwo]
  exact mul_comm _ _

/-- The actual boundary pairing uses the normalized primitive on positive tests. -/
theorem fourierBoundaryPairing_eq_primitive_head {q : ℕ → ℂ}
    (hq : Summable fun n : ℕ => ‖q (n + 1)‖ / ((n + 1 : ℕ) : ℝ) ^ 2)
    (A : ℂ) {φ : ℝ → ℂ} (hφ : ContDiff ℝ ∞ φ) (hs : HasCompactSupport φ)
    (h0 : ∃ a : ℝ, 0 < a ∧ ∀ x < a, φ x = 0) :
    fourierBoundaryPairing q A φ = A * (∫ x : ℝ in Ioi 0, φ x) +
      ∫ x : ℝ in Ioi 0, (fourierBoundaryPrimitive q x - fourierBoundaryPrimitive q 0) *
        iteratedDeriv 2 φ x := by
  rw [fourierBoundaryPairing_eq_primitive hq A hφ hs,
    integral_Ioi_eq_integral_of_zero_near_origin h0,
    integral_primitive_compact_pos (continuous_fourierBoundaryPrimitive hq) hφ hs h0]
end RHTower.WeilHigherDenominator
