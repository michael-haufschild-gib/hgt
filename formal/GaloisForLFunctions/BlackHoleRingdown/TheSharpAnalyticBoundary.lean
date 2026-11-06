import GaloisForLFunctions.BlackHoleRingdown.TheCausalSymbolOfTheModularHorizon
import GaloisForLFunctions.RHTower.XiHadamardFactorization

/-!
# The sharp analytic boundary of modular-horizon scattering

The affine frequency coordinate preserves meromorphic orders. Consequently every nontrivial
zeta zero is a pole, with no additional poles, of the normalized causal response. Analyticity
above any horizontal frequency line is exactly a lower bound on all resonance damping rates.

Functional-equation partners have a fixed sum of damping rates. Their slower rate is the
critical rate minus half the absolute transverse displacement. Thus a one-sided quarter-line
bound already forces equality and is equivalent to RH. Ordinary stability follows from the
open critical strip.
-/

open Complex Filter Topology

noncomputable section

namespace GaloisForLFunctions.BlackHoleRingdown

open _root_.RHTower

/-- Frequency corresponding to a centered spectral point and a radial decay. -/
def resonanceFrequency (D : ℝ) (z : ℂ) : ℂ := -z / 2 - I * D - I / 4

theorem causalCoordinate_resonanceFrequency (D : ℝ) (z : ℂ) :
    causalCoordinate D (resonanceFrequency D z) = z := by
  unfold causalCoordinate resonanceFrequency
  ring

theorem resonanceFrequency_causalCoordinate (D : ℝ) (ω : ℂ) :
    resonanceFrequency D (causalCoordinate D ω) = ω := by
  unfold causalCoordinate resonanceFrequency
  ring

theorem resonanceFrequency_im (D : ℝ) (z : ℂ) :
    (resonanceFrequency D z).im = -ringdownRate D z := by
  simp [resonanceFrequency, ringdownRate]
  ring

theorem hasDerivAt_causalCoordinate (D : ℝ) (ω : ℂ) :
    HasDerivAt (causalCoordinate D) (-2) ω := by
  exact ((hasDerivAt_const_mul (x := ω) (-2 : ℂ)).sub_const
    (2 * I * (D : ℂ))).sub_const (I / 2)

/-- The frequency change preserves every pole order, including multiple zeros. -/
theorem causalSymbol_meromorphicOrderAt (D : ℝ) (ω : ℂ) :
    meromorphicOrderAt (causalSymbol D) ω =
      meromorphicOrderAt thetaCuspHawkingOpticalCuspScattering (causalCoordinate D ω) := by
  change meromorphicOrderAt
    (thetaCuspHawkingOpticalCuspScattering ∘ causalCoordinate D) ω = _
  exact meromorphicOrderAt_comp_of_deriv_ne_zero
    ((differentiable_causalCoordinate D).analyticAt ω)
    (by rw [(hasDerivAt_causalCoordinate D ω).deriv]; norm_num)

/-- Every divisor point remains a genuine frequency pole at every radial shift. -/
theorem causalSymbol_resonance_isPole (D : ℝ) (q : XiZeroCopy) :
    meromorphicOrderAt (causalSymbol D) (resonanceFrequency D (xiSpectralPoint q)) < 0 := by
  rw [causalSymbol_meromorphicOrderAt, causalCoordinate_resonanceFrequency]
  exact thetaCuspHawkingOpticalCusp_xiSpectralPoint_isPole q

/-- The pole multiplicity is exactly the multiplicity of the centered Xi zero. -/
theorem causalSymbol_resonance_order (D : ℝ) (q : XiZeroCopy) :
    meromorphicOrderAt (causalSymbol D) (resonanceFrequency D (xiSpectralPoint q)) =
      -meromorphicOrderAt XiC (xiSpectralPoint q) := by
  rw [causalSymbol_meromorphicOrderAt, causalCoordinate_resonanceFrequency]
  have hfun : thetaCuspHawkingOpticalCuspScattering =
      thetaCuspHawkingOpticalCuspNumerator * XiC⁻¹ := by
    funext z
    simp only [thetaCuspHawkingOpticalCuspScattering,
      thetaCuspHawkingOpticalCuspDenominator, Pi.mul_apply, Pi.inv_apply, div_eq_mul_inv]
  rw [hfun, meromorphicOrderAt_mul_of_ne_zero
    (thetaCuspHawkingOpticalCuspNumerator_analyticAt _)
    (thetaCuspHawkingOpticalCuspNumerator_xiSpectralPoint_ne_zero q), meromorphicOrderAt_inv]

/-- Analyticity is exactly nonvanishing of the denominator; no divisor cancels. -/
theorem causalSymbol_analyticAt_iff (D : ℝ) (ω : ℂ) :
    AnalyticAt ℂ (causalSymbol D) ω ↔ XiC (causalCoordinate D ω) ≠ 0 := by
  constructor
  · intro han hz
    obtain ⟨q, hq⟩ := (XiC_eq_zero_iff_exists_xiZeroCopy _).mp hz
    have hp : meromorphicOrderAt (causalSymbol D) ω < 0 := by
      rw [causalSymbol_meromorphicOrderAt, ← hq]
      exact thetaCuspHawkingOpticalCusp_xiSpectralPoint_isPole q
    exact (not_lt_of_ge han.meromorphicOrderAt_nonneg) hp
  · intro hn
    have hcoord := (differentiable_causalCoordinate D).analyticAt ω
    exact ((thetaCuspHawkingOpticalCuspNumerator_analyticAt _).comp hcoord).div
      ((thetaCuspHawkingOpticalCuspDenominator_analyticAt _).comp hcoord) hn

/-- All poles are accounted for by the actual Xi divisor. -/
theorem causalSymbol_isPole_iff (D : ℝ) (ω : ℂ) :
    meromorphicOrderAt (causalSymbol D) ω < 0 ↔
      ∃ q : XiZeroCopy, ω = resonanceFrequency D (xiSpectralPoint q) := by
  constructor
  · intro hp
    have hz : XiC (causalCoordinate D ω) = 0 := by
      by_contra hn
      exact (not_lt_of_ge ((causalSymbol_analyticAt_iff D ω).mpr hn).meromorphicOrderAt_nonneg) hp
    obtain ⟨q, hq⟩ := (XiC_eq_zero_iff_exists_xiZeroCopy _).mp hz
    exact ⟨q, by rw [hq, resonanceFrequency_causalCoordinate]⟩
  · rintro ⟨q, rfl⟩
    exact causalSymbol_resonance_isPole D q

/-- A frequency half-plane is analytic exactly when all damping rates lie below its boundary
in the frequency plane, or equivalently above the corresponding decay threshold. -/
theorem causalSymbol_analyticOnNhd_halfPlane_iff (D a : ℝ) :
    AnalyticOnNhd ℂ (causalSymbol D) {ω : ℂ | -a < ω.im} ↔
      ∀ q : XiZeroCopy, a ≤ ringdownRate D (xiSpectralPoint q) := by
  constructor
  · intro han q
    by_contra h
    have hlt : ringdownRate D (xiSpectralPoint q) < a := lt_of_not_ge h
    have hmem : -a < (resonanceFrequency D (xiSpectralPoint q)).im := by
      rw [resonanceFrequency_im]
      linarith
    exact (not_lt_of_ge (han _ hmem).meromorphicOrderAt_nonneg)
      (causalSymbol_resonance_isPole D q)
  · intro h ω hω
    apply (causalSymbol_analyticAt_iff D ω).mpr
    intro hz
    obtain ⟨q, hq⟩ := (XiC_eq_zero_iff_exists_xiZeroCopy _).mp hz
    have hf : resonanceFrequency D (xiSpectralPoint q) = ω := by
      rw [hq, resonanceFrequency_causalCoordinate]
    have hi := resonanceFrequency_im D (xiSpectralPoint q)
    rw [hf] at hi
    have hb := h q
    change -a < ω.im at hω
    linarith

/-- Functional-equation partners have opposite deviations from the critical damping rate. -/
theorem ringdownRate_reflection_sum (D : ℝ) (q : XiZeroCopy) :
    ringdownRate D (xiSpectralPoint q) +
      ringdownRate D (xiSpectralPoint (xiZeroCopyReflectEquiv q)) = 2 * (D + 1 / 4) := by
  rw [xiSpectralPoint_reflect]
  simp only [ringdownRate, neg_im]
  ring

/-- The slower partner measures the full absolute transverse displacement. -/
theorem ringdownRate_reflection_min (D : ℝ) (q : XiZeroCopy) :
    min (ringdownRate D (xiSpectralPoint q))
      (ringdownRate D (xiSpectralPoint (xiZeroCopyReflectEquiv q))) =
        D + 1 / 4 - |(xiSpectralPoint q).im| / 2 := by
  rw [xiSpectralPoint_reflect]
  simp only [ringdownRate, neg_im]
  by_cases h : 0 ≤ (xiSpectralPoint q).im
  · rw [abs_of_nonneg h, min_eq_right (by linarith)]
    ring
  · have hn := le_of_lt (lt_of_not_ge h)
    rw [abs_of_nonpos hn, min_eq_left (by linarith)]
    ring

/-- The critical-strip theorem already gives stability relative to every radial decay. -/
theorem ringdownRate_mem_open_strip (D : ℝ) (q : XiZeroCopy) :
    D < ringdownRate D (xiSpectralPoint q) ∧
      ringdownRate D (xiSpectralPoint q) < D + 1 / 2 := by
  obtain ⟨hlo, hhi⟩ := abs_lt.mp (abs_im_xiSpectralPoint_lt_half q)
  simp only [ringdownRate]
  constructor <;> linarith

/-- Functional-equation pairing turns the one-sided sharp bound into exact universal damping. -/
theorem riemannHypothesis_iff_damping_lower_bound (D : ℝ) :
    RiemannHypothesis ↔ ∀ q : XiZeroCopy, D + 1 / 4 ≤ ringdownRate D (xiSpectralPoint q) := by
  rw [riemannHypothesis_iff_universal_damping D]
  constructor
  · intro h q
    exact (h q).ge
  · intro h q
    have hq := h q
    have hr := h (xiZeroCopyReflectEquiv q)
    have hs := ringdownRate_reflection_sum D q
    linarith

/-- RH is precisely analyticity of the normalized causal symbol above the quarter line. -/
theorem riemannHypothesis_iff_causalSymbol_analytic (D : ℝ) :
    RiemannHypothesis ↔
      AnalyticOnNhd ℂ (causalSymbol D) {ω : ℂ | -(D + 1 / 4) < ω.im} := by
  rw [causalSymbol_analyticOnNhd_halfPlane_iff, riemannHypothesis_iff_damping_lower_bound D]

/-- The ordinary stability half-plane follows unconditionally from the open critical strip. -/
theorem causalSymbol_analytic_above_radial_decay (D : ℝ) :
    AnalyticOnNhd ℂ (causalSymbol D) {ω : ℂ | -D < ω.im} := by
  rw [causalSymbol_analyticOnNhd_halfPlane_iff]
  exact fun q => (ringdownRate_mem_open_strip D q).1.le

#print axioms causalSymbol_resonance_order
#print axioms causalSymbol_isPole_iff
#print axioms ringdownRate_reflection_min
#print axioms riemannHypothesis_iff_causalSymbol_analytic
#print axioms causalSymbol_analytic_above_radial_decay

end GaloisForLFunctions.BlackHoleRingdown
