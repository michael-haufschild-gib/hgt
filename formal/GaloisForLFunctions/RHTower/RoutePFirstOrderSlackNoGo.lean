import GaloisForLFunctions.RHTower.MobiusGammaXiGraphNormalComplementTangent
import GaloisForLFunctions.RHTower.XiWardInfinitesimalDefectIndexQuantization

/-!
# Route-P first-order Schur slack no-go

P-G160 proves that a graph-normal Hardy mass coefficient `d` costs exactly
`|d|²` additional bottom curvature.  P-G161 identifies the critical
coefficient with the fixed Ward value `r(1/2)`.  This file compares that
quadratic toll with the actual finite-aperture Julia defect.

If RH fails, `Re r(1/2)>0` and the Julia defect opens to first order as
`2 a Re r(1/2)`, whereas the scaled graph-normal toll is
`a² |r(1/2)|²`.  Hence the ordinary Schur defect strictly dominates the
toll at every sufficiently small positive aperture.  Finite-aperture
contractivity cannot force the mass coefficient to vanish; a successful
Route-P producer must cancel its first-order loss before taking curvature.
-/

open Complex Filter Set Topology

namespace RHTower

noncomputable section

/-- Extra curvature required by the P-G160 mass mode when the fixed
graph-normal coefficient is opened through real aperture `a`. -/
def xiWardCriticalMassCurvatureToll (a : ℝ) : ℝ :=
  Complex.normSq (((a : ℂ) *
    continuedXiAntiCausalWardResponse (1 / 2 : ℂ)))

theorem xiWardCriticalMassCurvatureToll_eq (a : ℝ) :
    xiWardCriticalMassCurvatureToll a =
      a ^ 2 * Complex.normSq
        (continuedXiAntiCausalWardResponse (1 / 2 : ℂ)) := by
  rw [xiWardCriticalMassCurvatureToll, Complex.normSq_mul,
    Complex.normSq_ofReal]
  ring

/-- **First-order-slack no-go.**  If RH fails, then on every sufficiently
small positive aperture the unconditional Schur/Julia defect is strictly
larger than the exact mass-curvature toll.  Ordinary finite-aperture
contractivity therefore has enough linear slack to hide the quadratic
graph-normal mass obstruction; only a mechanism cancelling the first-order
loss can feed P-G160 rigidity. -/
theorem eventually_xiWardCriticalMassCurvatureToll_lt_boundaryPhaseDefect_of_not_rh
    (hRH : ¬ RiemannHypothesis) :
    ∀ᶠ a : ℝ in nhdsWithin 0 (Ioi 0),
      xiWardCriticalMassCurvatureToll a <
        xiWardBoundaryPhaseDefect (1 / 2 : ℂ) a := by
  let r : ℂ := continuedXiAntiCausalWardResponse (1 / 2 : ℂ)
  have hrpos : 0 < r.re := by
    exact re_continuedXiAntiCausalWardResponse_half_pos_of_not_rh hRH
  have hhalf : 0 < ((1 / 2 : ℂ)).re := by norm_num
  have hzero : xiWardBoundaryPhaseDefect (1 / 2 : ℂ) 0 = 0 := by
    rw [xiWardBoundaryPhaseDefect_eq_transport hhalf]
    norm_num [mobiusGammaXiAntiCausalWardTransportV_zero hhalf]
  have hderiv := hasDerivAt_xiWardBoundaryPhaseDefect_zero hhalf
  have hslope := hderiv.tendsto_slope_zero_right
  have hthreshold : r.re < 2 * r.re := by linarith
  have hslopeEvent : ∀ᶠ a : ℝ in nhdsWithin 0 (Ioi 0),
      r.re < a⁻¹ •
        (xiWardBoundaryPhaseDefect (1 / 2 : ℂ) (0 + a) -
          xiWardBoundaryPhaseDefect (1 / 2 : ℂ) 0) := by
    exact hslope.eventually (Ioi_mem_nhds hthreshold)
  let delta : ℝ := r.re / (Complex.normSq r + 1)
  have hden : 0 < Complex.normSq r + 1 := by
    nlinarith [Complex.normSq_nonneg r]
  have hdelta : 0 < delta := div_pos hrpos hden
  have hsmall : ∀ᶠ a : ℝ in nhdsWithin 0 (Ioi 0), a < delta :=
    Filter.Eventually.filter_mono inf_le_left (Iio_mem_nhds hdelta)
  filter_upwards [hslopeEvent, hsmall, self_mem_nhdsWithin]
    with a hsl haSmall ha
  have ha0 : 0 < a := ha
  have hsl' : r.re < a⁻¹ *
      xiWardBoundaryPhaseDefect (1 / 2 : ℂ) a := by
    simpa only [zero_add, hzero, sub_zero, smul_eq_mul] using hsl
  have hlinear : a * r.re <
      xiWardBoundaryPhaseDefect (1 / 2 : ℂ) a := by
    have hmul := mul_lt_mul_of_pos_left hsl' ha0
    rw [← mul_assoc, mul_inv_cancel₀ ha0.ne', one_mul] at hmul
    exact hmul
  have hcostRate : a * Complex.normSq r < r.re := by
    dsimp only [delta] at haSmall
    have hmul := (lt_div_iff₀ hden).mp haSmall
    nlinarith [Complex.normSq_nonneg r]
  rw [xiWardCriticalMassCurvatureToll_eq]
  change a ^ 2 * Complex.normSq r < _
  calc
    a ^ 2 * Complex.normSq r =
        a * (a * Complex.normSq r) := by ring
    _ < a * r.re := mul_lt_mul_of_pos_left hcostRate ha0
    _ < xiWardBoundaryPhaseDefect (1 / 2 : ℂ) a := hlinear

end

end RHTower
