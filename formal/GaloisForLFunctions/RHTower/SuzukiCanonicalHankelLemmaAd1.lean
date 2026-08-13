import GaloisForLFunctions.RHTower.SuzukiCanonicalKernelDifferentiability
import GaloisForLFunctions.RHTower.SuzukiCanonicalLogConvolution

/-!
# Suzuki (2012), Lemma `lem_ad1`

This module proves the printed regularity theorem for Suzuki's literal extended Fredholm solution.
The moving arithmetic cusps are handled through logarithmic `W^{1,1}` translation; no pointwise
dominator for the moving cusp derivatives is assumed.
-/

open Complex Real MeasureTheory Set Filter Topology

noncomputable section

namespace RHTower

/-- Pointwise form of Suzuki's Lemma `lem_ad1`: the literal extended solution is `C¹` at every
positive point away from the exact arithmetic breakpoints `n / a`. -/
theorem contDiffAt_one_suzukiHankelPhiGlobal_of_regular
    (epsilon : SuzukiHankelSign) {omega a x : ℝ}
    (homega : 1 < omega) (ha : 1 < a)
    (hx : x ∈ SuzukiHankelRegularX a) :
    ContDiffAt ℝ 1 (suzukiHankelPhiGlobal epsilon omega a homega ha) x := by
  let phi := suzukiHankelPhiContinuous epsilon omega a homega ha
  have hboundary : ContDiffAt ℝ 1
      (fun z : ℝ => suzukiSourceHFinite omega (a * z)) x :=
    contDiffAt_one_suzukiHankelBoundaryGlobal homega ha hx
  have hintegral : ContDiffAt ℝ 1
      (suzukiSourceHIntervalIntegral omega a phi) x :=
    contDiffAt_one_suzukiSourceHIntervalIntegral homega (by linarith) hx.1 phi
  have hlocal : ContDiffAt ℝ 1
      (fun z : ℝ => suzukiSourceHFinite omega (a * z) -
        epsilon.coeff * suzukiSourceHIntervalIntegral omega a phi z) x :=
    hboundary.sub (contDiffAt_const.mul hintegral)
  have hphiAe := suzukiHankelPhiContinuous_ae epsilon homega ha
  have hev : suzukiHankelPhiGlobal epsilon omega a homega ha =ᶠ[nhds x]
      fun z : ℝ => suzukiSourceHFinite omega (a * z) -
        epsilon.coeff * suzukiSourceHIntervalIntegral omega a phi z := by
    apply Eventually.of_forall
    intro z
    rw [suzukiHankelPhiGlobal]
    congr 2
    rw [suzukiSourceHIntervalIntegral]
    apply integral_congr_ae
    filter_upwards [hphiAe] with y hy
    rw [hy]
  exact hlocal.congr_of_eventuallyEq hev

/-- Setwise form of Suzuki's Lemma `lem_ad1`, on precisely the positive regular locus appearing in
the paper. -/
theorem contDiffOn_one_suzukiHankelPhiGlobal_regular
    (epsilon : SuzukiHankelSign) {omega a : ℝ}
    (homega : 1 < omega) (ha : 1 < a) :
    ContDiffOn ℝ 1 (suzukiHankelPhiGlobal epsilon omega a homega ha)
      (SuzukiHankelRegularX a) := by
  intro x hx
  exact (contDiffAt_one_suzukiHankelPhiGlobal_of_regular epsilon homega ha hx).contDiffWithinAt

/-- Closed universal formulation of Suzuki (2012), Lemma `lem_ad1`.  All analytic obligations are
discharged internally; the only quantified inequalities are the theorem's printed hypotheses. -/
theorem suzuki_lemma_ad1 :
    ∀ (epsilon : SuzukiHankelSign) (omega a : ℝ)
      (homega : 1 < omega) (ha : 1 < a),
      ContDiffOn ℝ 1 (suzukiHankelPhiGlobal epsilon omega a homega ha)
        (SuzukiHankelRegularX a) := by
  intro epsilon omega a homega ha
  exact contDiffOn_one_suzukiHankelPhiGlobal_regular epsilon homega ha

end RHTower
