import GaloisForLFunctions.SquareRootThreshold.GroundEnergyAbscissaAndLagGridAttainmentBridge
import GaloisForLFunctions.SquareRootThreshold.OneParameterLagFamilySeesNearTopZerosAtAnExplicitLag

/-!
# A near-top zero makes the restricted Weil ground energy negative beyond an explicit aperture

The restricted Weil ground energy `μ(A)` of `ArithmeticCriticalityTheory` is antitone in the
aperture, positive through the certified small apertures, and tends to `0` under RH and to `−∞`
otherwise. Off RH it therefore has a first contact aperture `a* = inf {A : μ(A) < 0}`. The
one-parameter lag family of `SquareRootThreshold` sees a near-top zero at an explicit lag
(`one_param_near_top_visible_at_explicit_lag`), and the Rayleigh bridge
`μ(v/2 + w) ∫|f_v|² ≤ Re W_ζ(f_v, f_v)` (`ccmRestrictedWeilGroundEnergy_mul_le_re_W_twoBump`)
transfers every negative lag value into a negative ground energy. Joined:

* a negative value of the difference test at lag `v` gives `μ(v/2 + w) < 0`
  (`ccmRestrictedWeilGroundEnergy_neg_of_re_W_twoBump_neg`);
* a zero `½ + z₀` right of the line with `η ≤ |h_w(−iz₀)|`, seen at the explicit lag
  `V ≥ V₀(w, η, Re z₀)`, with no zero deeper than `Re z₀ + 1/V`, gives `μ(A) < 0` for every
  aperture `A ≥ V/2 + w` (`ccmRestrictedWeilGroundEnergy_neg_of_near_top_zero`);
* equivalently every aperture with `μ(A) ≥ 0` lies below `V/2 + w`
  (`lt_of_ccmRestrictedWeilGroundEnergy_nonneg_of_near_top_zero`).

So the contact aperture of a hypothetical near-top zero is bounded above by half its visibility
lag plus the width, and every certified aperture `μ(A) ≥ 0` is a lower bound on the visibility
lag of every near-top zero: `V > 2(A − w)`.
-/

open MeasureTheory Complex Set Filter Topology
open scoped Real

namespace GaloisForLFunctions.SquareRootThreshold

open Zeta23 _root_.RHTower GaloisForLFunctions.ArithmeticCriticalityTheory

/-- **A negative lag value is a negative ground energy.** If the difference test
`f_v = κ_w(· + v/2) − κ_w(· − v/2)` at lag `v ≥ 0`, width `w > 0`, has `Re W_ζ(f_v, f_v) < 0`,
then `μ(v/2 + w) < 0`: the Rayleigh quotient of `f_v` lies below zero at its own aperture. -/
theorem ccmRestrictedWeilGroundEnergy_neg_of_re_W_twoBump_neg {w v : ℝ} (hw : 0 < w) (hv : 0 ≤ v)
    (hneg : (zetaZeroConfig.W (twoBump (modScaledBump w 0) v (-1))
      (twoBump (modScaledBump w 0) v (-1))).re < 0) :
    ccmRestrictedWeilGroundEnergy ⟨v / 2 + w, by positivity⟩ < 0 := by
  have h := ccmRestrictedWeilGroundEnergy_mul_le_re_W_twoBump hw hv
  refine lt_of_not_ge fun hcon => ?_
  have hI : 0 ≤ ∫ t, ‖twoBump (modScaledBump w 0) v (-1) t‖ ^ 2 :=
    integral_nonneg fun _ => by positivity
  exact absurd (lt_of_le_of_lt h hneg) (not_lt.mpr (mul_nonneg hcon hI))

/-- **Near-top zeros force negative ground energy beyond an explicit aperture.** Let `½ + z₀` be
a zero of `ζ` right of the line, `η ≤ |h_w(−iz₀)|`, and `V ≥ V₀(w, η, Re z₀)` the explicit lag
at which the one-parameter family sees it. If no zero is deeper than `Re z₀ + 1/V`, then
`μ(A) < 0` for every aperture `A ≥ V/2 + w`. -/
theorem ccmRestrictedWeilGroundEnergy_neg_of_near_top_zero {w : ℝ} (hw : 0 < w) {z₀ : ℂ}
    (hz₀ : (1 / 2 + z₀) ∈ zetaZeroConfig.carrier) (hre₀ : 0 < z₀.re)
    {η : ℝ} (hη : 0 < η) (hηle : η ≤ ‖paperFT (scaledBump w) (-(I * z₀))‖)
    {V : ℝ} (hV : oneParamLag w η z₀.re ≤ V)
    (htop : ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re - 1 / 2 ≤ z₀.re + 1 / V)
    (A : SuzukiPositiveAperture) (hA : V / 2 + w ≤ A.1) :
    ccmRestrictedWeilGroundEnergy A < 0 := by
  obtain ⟨v, hv, hneg⟩ :=
    one_param_near_top_visible_at_explicit_lag hw hz₀ hre₀ hη hηle hV htop
  have h1 := ccmRestrictedWeilGroundEnergy_neg_of_re_W_twoBump_neg hw hv.1 hneg
  have h2 := ccmRestrictedWeilGroundEnergy_antitone (a := ⟨v / 2 + w, by have := hv.1; positivity⟩)
    (b := A) (show v / 2 + w ≤ A.1 by linarith [hv.2])
  exact lt_of_le_of_lt h2 h1

/-- **The contact aperture lies below the visibility lag.** Under the hypotheses of
`ccmRestrictedWeilGroundEnergy_neg_of_near_top_zero`, every aperture with `μ(A) ≥ 0` satisfies
`A < V/2 + w`. -/
theorem lt_of_ccmRestrictedWeilGroundEnergy_nonneg_of_near_top_zero {w : ℝ} (hw : 0 < w) {z₀ : ℂ}
    (hz₀ : (1 / 2 + z₀) ∈ zetaZeroConfig.carrier) (hre₀ : 0 < z₀.re)
    {η : ℝ} (hη : 0 < η) (hηle : η ≤ ‖paperFT (scaledBump w) (-(I * z₀))‖)
    {V : ℝ} (hV : oneParamLag w η z₀.re ≤ V)
    (htop : ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re - 1 / 2 ≤ z₀.re + 1 / V)
    {A : SuzukiPositiveAperture} (hA : 0 ≤ ccmRestrictedWeilGroundEnergy A) :
    A.1 < V / 2 + w := by
  by_contra hcon
  exact absurd hA (not_le.mpr (ccmRestrictedWeilGroundEnergy_neg_of_near_top_zero hw hz₀ hre₀ hη
    hηle hV htop A (not_lt.mp hcon)))

end GaloisForLFunctions.SquareRootThreshold
