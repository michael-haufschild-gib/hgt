import GaloisForLFunctions.RHTower.Deninger.DeningerMeyerUnitZeroGeometry

/-! # Bezout inversion within the original all-weight Mellin class

Horizontal full-germ interpolation removes every denominator zero. Uniform
vertical invertibility then preserves all source weights in the quotient.
-/

open Complex Filter Set Topology
open GaloisForLFunctions.HTGeometry

namespace RHTower
noncomputable section

/-- Entire division by a unitized source preserves every Mellin strip weight. -/
theorem deningerMeyerUnitQuotient_regular {F A U : ℂ → ℂ}
    (hF : DeningerEntireMellinRegular F) (hA : DeningerEntireMellinRegular A)
    (hU : Differentiable ℂ U) (hdiv : ∀ z, U z*(1+F z) = A z) :
    DeningerEntireMellinRegular U := by
  intro α β
  refine ⟨fun z _ _ => hU z, fun a b _ _ K => ?_⟩
  let r := |a|+|b|
  obtain ⟨R, hR, htail⟩ := hF.unit_tail r
  obtain ⟨C, _, hC⟩ := hA.weighted_strip_bound r K
  have hc : Continuous (fun z : ℂ => ‖U z‖*(1+z.im^2)^K) := by
    have := hU.continuous
    fun_prop
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : ℂ) (r+R)).exists_bound_of_continuousOn
    hc.continuousOn
  refine ⟨max B (2*C), fun z hza hzb => ?_⟩
  apply (le_div_iff₀ (by positivity : 0 < (1+z.im^2)^K)).mpr
  have hzr : |z.re| ≤ r := by
    dsimp [r]
    rw [abs_le]
    constructor <;> linarith [le_abs_self a, neg_le_abs a, le_abs_self b,
      neg_le_abs b, abs_nonneg a, abs_nonneg b]
  by_cases hz : |z.im| ≤ R
  · have hnorm : ‖z‖ ≤ r+R :=
      (Complex.norm_le_abs_re_add_abs_im z).trans (add_le_add hzr hz)
    have hb := hB z (by simpa only [Metric.mem_closedBall, dist_zero_right] using hnorm)
    have hb' : ‖U z‖*(1+z.im^2)^K ≤ B := by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (by positivity :
        0 ≤ ‖U z‖*(1+z.im^2)^K)] using hb
    exact hb'.trans (le_max_left _ _)
  · have hd := htail z hzr (le_of_lt (lt_of_not_ge hz))
    have he : ‖U z‖*‖1+F z‖ = ‖A z‖ := by rw [← norm_mul, hdiv]
    have hu : ‖U z‖ ≤ 2*‖A z‖ := by nlinarith [norm_nonneg (U z)]
    calc ‖U z‖*(1+z.im^2)^K ≤ (2*‖A z‖)*(1+z.im^2)^K := by
          gcongr
      _ = 2*(‖A z‖*(1+z.im^2)^K) := by ring
      _ ≤ 2*C := mul_le_mul_of_nonneg_left (hC z hzr) (by norm_num)
      _ ≤ max B (2*C) := le_max_right _ _

/-- A unitized source with no common zero with X has an inverse modulo X
whose correction and Bezout coefficient are both original source transforms. -/
theorem exists_deningerMeyerStripBezout {F X : ℂ → ℂ}
    (hF : DeningerEntireMellinRegular F) (hX : DeningerEntireMellinRegular X)
    (hcop : ∀ z, 1+F z = 0 → X z ≠ 0) :
    ∃ K H : ℂ → ℂ, DeningerEntireMellinRegular K ∧
      DeningerEntireMellinRegular H ∧
      ∀ z, (1+F z)*(1+K z)+X z*H z = 1 := by
  let Z := {z : ℂ // 1+F z = 0}
  letI : Countable Z := hF.unit_zeros_countable
  let D : ℂ → ℂ := fun z => 1+F z
  have hD : Differentiable ℂ D := (differentiable_const 1).add hF.differentiable
  have hDA : ∀ z, AnalyticAt ℂ D z := fun z => hD.differentiableOn.analyticAt univ_mem
  have hXA : ∀ z, AnalyticAt ℂ X z := fun z => hX.differentiable.differentiableOn.analyticAt univ_mem
  let m : Z → ℕ := fun z => (analyticOrderAt D z.val).toNat
  have hm : ∀ z : Z, analyticOrderAt D z.val = (m z : ℕ∞) := fun z =>
    (ENat.coe_toNat (hF.unit_order_ne_top z.val)).symm
  obtain ⟨H, hH, hHgerm⟩ := exists_deningerMeyerHorizontalInterpolation hD
    hF.unit_strip_bound (w := Subtype.val) Subtype.coe_injective m hm
    hF.unit_zeros_horizontal_escape (fun _ z => (X z)⁻¹)
    (fun z : Z => (hXA z.val).inv (hcop z.val z.property))
  have hHA : ∀ z, AnalyticAt ℂ H z := fun z => hH.differentiable.differentiableOn.analyticAt univ_mem
  have hN : Differentiable ℂ (fun z => 1-X z*H z) :=
    (differentiable_const 1).sub (hX.differentiable.mul hH.differentiable)
  have hord : ∀ z, analyticOrderAt D z ≤ analyticOrderAt (fun z => 1-X z*H z) z := by
    intro z
    by_cases hz : D z = 0
    · let q : Z := ⟨z, hz⟩
      have hx : X z ≠ 0 := hcop z hz
      have he : (fun z => 1-X z*H z) =ᶠ[𝓝 z]
          (fun z => -X z*(H z-(X z)⁻¹)) := by
        filter_upwards [hX.differentiable.continuous.continuousAt.eventually_ne hx] with s hs
        field_simp
        ring
      rw [analyticOrderAt_congr he]
      change analyticOrderAt D z ≤ analyticOrderAt ((-X)*(H-X⁻¹)) z
      rw [analyticOrderAt_mul (hXA z).neg ((hHA z).sub ((hXA z).inv hx)), hm q]
      exact (hHgerm q).trans (le_add_of_nonneg_left bot_le)
    · rw [(hDA z).analyticOrderAt_eq_zero.mpr hz]
      exact bot_le
  obtain ⟨U, hU, hNU⟩ := exists_entire_quotient hN hD hF.unit_not_identically_zero hord
  have hA : DeningerEntireMellinRegular (fun z => -(F z+X z*H z)) := by
    intro a b
    convert ((hF a b).add ((hX.mul hH) a b)).const_mul (-1) using 1
    ext z
    ring
  have hdiv : ∀ z, (U z-1)*(1+F z) = -(F z+X z*H z) := by
    intro z
    have h := hNU z
    dsimp [D] at h
    linear_combination -h
  refine ⟨fun z => U z-1, H,
    deningerMeyerUnitQuotient_regular hF hA (hU.sub (differentiable_const 1)) hdiv, hH, ?_⟩
  intro z
  have h := hNU z
  dsimp [D] at h
  linear_combination -h

end
end RHTower
