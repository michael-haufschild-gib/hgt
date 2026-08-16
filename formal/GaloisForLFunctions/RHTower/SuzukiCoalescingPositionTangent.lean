import GaloisForLFunctions.HTGeometry.ApertureHyperbolicL2Expansion
import GaloisForLFunctions.RHTower.SuzukiGroundEdgeCayleyUniversality
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The coalescing defect is a position-resolvent quotient

At a fixed shift below the floor the two parity energies of the movable deficiency base are
resolvent quadratic forms of `cosh(cX)` and `sinh(cX)`.  As the base collapses, the even profile
tends to the constant source vector and the normalized odd profile to the position source vector,
so the defect gap is exactly twice the squared base times the position-to-constant resolvent
quotient.

The quotient is produced by the operator and the fixed polynomial source pair alone.  At the free
end — the identity resolvent — it is the aperture constant `a²/3`, the same coefficient that the
free hyperbolic endpoint carries.
-/

open MeasureTheory Filter Topology Set
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

/-- `(44)`: the even resolvent energy of the movable deficiency base. -/
def suzukiCoalescingEvenEnergy (a : ℝ)
    (R : Lp ℝ 2 (apertureMeasure a) →L[ℝ] Lp ℝ 2 (apertureMeasure a)) (c : ℝ) : ℝ :=
  inner ℝ (apertureCoshL2 a c) (R (apertureCoshL2 a c))

/-- `(44)`: the odd resolvent energy of the movable deficiency base. -/
def suzukiCoalescingOddEnergy (a : ℝ)
    (R : Lp ℝ 2 (apertureMeasure a) →L[ℝ] Lp ℝ 2 (apertureMeasure a)) (c : ℝ) : ℝ :=
  inner ℝ (apertureSinhL2 a c) (R (apertureSinhL2 a c))

/-- `(45)`: the intrinsic source tangent, the position-to-constant resolvent quotient. -/
def suzukiPositionResolventTangent (a : ℝ)
    (R : Lp ℝ 2 (apertureMeasure a) →L[ℝ] Lp ℝ 2 (apertureMeasure a)) : ℝ :=
  inner ℝ (apertureMonomialL2 a 1) (R (apertureMonomialL2 a 1)) /
    inner ℝ (apertureMonomialL2 a 0) (R (apertureMonomialL2 a 0))

set_option maxHeartbeats 1000000 in
/-- **Theorem E `(46)`.**  The coalescing defect gap is twice the squared base times the
position-resolvent quotient. -/
theorem tendsto_one_sub_suzukiCoalescingDefect_rate {a : ℝ} (ha : 0 < a)
    (R : Lp ℝ 2 (apertureMeasure a) →L[ℝ] Lp ℝ 2 (apertureMeasure a))
    (hR : 0 < inner ℝ (apertureMonomialL2 a 0) (R (apertureMonomialL2 a 0))) :
    Tendsto (fun c : ℝ =>
        (1 - GaloisForLFunctions.RHTower.suzukiDefectAngle (suzukiCoalescingEvenEnergy a R c)
          (suzukiCoalescingOddEnergy a R c)) / (2 * c ^ 2))
      (𝓝[>] (0 : ℝ)) (𝓝 (suzukiPositionResolventTangent a R)) := by
  have hcosh := tendsto_apertureCoshL2 (a := a) ha.le
  have hsinh := tendsto_inv_smul_apertureSinhL2 (a := a) ha.le
  have hE : Tendsto (fun c : ℝ => suzukiCoalescingEvenEnergy a R c) (𝓝[>] (0 : ℝ))
      (𝓝 (inner ℝ (apertureMonomialL2 a 0) (R (apertureMonomialL2 a 0)))) :=
    hcosh.inner ((R.continuous.tendsto _).comp hcosh)
  have hOsq : Tendsto (fun c : ℝ => suzukiCoalescingOddEnergy a R c / c ^ 2) (𝓝[>] (0 : ℝ))
      (𝓝 (inner ℝ (apertureMonomialL2 a 1) (R (apertureMonomialL2 a 1)))) := by
    have h : Tendsto
        (fun c : ℝ => inner ℝ (c⁻¹ • apertureSinhL2 a c) (R (c⁻¹ • apertureSinhL2 a c)))
        (𝓝[>] (0 : ℝ))
        (𝓝 (inner ℝ (apertureMonomialL2 a 1) (R (apertureMonomialL2 a 1)))) :=
      hsinh.inner ((R.continuous.tendsto _).comp hsinh)
    refine h.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with c hc
    have hcpos : (0 : ℝ) < c := mem_Ioi.mp hc
    rw [suzukiCoalescingOddEnergy, ContinuousLinearMap.map_smul, real_inner_smul_left,
      real_inner_smul_right]
    field_simp
  have hc2 : Tendsto (fun c : ℝ => c ^ 2) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h0 : Tendsto (fun c : ℝ => c ^ 2) (𝓝 (0 : ℝ)) (𝓝 0) := by
      simpa using (continuous_pow 2).tendsto (0 : ℝ)
    exact h0.mono_left nhdsWithin_le_nhds
  have hO : Tendsto (fun c : ℝ => suzukiCoalescingOddEnergy a R c) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h := hc2.mul hOsq
    rw [zero_mul] at h
    refine h.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with c hc
    have hcpos : (0 : ℝ) < c := mem_Ioi.mp hc
    field_simp
  have hsum : Tendsto (fun c : ℝ =>
        suzukiCoalescingEvenEnergy a R c + suzukiCoalescingOddEnergy a R c) (𝓝[>] (0 : ℝ))
      (𝓝 (inner ℝ (apertureMonomialL2 a 0) (R (apertureMonomialL2 a 0)))) := by
    have h := hE.add hO
    rwa [add_zero] at h
  have hne : ∀ᶠ c : ℝ in 𝓝[>] (0 : ℝ),
      suzukiCoalescingEvenEnergy a R c + suzukiCoalescingOddEnergy a R c ≠ 0 :=
    hsum.eventually (eventually_ne_nhds (ne_of_gt hR))
  have hlim := hOsq.div hsum (ne_of_gt hR)
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin, hne] with c hc hden
  have hcpos : (0 : ℝ) < c := mem_Ioi.mp hc
  simp only [Pi.div_apply, GaloisForLFunctions.RHTower.suzukiDefectAngle]
  field_simp
  ring

/-! ## The free endpoint value of the tangent -/

theorem inner_apertureMonomialL2_zero_self {a : ℝ} (ha : 0 ≤ a) :
    inner ℝ (apertureMonomialL2 a 0) (apertureMonomialL2 a 0) = 2 * a := by
  rw [MeasureTheory.L2.inner_def]
  have hcongr : ∫ x : ℝ, inner ℝ ((apertureMonomialL2 a 0 : Lp ℝ 2 (apertureMeasure a)) x)
        ((apertureMonomialL2 a 0 : Lp ℝ 2 (apertureMeasure a)) x) ∂(apertureMeasure a)
      = ∫ _x : ℝ, (1 : ℝ) ∂(apertureMeasure a) := by
    refine integral_congr_ae ?_
    filter_upwards [coeFn_apertureMonomialL2 a 0] with x hx
    rw [hx]
    simp
  rw [hcongr, integral_const, smul_eq_mul, mul_one,
    show (apertureMeasure a).real univ = (apertureMeasure a univ).toReal from rfl,
    apertureMeasure_univ_toReal ha]

theorem inner_apertureMonomialL2_one_self {a : ℝ} (ha : 0 ≤ a) :
    inner ℝ (apertureMonomialL2 a 1) (apertureMonomialL2 a 1) = 2 * a ^ 3 / 3 := by
  rw [MeasureTheory.L2.inner_def]
  have hcongr : ∫ x : ℝ, inner ℝ ((apertureMonomialL2 a 1 : Lp ℝ 2 (apertureMeasure a)) x)
        ((apertureMonomialL2 a 1 : Lp ℝ 2 (apertureMeasure a)) x) ∂(apertureMeasure a)
      = ∫ x : ℝ, x ^ 2 ∂(apertureMeasure a) := by
    refine integral_congr_ae ?_
    filter_upwards [coeFn_apertureMonomialL2 a 1] with x hx
    rw [hx]
    simp
  rw [hcongr, apertureMeasure, ← MeasureTheory.integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (by linarith : (-a : ℝ) ≤ a), integral_pow]
  ring

/-- **`(50)`: the free endpoint value of the intrinsic tangent.**  At the identity resolvent the
position-to-constant quotient is the aperture constant `a²/3`. -/
theorem suzukiPositionResolventTangent_id {a : ℝ} (ha : 0 < a) :
    suzukiPositionResolventTangent a
        (ContinuousLinearMap.id ℝ (Lp ℝ 2 (apertureMeasure a))) = a ^ 2 / 3 := by
  rw [suzukiPositionResolventTangent, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.id_apply, inner_apertureMonomialL2_zero_self ha.le,
    inner_apertureMonomialL2_one_self ha.le]
  field_simp

end RHTower
