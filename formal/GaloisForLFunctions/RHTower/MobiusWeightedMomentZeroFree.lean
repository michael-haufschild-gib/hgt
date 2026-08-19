import GaloisForLFunctions.RHTower.MobiusCriticalLaplaceIdentity
import GaloisForLFunctions.RHTower.MobiusCenteredMertensLimit
import GaloisForLFunctions.RHTower.ZetaPoleSplit

/-!
# One exponential moment gives one zero-free half plane

The weighted domain condition `M(α)`, that `e^{αt} m₀(t)` be square integrable on the positive
ray, makes the causal Laplace transform of the weighted vector holomorphic on the whole open right
half plane.  On the initial overlap it equals `1/((z-α) ζ(1+z-α))`, so the identity theorem
continues that expression, and a zeta zero right of `1-α` would contradict holomorphy.
-/

open MeasureTheory Set Filter
open scoped Topology

namespace RHTower

noncomputable section

/-- The weighted critical Möbius boundary vector `e^{αt} m₀(t)`. -/
def weightedMertensVector (α : ℝ) (t : ℝ) : ℂ :=
  (Real.exp (α * t) : ℂ) * criticalMertensVector t

/-- Card equation `(4)`: the weighted domain condition `M(α)`. -/
def WeightedMertensMoment (α : ℝ) : Prop :=
  MemLp (weightedMertensVector α) 2 (volume.restrict (Ioi (0 : ℝ)))

theorem weightedMertensVector_zero : weightedMertensVector 0 = criticalMertensVector := by
  funext t
  simp [weightedMertensVector]

/-- Card equation `(2)`: the unweighted critical vector is unconditionally square integrable. -/
theorem weightedMertensMoment_zero : WeightedMertensMoment 0 := by
  rw [WeightedMertensMoment, weightedMertensVector_zero]
  exact memLp_criticalMertensVector.restrict _

/-- Multiplying by `e^{αt}` translates the causal transform by `α`. -/
theorem causalTransform_weightedMertensVector (α : ℝ) (z : ℂ) :
    causalTransform (weightedMertensVector α) z
      = causalTransform criticalMertensVector (z - (α : ℂ)) := by
  rw [causalTransform, causalTransform]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  rw [weightedMertensVector, ← mul_assoc]
  congr 1
  rw [Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- **Section 2: one weight gives one zero-free half plane.** -/
theorem zeta_ne_zero_of_weightedMertensMoment {α : ℝ} (hα : 0 ≤ α)
    (h : WeightedMertensMoment α) {s : ℂ} (hs : 1 - α < s.re) (hs1 : s ≠ 1) :
    riemannZeta s ≠ 0 := by
  intro hzero
  set F : ℂ → ℂ := causalTransform (weightedMertensVector α) with hF
  set H : ℂ → ℂ := fun z => F z * zetaPoleUnit (1 + z - (α : ℂ)) - 1 with hH
  have hU : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hUconn : IsPreconnected {z : ℂ | 0 < z.re} :=
    (convex_halfSpace_re_gt 0).isPreconnected
  have hFdiff : DifferentiableOn ℂ F {z : ℂ | 0 < z.re} := differentiableOn_causalTransform h
  have hpoly : Differentiable ℂ (fun z : ℂ => zetaPoleUnit (1 + z - (α : ℂ))) :=
    differentiable_zetaPoleUnit.comp (by fun_prop)
  have hHdiff : DifferentiableOn ℂ H {z : ℂ | 0 < z.re} :=
    (hFdiff.mul hpoly.differentiableOn).sub_const 1
  have hHan : AnalyticOnNhd ℂ H {z : ℂ | 0 < z.re} := hHdiff.analyticOnNhd hU
  have hV : IsOpen {z : ℂ | α < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hmem : ((α : ℂ) + 1) ∈ {z : ℂ | α < z.re} := by
    simp only [Set.mem_setOf_eq, Complex.add_re, Complex.ofReal_re, Complex.one_re]
    linarith
  have hzero_nbhd : H =ᶠ[nhds ((α : ℂ) + 1)] 0 := by
    filter_upwards [hV.mem_nhds hmem] with z hz
    have hzre : α < z.re := hz
    have hzα : z ≠ (α : ℂ) := by
      intro hc
      rw [hc] at hzre
      simp at hzre
    have hre : 0 < (z - (α : ℂ)).re := by
      simp only [Complex.sub_re, Complex.ofReal_re]
      linarith
    have hzα0 : (z - (α : ℂ)) ≠ 0 := sub_ne_zero.mpr hzα
    have hne1 : (1 + z - (α : ℂ)) ≠ 1 := by
      intro hc
      apply hzα0
      linear_combination hc
    have hzeta : riemannZeta (1 + (z - (α : ℂ))) ≠ 0 := by
      refine riemannZeta_ne_zero_of_one_lt_re ?_
      simp only [Complex.add_re, Complex.one_re, Complex.sub_re, Complex.ofReal_re]
      linarith
    show F z * zetaPoleUnit (1 + z - (α : ℂ)) - 1 = 0
    rw [hF, causalTransform_weightedMertensVector, causalTransform_criticalMertensVector hre,
      centeredSchurLimit, zetaPoleUnit_of_ne hne1,
      show (1 + z - (α : ℂ)) = 1 + (z - (α : ℂ)) by ring,
      show (1 + (z - (α : ℂ)) - 1 : ℂ) = z - (α : ℂ) by ring]
    field_simp
    ring
  have hbase : ((α : ℂ) + 1) ∈ {z : ℂ | 0 < z.re} := by
    simp only [Set.mem_setOf_eq, Complex.add_re, Complex.ofReal_re, Complex.one_re]
    linarith
  have hHzero := hHan.eqOn_zero_of_preconnected_of_eventuallyEq_zero hUconn hbase hzero_nbhd
  have hz0mem : (s - 1 + (α : ℂ)) ∈ {z : ℂ | 0 < z.re} := by
    simp only [Set.mem_setOf_eq, Complex.add_re, Complex.sub_re, Complex.one_re,
      Complex.ofReal_re]
    linarith
  have h0 := hHzero hz0mem
  have hshift : (1 + (s - 1 + (α : ℂ)) - (α : ℂ)) = s := by ring
  rw [hH] at h0
  simp only [hshift, Pi.zero_apply] at h0
  rw [zetaPoleUnit_of_ne hs1, hzero, mul_zero, mul_zero] at h0
  norm_num at h0

end

end RHTower
