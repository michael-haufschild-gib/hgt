import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Integral representation of the cube-root divided difference

With `κ = (∫_0^∞ t^{-2/3}/(1+t) dt)⁻¹ > 0`, the substitution `t = x u` gives, for `x > 0`,
`x^{1/3} = κ ∫_0^∞ t^{-2/3} x/(x+t) dt`.  Subtracting two such identities,
`x^{1/3} - y^{1/3} = κ (x - y) ∫_0^∞ t^{1/3} / ((x+t)(y+t)) dt`, and with `x = a³`, `y = b³`,

`1/(a² + ab + b²) = κ ∫_0^∞ t^{1/3} / ((a³+t)(b³+t)) dt`  for all `a, b > 0`,

the diagonal `a = b` (value `1/(3a²)`) following by continuity of both sides.
-/

open MeasureTheory Set Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The cube-root kernel `t^{-2/3}/(c + t)`. -/
def cubeRootKernel (c t : ℝ) : ℝ := t ^ (-(2 / 3 : ℝ)) / (c + t)

theorem cubeRootKernel_nonneg {c t : ℝ} (hc : 0 ≤ c) (ht : 0 ≤ t) : 0 ≤ cubeRootKernel c t := by
  unfold cubeRootKernel; positivity

theorem continuousOn_cubeRootKernel {c : ℝ} (hc : 0 ≤ c) :
    ContinuousOn (cubeRootKernel c) (Ioi 0) := by
  intro t ht
  have ht0 : (0 : ℝ) < t := ht
  apply ContinuousAt.continuousWithinAt
  unfold cubeRootKernel
  exact (Real.continuousAt_rpow_const _ _ (Or.inl ht0.ne')).div
    (continuousAt_const.add continuousAt_id) (show c + t ≠ 0 by positivity)

theorem integrableOn_cubeRootKernel_one : IntegrableOn (cubeRootKernel 1) (Ioi 0) := by
  have hmeas : ∀ s : Set ℝ, s ⊆ Ioi 0 → MeasurableSet s →
      AEStronglyMeasurable (cubeRootKernel 1) (volume.restrict s) := fun s hs hms =>
    ((continuousOn_cubeRootKernel zero_le_one).mono hs).aestronglyMeasurable hms
  rw [← Ioc_union_Ioi_eq_Ioi zero_le_one]
  refine IntegrableOn.union ?_ ?_
  · have h0 : IntegrableOn (fun t : ℝ => t ^ (-(2 / 3 : ℝ))) (Ioc 0 1) := by
      have := intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1)
        (r := -(2 / 3 : ℝ)) (by norm_num)
      exact (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp this
    refine h0.mono' (hmeas _ (fun t ht => ht.1) measurableSet_Ioc) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (cubeRootKernel_nonneg zero_le_one ht.1.le),
      cubeRootKernel]
    exact div_le_self (Real.rpow_nonneg ht.1.le _) (by linarith [ht.1])
  · have h0 : IntegrableOn (fun t : ℝ => t ^ (-(5 / 3 : ℝ))) (Ioi 1) :=
      integrableOn_Ioi_rpow_of_lt (by norm_num) one_pos
    refine h0.mono' (hmeas _ (fun t ht => mem_Ioi.mpr (lt_trans one_pos (mem_Ioi.mp ht)))
      measurableSet_Ioi) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := lt_trans one_pos ht
    rw [Real.norm_eq_abs, abs_of_nonneg (cubeRootKernel_nonneg zero_le_one ht0.le),
      cubeRootKernel, div_le_iff₀ (by linarith)]
    have h53 : t ^ (-(5 / 3 : ℝ)) * t = t ^ (-(2 / 3 : ℝ)) := by
      rw [← Real.rpow_add_one ht0.ne']; norm_num
    have hpos : 0 ≤ t ^ (-(5 / 3 : ℝ)) := Real.rpow_nonneg ht0.le _
    nlinarith

/-- The kernel with any positive constant is integrable on `(0, ∞)`. -/
theorem integrableOn_cubeRootKernel {c : ℝ} (hc : 0 < c) :
    IntegrableOn (cubeRootKernel c) (Ioi 0) := by
  set m := min c 1
  have hm : 0 < m := lt_min hc one_pos
  refine (integrableOn_cubeRootKernel_one.const_mul m⁻¹).mono' ?_ ?_
  · exact (continuousOn_cubeRootKernel hc.le).aestronglyMeasurable measurableSet_Ioi
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : (0 : ℝ) < t := ht
    rw [Real.norm_eq_abs, abs_of_nonneg (cubeRootKernel_nonneg hc.le ht0.le), cubeRootKernel,
      cubeRootKernel, ← div_eq_inv_mul, div_div]
    apply div_le_div_of_nonneg_left (Real.rpow_nonneg ht0.le _) (by positivity)
    have h1 : m ≤ c := min_le_left _ _
    have h2 : m ≤ 1 := min_le_right _ _
    nlinarith

/-- The total kernel mass `C = ∫_0^∞ t^{-2/3}/(1+t) dt`. -/
def cubeRootKernelMass : ℝ := ∫ t in Ioi (0 : ℝ), cubeRootKernel 1 t

theorem cubeRootKernelMass_pos : 0 < cubeRootKernelMass := by
  rw [cubeRootKernelMass, setIntegral_pos_iff_support_of_nonneg_ae
    (by filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        exact cubeRootKernel_nonneg zero_le_one (le_of_lt ht))
    integrableOn_cubeRootKernel_one]
  have hsupp : Ioi (0 : ℝ) ⊆ Function.support (cubeRootKernel 1) ∩ Ioi 0 := by
    intro t ht
    refine ⟨?_, ht⟩
    have ht0 : (0 : ℝ) < t := ht
    rw [Function.mem_support, cubeRootKernel]
    positivity
  exact lt_of_lt_of_le (by simp) (measure_mono hsupp)

/-- The normalizing constant `κ = C⁻¹`. -/
def cubeRootKappa : ℝ := cubeRootKernelMass⁻¹

theorem cubeRootKappa_pos : 0 < cubeRootKappa := inv_pos.mpr cubeRootKernelMass_pos

/-- Scaling identity `∫_0^∞ t^{-2/3} x/(x+t) dt = x^{1/3} C` for `x > 0`. -/
theorem integral_rpow_mul_div_add {x : ℝ} (hx : 0 < x) :
    ∫ t in Ioi (0 : ℝ), x * cubeRootKernel x t = x ^ (1 / 3 : ℝ) * cubeRootKernelMass := by
  have hsub := integral_comp_mul_left_Ioi (fun t => x * cubeRootKernel x t) 0 hx
  rw [mul_zero] at hsub
  have hcongr : ∫ u in Ioi (0 : ℝ), x * cubeRootKernel x (x * u) =
      ∫ u in Ioi (0 : ℝ), x ^ (-(2 / 3 : ℝ)) * cubeRootKernel 1 u := by
    refine setIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
    have hu0 : (0 : ℝ) < u := hu
    simp only [cubeRootKernel]
    rw [Real.mul_rpow hx.le hu0.le]
    field_simp
  rw [hcongr, integral_const_mul] at hsub
  have hx' : x ≠ 0 := hx.ne'
  have hscale : x ^ (1 / 3 : ℝ) = x * x ^ (-(2 / 3 : ℝ)) := by
    have h := Real.rpow_add hx 1 (-(2 / 3 : ℝ))
    rw [Real.rpow_one] at h
    rw [← h]; norm_num
  rw [hscale, cubeRootKernelMass, mul_assoc, hsub, smul_eq_mul, ← mul_assoc,
    mul_inv_cancel₀ hx', one_mul]

/-- `x^{1/3} = κ ∫_0^∞ t^{-2/3} x/(x+t) dt` for `x > 0`. -/
theorem rpow_third_eq_kappa_mul_integral {x : ℝ} (hx : 0 < x) :
    x ^ (1 / 3 : ℝ) = cubeRootKappa * ∫ t in Ioi (0 : ℝ), x * cubeRootKernel x t := by
  rw [integral_rpow_mul_div_add hx, cubeRootKappa, mul_comm, mul_assoc,
    mul_inv_cancel₀ cubeRootKernelMass_pos.ne', mul_one]

/-- The divided-difference integrand `t^{1/3}/((x+t)(y+t))`. -/
def cubeRootDividedKernel (x y t : ℝ) : ℝ := t ^ (1 / 3 : ℝ) / ((x + t) * (y + t))

theorem cubeRootDividedKernel_nonneg {x y t : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (ht : 0 ≤ t) :
    0 ≤ cubeRootDividedKernel x y t := by
  unfold cubeRootDividedKernel; positivity

theorem cubeRootDividedKernel_le {x y t : ℝ} (hx : 0 < x) (hy : 0 < y) (ht : 0 < t) :
    cubeRootDividedKernel x y t ≤ cubeRootKernel x t := by
  have h13 : t ^ (1 / 3 : ℝ) = t ^ (-(2 / 3 : ℝ)) * t := by
    rw [← Real.rpow_add_one ht.ne']; norm_num
  rw [cubeRootDividedKernel, cubeRootKernel, h13,
    div_le_div_iff₀ (by positivity) (by positivity)]
  have hp : 0 ≤ t ^ (-(2 / 3 : ℝ)) * (x + t) := by positivity
  nlinarith [mul_le_mul_of_nonneg_left (show t ≤ y + t by linarith) hp]

theorem integrableOn_cubeRootDividedKernel {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    IntegrableOn (cubeRootDividedKernel x y) (Ioi 0) := by
  refine (integrableOn_cubeRootKernel hx).mono' ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable (fun t ht => ?_) measurableSet_Ioi
    have ht0 : (0 : ℝ) < t := ht
    apply ContinuousAt.continuousWithinAt
    unfold cubeRootDividedKernel
    exact (Real.continuousAt_rpow_const _ _ (Or.inl ht0.ne')).div
      ((continuousAt_const.add continuousAt_id).mul (continuousAt_const.add continuousAt_id))
      (show (x + t) * (y + t) ≠ 0 by positivity)
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : (0 : ℝ) < t := ht
    rw [Real.norm_eq_abs, abs_of_nonneg (cubeRootDividedKernel_nonneg hx.le hy.le ht0.le)]
    exact cubeRootDividedKernel_le hx hy ht0

/-- **Divided difference.**  `x^{1/3} - y^{1/3} = κ (x - y) ∫_0^∞ t^{1/3}/((x+t)(y+t)) dt`. -/
theorem rpow_third_sub_eq {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    x ^ (1 / 3 : ℝ) - y ^ (1 / 3 : ℝ) =
      cubeRootKappa * ((x - y) * ∫ t in Ioi (0 : ℝ), cubeRootDividedKernel x y t) := by
  have hI : ∫ t in Ioi (0 : ℝ), (x * cubeRootKernel x t - y * cubeRootKernel y t) =
      (x - y) * ∫ t in Ioi (0 : ℝ), cubeRootDividedKernel x y t := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have ht0 : (0 : ℝ) < t := ht
    have h13 : t ^ (1 / 3 : ℝ) = t ^ (-(2 / 3 : ℝ)) * t := by
      rw [← Real.rpow_add_one ht0.ne']; norm_num
    simp only [cubeRootKernel, cubeRootDividedKernel, h13]
    have hxt : x + t ≠ 0 := by positivity
    have hyt : y + t ≠ 0 := by positivity
    field_simp
    ring
  rw [rpow_third_eq_kappa_mul_integral hx, rpow_third_eq_kappa_mul_integral hy, ← mul_sub,
    ← integral_sub ((integrableOn_cubeRootKernel hx).const_mul x)
      ((integrableOn_cubeRootKernel hy).const_mul y), hI]

theorem one_div_sq_add_mul_add_sq_eq_of_ne {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b) :
    1 / (a ^ 2 + a * b + b ^ 2) =
      cubeRootKappa * ∫ t in Ioi (0 : ℝ), cubeRootDividedKernel (a ^ 3) (b ^ 3) t := by
  have h := rpow_third_sub_eq (pow_pos ha 3) (pow_pos hb 3)
  have hcube : ∀ z : ℝ, 0 < z → (z ^ 3) ^ (1 / 3 : ℝ) = z := by
    intro z hz
    rw [show (1 / 3 : ℝ) = ((3 : ℕ) : ℝ)⁻¹ by norm_num]
    exact Real.pow_rpow_inv_natCast hz.le (by norm_num)
  rw [hcube a ha, hcube b hb] at h
  have hne : a - b ≠ 0 := sub_ne_zero.mpr hab
  have hq : 0 < a ^ 2 + a * b + b ^ 2 := by positivity
  set I := ∫ t in Ioi (0 : ℝ), cubeRootDividedKernel (a ^ 3) (b ^ 3) t
  have h' : (a - b) * 1 = (a - b) * (cubeRootKappa * (a ^ 2 + a * b + b ^ 2) * I) := by
    linear_combination h
  have h'' := mul_left_cancel₀ hne h'
  rw [div_eq_iff hq.ne']
  linear_combination h''

/-- Continuity of the divided-difference integral in its second argument. -/
theorem continuousAt_integral_cubeRootDividedKernel {x b : ℝ} (hx : 0 < x) (hb : 0 < b) :
    ContinuousAt (fun c : ℝ => ∫ t in Ioi (0 : ℝ), cubeRootDividedKernel x (c ^ 3) t) b := by
  have hb2 : 0 < (b / 2) ^ 3 := by positivity
  have hhalf : b / 2 < b := half_lt_self hb
  have hnear : ∀ᶠ c in 𝓝 b, b / 2 < c := Ioi_mem_nhds hhalf
  refine continuousAt_of_dominated (bound := cubeRootDividedKernel x ((b / 2) ^ 3)) ?_ ?_
    (integrableOn_cubeRootDividedKernel hx hb2) ?_
  · filter_upwards [hnear] with c hc
    have hc0 : 0 < c ^ 3 := pow_pos (lt_trans (half_pos hb) hc) 3
    exact (integrableOn_cubeRootDividedKernel hx hc0).aestronglyMeasurable
  · filter_upwards [hnear] with c hc
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : (0 : ℝ) < t := ht
    have hc0 : 0 < c := lt_trans (half_pos hb) hc
    have hc3 : (b / 2) ^ 3 ≤ c ^ 3 := pow_le_pow_left₀ (half_pos hb).le hc.le 3
    rw [Real.norm_eq_abs, abs_of_nonneg (cubeRootDividedKernel_nonneg hx.le
      (pow_pos hc0 3).le ht0.le)]
    unfold cubeRootDividedKernel
    apply div_le_div_of_nonneg_left (Real.rpow_nonneg ht0.le _) (by positivity)
    exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : (0 : ℝ) < t := ht
    unfold cubeRootDividedKernel
    exact continuousAt_const.div
      (continuousAt_const.mul ((continuous_pow 3).continuousAt.add continuousAt_const))
      (show (x + t) * (b ^ 3 + t) ≠ 0 by positivity)

/-- **Integral representation (6).**  For all `a, b > 0`,
`1/(a² + ab + b²) = κ ∫_0^∞ t^{1/3} / ((a³+t)(b³+t)) dt`. -/
theorem one_div_sq_add_mul_add_sq_eq {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    1 / (a ^ 2 + a * b + b ^ 2) =
      cubeRootKappa * ∫ t in Ioi (0 : ℝ), cubeRootDividedKernel (a ^ 3) (b ^ 3) t := by
  rcases ne_or_eq a b with hab | rfl
  · exact one_div_sq_add_mul_add_sq_eq_of_ne ha hb hab
  · have hf : ContinuousAt (fun c : ℝ => 1 / (a ^ 2 + a * c + c ^ 2)) a :=
      continuousAt_const.div (by fun_prop) (by positivity)
    have hg : ContinuousAt (fun c : ℝ => cubeRootKappa *
        ∫ t in Ioi (0 : ℝ), cubeRootDividedKernel (a ^ 3) (c ^ 3) t) a :=
      (continuousAt_integral_cubeRootDividedKernel (pow_pos ha 3) ha).const_mul _
    have heq : (fun c : ℝ => 1 / (a ^ 2 + a * c + c ^ 2)) =ᶠ[𝓝[≠] a] fun c =>
        cubeRootKappa * ∫ t in Ioi (0 : ℝ), cubeRootDividedKernel (a ^ 3) (c ^ 3) t := by
      filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Ioi_mem_nhds ha)] with c hc hc0
      exact one_div_sq_add_mul_add_sq_eq_of_ne ha hc0 (Ne.symm hc)
    exact tendsto_nhds_unique ((hf.tendsto.mono_left nhdsWithin_le_nhds).congr' heq)
      (hg.tendsto.mono_left nhdsWithin_le_nhds)

/-- Diagonal value: `1/(3a²) = κ ∫_0^∞ t^{1/3}/(a³+t)² dt`. -/
theorem one_div_three_mul_sq_eq {a : ℝ} (ha : 0 < a) :
    1 / (3 * a ^ 2) =
      cubeRootKappa * ∫ t in Ioi (0 : ℝ), cubeRootDividedKernel (a ^ 3) (a ^ 3) t := by
  rw [← one_div_sq_add_mul_add_sq_eq ha ha]
  ring_nf

end

end GaloisForLFunctions.HTGeometry
