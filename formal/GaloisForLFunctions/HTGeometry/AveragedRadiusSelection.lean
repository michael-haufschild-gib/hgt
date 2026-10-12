import Mathlib

/-!
# A radius away from finitely many points, by averaging

**Theorem** (`exists_mem_Icc_sum_rpow_le`). For any finite family `a_j` of reals and `r > 0` there is
`x ∈ [r/2, r]`, different from every `a_j`, with
`Σ_j |x − a_j|^{−1/2} ≤ #J · 3√(r/2)/(r/2)`.

So a circle radius can be chosen whose reciprocal square-root distances to `M` given radii sum to
`O(M/√r)`. A pigeonhole choice only guarantees each distance `≥ r/(4(M+1))`, which loses a factor
`log M` in products of `M` factors.

**Proof.** The first moment method (`exists_notMem_null_le_average`) on `[r/2, r]`, avoiding the
null set `{a_j}`. The averages come from `∫_p^q |y|^{−1/2} dy ≤ 3√(q − p)`.
-/

open MeasureTheory Set intervalIntegral

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- `∫_0^b y^{−1/2} dy = 2√b`. -/
theorem integral_rpow_neg_half_zero (b : ℝ) :
    ∫ y in (0 : ℝ)..b, y ^ (-(1 / 2) : ℝ) = 2 * Real.sqrt b := by
  rw [integral_rpow (Or.inl (by norm_num))]
  rw [Real.zero_rpow (by norm_num), Real.sqrt_eq_rpow]
  norm_num
  ring

theorem intervalIntegrable_abs_rpow_neg_half (p q : ℝ) :
    IntervalIntegrable (fun y : ℝ => |y| ^ (-(1 / 2) : ℝ)) volume p q := by
  have hpos : ∀ u v : ℝ, 0 ≤ u → 0 ≤ v →
      IntervalIntegrable (fun y : ℝ => |y| ^ (-(1 / 2) : ℝ)) volume u v := by
    intro u v hu hv
    have h := intervalIntegral.intervalIntegrable_rpow' (a := u) (b := v)
      (r := (-(1 / 2) : ℝ)) (by norm_num)
    refine h.congr ?_
    intro y hy
    have : 0 ≤ y := by
      rcases le_total u v with huv | huv
      · rw [uIoc_of_le huv] at hy; exact le_trans hu hy.1.le
      · rw [uIoc_of_ge huv] at hy; exact le_trans hv hy.1.le
    simp [abs_of_nonneg this]
  have hneg : ∀ u v : ℝ, u ≤ 0 → v ≤ 0 →
      IntervalIntegrable (fun y : ℝ => |y| ^ (-(1 / 2) : ℝ)) volume u v := by
    intro u v hu hv
    have h := (hpos (-u) (-v) (by linarith) (by linarith)).comp_mul_left (c := -1)
      enorm_ne_top enorm_ne_top
    simp only [neg_mul, one_mul, abs_neg, div_neg, div_one, neg_neg] at h
    exact h
  rcases le_total 0 p with hp | hp <;> rcases le_total 0 q with hq | hq
  · exact hpos p q hp hq
  · exact (hpos p 0 hp le_rfl).trans (hneg 0 q le_rfl hq)
  · exact (hneg p 0 hp le_rfl).trans (hpos 0 q le_rfl hq)
  · exact hneg p q hp hq

/-- `∫_p^q |y|^{−1/2} dy = 2√q − 2√p` for `0 ≤ p ≤ q`. -/
theorem integral_abs_rpow_neg_half_of_nonneg {p q : ℝ} (hp : 0 ≤ p) (hpq : p ≤ q) :
    ∫ y in p..q, |y| ^ (-(1 / 2) : ℝ) = 2 * Real.sqrt q - 2 * Real.sqrt p := by
  have e : ∫ y in p..q, |y| ^ (-(1 / 2) : ℝ) = ∫ y in p..q, y ^ (-(1 / 2) : ℝ) := by
    refine integral_congr fun y hy => ?_
    rw [uIcc_of_le hpq] at hy
    simp [abs_of_nonneg (le_trans hp hy.1)]
  rw [e, ← integral_add_adjacent_intervals (b := 0)
      (intervalIntegral.intervalIntegrable_rpow' (by norm_num))
      (intervalIntegral.intervalIntegrable_rpow' (by norm_num)),
    integral_symm, integral_rpow_neg_half_zero p, integral_rpow_neg_half_zero q]
  ring

theorem sqrt_sub_le {p q : ℝ} (hp : 0 ≤ p) (hpq : p ≤ q) :
    Real.sqrt q - Real.sqrt p ≤ Real.sqrt (q - p) := by
  have hA := Real.sqrt_nonneg p
  have hB := Real.sqrt_nonneg (q - p)
  have hC := Real.sqrt_nonneg q
  have hA2 := Real.sq_sqrt hp
  have hB2 := Real.sq_sqrt (show 0 ≤ q - p by linarith)
  have hC2 := Real.sq_sqrt (show 0 ≤ q by linarith)
  nlinarith [mul_nonneg hA hB]

/-- `∫_p^q |y|^{−1/2} dy ≤ 3√(q − p)` for `p ≤ q`. -/
theorem integral_abs_rpow_neg_half_le {p q : ℝ} (hpq : p ≤ q) :
    ∫ y in p..q, |y| ^ (-(1 / 2) : ℝ) ≤ 3 * Real.sqrt (q - p) := by
  have hs : 0 ≤ Real.sqrt (q - p) := Real.sqrt_nonneg _
  rcases le_total 0 p with hp | hp
  · rw [integral_abs_rpow_neg_half_of_nonneg hp hpq]
    linarith [sqrt_sub_le hp hpq]
  rcases le_total q 0 with hq | hq
  · -- reflect to the positive side
    have e : ∫ y in p..q, |y| ^ (-(1 / 2) : ℝ) = ∫ y in -q..-p, |y| ^ (-(1 / 2) : ℝ) := by
      have := intervalIntegral.integral_comp_neg (a := -q) (b := -p)
        (fun y : ℝ => |y| ^ (-(1 / 2) : ℝ))
      simp only [abs_neg, neg_neg] at this
      rw [this]
    rw [e, integral_abs_rpow_neg_half_of_nonneg (by linarith) (by linarith)]
    have := sqrt_sub_le (by linarith : (0 : ℝ) ≤ -q) (by linarith : -q ≤ -p)
    rw [show -p - -q = q - p by ring] at this
    linarith
  · -- split at zero
    rw [← integral_add_adjacent_intervals (b := 0) (intervalIntegrable_abs_rpow_neg_half _ _)
      (intervalIntegrable_abs_rpow_neg_half _ _)]
    have e : ∫ y in p..0, |y| ^ (-(1 / 2) : ℝ) = ∫ y in (0 : ℝ)..-p, |y| ^ (-(1 / 2) : ℝ) := by
      have := intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := -p)
        (fun y : ℝ => |y| ^ (-(1 / 2) : ℝ))
      simp only [abs_neg, neg_neg, neg_zero] at this
      rw [this]
    rw [e, integral_abs_rpow_neg_half_of_nonneg le_rfl (by linarith),
      integral_abs_rpow_neg_half_of_nonneg le_rfl hq, Real.sqrt_zero]
    have hA := Real.sqrt_nonneg (-p)
    have hB := Real.sqrt_nonneg q
    have hA2 := Real.sq_sqrt (show 0 ≤ -p by linarith)
    have hB2 := Real.sq_sqrt hq
    have hS2 := Real.sq_sqrt (show 0 ≤ q - p by linarith)
    have key : (Real.sqrt (-p) + Real.sqrt q) ^ 2 ≤ (3 / 2 * Real.sqrt (q - p)) ^ 2 := by
      nlinarith [sq_nonneg (Real.sqrt (-p) - Real.sqrt q)]
    have := (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).mp key
    linarith

/-- `∫_u^v |x − a|^{−1/2} dx ≤ 3√(v − u)` for `u ≤ v`. -/
theorem integral_abs_sub_rpow_neg_half_le (a : ℝ) {u v : ℝ} (huv : u ≤ v) :
    ∫ x in u..v, |x - a| ^ (-(1 / 2) : ℝ) ≤ 3 * Real.sqrt (v - u) := by
  rw [intervalIntegral.integral_comp_sub_right (fun y : ℝ => |y| ^ (-(1 / 2) : ℝ)) a]
  have := integral_abs_rpow_neg_half_le (p := u - a) (q := v - a) (by linarith)
  rwa [show v - a - (u - a) = v - u by ring] at this

/-- **Averaged radius.** -/
theorem exists_mem_Icc_sum_rpow_le {ι : Type*} (J : Finset ι) (a : ι → ℝ) {r : ℝ} (hr : 0 < r) :
    ∃ x ∈ Icc (r / 2) r, (∀ j ∈ J, x ≠ a j) ∧
      ∑ j ∈ J, |x - a j| ^ (-(1 / 2) : ℝ) ≤ J.card * (3 * Real.sqrt (r / 2) / (r / 2)) := by
  classical
  set μ : Measure ℝ := volume.restrict (Icc (r / 2) r) with hμ
  haveI : IsFiniteMeasure μ := by rw [hμ]; infer_instance
  have hle : r / 2 ≤ r := by linarith
  have hμuniv : μ univ = ENNReal.ofReal (r / 2) := by
    rw [hμ, Measure.restrict_apply_univ, Real.volume_Icc]
    congr 1; ring
  have hμ0 : μ ≠ 0 := by
    intro h
    have := congrArg (fun m : Measure ℝ => m univ) h
    simp only [Measure.coe_zero, Pi.zero_apply] at this
    rw [hμuniv, ENNReal.ofReal_eq_zero] at this
    linarith
  set f : ℝ → ℝ := fun x => ∑ j ∈ J, |x - a j| ^ (-(1 / 2) : ℝ) with hf
  have hint1 : ∀ j, IntervalIntegrable (fun x => |x - a j| ^ (-(1 / 2) : ℝ)) volume (r / 2) r := by
    intro j
    have := (intervalIntegrable_abs_rpow_neg_half (r / 2 - a j) (r - a j)).comp_sub_right (a j)
    simpa using this
  have hfint : Integrable f μ := by
    rw [hμ, hf]
    refine integrable_finsetSum _ fun j _ => ?_
    exact (intervalIntegrable_iff_integrableOn_Icc_of_le hle).mp (hint1 j)
  set N : Set ℝ := (Icc (r / 2) r)ᶜ ∪ (J.image a : Set ℝ) with hN
  have hN0 : μ N = 0 := by
    rw [hμ, Measure.restrict_apply' measurableSet_Icc]
    refine measure_mono_null (t := (J.image a : Set ℝ)) ?_ (Finset.measure_zero _ _)
    intro x hx
    rcases hx.1 with h | h
    · exact absurd hx.2 h
    · exact h
  obtain ⟨x, hxN, hx⟩ := exists_notMem_null_le_average hμ0 hfint hN0
  have hxI : x ∈ Icc (r / 2) r := by
    by_contra h
    exact hxN (Or.inl h)
  have hxa : ∀ j ∈ J, x ≠ a j := by
    intro j hj h
    exact hxN (Or.inr (by rw [h]; exact Finset.mem_coe.mpr (Finset.mem_image_of_mem a hj)))
  refine ⟨x, hxI, hxa, hx.trans ?_⟩
  -- compute the average
  rw [average_eq, smul_eq_mul, Measure.real, hμuniv, ENNReal.toReal_ofReal (by linarith)]
  have hint : ∫ y, f y ∂μ = ∑ j ∈ J, ∫ y in r / 2..r, |y - a j| ^ (-(1 / 2) : ℝ) := by
    rw [hμ, hf, integral_finsetSum _ fun j _ =>
      (intervalIntegrable_iff_integrableOn_Icc_of_le hle).mp (hint1 j)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_of_le hle, integral_Icc_eq_integral_Ioc]
  rw [hint]
  have hsum : ∑ j ∈ J, ∫ y in r / 2..r, |y - a j| ^ (-(1 / 2) : ℝ) ≤
      J.card * (3 * Real.sqrt (r / 2)) := by
    calc ∑ j ∈ J, ∫ y in r / 2..r, |y - a j| ^ (-(1 / 2) : ℝ)
        ≤ ∑ _j ∈ J, 3 * Real.sqrt (r - r / 2) :=
          Finset.sum_le_sum fun j _ => integral_abs_sub_rpow_neg_half_le (a j) hle
      _ = J.card * (3 * Real.sqrt (r / 2)) := by
          rw [Finset.sum_const, nsmul_eq_mul, show r - r / 2 = r / 2 by ring]
  have hr2 : 0 < r / 2 := by linarith
  calc (r / 2)⁻¹ * ∑ j ∈ J, ∫ y in r / 2..r, |y - a j| ^ (-(1 / 2) : ℝ)
      ≤ (r / 2)⁻¹ * (J.card * (3 * Real.sqrt (r / 2))) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = J.card * (3 * Real.sqrt (r / 2) / (r / 2)) := by field_simp

end

end GaloisForLFunctions.HTGeometry
