import GaloisForLFunctions.HTGeometry.MaximumTermLogarithmicDerivative
import GaloisForLFunctions.HTGeometry.CircleMaximumExistence
import GaloisForLFunctions.HTGeometry.CentralIndexDivergence

/-!
# Removing the constant term of a power series

Deleting the constant coefficient subtracts the value at the origin and does not affect entirety.
This is the normalisation a composition-growth argument needs: the inner function must vanish at the
centre of the disc, and replacing it by its difference with its value there costs only a translation
of the outer function.
-/

open Filter

namespace GaloisForLFunctions.HTGeometry

variable {a : ℕ → ℂ}

/-- The coefficients with the constant term deleted. -/
noncomputable def dropConst (a : ℕ → ℂ) : ℕ → ℂ := fun n => if n = 0 then 0 else a n

@[simp] theorem dropConst_zero (a : ℕ → ℂ) : dropConst a 0 = 0 := by simp [dropConst]

@[simp] theorem dropConst_succ (a : ℕ → ℂ) (n : ℕ) : dropConst a (n + 1) = a (n + 1) := by
  simp [dropConst]

/-- **Deleting the constant term preserves entirety.** -/
theorem entireCoeffs_dropConst (ha : EntireCoeffs a) : EntireCoeffs (dropConst a) := by
  intro r hr
  have hbase : Tendsto (fun n : ℕ => ‖a (n + 1)‖ * r ^ (n + 1)) atTop (nhds 0) :=
    (tendsto_add_atTop_iff_nat 1).mpr (ha r hr)
  refine (tendsto_add_atTop_iff_nat 1).mp ?_
  refine Filter.Tendsto.congr ?_ hbase
  intro n
  rw [dropConst_succ]

/-- The value of a power series at the origin is its constant term. -/
theorem coeffFun_zero (a : ℕ → ℂ) : coeffFun a 0 = a 0 := by
  rw [coeffFun_eq_tsum]
  rw [tsum_eq_single 0 ?_]
  · rw [pow_zero, mul_one]
  · intro n hn
    rw [zero_pow hn, mul_zero]

/-- **Deleting the constant term subtracts the value at the origin.** -/
theorem coeffFun_dropConst (ha : EntireCoeffs a) (z : ℂ) :
    coeffFun (dropConst a) z = coeffFun a z - a 0 := by
  rcases eq_or_ne z 0 with rfl | hz0
  · rw [coeffFun_zero, coeffFun_zero, dropConst_zero, sub_self]
  · have hz : (0 : ℝ) < ‖z‖ := norm_pos_iff.mpr hz0
    have hsum : Summable fun n : ℕ => a n * z ^ n := by
      refine Summable.of_norm ((summable_term ha hz).congr fun n => ?_)
      rw [norm_mul, norm_pow]
    have hsum' : Summable fun n : ℕ => dropConst a n * z ^ n := by
      refine Summable.of_norm ((summable_term (entireCoeffs_dropConst ha) hz).congr fun n => ?_)
      rw [norm_mul, norm_pow]
    rw [coeffFun_eq_tsum, coeffFun_eq_tsum, hsum.tsum_eq_zero_add, hsum'.tsum_eq_zero_add]
    simp

/-- **The inner function reaches its shifted maximum term.**  On every circle there is a point at
which the difference from the value at the origin is at least the maximum term of the shifted
coefficients.  This is the hypothesis `s ≤ ‖g z₀ − g 0‖` of the composition separation, with `s` the
shifted maximum term. -/
theorem exists_point_norm_sub_ge (ha : EntireCoeffs a) {r : ℝ} (hr : 0 < r) :
    ∃ z : ℂ, ‖z‖ = r ∧ maxTerm (dropConst a) r ≤ ‖coeffFun a z - coeffFun a 0‖ := by
  have ha' : EntireCoeffs (dropConst a) := entireCoeffs_dropConst ha
  obtain ⟨z, hz, hmax⟩ := exists_max_on_circle ha' hr
  refine ⟨z, hz, ?_⟩
  have hbase := maxTerm_le_norm_of_max_on_circle ha' hr hz hmax
  have heq : coeffFun (dropConst a) z = coeffFun a z - coeffFun a 0 := by
    rw [coeffFun_dropConst ha z, coeffFun_zero]
  rwa [heq] at hbase

/-- **A transcendental entire function is large on every large disc.**  For every centre, radius and
level, once the radius exceeds the centre's modulus by enough, some point of the disc carries a value
above the level. -/
theorem exists_norm_gt_of_transcendental (ha : EntireCoeffs a)
    (htrans : ∀ M : ℕ, ∃ n, M ≤ n ∧ a n ≠ 0) (c : ℂ) (K : ℝ) :
    ∀ᶠ ρ : ℝ in atTop, ∃ w ∈ Metric.closedBall c ρ, K < ‖coeffFun a w‖ := by
  have htend := tendsto_maxTerm_div_pow_atTop ha htrans 0
  have hev : ∀ᶠ r : ℝ in atTop, K < maxTerm a r := by
    have h := htend.eventually_gt_atTop K
    filter_upwards [h, eventually_gt_atTop (0 : ℝ)] with r hr hr0
    simpa using hr
  obtain ⟨r₀, hr₀⟩ := eventually_atTop.mp (hev.and (eventually_gt_atTop (0 : ℝ)))
  filter_upwards [eventually_ge_atTop (r₀ + ‖c‖ + 1)] with ρ hρ
  obtain ⟨hKr, hrpos⟩ := hr₀ (ρ - ‖c‖) (by linarith)
  obtain ⟨w, hw, hmax⟩ := exists_max_on_circle ha hrpos
  refine ⟨w, ?_, ?_⟩
  · simp only [Metric.mem_closedBall, dist_eq_norm]
    have h1 : ‖w - c‖ ≤ ‖w‖ + ‖c‖ := norm_sub_le w c
    rw [hw] at h1
    linarith
  · have := maxTerm_le_norm_of_max_on_circle ha hrpos hw hmax
    linarith

end GaloisForLFunctions.HTGeometry
