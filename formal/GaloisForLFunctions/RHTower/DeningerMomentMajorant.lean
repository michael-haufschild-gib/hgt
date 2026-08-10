import GaloisForLFunctions.RHTower.DeningerHigherMoment
import GaloisForLFunctions.RHTower.DeningerMeyerSeminorm

/-!
# The source-free majorant of the weighted moments

The two-sided estimate for the weighted derivative of the pullback separates into a factor
depending only on the source — the Meyer seminorm `q_{r+2,1}` — and a factor depending only on the
order,

`u^{r+1} |H_h'(u)| ≤ q_{r+2,1}(h) · min(u^{2r+2}, u^{-2})`.

The second factor is integrable on the ray with a mass that does not depend on the source, which is
what makes the weighted-moment estimate a *seminorm* bound rather than a bare finiteness statement.

* `deningerMomentMajorant` : the order-`r` majorant `min(u^{2r+2}, u^{-2})`.
* `deningerMomentMajorantMass` : its mass on the ray.
* `deningerLogPullDeriv_weightedPow_le_seminorm` : **the seminorm form of the moment estimate.**
-/

namespace RHTower

open MeasureTheory SchwartzMap

noncomputable section

/-- The order-`r` majorant `min(u^{2r+2}, u^{-2})` of the weighted pullback derivative. -/
def deningerMomentMajorant (r : ℕ) (u : ℝ) : ℝ := min (u ^ (2 * r + 2)) (1 / u ^ 2)

theorem deningerMomentMajorant_nonneg (r : ℕ) {u : ℝ} (hu : 0 < u) :
    0 ≤ deningerMomentMajorant r u := by
  rw [deningerMomentMajorant]
  refine le_min (by positivity) (by positivity)

theorem deningerMomentMajorant_continuousOn (r : ℕ) :
    ContinuousOn (deningerMomentMajorant r) (Set.Ioi 0) := by
  have h1 : ContinuousOn (fun u : ℝ => u ^ (2 * r + 2)) (Set.Ioi 0) := continuousOn_pow _
  have h2 : ContinuousOn (fun u : ℝ => 1 / u ^ 2) (Set.Ioi 0) := by
    refine ContinuousOn.div continuousOn_const (continuousOn_pow _) fun u hu => ?_
    have hu0 : (0 : ℝ) < u := hu
    positivity
  exact fun u hu => (h1 u hu).min (h2 u hu)

/-- **The order-`r` majorant is integrable on the ray**, with a mass independent of the source. -/
theorem deningerMomentMajorant_integrableOn (r : ℕ) :
    IntegrableOn (deningerMomentMajorant r) (Set.Ioi 0) := by
  have hnear : IntegrableOn (deningerMomentMajorant r) (Set.Ioc 0 1) := by
    have hconst : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Set.Ioc 0 1) := by
      refine integrableOn_const ?_
      simp
    refine Integrable.mono' hconst
      (((deningerMomentMajorant_continuousOn r).mono
        Set.Ioc_subset_Ioi_self).aestronglyMeasurable measurableSet_Ioc) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    have hu0 : (0 : ℝ) < u := hu.1
    have hu1 : u ≤ 1 := hu.2
    rw [Real.norm_of_nonneg (deningerMomentMajorant_nonneg r hu0)]
    refine le_trans (min_le_left _ _) ?_
    exact pow_le_one₀ hu0.le hu1
  have hfar : IntegrableOn (deningerMomentMajorant r) (Set.Ioi 1) := by
    have hmaj : IntegrableOn (fun u : ℝ => u ^ (-2 : ℝ)) (Set.Ioi 1) :=
      (integrableOn_Ioi_rpow_iff (by norm_num)).mpr (by norm_num)
    refine Integrable.mono' hmaj
      (((deningerMomentMajorant_continuousOn r).mono
        (Set.Ioi_subset_Ioi (by norm_num))).aestronglyMeasurable measurableSet_Ioi) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu1 : (1 : ℝ) < u := hu
    have hu0 : (0 : ℝ) < u := lt_trans zero_lt_one hu1
    rw [Real.norm_of_nonneg (deningerMomentMajorant_nonneg r hu0)]
    refine le_trans (min_le_right _ _) (le_of_eq ?_)
    rw [Real.rpow_neg hu0.le, show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num,
      Real.rpow_natCast, ← one_div]
  have hunion : Set.Ioc (0 : ℝ) 1 ∪ Set.Ioi 1 = Set.Ioi 0 :=
    Set.Ioc_union_Ioi_eq_Ioi (by norm_num)
  rw [← hunion]
  exact hnear.union hfar

/-- The mass of the order-`r` majorant on the ray. -/
def deningerMomentMajorantMass (r : ℕ) : ℝ := ∫ u in Set.Ioi (0 : ℝ), deningerMomentMajorant r u

theorem deningerMomentMajorantMass_nonneg (r : ℕ) : 0 ≤ deningerMomentMajorantMass r :=
  setIntegral_nonneg measurableSet_Ioi fun _ hu => deningerMomentMajorant_nonneg r hu

/-- The Meyer seminorm at order one bounds the derivative weight. -/
theorem deningerMeyerSeminorm_deriv_bound (A : ℝ) (h : DeningerExpSchwartz) (t : ℝ) :
    Real.exp (A * |t|) *
        ‖deriv (((h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) : ℝ → ℂ) t‖
      ≤ deningerMeyerSeminormFun A 1 h := by
  have hbase := deningerMeyerWeight_le A 1 h t
  rw [deningerMeyerWeight, norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_one] at hbase
  exact hbase

/-- **The seminorm form of the weighted-moment estimate.** -/
theorem deningerLogPullDeriv_weightedPow_le_seminorm (r : ℕ) (h : DeningerExpSchwartz) {y : ℝ}
    (hy : 0 < y) :
    y ^ (r + 1) * ‖deningerLogPullDeriv (((h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ))) y‖
      ≤ deningerMeyerSeminormFun ((r : ℝ) + 2) 1 h * deningerMomentMajorant r y := by
  set g : 𝓢(ℝ, ℂ) := ((h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) with hg
  set C : ℝ := deningerMeyerSeminormFun ((r : ℝ) + 2) 1 h with hC
  have hCnn : 0 ≤ C := deningerMeyerSeminormFun_nonneg _ _ _
  have hbase : ∀ t : ℝ, Real.exp (((r : ℝ) + 2) * |t|) * ‖deriv (g : ℝ → ℂ) t‖ ≤ C :=
    fun t => deningerMeyerSeminorm_deriv_bound ((r : ℝ) + 2) h t
  have hcancel : y * ‖deningerLogPullDeriv g y‖ = ‖deriv (g : ℝ → ℂ) (Real.log y)‖ := by
    rw [deningerLogPullDeriv, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_inv,
      abs_of_pos hy]
    field_simp
  have hval : ‖deriv (g : ℝ → ℂ) (Real.log y)‖
      ≤ C * Real.exp (-(((r : ℝ) + 2) * |Real.log y|)) := by
    have hepos : (0 : ℝ) < Real.exp (((r : ℝ) + 2) * |Real.log y|) := Real.exp_pos _
    rw [Real.exp_neg, ← div_eq_mul_inv, le_div_iff₀ hepos]
    calc ‖deriv (g : ℝ → ℂ) (Real.log y)‖ * Real.exp (((r : ℝ) + 2) * |Real.log y|)
        = Real.exp (((r : ℝ) + 2) * |Real.log y|) * ‖deriv (g : ℝ → ℂ) (Real.log y)‖ := by ring
      _ ≤ C := hbase (Real.log y)
  have hcast : ((r + 2 : ℕ) : ℝ) = (r : ℝ) + 2 := by push_cast; ring
  obtain ⟨hup, hdown⟩ := deningerExpWeight_le_pow (r + 2) hy
  rw [hcast] at hup hdown
  have hsplit : y ^ (r + 1) * ‖deningerLogPullDeriv g y‖
      = y ^ r * (y * ‖deningerLogPullDeriv g y‖) := by
    rw [pow_succ]
    ring
  rw [hsplit, hcancel]
  have hyr : (0 : ℝ) ≤ y ^ r := pow_nonneg hy.le r
  rw [deningerMomentMajorant, mul_min_of_nonneg _ _ hCnn]
  refine le_min ?_ ?_
  · have hstep : y ^ r * ‖deriv (g : ℝ → ℂ) (Real.log y)‖
        ≤ y ^ r * (C * y ^ (r + 2)) := by
      refine mul_le_mul_of_nonneg_left (le_trans hval ?_) hyr
      exact mul_le_mul_of_nonneg_left hup hCnn
    refine le_trans hstep (le_of_eq ?_)
    rw [show 2 * r + 2 = r + (r + 2) by ring, pow_add]
    ring
  · have hstep : y ^ r * ‖deriv (g : ℝ → ℂ) (Real.log y)‖
        ≤ y ^ r * (C * (1 / y ^ (r + 2))) := by
      refine mul_le_mul_of_nonneg_left (le_trans hval ?_) hyr
      exact mul_le_mul_of_nonneg_left hdown hCnn
    refine le_trans hstep (le_of_eq ?_)
    rw [pow_add]
    field_simp

end

end RHTower
