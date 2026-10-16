import GaloisForLFunctions.RHTower.ThetaZeroDivisionRealization
import GaloisForLFunctions.RHTower.CausalThetaHalfLaplace

/-!
# Global regularity of finite theta-divisor sources

Exponential moments bound the joined Green derivative on the positive half-line.
Reflection through absolute value then makes zero division globally Lipschitz,
even when its source has a nonzero Fourier value at the division point. Finite
polynomial combinations of successive divisions inherit this regularity.
-/

open MeasureTheory Set Filter Topology
noncomputable section
namespace RHTower

theorem ExpMomentSource.norm_weighted_tail_le {f : ℝ → ℂ} (hf : ExpMomentSource f)
    {a : ℝ} (ha : 0 ≤ a) {w : ℝ → ℂ} (hw : Integrable (fun t => w t * f t))
    (hb : ∀ t, ‖w t‖ ≤ Real.exp (a * |t|)) {x : ℝ} (hx : 0 ≤ x) :
    Real.exp (a * x) * ‖∫ t in Ioi x, w t * f t‖ ≤
      ∫ t, Real.exp ((2 * a) * |t|) * ‖f t‖ := by
  have hm := hf.moment (2 * a)
  calc
    _ ≤ Real.exp (a * x) * (∫ t in Ioi x, ‖w t * f t‖) :=
      mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (Real.exp_pos _).le
    _ = ∫ t in Ioi x, Real.exp (a * x) * ‖w t * f t‖ := (integral_const_mul _ _).symm
    _ ≤ ∫ t in Ioi x, Real.exp ((2 * a) * |t|) * ‖f t‖ := by
      apply setIntegral_mono_on (hw.integrableOn.norm.const_mul _) hm.integrableOn
        measurableSet_Ioi
      intro t ht
      have ht0 : 0 ≤ t := hx.trans ht.le
      rw [norm_mul]
      calc
        _ ≤ Real.exp (a * x) * (Real.exp (a * |t|) * ‖f t‖) := by
          gcongr
          exact hb t
        _ = Real.exp (a * x + a * |t|) * ‖f t‖ := by rw [Real.exp_add]; ring
        _ ≤ Real.exp ((2 * a) * |t|) * ‖f t‖ := by
          gcongr
          rw [abs_of_nonneg ht0]
          nlinarith [mul_le_mul_of_nonneg_left ht.le ha]
    _ ≤ _ := setIntegral_le_integral hm (Eventually.of_forall fun t => by positivity)

theorem ExpMomentSource.norm_joinedDivisionDeriv_le {f : ℝ → ℂ}
    (hf : ExpMomentSource f) (α : ℂ) {x : ℝ} (hx : 0 ≤ x) :
    ‖joinedDivisionDeriv α f x‖ ≤
      2 * ‖α‖ ^ 2 * (∫ t, Real.exp ((2 * |α.im|) * |t|) * ‖f t‖) := by
  have hs := hf.norm_weighted_tail_le (abs_nonneg α.im) (hf.integrable_sin α)
    (norm_csin_mul_ofReal_le α) hx
  have hc := hf.norm_weighted_tail_le (abs_nonneg α.im) (hf.integrable_cos α)
    (norm_ccos_mul_ofReal_le α) hx
  have hsin : ‖Complex.sin (α * x) * sineTail α f x‖ ≤
      ∫ t, Real.exp ((2 * |α.im|) * |t|) * ‖f t‖ := by
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_right
      (by simpa only [abs_of_nonneg hx] using norm_csin_mul_ofReal_le α x)
      (norm_nonneg _)).trans hs
  have hcos : ‖Complex.cos (α * x) * cosineTail α f x‖ ≤
      ∫ t, Real.exp ((2 * |α.im|) * |t|) * ‖f t‖ := by
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_right
      (by simpa only [abs_of_nonneg hx] using norm_ccos_mul_ofReal_le α x)
      (norm_nonneg _)).trans hc
  rw [joinedDivisionDeriv, norm_neg, norm_mul, norm_pow]
  calc
    _ ≤ ‖α‖ ^ 2 * (‖Complex.sin (α * x) * sineTail α f x‖ +
        ‖Complex.cos (α * x) * cosineTail α f x‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) (sq_nonneg _)
    _ ≤ _ := by nlinarith [sq_nonneg ‖α‖]

/-- Zero division is globally Lipschitz without a seam-cancellation hypothesis. -/
theorem ExpMomentSource.exists_lipschitz_zeroDivision {f : ℝ → ℂ}
    (hf : ExpMomentSource f) (α : ℂ) : ∃ C, LipschitzWith C (zeroDivision α f) := by
  let M := 2 * ‖α‖ ^ 2 * (∫ t, Real.exp ((2 * |α.im|) * |t|) * ‖f t‖)
  have hM : 0 ≤ M := mul_nonneg (by positivity)
    (integral_nonneg fun t => by positivity)
  let C : NNReal := ⟨M, hM⟩
  have hl : LipschitzOnWith C (joinedDivision α f) (Ici 0) := by
    apply Convex.lipschitzOnWith_of_nnnorm_deriv_le
      (fun x _ => (hasDerivAt_joinedDivision hf α x).differentiableAt) ?_ (convex_Ici 0)
    intro x hx
    change ‖deriv (joinedDivision α f) x‖ ≤ M
    rw [(hasDerivAt_joinedDivision hf α x).deriv]
    exact hf.norm_joinedDivisionDeriv_le α hx
  refine ⟨C, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
  rw [zeroDivision_eq_joinedDivision_abs hf α x, zeroDivision_eq_joinedDivision_abs hf α y]
  exact (hl.dist_le_mul |x| (abs_nonneg x) |y| (abs_nonneg y)).trans
    (mul_le_mul_of_nonneg_left (by
      simpa only [Real.dist_eq] using abs_abs_sub_abs_le_abs_sub x y) C.coe_nonneg)

theorem exists_lipschitz_thetaCuspFullSource : ∃ C, LipschitzWith C thetaCuspFullSource := by
  obtain ⟨C, hC, hb⟩ := exists_abs_deriv_thetaCuspFullSource_le 0
  refine ⟨⟨C, hC⟩, lipschitzWith_of_nnnorm_deriv_le differentiable_thetaCuspFullSource
    fun x => ?_⟩
  change ‖deriv thetaCuspFullSource x‖ ≤ C
  simpa using hb x

theorem exists_lipschitz_thetaSourceC : ∃ C, LipschitzWith C thetaSourceC := by
  obtain ⟨C, hC⟩ := exists_lipschitz_thetaCuspFullSource
  exact ⟨1 * C, RCLike.lipschitzWith_ofReal.comp hC⟩

theorem exists_lipschitz_thetaListDivision (L : List ℂ) :
    ∃ C, LipschitzWith C (thetaListDivision L) := by
  cases L with
  | nil => exact exists_lipschitz_thetaSourceC
  | cons α L => exact (expMomentSource_thetaListDivision L).exists_lipschitz_zeroDivision α

theorem exists_lipschitz_listComb (L : List ℂ) (e : Polynomial ℂ) :
    ∃ C, LipschitzWith C (listComb thetaListDivision L e) := by
  induction L generalizing e with
  | nil =>
    obtain ⟨C, hC⟩ := exists_lipschitz_thetaSourceC
    exact ⟨‖e.coeff 0‖₊ * C, (lipschitzWith_smul (e.coeff 0)).comp hC⟩
  | cons α L ih =>
    obtain ⟨C, hC⟩ := exists_lipschitz_thetaListDivision (α :: L)
    obtain ⟨D, hD⟩ := ih (e /ₘ (Polynomial.X - Polynomial.C (α ^ 2)))
    exact ⟨_, ((lipschitzWith_smul (e.eval (α ^ 2))).comp hC).sub
      ((lipschitzWith_smul (α ^ 2)).comp hD)⟩

end RHTower
