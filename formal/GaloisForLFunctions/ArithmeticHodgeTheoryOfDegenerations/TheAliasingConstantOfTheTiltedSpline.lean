import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheAliasingIsTheDilationDerivativeOfTheBulk
import GaloisForLFunctions.HTGeometry.PeriodicMeanZeroAveraging

/-!
# The aliasing constant of the tilted spline

For the tilted spline the spectrum is explicit, `|φ̂(2πt)|² = (1/64) q(πt/4)(1 + (πt/4)²)^{−4}`
with the `π`-periodic numerator `q(x) = (sinh²1 + sin²x)⁴` of mean `μ_q`. At depth `y` of a
horizon window the `k`-th harmonic of the atom grid sits at `πkce^y/4`, where `q` oscillates with
frequency `≍ c`. Against the slowly varying window weight the oscillation averages to `μ_q`
(`abs_integral_mul_numerator_sub_le`, cell by cell on the periods of `q`), the Riemann sums over
`n ≤ N` see the oscillation only through `c/N → 0`, and the harmonics sum to `ζ(8)`:

`c⁸ 𝒜_N → 2 (1/64)(4/π)⁸ μ_q ζ(8) ∫ e^{−7y} h(y)² dy`   (`tendsto_rpow_eight_mul_horizonAlias`).

With `J(1) = lim c⁷ E₁(c) = (2/∫φ²) A_φ ζ(8)` the conductor-one Jordan coefficient of the bulk
(ADT), the constant is `7 J(1) ∫φ²`: the horizon window pays `β J(1)` per unit of
`∫ e^{−(β+1)y} H(y)²`, `β = 7` — the pointwise density `−d/ds (J(1) s^{−7}) = 7 J(1) s^{−8}` of the
bulk limit, read at the local overlaps `s = c e^y`.
-/

noncomputable section

open Finset Filter Topology MeasureTheory Zeta23
open scoped Real

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

open SpacingScaleHarmonicAnalysis RenormalizedArithmeticPotentialTheory.CompletedShell
  ArithmeticDegenerationTheory

variable {g h : ℝ → ℝ} {A : ℝ}

/-! ### The periodic numerator -/

/-- The numerator `q(x) = (sinh²1 + sin²x)⁴` is Lipschitz with constant `4 (sinh²1 + 1)³`. -/
theorem abs_splineNumerator_sub_le (u v : ℝ) :
    |splineNumerator u - splineNumerator v| ≤ 4 * (Real.sinh 1 ^ 2 + 1) ^ 3 * |u - v| := by
  set a := Real.sinh 1 ^ 2 with ha
  have ha0 : 0 ≤ a := sq_nonneg _
  have hd : ∀ x, HasDerivAt splineNumerator
      (4 * (a + Real.sin x ^ 2) ^ 3 * (2 * Real.sin x * Real.cos x)) x := by
    intro x
    have h1 : HasDerivAt (fun x => a + Real.sin x ^ 2) (2 * Real.sin x * Real.cos x) x :=
      (((Real.hasDerivAt_sin x).pow 2).const_add a).congr_deriv (by
        rw [show (2 : ℕ) - 1 = 1 from rfl, pow_one]; push_cast; ring)
    exact (h1.pow 4).congr_deriv (by rw [show (4 : ℕ) - 1 = 3 from rfl]; push_cast; ring)
  have hb : ∀ x, ‖deriv splineNumerator x‖ ≤ 4 * (a + 1) ^ 3 := by
    intro x
    rw [(hd x).deriv, Real.norm_eq_abs, abs_mul, abs_mul]
    have h1 : |a + Real.sin x ^ 2| ^ 3 ≤ (a + 1) ^ 3 := by
      rw [abs_of_nonneg (by positivity)]
      exact pow_le_pow_left₀ (by positivity) (by nlinarith [Real.sin_sq_le_one x]) 3
    have h2 : |2 * Real.sin x * Real.cos x| ≤ 1 := by
      rw [abs_le]
      constructor <;> nlinarith [Real.sin_sq_add_cos_sq x, sq_nonneg (Real.sin x + Real.cos x),
        sq_nonneg (Real.sin x - Real.cos x)]
    rw [abs_pow, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
    calc 4 * |a + Real.sin x ^ 2| ^ 3 * |2 * Real.sin x * Real.cos x| ≤ 4 * (a + 1) ^ 3 * 1 :=
          mul_le_mul (mul_le_mul_of_nonneg_left h1 (by norm_num)) h2 (abs_nonneg _) (by positivity)
      _ = 4 * (a + 1) ^ 3 := mul_one _
  have hlip := lipschitzWith_of_nnnorm_deriv_le (C := Real.toNNReal (4 * (a + 1) ^ 3))
    (fun x => (hd x).differentiableAt) fun x => by
      rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal _ (by positivity)]
      exact hb x
  have := hlip.dist_le_mul u v
  rwa [Real.coe_toNNReal _ (by positivity), Real.dist_eq, Real.dist_eq] at this

/-- **Averaging the numerator.** For a weight `F` with continuous derivative, vanishing on
`[1, ∞)`, and `λ ≥ π`: `|∫_0^1 F(x) q(λx) dx − μ_q ∫_0^1 F| ≤ B_q (π/λ) ∫_0^2 |F'|`. -/
theorem abs_integral_mul_numerator_sub_le {F F' : ℝ → ℝ} (hF : ∀ x, HasDerivAt F (F' x) x)
    (hF' : Continuous F') (hF1 : ∀ x, 1 ≤ x → F x = 0) {lam : ℝ} (hlam : π ≤ lam) :
    |(∫ x in (0 : ℝ)..1, F x * splineNumerator (lam * x)) -
        splineNumeratorMean * ∫ x in (0 : ℝ)..1, F x| ≤
      (Real.sinh 1 ^ 2 + 1) ^ 4 * (π / lam) * ∫ x in (0 : ℝ)..2, |F' x| := by
  have hpi := Real.pi_pos
  have hlam0 : 0 < lam := by linarith
  set μq := splineNumeratorMean with hμq
  set Bq := (Real.sinh 1 ^ 2 + 1) ^ 4 with hBq
  have hμ0 : 0 ≤ μq := splineNumeratorMean_pos.le
  have hμB : μq ≤ Bq := by
    rw [hμq, splineNumeratorMean, div_le_iff₀ hpi]
    calc ∫ x in (0 : ℝ)..π, splineNumerator x ≤ ∫ x in (0 : ℝ)..π, Bq :=
          intervalIntegral.integral_mono_on hpi.le (continuous_splineNumerator.intervalIntegrable _ _)
            intervalIntegrable_const fun x _ => splineNumerator_le x
      _ = Bq * π := by simp; ring
  set S : ℝ → ℝ := fun y => splineNumerator (lam * y) - μq with hS
  have hScont : Continuous S := (continuous_splineNumerator.comp (continuous_const.mul
    continuous_id)).sub continuous_const
  have hSb : ∀ y, |S y| ≤ Bq := fun y => by
    rw [hS, abs_le]
    have := splineNumerator_nonneg (lam * y)
    have := splineNumerator_le (lam * y)
    constructor <;> linarith
  set T := π / lam with hT
  have hT0 : 0 < T := by positivity
  set x : ℕ → ℝ := fun k => k * T with hx
  set n := ⌈lam / π⌉₊ with hn
  have hxmono : Monotone x := fun i j hij => by
    simp only [hx]; exact mul_le_mul_of_nonneg_right (by exact_mod_cast hij) hT0.le
  have hlen : ∀ k, x (k + 1) - x k ≤ T := fun k => by simp only [hx]; push_cast; ring_nf; rfl
  have hmean : ∀ k, ∫ y in (x k)..(x (k + 1)), S y = 0 := by
    intro k
    simp only [hx, hS]
    have i1 : IntervalIntegrable (fun y => splineNumerator (lam * y)) volume (k * T) ((k + 1 : ℕ) * T) :=
      (continuous_splineNumerator.comp (continuous_const.mul continuous_id)).intervalIntegrable _ _
    rw [intervalIntegral.integral_sub i1 intervalIntegrable_const,
      intervalIntegral.integral_comp_mul_left (fun y => splineNumerator y) hlam0.ne',
      intervalIntegral.integral_const, smul_eq_mul, smul_eq_mul]
    have hper : ∫ y in (lam * (k * T))..(lam * ((k + 1 : ℕ) * T)), splineNumerator y =
        ∫ y in (0 : ℝ)..π, splineNumerator y := by
      have e1 : lam * (k * T) = k * π := by rw [hT]; field_simp
      have e2 : lam * ((k + 1 : ℕ) * T) = k * π + π := by rw [hT]; push_cast; field_simp
      rw [e1, e2, splineNumerator_periodic.intervalIntegral_add_eq (k * π) 0, zero_add]
    rw [hper]
    have hmeanq : ∫ y in (0 : ℝ)..π, splineNumerator y = π * μq := by
      rw [hμq, splineNumeratorMean]; field_simp
    rw [hmeanq]
    push_cast
    rw [hT]; field_simp; ring
  have hSint : ∀ u v : ℝ, IntervalIntegrable S volume u v := fun u v => hScont.intervalIntegrable _ _
  have hF'int : ∀ u v : ℝ, IntervalIntegrable F' volume u v := fun u v => hF'.intervalIntegrable _ _
  have hbound := HTGeometry.abs_integral_mul_meanZero_partition_le x n hxmono hlen hmean hSb hSint hF
    hF'int
  have hx0 : x 0 = 0 := by simp [hx]
  have hxn1 : 1 ≤ x n := by
    simp only [hx, hT]
    have : lam / π ≤ n := Nat.le_ceil _
    rw [mul_div_assoc', le_div_iff₀ hlam0, one_mul]
    calc lam = lam / π * π := by field_simp
      _ ≤ n * π := mul_le_mul_of_nonneg_right this hpi.le
  have hxn2 : x n ≤ 2 := by
    simp only [hx, hT]
    have : (n : ℝ) < lam / π + 1 := Nat.ceil_lt_add_one (by positivity)
    have h1 : (n : ℝ) * (π / lam) < (lam / π + 1) * (π / lam) :=
      mul_lt_mul_of_pos_right this (by positivity)
    have h2 : (lam / π + 1) * (π / lam) = 1 + π / lam := by field_simp
    have h3 : π / lam ≤ 1 := by rw [div_le_one hlam0]; exact hlam
    linarith
  have hFcont : Continuous F := continuous_iff_continuousAt.mpr fun z => (hF z).continuousAt
  have hprod : Continuous fun y => F y * S y := hFcont.mul hScont
  -- the integral up to `x n` is the integral up to `1`
  have hext : ∫ y in (0 : ℝ)..(x n), F y * S y = ∫ y in (0 : ℝ)..1, F y * S y := by
    rw [← intervalIntegral.integral_add_adjacent_intervals (b := 1) (hprod.intervalIntegrable _ _)
      (hprod.intervalIntegrable _ _)]
    have hz : ∫ y in (1 : ℝ)..(x n), F y * S y = 0 := by
      rw [intervalIntegral.integral_of_le hxn1]
      refine setIntegral_eq_zero_of_forall_eq_zero fun y hy => ?_
      rw [hF1 y hy.1.le, zero_mul]
    rw [hz, add_zero]
  have hsplit : ∫ y in (0 : ℝ)..1, F y * S y =
      (∫ y in (0 : ℝ)..1, F y * splineNumerator (lam * y)) - μq * ∫ y in (0 : ℝ)..1, F y := by
    simp only [hS, mul_sub]
    have i1 : IntervalIntegrable (fun y => F y * splineNumerator (lam * y)) volume 0 1 :=
      (hFcont.mul (continuous_splineNumerator.comp (continuous_const.mul continuous_id))).intervalIntegrable _ _
    have i2 : IntervalIntegrable (fun y => F y * μq) volume 0 1 :=
      (hFcont.mul continuous_const).intervalIntegrable _ _
    rw [intervalIntegral.integral_sub i1 i2, intervalIntegral.integral_mul_const]
    ring
  have hvar : ∫ u in (0 : ℝ)..(x n), |F' u| ≤ ∫ u in (0 : ℝ)..2, |F' u| :=
    intervalIntegral.integral_mono_interval le_rfl (by linarith) hxn2
      (Eventually.of_forall fun u => abs_nonneg _) (hF'.abs.intervalIntegrable _ _)
  rw [hx0, hext, hsplit] at hbound
  calc _ ≤ Bq * T * ∫ u in (0 : ℝ)..(x n), |F' u| := hbound
    _ ≤ Bq * T * ∫ u in (0 : ℝ)..2, |F' u| := mul_le_mul_of_nonneg_left hvar (by positivity)

/-! ### Window weights in the linear variable -/

/-- `F_g(x) = g(log x)` for `x > 0`, extended by `0`. -/
def logProfile (g : ℝ → ℝ) (x : ℝ) : ℝ := if 0 < x then g (Real.log x) else 0

/-- Its derivative `g'(log x)/x`, extended by `0`. -/
def logProfileDeriv (g : ℝ → ℝ) (x : ℝ) : ℝ := if 0 < x then deriv g (Real.log x) / x else 0

theorem logProfile_eq_zero_of_lt (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → g y = 0) {x : ℝ}
    (hx : x < Real.exp (-A)) : logProfile g x = 0 := by
  unfold logProfile
  split_ifs with h0
  · exact hsupp _ fun hm => by
      have : Real.log x < -A := by rw [Real.log_lt_iff_lt_exp h0]; exact hx
      linarith [hm.1]
  · rfl

theorem logProfile_eq_zero_of_one_le (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → g y = 0) (hg0 : g 0 = 0)
    {x : ℝ} (hx : 1 ≤ x) : logProfile g x = 0 := by
  rw [logProfile, if_pos (by linarith)]
  rcases eq_or_lt_of_le hx with h1 | h1
  · rw [← h1, Real.log_one, hg0]
  · exact hsupp _ fun hm => by linarith [hm.2, Real.log_pos h1]

theorem logProfile_eq_horizonProfile (g : ℝ → ℝ) (x : ℝ) :
    (logProfile g x : ℂ) = horizonProfile g 1 x := by
  unfold logProfile horizonProfile
  split_ifs <;> simp

theorem hasDerivAt_logProfile (hg : ContDiff ℝ 2 g) (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → g y = 0)
    (x : ℝ) : HasDerivAt (logProfile g) (logProfileDeriv g x) x := by
  rcases le_or_gt x 0 with hx | hx
  · have hev : logProfile g =ᶠ[𝓝 x] fun _ => 0 :=
      (gt_mem_nhds (lt_of_le_of_lt hx (Real.exp_pos (-A)))).mono fun t ht =>
        logProfile_eq_zero_of_lt hsupp ht
    rw [logProfileDeriv, if_neg (not_lt.mpr hx)]
    exact (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq hev
  · have hev : logProfile g =ᶠ[𝓝 x] fun t => g (Real.log t) :=
      (lt_mem_nhds hx).mono fun t ht => by simp only [logProfile, if_pos ht]
    rw [logProfileDeriv, if_pos hx]
    have := ((hg.differentiable (by norm_num)) (Real.log x)).hasDerivAt.comp x
      (Real.hasDerivAt_log hx.ne')
    exact (this.congr_deriv (by rw [div_eq_mul_inv])).congr_of_eventuallyEq hev

theorem continuous_logProfileDeriv (hg : ContDiff ℝ 2 g)
    (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → g y = 0) : Continuous (logProfileDeriv g) := by
  have hd : Continuous (deriv g) := hg.continuous_deriv (by norm_num)
  rw [continuous_iff_continuousAt]
  intro x
  rcases le_or_gt x 0 with hx | hx
  · have hev : logProfileDeriv g =ᶠ[𝓝 x] fun _ => 0 := by
      refine (gt_mem_nhds (lt_of_le_of_lt hx (Real.exp_pos (-A)))).mono fun t ht => ?_
      unfold logProfileDeriv
      split_ifs with h0
      · rw [deriv_eq_zero_of_notMem_window hsupp fun hm => by
          have : Real.log t < -A := by rw [Real.log_lt_iff_lt_exp h0]; exact ht
          linarith [hm.1], zero_div]
      · rfl
    exact ContinuousAt.congr continuousAt_const hev.symm
  · have hev : logProfileDeriv g =ᶠ[𝓝 x] fun t => deriv g (Real.log t) / t :=
      (lt_mem_nhds hx).mono fun t ht => by simp only [logProfileDeriv, if_pos ht]
    refine ContinuousAt.congr ?_ hev.symm
    exact ((hd.continuousAt).comp (Real.continuousAt_log hx.ne')).div continuousAt_id hx.ne'

/-- `∫_0^1 g(log x) dx = ∫ e^y g(y) dy`. -/
theorem integral_logProfile (hg : ContDiff ℝ 2 g) (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → g y = 0)
    (hA : 0 ≤ A) : ∫ x in (0 : ℝ)..1, logProfile g x = ∫ y, Real.exp y * g y := by
  have h1 := integral_horizonProfile hg.continuous hsupp hA 1
  have hL : ∫ x in (0 : ℝ)..1, logProfile g x = ∫ x, logProfile g x := by
    rw [intervalIntegral.integral_of_le zero_le_one, ← integral_Icc_eq_integral_Ioc,
      setIntegral_eq_integral_of_forall_compl_eq_zero]
    intro x hx
    have := horizonProfile_eq_zero_of_notMem hsupp 1 hx
    rw [← logProfile_eq_horizonProfile] at this
    exact_mod_cast this
  have hR : horizonTransform g 1 = ((∫ y, Real.exp y * g y : ℝ) : ℂ) := by
    rw [horizonTransform, ← integral_complex_ofReal]
    congr 1; funext y
    push_cast; rw [one_mul]; ring
  have hc : ((∫ x, logProfile g x : ℝ) : ℂ) = ∫ x, horizonProfile g 1 x := by
    rw [← integral_complex_ofReal]
    congr 1; funext x; exact logProfile_eq_horizonProfile g x
  rw [hL]
  exact_mod_cast hc.trans (h1.trans hR)

/-- The window weight is Lipschitz with constant `L_g e^{2A}`. -/
theorem abs_logProfile_sub_le (hg : ContDiff ℝ 2 g) (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → g y = 0)
    (hA : 0 ≤ A) {Bg : ℝ} (hBg : ∀ y, |g y| ≤ Bg) {Lg : NNReal} (hLg : LipschitzWith Lg g)
    (u v : ℝ) : |logProfile g u - logProfile g v| ≤ (Lg : ℝ) * Real.exp (2 * A) * |u - v| := by
  have hBg0 : 0 ≤ Bg := (abs_nonneg _).trans (hBg 0)
  have hlip := lipschitzWith_horizonProfile hg hsupp hA hBg hLg (s := 1) (by norm_num)
    (by norm_num)
  have := hlip.dist_le_mul u v
  rw [Real.coe_toNNReal _ (by positivity), dist_eq_norm, Real.dist_eq, sub_self, norm_zero,
    zero_mul, add_zero, ← logProfile_eq_horizonProfile, ← logProfile_eq_horizonProfile,
    ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at this
  exact this

theorem abs_logProfile_le {Bg : ℝ} (hBg : ∀ y, |g y| ≤ Bg) (x : ℝ) : |logProfile g x| ≤ Bg := by
  have hBg0 : 0 ≤ Bg := (abs_nonneg _).trans (hBg 0)
  unfold logProfile
  split_ifs
  · exact hBg _
  · simpa using hBg0

/-! ### Riemann sums of the modulated weight -/

/-- `|N⁻¹ Σ_{r ≤ N} F(r/N) q(λr/N) − ∫_0^1 F(x) q(λx) dx| ≤ (L_F B_q + B_F λ L_q)/N`. -/
theorem abs_riemann_modulated_sub_le (hg : ContDiff ℝ 2 g)
    (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → g y = 0) (hA : 0 ≤ A) {Bg : ℝ} (hBg : ∀ y, |g y| ≤ Bg)
    {Lg : NNReal} (hLg : LipschitzWith Lg g) {lam : ℝ} (hlam : 0 ≤ lam) {N : ℕ} (hN : 1 ≤ N) :
    |(N : ℝ)⁻¹ * ∑ r ∈ Icc 1 N, logProfile g (r / N) * splineNumerator (lam * (r / N)) -
        ∫ x in (0 : ℝ)..1, logProfile g x * splineNumerator (lam * x)| ≤
      ((Lg : ℝ) * Real.exp (2 * A) * (Real.sinh 1 ^ 2 + 1) ^ 4 +
        Bg * (lam * (4 * (Real.sinh 1 ^ 2 + 1) ^ 3))) / N := by
  have hBg0 : 0 ≤ Bg := (abs_nonneg _).trans (hBg 0)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  set Bq := (Real.sinh 1 ^ 2 + 1) ^ 4 with hBq
  set Lq := 4 * (Real.sinh 1 ^ 2 + 1) ^ 3 with hLq
  set K := (Lg : ℝ) * Real.exp (2 * A) * Bq + Bg * (lam * Lq) with hK
  have hK0 : 0 ≤ K := by positivity
  set G : ℝ → ℝ := fun x => logProfile g x * splineNumerator (lam * x) with hG
  have hGlip : LipschitzOnWith (Real.toNNReal K) G (Set.Icc 0 1) := by
    refine LipschitzOnWith.of_dist_le_mul fun u _ v _ => ?_
    rw [Real.coe_toNNReal _ hK0, Real.dist_eq, Real.dist_eq]
    have e : G u - G v = (logProfile g u - logProfile g v) * splineNumerator (lam * u) +
        logProfile g v * (splineNumerator (lam * u) - splineNumerator (lam * v)) := by
      simp only [hG]; ring
    rw [e]
    have h1 := abs_logProfile_sub_le hg hsupp hA hBg hLg u v
    have h2 := abs_splineNumerator_sub_le (lam * u) (lam * v)
    rw [← mul_sub, abs_mul, abs_of_nonneg hlam] at h2
    have hq := splineNumerator_le (lam * u)
    have hq0 := splineNumerator_nonneg (lam * u)
    have hF := abs_logProfile_le hBg v
    calc |(logProfile g u - logProfile g v) * splineNumerator (lam * u) +
          logProfile g v * (splineNumerator (lam * u) - splineNumerator (lam * v))|
        ≤ |logProfile g u - logProfile g v| * Bq + Bg * (Lq * (lam * |u - v|)) := by
          refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
          · rw [abs_mul, abs_of_nonneg hq0]
            exact mul_le_mul_of_nonneg_left hq (abs_nonneg _)
          · rw [abs_mul]; exact mul_le_mul hF h2 (abs_nonneg _) hBg0
      _ ≤ ((Lg : ℝ) * Real.exp (2 * A) * |u - v|) * Bq + Bg * (Lq * (lam * |u - v|)) := by
          gcongr
      _ = K * |u - v| := by rw [hK]; ring
  have hGc : ContinuousOn G (Set.Icc 0 1) := hGlip.continuousOn
  have h := RHTower.abs_riemannSum_sub_integral_le hGlip hGc N (h := 1 / N) (by positivity)
    (by rw [mul_one_div, div_self hN0.ne'])
  rw [Real.coe_toNNReal _ hK0, mul_one_div, div_self hN0.ne'] at h
  have hsum : ∑ i ∈ Finset.range N, G ((i + 1) * (1 / N)) = ∑ r ∈ Icc 1 N, G (r / N) := by
    rw [show Icc 1 N = Finset.Ico 1 (N + 1) by ext; simp, Finset.sum_Ico_eq_sum_range,
      show N + 1 - 1 = N by omega]
    refine sum_congr rfl fun i _ => ?_
    congr 1; push_cast; ring
  rw [hsum] at h
  have e2 : K * N * (1 / N) ^ 2 = K / N := by field_simp
  rw [e2] at h
  rw [show (N : ℝ)⁻¹ = 1 / N by ring]
  exact h

/-! ### The modulated window average -/

/-- **Equidistribution of the numerator on the window**: for `λ_N → ∞`, `λ_N/N → 0`,
`N⁻¹ Σ_{r ≤ N} g(log(r/N)) q(λ_N r/N) → μ_q ∫ e^y g(y) dy`. -/
theorem tendsto_modulated (hg : ContDiff ℝ 2 g) (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → g y = 0)
    (hA : 0 ≤ A) {lam : ℕ → ℝ} (hlam : Tendsto lam atTop atTop)
    (hlamN : Tendsto (fun N : ℕ => lam N / N) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ∑ r ∈ Icc 1 N, logProfile g (r / N) *
      splineNumerator (lam N * (r / N))) atTop
      (𝓝 (splineNumeratorMean * ∫ y, Real.exp y * g y)) := by
  obtain ⟨Bg, L, hBg, hL⟩ := exists_bound_lipschitz hg hsupp
  obtain ⟨Lg, hLg⟩ := ContDiff.lipschitzWith_of_hasCompactSupport
    (hasCompactSupport_of_window hsupp) hg (by norm_num)
  have hBg0 : 0 ≤ Bg := (abs_nonneg _).trans (hBg 0)
  have hg0 : g 0 = 0 := horizon_zero_at_zero hsupp hL
  set Bq := (Real.sinh 1 ^ 2 + 1) ^ 4 with hBq
  set Lq := 4 * (Real.sinh 1 ^ 2 + 1) ^ 3 with hLq
  set V := ∫ x in (0 : ℝ)..2, |logProfileDeriv g x| with hV
  have hV0 : 0 ≤ V := intervalIntegral.integral_nonneg (by norm_num) fun _ _ => abs_nonneg _
  have hint := integral_logProfile hg hsupp hA
  -- the bound
  set b : ℕ → ℝ := fun N => ((Lg : ℝ) * Real.exp (2 * A) * Bq) * (N : ℝ)⁻¹ +
    Bg * Lq * (lam N / N) + Bq * Real.pi * V * (lam N)⁻¹ with hb
  have hblim : Tendsto b atTop (𝓝 0) := by
    have t1 := (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).const_mul
      ((Lg : ℝ) * Real.exp (2 * A) * Bq)
    have t2 := hlamN.const_mul (Bg * Lq)
    have t3 := (tendsto_inv_atTop_zero.comp hlam).const_mul (Bq * Real.pi * V)
    have := (t1.add t2).add t3
    simp only [mul_zero, add_zero] at this
    exact this.congr fun N => by simp only [hb, Function.comp_apply]
  refine tendsto_sub_nhds_zero_iff.mp (squeeze_zero_norm' ?_ hblim)
  filter_upwards [hlam.eventually (eventually_ge_atTop Real.pi), eventually_ge_atTop 1] with N h1 hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hlam0 : 0 < lam N := lt_of_lt_of_le Real.pi_pos h1
  have hR := abs_riemann_modulated_sub_le hg hsupp hA hBg hLg hlam0.le hN
  have hAv := abs_integral_mul_numerator_sub_le (hasDerivAt_logProfile hg hsupp)
    (continuous_logProfileDeriv hg hsupp) (fun x hx => logProfile_eq_zero_of_one_le hsupp hg0 hx) h1
  rw [hint] at hAv
  rw [Real.norm_eq_abs]
  calc _ ≤ |(N : ℝ)⁻¹ * ∑ r ∈ Icc 1 N, logProfile g (r / N) * splineNumerator (lam N * (r / N)) -
        ∫ x in (0 : ℝ)..1, logProfile g x * splineNumerator (lam N * x)| +
      |(∫ x in (0 : ℝ)..1, logProfile g x * splineNumerator (lam N * x)) -
        splineNumeratorMean * ∫ y, Real.exp y * g y| := abs_sub_le _ _ _
    _ ≤ ((Lg : ℝ) * Real.exp (2 * A) * Bq + Bg * (lam N * Lq)) / N + Bq * (Real.pi / lam N) * V :=
        add_le_add hR hAv
    _ = b N := by simp only [hb]; field_simp

/-! ### One harmonic -/

/-- The window weight of the aliasing, `h(y)² e^{−8y}`. -/
def aliasWeight (h : ℝ → ℝ) (y : ℝ) : ℝ := h y ^ 2 * Real.exp (-(8 * y))

theorem contDiff_aliasWeight (hh : ContDiff ℝ 2 h) : ContDiff ℝ 2 (aliasWeight h) :=
  (hh.pow 2).mul (Real.contDiff_exp.comp (contDiff_const.mul contDiff_id).neg)

theorem aliasWeight_eq_zero (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0) {y : ℝ}
    (hy : y ∉ Set.Icc (-A) 0) : aliasWeight h y = 0 := by
  rw [aliasWeight, hsupp y hy]; ring

theorem integral_exp_mul_aliasWeight (h : ℝ → ℝ) :
    ∫ y, Real.exp y * aliasWeight h y = ∫ y, Real.exp (-(7 * y)) * h y ^ 2 := by
  congr 1; funext y
  rw [aliasWeight, show Real.exp y * (h y ^ 2 * Real.exp (-(8 * y))) =
    (Real.exp y * Real.exp (-(8 * y))) * h y ^ 2 by ring, ← Real.exp_add]
  congr 2; ring

/-- One harmonic of the spectrum against the window: `c⁸ |φ̂(2π(k+1)cx)|²` is
`(1/64)(4/π)⁸ (k+1)^{−8} x^{−8} q(λx)` up to `O(c^{−2} x^{−10})`, `λ = π(k+1)c/4`. -/
theorem abs_harmonic_sub_le {c x : ℝ} (hc : 0 < c) (hx : 0 < x) (k : ℕ) {H2 : ℝ} (hH2 : 0 ≤ H2) :
    |H2 * (c ^ 8 * shellSpectrum tiltedUnitSpline ((k + 1) * (c * x))) -
        1 / 64 * (4 / Real.pi) ^ 8 * (((k : ℝ) + 1) ^ 8)⁻¹ *
          (H2 * (x ^ 8)⁻¹ * splineNumerator (Real.pi * (k + 1) * c / 4 * x))| ≤
      1 / 64 * (Real.sinh 1 ^ 2 + 1) ^ 4 * 4 * (4 / Real.pi) ^ 10 * H2 * (c ^ 2)⁻¹ * (x ^ 10)⁻¹ := by
  have hpi := Real.pi_pos
  have hk : (1 : ℝ) ≤ k + 1 := by have := (Nat.cast_nonneg k : (0 : ℝ) ≤ k); linarith
  set z := Real.pi * ((k + 1) * (c * x)) / 4 with hz
  have hz0 : 0 < z := by positivity
  have hzeq : Real.pi * (k + 1) * c / 4 * x = z := by rw [hz]; ring
  rw [shellSpectrum_tiltedUnitSpline, hzeq]
  set q := splineNumerator z with hq
  have hq0 : 0 ≤ q := splineNumerator_nonneg z
  have hqB : q ≤ (Real.sinh 1 ^ 2 + 1) ^ 4 := splineNumerator_le z
  have hw1 := splineWeight_le z hz0
  have hw2 := le_splineWeight z hz0
  have h8 : z ^ (-8 : ℝ) = (z ^ 8)⁻¹ := by
    rw [Real.rpow_neg hz0.le, show (8 : ℝ) = (8 : ℕ) by norm_num, Real.rpow_natCast]
  have h10 : z ^ (-10 : ℝ) = (z ^ 10)⁻¹ := by
    rw [Real.rpow_neg hz0.le, show (10 : ℝ) = (10 : ℕ) by norm_num, Real.rpow_natCast]
  rw [h8] at hw1 hw2
  rw [h10] at hw2
  have hid : c ^ 8 * (z ^ 8)⁻¹ = (4 / Real.pi) ^ 8 * (((k : ℝ) + 1) ^ 8)⁻¹ * (x ^ 8)⁻¹ := by
    rw [hz]; field_simp
  have hid10 : c ^ 8 * (z ^ 10)⁻¹ =
      (4 / Real.pi) ^ 10 * (((k : ℝ) + 1) ^ 10)⁻¹ * (c ^ 2)⁻¹ * (x ^ 10)⁻¹ := by
    rw [hz]; field_simp
  have hdiff : |splineWeight z - (z ^ 8)⁻¹| ≤ 4 * (z ^ 10)⁻¹ := by
    rw [abs_le]; constructor <;> linarith
  have e : H2 * (c ^ 8 * (1 / 64 * (q * splineWeight z))) -
      1 / 64 * (4 / Real.pi) ^ 8 * (((k : ℝ) + 1) ^ 8)⁻¹ * (H2 * (x ^ 8)⁻¹ * q) =
      1 / 64 * H2 * q * c ^ 8 * (splineWeight z - (z ^ 8)⁻¹) := by
    rw [mul_sub, show 1 / 64 * H2 * q * c ^ 8 * (z ^ 8)⁻¹ = 1 / 64 * H2 * q * (c ^ 8 * (z ^ 8)⁻¹) by
      ring, hid]
    ring
  rw [e, abs_mul, abs_of_nonneg (by positivity)]
  have hk10 : (((k : ℝ) + 1) ^ 10)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hk)
  calc 1 / 64 * H2 * q * c ^ 8 * |splineWeight z - (z ^ 8)⁻¹| ≤
        1 / 64 * H2 * (Real.sinh 1 ^ 2 + 1) ^ 4 * c ^ 8 * (4 * (z ^ 10)⁻¹) := by
        gcongr
    _ = 1 / 64 * (Real.sinh 1 ^ 2 + 1) ^ 4 * 4 * H2 * (c ^ 8 * (z ^ 10)⁻¹) := by ring
    _ = 1 / 64 * (Real.sinh 1 ^ 2 + 1) ^ 4 * 4 * H2 *
        ((4 / Real.pi) ^ 10 * (((k : ℝ) + 1) ^ 10)⁻¹ * (c ^ 2)⁻¹ * (x ^ 10)⁻¹) := by rw [hid10]
    _ ≤ 1 / 64 * (Real.sinh 1 ^ 2 + 1) ^ 4 * 4 * H2 *
        ((4 / Real.pi) ^ 10 * 1 * (c ^ 2)⁻¹ * (x ^ 10)⁻¹) := by gcongr
    _ = _ := by ring

/-- The harmonics are dominated: `c⁸ |φ̂(2π(k+1)cx)|² ≤ (1/64) B_q (4/π)⁸ (k+1)^{−8} x^{−8}`. -/
theorem harmonic_le {c x : ℝ} (hc : 0 < c) (hx : 0 < x) (k : ℕ) :
    c ^ 8 * shellSpectrum tiltedUnitSpline ((k + 1) * (c * x)) ≤
      1 / 64 * (Real.sinh 1 ^ 2 + 1) ^ 4 * (4 / Real.pi) ^ 8 * (((k : ℝ) + 1) ^ 8)⁻¹ * (x ^ 8)⁻¹ := by
  have hpi := Real.pi_pos
  set z := Real.pi * ((k + 1) * (c * x)) / 4 with hz
  have hz0 : 0 < z := by positivity
  rw [shellSpectrum_tiltedUnitSpline]
  have hw1 := splineWeight_le z hz0
  rw [Real.rpow_neg hz0.le, show (8 : ℝ) = (8 : ℕ) by norm_num, Real.rpow_natCast] at hw1
  have hid : c ^ 8 * (z ^ 8)⁻¹ = (4 / Real.pi) ^ 8 * (((k : ℝ) + 1) ^ 8)⁻¹ * (x ^ 8)⁻¹ := by
    rw [hz]; field_simp
  have hq := splineNumerator_le z
  have hq0 := splineNumerator_nonneg z
  have hw0 := splineWeight_nonneg z
  calc c ^ 8 * (1 / 64 * (splineNumerator z * splineWeight z)) ≤
        c ^ 8 * (1 / 64 * ((Real.sinh 1 ^ 2 + 1) ^ 4 * (z ^ 8)⁻¹)) := by gcongr
    _ = 1 / 64 * (Real.sinh 1 ^ 2 + 1) ^ 4 * (c ^ 8 * (z ^ 8)⁻¹) := by ring
    _ = _ := by rw [hid]; ring

/-- On the support of the window, `x = n/N ≥ e^{−A}`: `h(log x)² x^{−p} ≤ h(log x)² e^{pA}`. -/
theorem sq_mul_inv_pow_le (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0) {x : ℝ} (hx : 0 < x)
    (p : ℕ) : h (Real.log x) ^ 2 * (x ^ p)⁻¹ ≤ h (Real.log x) ^ 2 * Real.exp (p * A) := by
  by_cases hw : Real.log x ∈ Set.Icc (-A) 0
  · refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
    have hxA : Real.exp (-A) ≤ x := by rw [← Real.exp_log hx]; exact Real.exp_le_exp.mpr hw.1
    rw [show Real.exp (p * A) = (Real.exp (-A) ^ p)⁻¹ by
      rw [← Real.exp_nat_mul, ← Real.exp_neg]; ring_nf]
    exact inv_anti₀ (by positivity) (pow_le_pow_left₀ (Real.exp_pos _).le hxA p)
  · rw [hsupp _ hw]; simp

/-- **One harmonic**: `N⁻¹ Σ_n h(log(n/N))² c⁸ |φ̂(2π(k+1)cn/N)|² →
(1/64)(4/π)⁸ (k+1)^{−8} μ_q ∫ e^{−7y} h²`. -/
theorem tendsto_harmonic (hh : ContDiff ℝ 2 h) (hA : 0 ≤ A)
    (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0) {c : ℕ → ℝ} (hc1 : ∀ N, 1 ≤ c N)
    (hcinf : Tendsto c atTop atTop) (hcN : Tendsto (fun N : ℕ => c N / N) atTop (𝓝 0)) (k : ℕ) :
    Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ∑ n ∈ Icc 1 N, h (Real.log n - Real.log N) ^ 2 *
      (c N ^ 8 * shellSpectrum tiltedUnitSpline ((k + 1) * (c N * (n / N))))) atTop
      (𝓝 (1 / 64 * (4 / Real.pi) ^ 8 * (((k : ℝ) + 1) ^ 8)⁻¹ *
        (splineNumeratorMean * ∫ y, Real.exp (-(7 * y)) * h y ^ 2))) := by
  have hpi := Real.pi_pos
  obtain ⟨Bh, -, hB, -⟩ := exists_bound_lipschitz hh hsupp
  have hB0 : 0 ≤ Bh := (abs_nonneg _).trans (hB 0)
  set r : ℝ := Real.pi * (k + 1) / 4 with hr
  have hr0 : 0 < r := by positivity
  set lam : ℕ → ℝ := fun N => r * c N with hlam
  have hlamT : Tendsto lam atTop atTop := hcinf.const_mul_atTop hr0
  have hlamN : Tendsto (fun N : ℕ => lam N / N) atTop (𝓝 0) := by
    have := hcN.const_mul r
    rw [mul_zero] at this
    exact this.congr fun N => by simp only [hlam]; ring
  have hmod := tendsto_modulated (contDiff_aliasWeight hh) (fun y hy => aliasWeight_eq_zero hsupp hy)
    hA hlamT hlamN
  rw [integral_exp_mul_aliasWeight] at hmod
  have hmain := hmod.const_mul (1 / 64 * (4 / Real.pi) ^ 8 * (((k : ℝ) + 1) ^ 8)⁻¹)
  -- the comparison error is `O(c^{−2})`
  set D := 1 / 64 * (Real.sinh 1 ^ 2 + 1) ^ 4 * 4 * (4 / Real.pi) ^ 10 * Real.exp (10 * A) * Bh ^ 2
    with hD
  have hc2 : Tendsto (fun N : ℕ => D * (c N ^ 2)⁻¹) atTop (𝓝 0) := by
    have hc2' : Tendsto (fun N : ℕ => c N ^ 2) atTop atTop :=
      tendsto_atTop_mono (fun N => by nlinarith [hc1 N]) hcinf
    have := (tendsto_inv_atTop_zero.comp hc2').const_mul D
    rw [mul_zero] at this
    exact this
  set Cm := 1 / 64 * (4 / Real.pi) ^ 8 * (((k : ℝ) + 1) ^ 8)⁻¹ with hCm
  have hdiff : Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ∑ n ∈ Icc 1 N, h (Real.log n - Real.log N) ^ 2 *
      (c N ^ 8 * shellSpectrum tiltedUnitSpline ((k + 1) * (c N * (n / N)))) -
      Cm * ((N : ℝ)⁻¹ * ∑ r ∈ Icc 1 N, logProfile (aliasWeight h) (r / N) *
        splineNumerator (lam N * (r / N)))) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hc2
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    have hc0 : 0 < c N := by linarith [hc1 N]
    have hrw : (N : ℝ)⁻¹ * ∑ n ∈ Icc 1 N, h (Real.log n - Real.log N) ^ 2 *
        (c N ^ 8 * shellSpectrum tiltedUnitSpline ((k + 1) * (c N * (n / N)))) -
        Cm * ((N : ℝ)⁻¹ * ∑ r ∈ Icc 1 N, logProfile (aliasWeight h) (r / N) *
          splineNumerator (lam N * (r / N))) =
        (N : ℝ)⁻¹ * ∑ n ∈ Icc 1 N, (h (Real.log n - Real.log N) ^ 2 *
          (c N ^ 8 * shellSpectrum tiltedUnitSpline ((k + 1) * (c N * (n / N)))) -
          Cm * (logProfile (aliasWeight h) (n / N) * splineNumerator (lam N * (n / N)))) := by
      rw [mul_sum, mul_sum, mul_sum, mul_sum, ← sum_sub_distrib]
      refine sum_congr rfl fun n _ => by ring
    rw [hrw, Real.norm_eq_abs, abs_mul, abs_of_pos (inv_pos.mpr hN0)]
    have hterm : ∀ n ∈ Icc 1 N, |h (Real.log n - Real.log N) ^ 2 *
        (c N ^ 8 * shellSpectrum tiltedUnitSpline ((k + 1) * (c N * (n / N)))) -
        Cm * (logProfile (aliasWeight h) (n / N) * splineNumerator (lam N * (n / N)))| ≤
        D * (c N ^ 2)⁻¹ := by
      intro n hn
      have hn0 : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
      have hx : (0 : ℝ) < n / N := div_pos hn0 hN0
      have hlogx : Real.log (n / N) = Real.log n - Real.log N := Real.log_div hn0.ne' hN0.ne'
      have hlp : logProfile (aliasWeight h) (n / N) =
          h (Real.log n - Real.log N) ^ 2 * (((n : ℝ) / N) ^ 8)⁻¹ := by
        rw [logProfile, if_pos hx, aliasWeight, hlogx, ← hlogx, Real.exp_neg,
          show 8 * Real.log ((n : ℝ) / N) = (8 : ℕ) * Real.log ((n : ℝ) / N) by norm_num,
          Real.exp_nat_mul, Real.exp_log hx]
      have hlam' : lam N * (n / N) = Real.pi * (k + 1) * c N / 4 * (n / N) := by
        simp only [hlam, hr]; ring
      rw [hlp, hlam', hCm]
      refine (abs_harmonic_sub_le hc0 hx k (sq_nonneg _)).trans ?_
      have h10 := sq_mul_inv_pow_le hsupp hx 10
      rw [hlogx] at h10
      have hh2 : h (Real.log n - Real.log N) ^ 2 ≤ Bh ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hB _) 2
      calc 1 / 64 * (Real.sinh 1 ^ 2 + 1) ^ 4 * 4 * (4 / Real.pi) ^ 10 *
            h (Real.log n - Real.log N) ^ 2 * (c N ^ 2)⁻¹ * (((n : ℝ) / N) ^ 10)⁻¹ =
          1 / 64 * (Real.sinh 1 ^ 2 + 1) ^ 4 * 4 * (4 / Real.pi) ^ 10 * (c N ^ 2)⁻¹ *
            (h (Real.log n - Real.log N) ^ 2 * (((n : ℝ) / N) ^ 10)⁻¹) := by ring
        _ ≤ 1 / 64 * (Real.sinh 1 ^ 2 + 1) ^ 4 * 4 * (4 / Real.pi) ^ 10 * (c N ^ 2)⁻¹ *
            (Bh ^ 2 * Real.exp (10 * A)) := by
            refine mul_le_mul_of_nonneg_left (h10.trans ?_) (by positivity)
            push_cast
            exact mul_le_mul_of_nonneg_right hh2 (Real.exp_pos _).le
        _ = D * (c N ^ 2)⁻¹ := by rw [hD]; ring
    calc (N : ℝ)⁻¹ * |∑ n ∈ Icc 1 N, (h (Real.log n - Real.log N) ^ 2 *
          (c N ^ 8 * shellSpectrum tiltedUnitSpline ((k + 1) * (c N * (n / N)))) -
          Cm * (logProfile (aliasWeight h) (n / N) * splineNumerator (lam N * (n / N))))|
        ≤ (N : ℝ)⁻¹ * ∑ n ∈ Icc 1 N, D * (c N ^ 2)⁻¹ :=
          mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans
            (Finset.sum_le_sum hterm)) (by positivity)
      _ = D * (c N ^ 2)⁻¹ := by
          rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]; field_simp
  have := hdiff.add hmain
  rw [zero_add] at this
  refine this.congr fun N => ?_
  ring

/-! ### All harmonics -/

theorem hasAlias_tilted (a : ℝ) (ha : 0 < a) :
    HasSum (fun k : ℕ => shellSpectrum tiltedUnitSpline ((k + 1) * a)) (aliasDensity tiltedUnitSpline a) :=
  (hasSum_aliasDensity contDiff_tiltedUnitSpline tiltedUnitSpline_support ha).1

theorem rpow_eight_mul_horizonAlias_eq (h : ℝ → ℝ) {c : ℝ} (hc : 0 < c) {N : ℕ} (hN : 1 ≤ N) :
    c ^ 8 * horizonAlias tiltedUnitSpline h c N = 2 * ∑' k : ℕ, (N : ℝ)⁻¹ *
      ∑ n ∈ Icc 1 N, h (Real.log n - Real.log N) ^ 2 *
        (c ^ 8 * shellSpectrum tiltedUnitSpline ((k + 1) * (c * (n / N)))) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hsum : ∀ n ∈ Icc 1 N, Summable fun k : ℕ => h (Real.log n - Real.log N) ^ 2 *
      (c ^ 8 * shellSpectrum tiltedUnitSpline ((k + 1) * (c * (n / N)))) := by
    intro n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
    exact (((hasAlias_tilted (c * (n / N)) (by positivity)).summable).mul_left _).mul_left _
  have e1 : ∀ n ∈ Icc 1 N, ∑' k : ℕ, h (Real.log n - Real.log N) ^ 2 *
      (c ^ 8 * shellSpectrum tiltedUnitSpline ((k + 1) * (c * (n / N)))) =
      h (Real.log n - Real.log N) ^ 2 * (c ^ 8 * aliasDensity tiltedUnitSpline (c * n / N)) := by
    intro n _
    rw [tsum_mul_left, tsum_mul_left, aliasDensity, show c * n / N = c * (n / N) by ring]
  rw [tsum_mul_left, Summable.tsum_finsetSum hsum, sum_congr rfl e1, horizonAlias, mul_sum,
    mul_sum, mul_sum, mul_sum]
  exact sum_congr rfl fun n _ => by ring

/-- **The aliasing constant of the tilted spline**: along `c → ∞`, `c/N → 0`,
`c⁸ 𝒜_N → 2 Σ_k (1/64)(4/π)⁸ (k+1)^{−8} μ_q ∫ e^{−7y} h²`. -/
theorem tendsto_rpow_eight_mul_horizonAlias (hh : ContDiff ℝ 2 h) (hA : 0 ≤ A)
    (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0) {c : ℕ → ℝ} (hc1 : ∀ N, 1 ≤ c N)
    (hcinf : Tendsto c atTop atTop) (hcN : Tendsto (fun N : ℕ => c N / N) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => c N ^ 8 * horizonAlias tiltedUnitSpline h (c N) N) atTop
      (𝓝 (2 * ∑' k : ℕ, 1 / 64 * (4 / Real.pi) ^ 8 * (((k : ℝ) + 1) ^ 8)⁻¹ *
        (splineNumeratorMean * ∫ y, Real.exp (-(7 * y)) * h y ^ 2))) := by
  obtain ⟨Bh, -, hB, -⟩ := exists_bound_lipschitz hh hsupp
  have hB0 : 0 ≤ Bh := (abs_nonneg _).trans (hB 0)
  set E := Bh ^ 2 * Real.exp (8 * A) * (1 / 64 * (Real.sinh 1 ^ 2 + 1) ^ 4 * (4 / Real.pi) ^ 8)
    with hE
  have hE0 : 0 ≤ E := by positivity
  have hbound : Summable fun k : ℕ => E * (((k : ℝ) + 1) ^ 8)⁻¹ := by
    have h8 := (summable_nat_add_iff 1).mpr (Real.summable_nat_pow_inv.mpr (by norm_num : 1 < 8))
    exact (h8.congr fun k => by push_cast; rfl).mul_left E
  have hT := tendsto_tsum_of_dominated_convergence (𝓕 := atTop) hbound
    (tendsto_harmonic hh hA hsupp hc1 hcinf hcN) (by
      filter_upwards [eventually_ge_atTop 1] with N hN
      intro k
      have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
      have hc0 : 0 < c N := by linarith [hc1 N]
      have hterm : ∀ n ∈ Icc 1 N, 0 ≤ h (Real.log n - Real.log N) ^ 2 *
          (c N ^ 8 * shellSpectrum tiltedUnitSpline ((k + 1) * (c N * (n / N)))) := fun n _ => by
        have := RenormalizedArithmeticPotentialTheory.CompletedShell.shellSpectrum_nonneg (φ := tiltedUnitSpline) ((k + 1) * (c N * (n / N)))
        positivity
      have hle : ∀ n ∈ Icc 1 N, h (Real.log n - Real.log N) ^ 2 *
          (c N ^ 8 * shellSpectrum tiltedUnitSpline ((k + 1) * (c N * (n / N)))) ≤
          E * (((k : ℝ) + 1) ^ 8)⁻¹ := by
        intro n hn
        have hn0 : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
        have hx : (0 : ℝ) < n / N := div_pos hn0 hN0
        have hlogx : Real.log (n / N) = Real.log n - Real.log N := Real.log_div hn0.ne' hN0.ne'
        have h1 := harmonic_le hc0 hx k
        have h8 := sq_mul_inv_pow_le hsupp hx 8
        rw [hlogx] at h8
        have hh2 : h (Real.log n - Real.log N) ^ 2 ≤ Bh ^ 2 := by
          rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hB _) 2
        calc h (Real.log n - Real.log N) ^ 2 *
              (c N ^ 8 * shellSpectrum tiltedUnitSpline ((k + 1) * (c N * (n / N))))
            ≤ h (Real.log n - Real.log N) ^ 2 * (1 / 64 * (Real.sinh 1 ^ 2 + 1) ^ 4 *
              (4 / Real.pi) ^ 8 * (((k : ℝ) + 1) ^ 8)⁻¹ * (((n : ℝ) / N) ^ 8)⁻¹) :=
              mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
          _ = (h (Real.log n - Real.log N) ^ 2 * (((n : ℝ) / N) ^ 8)⁻¹) *
              (1 / 64 * (Real.sinh 1 ^ 2 + 1) ^ 4 * (4 / Real.pi) ^ 8 * (((k : ℝ) + 1) ^ 8)⁻¹) := by
              ring
          _ ≤ (Bh ^ 2 * Real.exp (8 * A)) *
              (1 / 64 * (Real.sinh 1 ^ 2 + 1) ^ 4 * (4 / Real.pi) ^ 8 * (((k : ℝ) + 1) ^ 8)⁻¹) := by
              refine mul_le_mul_of_nonneg_right (h8.trans ?_) (by positivity)
              push_cast
              exact mul_le_mul_of_nonneg_right hh2 (Real.exp_pos _).le
          _ = E * (((k : ℝ) + 1) ^ 8)⁻¹ := by rw [hE]; ring
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (inv_nonneg.mpr hN0.le)
        (Finset.sum_nonneg hterm))]
      calc (N : ℝ)⁻¹ * ∑ n ∈ Icc 1 N, h (Real.log n - Real.log N) ^ 2 *
            (c N ^ 8 * shellSpectrum tiltedUnitSpline ((k + 1) * (c N * (n / N))))
          ≤ (N : ℝ)⁻¹ * ∑ n ∈ Icc 1 N, E * (((k : ℝ) + 1) ^ 8)⁻¹ :=
            mul_le_mul_of_nonneg_left (Finset.sum_le_sum hle) (by positivity)
        _ = E * (((k : ℝ) + 1) ^ 8)⁻¹ := by
            rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]; field_simp)
  refine (hT.const_mul 2).congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  exact (rpow_eight_mul_horizonAlias_eq h (by linarith [hc1 N]) hN).symm

/-! ### The constant is the bulk Jordan coefficient -/

/-- The conductor-one Jordan coefficient of the tilted spline, `J(1) = (2/∫φ²) A_φ ζ(8)`. -/
def tiltedJordanOne : ℝ := 2 / (∫ u, tiltedUnitSpline u ^ 2) * tiltedTailConstant * zetaSum 8

/-- `J(1)` is the rescaled limit of the bulk energy: `c⁷ E₁(c) → J(1)`. -/
theorem tendsto_rpow_seven_mul_completedShellEnergy_tilted :
    Tendsto (fun c : ℝ => c ^ (7 : ℝ) * completedShellEnergy tiltedUnitSpline c) atTop
      (𝓝 tiltedJordanOne) := by
  have h := tendsto_rpow_seven_mul_completedConductorEnergy_tiltedUnitSpline 1
  have hJ : jordanTotient 8 1 = 1 := by simp [jordanTotient]
  rw [hJ, Nat.totient_one, Nat.cast_one, div_one, mul_one] at h
  refine h.congr fun c => ?_
  simp [completedConductorEnergy]

/-- **The aliasing constant is `β J(1) ∫φ²`, `β = 7`.** -/
theorem aliasLimit_eq (I : ℝ) :
    2 * ∑' k : ℕ, 1 / 64 * (4 / Real.pi) ^ 8 * (((k : ℝ) + 1) ^ 8)⁻¹ * (splineNumeratorMean * I) =
      7 * (∫ u, tiltedUnitSpline u ^ 2) * tiltedJordanOne * I := by
  have hM : (∫ u, tiltedUnitSpline u ^ 2) ≠ 0 := integral_tiltedUnitSpline_sq_pos.ne'
  have hz : ∑' k : ℕ, (((k : ℝ) + 1) ^ 8)⁻¹ = zetaSum 8 := by
    rw [zetaSum]
    congr 1; funext k
    rw [Real.rpow_neg (by positivity), show (8 : ℝ) = (8 : ℕ) by norm_num, Real.rpow_natCast]
  have h7 : (4 / Real.pi) ^ (7 : ℝ) = (4 / Real.pi) ^ 7 := by
    rw [show (7 : ℝ) = (7 : ℕ) by norm_num, Real.rpow_natCast]
  have e : ∑' k : ℕ, 1 / 64 * (4 / Real.pi) ^ 8 * (((k : ℝ) + 1) ^ 8)⁻¹ * (splineNumeratorMean * I) =
      1 / 64 * (4 / Real.pi) ^ 8 * (splineNumeratorMean * I) * ∑' k : ℕ, (((k : ℝ) + 1) ^ 8)⁻¹ := by
    rw [← tsum_mul_left]; congr 1; funext k; ring
  rw [e, hz, tiltedJordanOne, tiltedTailConstant, h7]
  have hpi := Real.pi_pos
  field_simp
  ring

/-! ### The second-order term at the critical curve -/

theorem integral_exp_mul_halfWeight_sq (h : ℝ → ℝ) :
    ∫ y, Real.exp (-(8 * y)) * halfWeight h y ^ 2 = ∫ y, Real.exp (-(7 * y)) * h y ^ 2 := by
  congr 1; funext y
  rw [halfWeight, mul_pow, ← Real.exp_nat_mul,
    show Real.exp (-(8 * y)) * (Real.exp ((2 : ℕ) * (y / 2)) * h y ^ 2) =
      (Real.exp (-(8 * y)) * Real.exp ((2 : ℕ) * (y / 2))) * h y ^ 2 by ring, ← Real.exp_add]
  congr 2; push_cast; ring

/-- Along the critical curve the schedule grows and stays far below the horizon. -/
theorem criticalCurve_facts {c : ℕ → ℝ} (hc1 : ∀ N, 1 ≤ c N) {K : ℝ} (hK : 0 < K)
    (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 K)) :
    Tendsto c atTop atTop ∧ Tendsto (fun N : ℕ => c N * Real.log N ^ 2 / N) atTop (𝓝 0) := by
  have hlogN := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hc8 : Tendsto (fun N : ℕ => c N ^ 8) atTop atTop := by
    have := Tendsto.pos_mul_atTop hK hcrit hlogN
    refine this.congr' ?_
    filter_upwards [hlogN.eventually (eventually_gt_atTop 0)] with N hN
    simp only [Function.comp_apply] at hN ⊢
    field_simp
  refine ⟨?_, ?_⟩
  · rw [tendsto_atTop]
    intro B
    filter_upwards [hc8.eventually (eventually_ge_atTop (max B 1 ^ 8))] with N hN
    have hc0 : 0 ≤ c N := by linarith [hc1 N]
    exact (le_max_left B 1).trans
      ((pow_le_pow_iff_left₀ (by positivity) hc0 (by norm_num : 8 ≠ 0)).mp hN)
  · have hev : ∀ᶠ N : ℕ in atTop, c N ^ 8 ≤ 2 * K * Real.log N := by
      filter_upwards [hcrit.eventually (gt_mem_nhds (by linarith : K < 2 * K)),
        hlogN.eventually (eventually_gt_atTop 0)] with N h1 h2
      simp only [Function.comp_apply] at h2
      rw [div_lt_iff₀ h2] at h1
      linarith
    have hlim := (tendsto_log_pow_div_natCast 3).const_mul (2 * K)
    rw [mul_zero] at hlim
    refine squeeze_zero' (Eventually.of_forall fun N => by
      have := hc1 N; have := Real.log_natCast_nonneg N; positivity) ?_ hlim
    filter_upwards [hev, eventually_ge_atTop 1] with N h1 hN
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    have hcc : c N ≤ c N ^ 8 := by
      have := hc1 N
      calc c N = c N ^ 1 := (pow_one _).symm
        _ ≤ c N ^ 8 := pow_le_pow_right₀ this (by norm_num)
    have hl0 := Real.log_natCast_nonneg N
    calc c N * Real.log N ^ 2 / N ≤ (2 * K * Real.log N) * Real.log N ^ 2 / N := by
          gcongr; exact hcc.trans h1
      _ = 2 * K * (Real.log N ^ 3 / N) := by ring

/-- **The second-order term at the critical curve (Conjecture HB, sharp form).** For the tilted
spline and a `C²` window profile `h` on `[−A, 0]`, along `c⁸/log N → K > 0`:
`c⁻¹ ⟨W x, x⟩ → κ Q(H) + (7 J(1)/K) ∫ e^{−8y} H(y)² dy`, `H = e^{y/2} h`, where
`J(1) = lim c⁷ E₁(c)` is the conductor-one Jordan coefficient of the bulk. -/
theorem horizon_layer_criticalCurve_exact (hh : ContDiff ℝ 2 h) (hA : 0 ≤ A)
    (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0) {c : ℕ → ℝ} (hc1 : ∀ N, 1 ≤ c N) {K : ℝ}
    (hK : 0 < K) (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 K)) :
    Tendsto (fun N : ℕ => (c N)⁻¹ * (weilQuad (ArithmeticElectrostatics.atomicTest N
        (horizonWeights h N) (atomDilate tiltedUnitSpline (c N / N))) /
          ∫ u, atomDilate tiltedUnitSpline (c N / N) u ^ 2)) atTop
      (𝓝 ((∫ u, tiltedUnitSpline u) ^ 2 / (∫ u, tiltedUnitSpline u ^ 2) * weilQuad (halfWeight h) +
        7 * tiltedJordanOne / K * ∫ y, Real.exp (-(8 * y)) * halfWeight h y ^ 2)) := by
  obtain ⟨hcinf, hclog⟩ := criticalCurve_facts hc1 hK hcrit
  have hcN := tendsto_div_of_log_sq hc1 hclog
  have hC : 0 ≤ tiltedDecayConst := by unfold tiltedDecayConst; positivity
  have hsharp := horizon_layer_sharp contDiff_tiltedUnitSpline tiltedUnitSpline_support
    integral_tiltedUnitSpline_sq_pos (p := 8) (by norm_num) hC tiltedUnitSpline_decay hh hA hsupp
    hc1 hcinf hclog
  set M := ∫ u, tiltedUnitSpline u ^ 2 with hM
  have hM0 : 0 < M := integral_tiltedUnitSpline_sq_pos
  set I := ∫ y, Real.exp (-(7 * y)) * h y ^ 2 with hI
  have halias := tendsto_rpow_eight_mul_horizonAlias hh hA hsupp hc1 hcinf hcN
  rw [aliasLimit_eq] at halias
  have hinv : Tendsto (fun N : ℕ => Real.log N / c N ^ 8) atTop (𝓝 K⁻¹) :=
    (hcrit.inv₀ hK.ne').congr fun N => by rw [inv_div]
  have hterm : Tendsto (fun N : ℕ => Real.log N / M * horizonAlias tiltedUnitSpline h (c N) N)
      atTop (𝓝 (K⁻¹ * (7 * M * tiltedJordanOne * I) / M)) := by
    refine ((hinv.mul halias).div_const M).congr' ?_
    filter_upwards with N
    have hcne : c N ≠ 0 := by linarith [hc1 N]
    have hc0 : c N ^ 8 ≠ 0 := pow_ne_zero 8 hcne
    field_simp
  have := (hsharp.add (tendsto_const_nhds (x := (∫ u, tiltedUnitSpline u) ^ 2 / M *
    weilQuad (halfWeight h)))).add hterm
  rw [zero_add] at this
  rw [integral_exp_mul_halfWeight_sq, ← hI]
  have hval : (∫ u, tiltedUnitSpline u) ^ 2 / M * weilQuad (halfWeight h) +
      K⁻¹ * (7 * M * tiltedJordanOne * I) / M =
      (∫ u, tiltedUnitSpline u) ^ 2 / M * weilQuad (halfWeight h) + 7 * tiltedJordanOne / K * I := by
    field_simp
  rw [hval] at this
  refine this.congr fun N => ?_
  ring

theorem tiltedJordanOne_pos : 0 < tiltedJordanOne := by
  have hz : 0 < zetaSum 8 := by
    rw [zetaSum]
    have hs := (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow.mpr (by norm_num : -(8 : ℝ) < -1))
    have hs' : Summable fun n : ℕ => ((n : ℝ) + 1) ^ (-(8 : ℝ)) := hs.congr fun n => by push_cast; rfl
    exact hs'.tsum_pos (fun n => by positivity) 0 (by norm_num)
  unfold tiltedJordanOne
  have := tiltedTailConstant_pos
  have := integral_tiltedUnitSpline_sq_pos
  positivity

/-- **The exact critical multiple of a window.** At the multiple `K` of the critical curve the
horizon block is eventually positive if `K κ (−Q(H)) < 7 J(1) ‖H‖²_{−8}` and eventually negative if
`K κ (−Q(H)) > 7 J(1) ‖H‖²_{−8}`, `‖H‖²_{−8} = ∫ e^{−8y} H²`. For `Q(H) < 0` the critical multiple
is `K*(H) = 7 J(1) ‖H‖²_{−8}/(κ |Q(H)|)`; for `Q(H) ≥ 0` every multiple is positive. -/
theorem criticalMultiple_exact (hh : ContDiff ℝ 2 h) (hA : 0 ≤ A)
    (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0) {c : ℕ → ℝ} (hc1 : ∀ N, 1 ≤ c N) {K : ℝ}
    (hK : 0 < K) (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 K)) :
    (K * ((∫ u, tiltedUnitSpline u) ^ 2 / (∫ u, tiltedUnitSpline u ^ 2) *
        -weilQuad (halfWeight h)) < 7 * tiltedJordanOne *
          ∫ y, Real.exp (-(8 * y)) * halfWeight h y ^ 2 →
      ∀ᶠ N : ℕ in atTop, 0 < (c N)⁻¹ * (weilQuad (ArithmeticElectrostatics.atomicTest N
        (horizonWeights h N) (atomDilate tiltedUnitSpline (c N / N))) /
          ∫ u, atomDilate tiltedUnitSpline (c N / N) u ^ 2)) ∧
    (7 * tiltedJordanOne * ∫ y, Real.exp (-(8 * y)) * halfWeight h y ^ 2 <
        K * ((∫ u, tiltedUnitSpline u) ^ 2 / (∫ u, tiltedUnitSpline u ^ 2) *
          -weilQuad (halfWeight h)) →
      ∀ᶠ N : ℕ in atTop, (c N)⁻¹ * (weilQuad (ArithmeticElectrostatics.atomicTest N
        (horizonWeights h N) (atomDilate tiltedUnitSpline (c N / N))) /
          ∫ u, atomDilate tiltedUnitSpline (c N / N) u ^ 2) < 0) := by
  have hlim := horizon_layer_criticalCurve_exact hh hA hsupp hc1 hK hcrit
  set κQ := (∫ u, tiltedUnitSpline u) ^ 2 / (∫ u, tiltedUnitSpline u ^ 2) * weilQuad (halfWeight h)
  set B := ∫ y, Real.exp (-(8 * y)) * halfWeight h y ^ 2
  refine ⟨fun hlt => ?_, fun hgt => ?_⟩
  · have hpos : 0 < κQ + 7 * tiltedJordanOne / K * B := by
      have : 7 * tiltedJordanOne / K * B = (7 * tiltedJordanOne * B) / K := by ring
      rw [this, ← sub_lt_iff_lt_add', zero_sub, lt_div_iff₀ hK]
      have e : -κQ * K = K * ((∫ u, tiltedUnitSpline u) ^ 2 / (∫ u, tiltedUnitSpline u ^ 2) *
          -weilQuad (halfWeight h)) := by simp only [κQ]; ring
      rw [e]; exact hlt
    exact hlim.eventually (lt_mem_nhds hpos)
  · have hneg : κQ + 7 * tiltedJordanOne / K * B < 0 := by
      have : 7 * tiltedJordanOne / K * B = (7 * tiltedJordanOne * B) / K := by ring
      rw [this, ← lt_sub_iff_add_lt', zero_sub, div_lt_iff₀ hK]
      have e : -κQ * K = K * ((∫ u, tiltedUnitSpline u) ^ 2 / (∫ u, tiltedUnitSpline u ^ 2) *
          -weilQuad (halfWeight h)) := by simp only [κQ]; ring
      rw [e]; exact hgt
    exact hlim.eventually (gt_mem_nhds hneg)

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
