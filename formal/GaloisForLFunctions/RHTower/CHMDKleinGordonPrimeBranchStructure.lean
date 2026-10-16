import GaloisForLFunctions.RHTower.CHMDKleinGordonInverseLightCone

/-!
# CHMD: the exact singularity of the Klein–Gordon causal wave at the primes

At a prime point `q = s₁ log n + s₂ i` (`Λ(n) ≠ 0`) the continued massless wave has a simple pole,
`F(w) = L/(w − q) + G(w)`, `L = s₂ (2i/π) Λ(n)/√n`, with `G` analytic along the whole segment `[0, q]`
(`exists_masslessBoundaryWave_polar_split`).  The Klein–Gordon causal wave is the light-cone
transmutation `Φ(z) = F(z) − z² ∫_0^1 B(2z²(1−t²)) F(zt) dt`.  Splitting the Bessel kernel at the
point `zt = q`,

`B(2z²(1−t²)) = B(2(z² − q²)) − 2(zt − q)(zt + q) Q(2z²(1−t²), 2(z² − q²))`

with the entire divided difference `Q(x, y) = (B(x) − B(y))/(x − y)` (`lightConeBessel_sub_eq_mul_quot`),
and using `∫_0^1 z dt/(zt − q) = Log(1 − z/q)` (`integral_div_mul_sub_eq_log_one_sub`), gives the exact
local form (`kgBoundaryWave_prime_branch`):

`Φ(z) = L/(z − q) − L z B(2(z² − q²)) Log(1 − z/q) + H(z)`,   `H` holomorphic on a disc around `q`,

valid on the disc cut along the ray `{sq : s ≥ 1}`.  So each prime point is a simple pole with the
Cramér residue `L` together with a logarithmic branch point, whose cut runs outward along the ray through
`q` and whose coefficient is the light-cone Bessel function on the complex light cone through `q`.
The two boundary values of `Φ` across the cut differ by `2πi L z B(2(z² − q²))`
(`tendsto_kgBoundaryWave_jump`), which is nonzero near `q`.
-/

open Complex MeasureTheory Set Filter Topology Metric Zeta23
open scoped Real ComplexConjugate Nat
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower.CHMDLightCone

open RHTower.CHMDGrowthCollapse

/-! ## The divided difference of the Bessel kernel -/

/-- The Taylor coefficients `c_k = (−1/4)^k/(k!(k+1)!)` of `B(x) = Σ c_k x^k`. -/
def lightConeBesselCoeff (k : ℕ) : ℂ := (-1 / 4 : ℂ) ^ k / ((k ! : ℂ) * ((k + 1)! : ℂ))

theorem lightConeBesselTerm_eq_coeff_mul (x : ℂ) (k : ℕ) :
    lightConeBesselTerm x k = lightConeBesselCoeff k * x ^ k := by
  unfold lightConeBesselTerm lightConeBesselCoeff
  rw [show -x / 4 = (-1 / 4 : ℂ) * x by ring, mul_pow]
  ring

theorem norm_lightConeBesselCoeff_le (k : ℕ) : ‖lightConeBesselCoeff k‖ ≤ (1 / 4) ^ k / k ! := by
  have hk : (0 : ℝ) < k ! := by exact_mod_cast Nat.factorial_pos k
  have hk1 : (1 : ℝ) ≤ (k + 1)! := by exact_mod_cast Nat.succ_le_of_lt (Nat.factorial_pos (k + 1))
  unfold lightConeBesselCoeff
  rw [norm_div, norm_pow, norm_mul, Complex.norm_natCast, Complex.norm_natCast,
    show ‖(-1 / 4 : ℂ)‖ = 1 / 4 by norm_num]
  exact div_le_div_of_nonneg_left (by positivity) hk (le_mul_of_one_le_right hk.le hk1)

/-- The divided difference `Q(x, y) = Σ_k c_k Σ_{i<k} x^i y^{k−1−i}` of the Bessel kernel. -/
def lightConeBesselQuot (x y : ℂ) : ℂ :=
  ∑' k : ℕ, lightConeBesselCoeff k * ∑ i ∈ Finset.range k, x ^ i * y ^ (k - 1 - i)

theorem norm_lightConeBesselQuotTerm_le {x y : ℂ} {M : ℝ} (hM : 0 ≤ M) (hx : ‖x‖ ≤ M)
    (hy : ‖y‖ ≤ M) (k : ℕ) :
    ‖lightConeBesselCoeff k * ∑ i ∈ Finset.range k, x ^ i * y ^ (k - 1 - i)‖ ≤
      ((M + 1) / 2) ^ k / k ! := by
  have hterm : ∀ i ∈ Finset.range k, ‖x ^ i * y ^ (k - 1 - i)‖ ≤ (M + 1) ^ k := by
    intro i hi
    have hi' : i + (k - 1 - i) ≤ k := by have := Finset.mem_range.mp hi; omega
    rw [norm_mul, norm_pow, norm_pow]
    calc ‖x‖ ^ i * ‖y‖ ^ (k - 1 - i) ≤ (M + 1) ^ i * (M + 1) ^ (k - 1 - i) := by
          gcongr <;> linarith
      _ = (M + 1) ^ (i + (k - 1 - i)) := by rw [pow_add]
      _ ≤ (M + 1) ^ k := pow_le_pow_right₀ (by linarith) hi'
  have hsum : ‖∑ i ∈ Finset.range k, x ^ i * y ^ (k - 1 - i)‖ ≤ 2 ^ k * (M + 1) ^ k := by
    refine (norm_sum_le _ _).trans ((Finset.sum_le_sum hterm).trans ?_)
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    gcongr
    exact_mod_cast Nat.lt_two_pow_self.le
  rw [norm_mul]
  calc ‖lightConeBesselCoeff k‖ * ‖∑ i ∈ Finset.range k, x ^ i * y ^ (k - 1 - i)‖
      ≤ (1 / 4) ^ k / k ! * (2 ^ k * (M + 1) ^ k) :=
        mul_le_mul (norm_lightConeBesselCoeff_le k) hsum (norm_nonneg _) (by positivity)
    _ = ((M + 1) / 2) ^ k / k ! := by
        rw [div_mul_eq_mul_div, ← mul_assoc, ← mul_pow, ← mul_pow, div_pow]
        congr 1
        rw [show (1 / 4 : ℝ) * 2 * (M + 1) = (M + 1) / 2 by ring, div_pow]

theorem norm_lightConeBesselQuot_le {x y : ℂ} {M : ℝ} (hM : 0 ≤ M) (hx : ‖x‖ ≤ M)
    (hy : ‖y‖ ≤ M) :
    ‖lightConeBesselQuot x y‖ ≤ ∑' k : ℕ, ((M + 1) / 2) ^ k / k ! :=
  tsum_of_norm_bounded (Real.summable_pow_div_factorial _).hasSum
    (norm_lightConeBesselQuotTerm_le hM hx hy)

/-- **The divided-difference identity** `B(x) − B(y) = (x − y) Q(x, y)`. -/
theorem lightConeBessel_sub_eq_mul_quot (x y : ℂ) :
    lightConeBessel x - lightConeBessel y = (x - y) * lightConeBesselQuot x y := by
  unfold lightConeBessel lightConeBesselQuot
  rw [← (hasSum_lightConeBessel x).summable.tsum_sub (hasSum_lightConeBessel y).summable,
    ← tsum_mul_left]
  refine tsum_congr fun k => ?_
  rw [lightConeBesselTerm_eq_coeff_mul, lightConeBesselTerm_eq_coeff_mul, ← mul_sub, ← geom_sum₂_mul]
  ring

theorem differentiableOn_lightConeBesselQuot_comp {X Y : ℂ → ℂ} (hX : Differentiable ℂ X)
    (hY : Differentiable ℂ Y) {U : Set ℂ} (hU : IsOpen U) {M : ℝ} (hM : 0 ≤ M)
    (hXM : ∀ z ∈ U, ‖X z‖ ≤ M) (hYM : ∀ z ∈ U, ‖Y z‖ ≤ M) :
    DifferentiableOn ℂ (fun z => lightConeBesselQuot (X z) (Y z)) U :=
  differentiableOn_tsum_of_summable_norm (Real.summable_pow_div_factorial ((M + 1) / 2))
    (fun k => ((Differentiable.fun_sum fun i _ => (hX.pow i).mul (hY.pow (k - 1 - i))).const_mul
      _).differentiableOn) hU
    (fun k z hz => norm_lightConeBesselQuotTerm_le hM (hXM z hz) (hYM z hz) k)

theorem continuousOn_lightConeBesselQuot_comp {α : Type*} [TopologicalSpace α] {X Y : α → ℂ}
    {s : Set α} (hX : ContinuousOn X s) (hY : ContinuousOn Y s) {M : ℝ} (hM : 0 ≤ M)
    (hXM : ∀ a ∈ s, ‖X a‖ ≤ M) (hYM : ∀ a ∈ s, ‖Y a‖ ≤ M) :
    ContinuousOn (fun a => lightConeBesselQuot (X a) (Y a)) s :=
  continuousOn_tsum (fun k => continuousOn_const.mul
      (continuousOn_finsetSum _ fun i _ => (hX.pow i).mul (hY.pow (k - 1 - i))))
    (Real.summable_pow_div_factorial ((M + 1) / 2))
    (fun k a ha => norm_lightConeBesselQuotTerm_le hM (hXM a ha) (hYM a ha) k)

/-! ## The logarithm along the light-cone segment -/

theorem one_sub_mul_div_mem_slitPlane {z q : ℂ} (hz : 1 - z / q ∈ slitPlane) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) : 1 - z * t / q ∈ slitPlane := by
  have h := starConvex_one_slitPlane hz (sub_nonneg.mpr ht.2) ht.1 (by ring : (1 - t) + t = 1)
  have e : (1 - t) • (1 : ℂ) + t • (1 - z / q) = 1 - z * t / q := by
    rw [Complex.real_smul, Complex.real_smul]; push_cast; ring
  rwa [e] at h

theorem mul_ofReal_sub_ne_zero {z q : ℂ} (hq : q ≠ 0) (hz : 1 - z / q ∈ slitPlane) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) : z * t - q ≠ 0 := by
  intro h
  have hm := slitPlane_ne_zero (one_sub_mul_div_mem_slitPlane hz ht)
  exact hm (by rw [show 1 - z * t / q = -(z * t - q) / q by rw [neg_sub, sub_div, div_self hq], h,
    neg_zero, zero_div])

/-- `∫_0^1 z dt/(zt − q) = Log(1 − z/q)` when `1 − z/q` lies off the cut. -/
theorem integral_div_mul_sub_eq_log_one_sub {z q : ℂ} (hq : q ≠ 0) (hz : 1 - z / q ∈ slitPlane) :
    ∫ t in (0 : ℝ)..1, z / (z * t - q) = Complex.log (1 - z / q) := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun t : ℝ => Complex.log (1 - z * t / q))]
  · simp
  · intro t ht
    rw [uIcc_of_le zero_le_one] at ht
    have h1 : HasDerivAt (fun t : ℝ => 1 - z * (t : ℂ) / q) (-(z / q)) t := by
      simpa using (((hasDerivAt_id t).ofReal_comp.const_mul z).div_const q).const_sub 1
    have h2 := h1.clog_real (one_sub_mul_div_mem_slitPlane hz ht)
    refine h2.congr_deriv ?_
    have h3 := mul_ofReal_sub_ne_zero hq hz ht
    have h4 := slitPlane_ne_zero (one_sub_mul_div_mem_slitPlane hz ht)
    rw [div_eq_div_iff h4 h3]
    field_simp
    ring
  · refine ContinuousOn.intervalIntegrable fun t ht => ?_
    rw [uIcc_of_le zero_le_one] at ht
    exact (continuousAt_const.div ((continuous_const.mul continuous_ofReal).sub
      continuous_const).continuousAt (mul_ofReal_sub_ne_zero hq hz ht)).continuousWithinAt

/-! ## The singular part of the transmutation tail -/

theorem continuousOn_lightConeBesselQuot_segment (z q : ℂ) :
    ContinuousOn (fun t : ℝ => lightConeBesselQuot (2 * z ^ 2 * (1 - (t : ℂ) ^ 2))
      (2 * (z ^ 2 - q ^ 2))) (Icc 0 1) := by
  refine continuousOn_lightConeBesselQuot_comp (M := 2 * ‖z‖ ^ 2 + 2 * ‖q‖ ^ 2)
    (by fun_prop) continuousOn_const (by positivity) (fun t ht => ?_) (fun t _ => ?_)
  · have h1 : ‖(1 : ℂ) - (t : ℂ) ^ 2‖ ≤ 1 := by
      rw [show (1 : ℂ) - (t : ℂ) ^ 2 = ((1 - t ^ 2 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
        Real.norm_eq_abs, abs_le]
      constructor <;> nlinarith [ht.1, ht.2]
    rw [norm_mul, norm_mul, norm_pow, show ‖(2 : ℂ)‖ = 2 by norm_num]
    nlinarith [norm_nonneg z, norm_nonneg q, sq_nonneg ‖z‖, sq_nonneg ‖q‖,
      mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 2 * ‖z‖ ^ 2)]
  · rw [norm_mul, show ‖(2 : ℂ)‖ = 2 by norm_num]
    have := norm_sub_le (z ^ 2) (q ^ 2)
    rw [norm_pow, norm_pow] at this
    linarith

/-- **The singular part of the tail.**  For `1 − z/q` off the cut,
`z ∫_0^1 B(2z²(1−t²))/(zt − q) dt = B(2(z² − q²)) Log(1 − z/q) − 2z ∫_0^1 (zt + q) Q dt`. -/
theorem mul_integral_lightConeBessel_div_eq {z q : ℂ} (hq : q ≠ 0) (hz : 1 - z / q ∈ slitPlane) :
    z * ∫ t in (0 : ℝ)..1, lightConeBessel (2 * z ^ 2 * (1 - (t : ℂ) ^ 2)) / (z * t - q) =
      lightConeBessel (2 * (z ^ 2 - q ^ 2)) * Complex.log (1 - z / q) -
        2 * z * ∫ t in (0 : ℝ)..1, (z * t + q) *
          lightConeBesselQuot (2 * z ^ 2 * (1 - (t : ℂ) ^ 2)) (2 * (z ^ 2 - q ^ 2)) := by
  have hpt : ∀ t ∈ uIcc (0 : ℝ) 1,
      lightConeBessel (2 * z ^ 2 * (1 - (t : ℂ) ^ 2)) / (z * t - q) =
        lightConeBessel (2 * (z ^ 2 - q ^ 2)) * (1 / (z * t - q)) -
          2 * ((z * t + q) *
            lightConeBesselQuot (2 * z ^ 2 * (1 - (t : ℂ) ^ 2)) (2 * (z ^ 2 - q ^ 2))) := by
    intro t ht
    rw [uIcc_of_le zero_le_one] at ht
    have hne := mul_ofReal_sub_ne_zero hq hz ht
    have h := lightConeBessel_sub_eq_mul_quot (2 * z ^ 2 * (1 - (t : ℂ) ^ 2)) (2 * (z ^ 2 - q ^ 2))
    rw [show 2 * z ^ 2 * (1 - (t : ℂ) ^ 2) - 2 * (z ^ 2 - q ^ 2) =
      -2 * (z * t - q) * (z * t + q) by ring] at h
    field_simp
    linear_combination h
  have hc1 : ContinuousOn (fun t : ℝ => 1 / (z * t - q)) (Icc 0 1) := fun t ht =>
    (continuousAt_const.div ((continuous_const.mul continuous_ofReal).sub
      continuous_const).continuousAt (mul_ofReal_sub_ne_zero hq hz ht)).continuousWithinAt
  have hc2 : ContinuousOn (fun t : ℝ => (z * t + q) *
      lightConeBesselQuot (2 * z ^ 2 * (1 - (t : ℂ) ^ 2)) (2 * (z ^ 2 - q ^ 2))) (Icc 0 1) :=
    (by fun_prop : Continuous fun t : ℝ => z * (t : ℂ) + q).continuousOn.mul
      (continuousOn_lightConeBesselQuot_segment z q)
  have hII : ∀ f : ℝ → ℂ, ContinuousOn f (Icc 0 1) → IntervalIntegrable f volume 0 1 :=
    fun f hf => ContinuousOn.intervalIntegrable (by rwa [uIcc_of_le zero_le_one])
  have hlog := integral_div_mul_sub_eq_log_one_sub hq hz
  rw [show (∫ t in (0 : ℝ)..1, z / (z * t - q)) = z * ∫ t in (0 : ℝ)..1, 1 / (z * t - q) by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr fun t _ => by ring] at hlog
  rw [intervalIntegral.integral_congr hpt, intervalIntegral.integral_sub
    ((hII _ hc1).const_mul _) ((hII _ hc2).const_mul _), intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, ← hlog]
  ring

/-! ## Holomorphy of the regular pieces -/

/-- The divided-difference integral `∫_0^1 (zt + q) Q(2z²(1−t²), 2(z² − q²)) dt`. -/
def lightConeQuotIntegral (q z : ℂ) : ℂ :=
  ∫ t in (0 : ℝ)..1, (z * t + q) *
    lightConeBesselQuot (2 * z ^ 2 * (1 - (t : ℂ) ^ 2)) (2 * (z ^ 2 - q ^ 2))

/-- The transmutation tail `∫_0^1 B(2z²(1−t²)) A(zt) dt`. -/
def lightConeTailIntegral (A : ℂ → ℂ) (z : ℂ) : ℂ :=
  ∫ t in (0 : ℝ)..1, lightConeBessel (2 * z ^ 2 * (1 - (t : ℂ) ^ 2)) * A (z * t)

/-- The divided-difference integral is entire in `z`. -/
theorem differentiable_lightConeQuotIntegral (q : ℂ) : Differentiable ℂ (lightConeQuotIntegral q) := by
  intro z₁
  set ρ := ‖z₁‖ + 1 with hρ
  set M := 2 * ρ ^ 2 + 2 * ‖q‖ ^ 2 with hM
  have hM0 : 0 ≤ M := by positivity
  set c : ℝ → ℝ := fun x => max 0 (min x 1) with hc
  have hc0 : ∀ x, 0 ≤ c x := fun x => le_max_left _ _
  have hc1 : ∀ x, c x ≤ 1 := fun x => max_le zero_le_one (min_le_right _ _)
  have hcc : Continuous c := continuous_const.max (continuous_id.min continuous_const)
  have hcn : ∀ x, ‖(1 : ℂ) - ((c x : ℝ) : ℂ) ^ 2‖ ≤ 1 := by
    intro x
    rw [show (1 : ℂ) - ((c x : ℝ) : ℂ) ^ 2 = ((1 - c x ^ 2 : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> nlinarith [hc0 x, hc1 x]
  have hball : ∀ z ∈ ball z₁ 1, ‖z‖ ≤ ρ := fun z hz => by
    have := norm_sub_norm_le z z₁
    rw [mem_ball, dist_eq_norm] at hz
    linarith
  have hX : ∀ x, ∀ z : ℂ, ‖z‖ ≤ ρ → ‖2 * z ^ 2 * (1 - ((c x : ℝ) : ℂ) ^ 2)‖ ≤ M := by
    intro x z hz
    rw [norm_mul, norm_mul, norm_pow, show ‖(2 : ℂ)‖ = 2 by norm_num]
    have h1 := mul_le_mul_of_nonneg_left (hcn x) (by positivity : (0 : ℝ) ≤ 2 * ‖z‖ ^ 2)
    have h2 : ‖z‖ ^ 2 ≤ ρ ^ 2 := by gcongr
    nlinarith [sq_nonneg ‖q‖]
  have hY : ∀ z : ℂ, ‖z‖ ≤ ρ → ‖2 * (z ^ 2 - q ^ 2)‖ ≤ M := by
    intro z hz
    rw [norm_mul, show ‖(2 : ℂ)‖ = 2 by norm_num]
    have := norm_sub_le (z ^ 2) (q ^ 2)
    rw [norm_pow, norm_pow] at this
    have h2 : ‖z‖ ^ 2 ≤ ρ ^ 2 := by gcongr
    linarith
  set K := ∑' k : ℕ, ((M + 1) / 2) ^ k / k ! with hK
  have hK0 : 0 ≤ K := tsum_nonneg fun k => by positivity
  set F : ℂ → ℝ → ℂ := fun z x => (z * ((c x : ℝ) : ℂ) + q) *
    lightConeBesselQuot (2 * z ^ 2 * (1 - ((c x : ℝ) : ℂ) ^ 2)) (2 * (z ^ 2 - q ^ 2)) with hF
  have hbound : ∀ x, ∀ z ∈ ball z₁ 1, ‖F z x‖ ≤ (ρ + ‖q‖) * K := by
    intro x z hz
    simp only [hF]
    rw [norm_mul]
    refine mul_le_mul ?_ (norm_lightConeBesselQuot_le hM0 (hX x z (hball z hz))
      (hY z (hball z hz))) (norm_nonneg _) (by positivity)
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hc0 x)]
    have := mul_le_mul (hball z hz) (hc1 x) (hc0 x) (by positivity)
    linarith
  have hdiff : ∀ x, DifferentiableOn ℂ (fun z => F z x) (ball z₁ 1) := by
    intro x
    have hQ := differentiableOn_lightConeBesselQuot_comp
      (X := fun z => 2 * z ^ 2 * (1 - ((c x : ℝ) : ℂ) ^ 2)) (Y := fun z => 2 * (z ^ 2 - q ^ 2))
      (by fun_prop) (by fun_prop) isOpen_ball hM0 (fun z hz => hX x z (hball z hz))
      (fun z hz => hY z (hball z hz))
    exact ((by fun_prop : Differentiable ℂ fun z : ℂ => z * ((c x : ℝ) : ℂ) + q).differentiableOn).mul hQ
  have hmeas : ∀ z ∈ ball z₁ 1, AEStronglyMeasurable (F z) (volume.restrict (Ioc 0 1)) := by
    intro z hz
    have hXc : Continuous fun x : ℝ => 2 * z ^ 2 * (1 - ((c x : ℝ) : ℂ) ^ 2) :=
      continuous_const.mul (continuous_const.sub ((continuous_ofReal.comp hcc).pow 2))
    have hQ : Continuous fun x : ℝ => lightConeBesselQuot (2 * z ^ 2 * (1 - ((c x : ℝ) : ℂ) ^ 2))
        (2 * (z ^ 2 - q ^ 2)) :=
      continuousOn_univ.mp (continuousOn_lightConeBesselQuot_comp hXc.continuousOn
        continuousOn_const hM0 (fun x _ => hX x z (hball z hz)) (fun _ _ => hY z (hball z hz)))
    exact (((continuous_const.mul (continuous_ofReal.comp hcc)).add continuous_const).mul
      hQ).aestronglyMeasurable
  have hD := differentiableAt_integral_of_cauchy_dominated (μ := volume.restrict (Ioc 0 1))
    one_pos hmeas hdiff hbound (integrableOn_const (by simp))
  refine hD.congr_of_eventuallyEq (Eventually.of_forall fun z => ?_)
  simp only [lightConeQuotIntegral]
  rw [intervalIntegral.integral_of_le zero_le_one]
  refine setIntegral_congr_fun measurableSet_Ioc fun x hx => ?_
  have : c x = x := by simp only [hc]; rw [min_eq_left hx.2, max_eq_right hx.1.le]
  simp only [hF, this]

/-! ## The massless wave at a prime point -/

/-- The residue of the continued massless wave at `q = s₁ log n + s₂ i` is `s₂ (2i/π) Λ(n)/√n`. -/
theorem tendsto_masslessBoundaryWave_residue_of_abs {n : ℕ} (hw : chmdPrimeWeight n ≠ 0) {q : ℂ}
    (hre : |q.re| = Real.log n) (him : |q.im| = 1) :
    Tendsto (fun v => (v - q) * masslessBoundaryWave v) (𝓝[≠] q)
      (𝓝 ((q.im : ℂ) * (2 * I / π * chmdPrimeWeight n))) := by
  obtain ⟨h1, h2, h3, h4⟩ := tendsto_masslessBoundaryWave_residue hw
  rcases prime_point_cases (log_nonneg_of_weight hw) hre him with
    ⟨hv, hi⟩ | ⟨hv, hi⟩ | ⟨hv, hi⟩ | ⟨hv, hi⟩ <;> rw [hi, hv]
  · rw [ofReal_one, one_mul]; exact h1
  · rw [ofReal_neg, ofReal_one, neg_one_mul]; exact h2
  · rw [ofReal_one, one_mul]; exact h3
  · rw [ofReal_neg, ofReal_one, neg_one_mul]; exact h4

/-- **Polar split at a prime point**: `F(w) = L/(w − q) + G(w)` with `G` analytic along `[0, q]`. -/
theorem exists_masslessBoundaryWave_polar_split {n : ℕ} (hw : chmdPrimeWeight n ≠ 0) {q : ℂ}
    (hre : |q.re| = Real.log n) (him : |q.im| = 1) :
    ∃ G : ℂ → ℂ, (∀ w, w ≠ q → masslessBoundaryWave w =
        (q.im : ℂ) * (2 * I / π * chmdPrimeWeight n) / (w - q) + G w) ∧
      ∀ t ∈ Icc (0 : ℝ) 1, AnalyticAt ℂ G (q * t) := by
  classical
  set L : ℂ := (q.im : ℂ) * (2 * I / π * chmdPrimeWeight n) with hL
  obtain ⟨hM, hord⟩ := masslessBoundaryWave_simple_pole hw hre him
  obtain ⟨g, hg, -, hgeq⟩ := (meromorphicOrderAt_eq_int_iff hM).mp hord
  have hres := tendsto_masslessBoundaryWave_residue_of_abs hw hre him
  have hgq : g q = L := by
    refine tendsto_nhds_unique ((hg.continuousAt.tendsto).mono_left nhdsWithin_le_nhds)
      (hres.congr' ?_)
    filter_upwards [hgeq, self_mem_nhdsWithin] with w hw' hwq
    rw [hw', zpow_neg_one, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ (sub_ne_zero.mpr hwq),
      one_mul]
  set G : ℂ → ℂ := Function.update (fun w => masslessBoundaryWave w - L / (w - q)) q
    (deriv g q) with hG
  have hq0 : q ≠ 0 := fun h => by rw [h, Complex.zero_im, abs_zero] at him; norm_num at him
  refine ⟨G, fun w hwq => ?_, fun t ht => ?_⟩
  · simp only [hG, Function.update_of_ne hwq]; ring
  rcases ht.2.lt_or_eq with htlt | rfl
  · have hstrip : |(q * t).im| < 1 := by
      rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add, abs_mul, him,
        one_mul, abs_of_nonneg ht.1]
      exact htlt
    have hne : q * t ≠ q := fun h => by
      have h1 : (t : ℂ) = 1 := mul_left_cancel₀ hq0 (h.trans (mul_one q).symm)
      exact htlt.ne (by exact_mod_cast h1)
    have hdiv : AnalyticAt ℂ (fun w => L / (w - q)) (q * t) :=
      analyticAt_const.div (analyticAt_id.sub analyticAt_const) (sub_ne_zero.mpr hne)
    have hsub : AnalyticAt ℂ (fun w => masslessBoundaryWave w - L / (w - q)) (q * t) :=
      (analyticAt_masslessBoundaryWave (Or.inl hstrip)).sub hdiv
    refine hsub.congr ?_
    filter_upwards [isOpen_ne.mem_nhds hne] with w hw'
    simp only [hG, Function.update_of_ne hw']
  · rw [ofReal_one, mul_one]
    obtain ⟨p, hp⟩ := hg
    have hds : AnalyticAt ℂ (dslope g q) q := ⟨_, hp.has_fpower_series_dslope_fslope⟩
    refine hds.congr ?_
    filter_upwards [eventually_nhdsWithin_iff.mp hgeq] with w hw'
    by_cases hwq : w = q
    · rw [hwq, dslope_same]
      simp only [hG, Function.update_self]
    · rw [dslope_of_ne _ hwq, slope_def_field, hG, Function.update_of_ne hwq, hw' hwq, zpow_neg_one,
        smul_eq_mul, hgq, sub_div, inv_mul_eq_div]

/-! ## The exact singularity of the causal wave -/

/-- **The exact singularity of the causal wave at a prime point.**  At `q = s₁ log n + s₂ i`
(`Λ(n) ≠ 0`), with `L = s₂ (2i/π) Λ(n)/√n`, there are `r > 0` and `H` holomorphic on the disc
`|z − q| < r` such that on the disc cut along the ray `{sq : s ≥ 1}`

`Φ(z) = L/(z − q) − L z B(2(z² − q²)) Log(1 − z/q) + H(z)`. -/
theorem kgBoundaryWave_prime_branch {n : ℕ} (hw : chmdPrimeWeight n ≠ 0) {q : ℂ}
    (hre : |q.re| = Real.log n) (him : |q.im| = 1) :
    ∃ r > 0, ∃ H : ℂ → ℂ, DifferentiableOn ℂ H (ball q r) ∧
      ∀ z ∈ ball q r, 1 - z / q ∈ slitPlane →
        kgBoundaryWave z = (q.im : ℂ) * (2 * I / π * chmdPrimeWeight n) / (z - q) -
          (q.im : ℂ) * (2 * I / π * chmdPrimeWeight n) * z *
            lightConeBessel (2 * (z ^ 2 - q ^ 2)) * Complex.log (1 - z / q) + H z := by
  set L : ℂ := (q.im : ℂ) * (2 * I / π * chmdPrimeWeight n) with hL
  obtain ⟨G, hFG, hGa⟩ := exists_masslessBoundaryWave_polar_split hw hre him
  have hq0 : q ≠ 0 := fun h => by rw [h, Complex.zero_im, abs_zero] at him; norm_num at him
  set S := (fun t : ℝ => q * t) '' Icc (0 : ℝ) 1
  have hSc : IsCompact S := isCompact_Icc.image (continuous_const.mul continuous_ofReal)
  have hSU : S ⊆ {w | AnalyticAt ℂ G w} := by rintro _ ⟨t, ht, rfl⟩; exact hGa t ht
  obtain ⟨δ, hδ, hthick⟩ := hSc.exists_thickening_subset_open (isOpen_analyticAt ℂ G) hSU
  have hseg : ∀ z ∈ ball q δ, ∀ t ∈ Icc (0 : ℝ) 1, AnalyticAt ℂ G (z * t) := by
    intro z hz t ht
    refine hthick (Metric.mem_thickening_iff.mpr ⟨q * t, ⟨t, ht, rfl⟩, ?_⟩)
    rw [dist_eq_norm, ← sub_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg ht.1, ← dist_eq_norm]
    calc dist z q * t ≤ dist z q * 1 := mul_le_mul_of_nonneg_left ht.2 dist_nonneg
      _ < δ := by rw [mul_one]; exact hz
  refine ⟨δ, hδ, fun z => G z + 2 * z ^ 2 * L * lightConeQuotIntegral q z -
    z ^ 2 * lightConeTailIntegral G z, ?_, ?_⟩
  · intro z hz
    have h1 : DifferentiableAt ℂ G z := by
      simpa using (hseg z hz 1 ⟨zero_le_one, le_rfl⟩).differentiableAt
    have h2 : DifferentiableAt ℂ (lightConeTailIntegral G) z :=
      differentiableAt_lightConeTail (hseg z hz)
    have h3 : DifferentiableAt ℂ (lightConeQuotIntegral q) z :=
      differentiable_lightConeQuotIntegral q z
    exact (by fun_prop : DifferentiableAt ℂ (fun z => G z + 2 * z ^ 2 * L *
      lightConeQuotIntegral q z - z ^ 2 * lightConeTailIntegral G z) z).differentiableWithinAt
  · intro z hz hslit
    have hne : ∀ t ∈ Icc (0 : ℝ) 1, z * t - q ≠ 0 := fun t ht =>
      mul_ofReal_sub_ne_zero hq0 hslit ht
    have hzq : z ≠ q := fun h => hne 1 ⟨zero_le_one, le_rfl⟩ (by rw [ofReal_one, mul_one, h, sub_self])
    have hcG : ContinuousOn (fun t : ℝ => G (z * t)) (Icc 0 1) := fun t ht =>
      (ContinuousAt.comp (f := fun t : ℝ => z * t) (g := G) (hseg z hz t ht).continuousAt
        (continuous_const.mul continuous_ofReal).continuousAt).continuousWithinAt
    have hcB : Continuous fun t : ℝ => lightConeBessel (2 * z ^ 2 * (1 - (t : ℂ) ^ 2)) :=
      differentiable_lightConeBessel.continuous.comp (by fun_prop)
    have hc1 : ContinuousOn (fun t : ℝ => lightConeBessel (2 * z ^ 2 * (1 - (t : ℂ) ^ 2)) /
        (z * t - q)) (Icc 0 1) :=
      hcB.continuousOn.div (by fun_prop : Continuous fun t : ℝ => z * (t : ℂ) - q).continuousOn hne
    have hII : ∀ f : ℝ → ℂ, ContinuousOn f (Icc 0 1) → IntervalIntegrable f volume 0 1 :=
      fun f hf => ContinuousOn.intervalIntegrable (by rwa [uIcc_of_le zero_le_one])
    have hsplit : (∫ t in (0 : ℝ)..1, lightConeBessel (2 * z ^ 2 * (1 - (t : ℂ) ^ 2)) *
        masslessBoundaryWave (z * t)) =
        L * (∫ t in (0 : ℝ)..1, lightConeBessel (2 * z ^ 2 * (1 - (t : ℂ) ^ 2)) / (z * t - q)) +
          lightConeTailIntegral G z := by
      unfold lightConeTailIntegral
      have h1 : IntervalIntegrable (fun t : ℝ => L * (lightConeBessel (2 * z ^ 2 * (1 - (t : ℂ) ^ 2)) /
          (z * t - q))) volume 0 1 := (hII _ hc1).const_mul L
      have h2 : IntervalIntegrable (fun t : ℝ => lightConeBessel (2 * z ^ 2 * (1 - (t : ℂ) ^ 2)) *
          G (z * t)) volume 0 1 := hII _ (hcB.continuousOn.mul hcG)
      have e : ∀ t ∈ uIcc (0 : ℝ) 1, lightConeBessel (2 * z ^ 2 * (1 - (t : ℂ) ^ 2)) *
          masslessBoundaryWave (z * t) = L * (lightConeBessel (2 * z ^ 2 * (1 - (t : ℂ) ^ 2)) /
            (z * t - q)) + lightConeBessel (2 * z ^ 2 * (1 - (t : ℂ) ^ 2)) * G (z * t) := by
        intro t ht
        rw [uIcc_of_le zero_le_one] at ht
        rw [hFG (z * t) (sub_ne_zero.mp (hne t ht))]
        ring
      rw [intervalIntegral.integral_congr e, intervalIntegral.integral_add h1 h2,
        intervalIntegral.integral_const_mul]
    have hI := mul_integral_lightConeBessel_div_eq hq0 hslit
    unfold kgBoundaryWave lightConeTransmuteC
    rw [hsplit, hFG z hzq]
    unfold lightConeQuotIntegral
    beta_reduce
    linear_combination (-(z * L)) * hI

/-! ## The discontinuity across the cut -/

theorem tendsto_log_cut_below {x : ℝ} (hx : x < 0) :
    Tendsto (fun ε : ℝ => Complex.log (x - ε * I)) (𝓝[>] 0) (𝓝 (Real.log |x| - π * I)) := by
  have h := tendsto_log_nhdsWithin_im_neg_of_re_neg_of_im_zero (z := (x : ℂ))
    (by rw [Complex.ofReal_re]; exact hx) (Complex.ofReal_im x)
  rw [Complex.norm_real, Real.norm_eq_abs] at h
  refine h.comp (tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩)
  · have hc : Continuous fun ε : ℝ => (x : ℂ) - ε * I := by fun_prop
    simpa using (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  · filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    show ((x : ℂ) - ε * I).im < 0
    rw [Complex.sub_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
    linarith

theorem tendsto_log_cut_above {x : ℝ} (hx : x < 0) :
    Tendsto (fun ε : ℝ => Complex.log (x + ε * I)) (𝓝[>] 0) (𝓝 (Real.log |x| + π * I)) := by
  have h := (continuousWithinAt_log_of_re_neg_of_im_zero (z := (x : ℂ))
    (by rw [Complex.ofReal_re]; exact hx) (Complex.ofReal_im x)).tendsto
  have hval : Complex.log (x : ℂ) = Real.log |x| + π * I := by
    apply Complex.ext
    · rw [Complex.log_re, Complex.norm_real, Real.norm_eq_abs, Complex.add_re, Complex.ofReal_re,
        Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
      ring
    · rw [Complex.log_im, Complex.arg_ofReal_of_neg hx, Complex.add_im, Complex.ofReal_im,
        Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
      ring
  rw [hval] at h
  refine h.comp (tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩)
  · have hc : Continuous fun ε : ℝ => (x : ℂ) + ε * I := by fun_prop
    simpa using (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  · filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    show 0 ≤ ((x : ℂ) + ε * I).im
    rw [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
    linarith

/-- **The jump across the cut.**  At the points `z = sq` (`1 < s < s₀`) of the ray through a prime
point `q`, the boundary values of the causal wave from the two sides of the ray differ by
`2πi L z B(2(z² − q²))`, `L = s₂ (2i/π) Λ(n)/√n`. -/
theorem tendsto_kgBoundaryWave_jump {n : ℕ} (hw : chmdPrimeWeight n ≠ 0) {q : ℂ}
    (hre : |q.re| = Real.log n) (him : |q.im| = 1) :
    ∃ s₀ > (1 : ℝ), ∀ s ∈ Ioo (1 : ℝ) s₀,
      Tendsto (fun ε : ℝ => kgBoundaryWave (s * q + ε * (I * q)) -
          kgBoundaryWave (s * q - ε * (I * q))) (𝓝[>] 0)
        (𝓝 (2 * π * I * ((q.im : ℂ) * (2 * I / π * chmdPrimeWeight n)) * (s * q) *
          lightConeBessel (2 * ((s * q) ^ 2 - q ^ 2)))) := by
  obtain ⟨r, hr, H, hH, hform⟩ := kgBoundaryWave_prime_branch hw hre him
  set L : ℂ := (q.im : ℂ) * (2 * I / π * chmdPrimeWeight n) with hL
  have hq0 : q ≠ 0 := fun h => by rw [h, Complex.zero_im, abs_zero] at him; norm_num at him
  have hqn : 0 < ‖q‖ := norm_pos_iff.mpr hq0
  refine ⟨1 + r / ‖q‖, by have := div_pos hr hqn; linarith, fun s hs => ?_⟩
  have hs1 : 0 < s - 1 := by linarith [hs.1]
  set z : ℂ := s * q with hz
  have hzr : z ∈ ball q r := by
    rw [mem_ball, dist_eq_norm, hz, show (s : ℂ) * q - q = ((s - 1 : ℝ) : ℂ) * q by push_cast; ring,
      norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs1, ← lt_div_iff₀ hqn]
    linarith [hs.2]
  have hzq : z ≠ q := fun h => by
    have h0 : ((s - 1 : ℝ) : ℂ) * q = 0 := by
      rw [show ((s - 1 : ℝ) : ℂ) * q = z - q by rw [hz]; push_cast; ring, h, sub_self]
    rcases mul_eq_zero.mp h0 with h1 | h1
    · exact hs1.ne' (by exact_mod_cast h1)
    · exact hq0 h1
  have hx : 1 - s < 0 := by linarith
  have hcp : ∀ ε : ℝ, 1 - (z + ε * (I * q)) / q = ((1 - s : ℝ) : ℂ) - ε * I := by
    intro ε; rw [hz]; field_simp; push_cast; ring
  have hcm : ∀ ε : ℝ, 1 - (z - ε * (I * q)) / q = ((1 - s : ℝ) : ℂ) + ε * I := by
    intro ε; rw [hz]; field_simp; push_cast; ring
  have hwp : Tendsto (fun ε : ℝ => z + ε * (I * q)) (𝓝[>] 0) (𝓝 z) := by
    have hc : Continuous fun ε : ℝ => z + ε * (I * q) := by fun_prop
    simpa using (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  have hwm : Tendsto (fun ε : ℝ => z - ε * (I * q)) (𝓝[>] 0) (𝓝 z) := by
    have hc : Continuous fun ε : ℝ => z - ε * (I * q) := by fun_prop
    simpa using (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  have hA : ContinuousAt (fun w => L / (w - q) + H w) z :=
    (continuousAt_const.div (continuousAt_id.sub continuousAt_const) (sub_ne_zero.mpr hzq)).add
      (hH.continuousOn.continuousAt (isOpen_ball.mem_nhds hzr))
  have hBc : Continuous lightConeBessel := differentiable_lightConeBessel.continuous
  have hC : ContinuousAt (fun w => L * w * lightConeBessel (2 * (w ^ 2 - q ^ 2))) z :=
    (by fun_prop : Continuous fun w : ℂ => L * w * lightConeBessel (2 * (w ^ 2 - q ^ 2))).continuousAt
  have hlp : Tendsto (fun ε : ℝ => Complex.log (1 - (z + ε * (I * q)) / q)) (𝓝[>] 0)
      (𝓝 (Real.log |1 - s| - π * I)) := (tendsto_log_cut_below hx).congr fun ε => by rw [hcp]
  have hlm : Tendsto (fun ε : ℝ => Complex.log (1 - (z - ε * (I * q)) / q)) (𝓝[>] 0)
      (𝓝 (Real.log |1 - s| + π * I)) := (tendsto_log_cut_above hx).congr fun ε => by rw [hcm]
  have hP := (hA.tendsto.comp hwp).sub ((hC.tendsto.comp hwp).mul hlp)
  have hM := (hA.tendsto.comp hwm).sub ((hC.tendsto.comp hwm).mul hlm)
  have hlim : Tendsto (fun ε : ℝ => kgBoundaryWave (z + ε * (I * q)) -
      kgBoundaryWave (z - ε * (I * q))) (𝓝[>] 0)
      (𝓝 ((L / (z - q) + H z - L * z * lightConeBessel (2 * (z ^ 2 - q ^ 2)) *
          (Real.log |1 - s| - π * I)) -
        (L / (z - q) + H z - L * z * lightConeBessel (2 * (z ^ 2 - q ^ 2)) *
          (Real.log |1 - s| + π * I)))) := (hP.sub hM).congr' (by
    filter_upwards [hwp.eventually (isOpen_ball.mem_nhds hzr),
      hwm.eventually (isOpen_ball.mem_nhds hzr), self_mem_nhdsWithin] with ε h1 h2 (h3 : 0 < ε)
    have hsp : 1 - (z + ε * (I * q)) / q ∈ slitPlane := by
      rw [hcp]
      refine mem_slitPlane_iff.mpr (Or.inr ?_)
      rw [Complex.sub_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im]
      linarith
    have hsm : 1 - (z - ε * (I * q)) / q ∈ slitPlane := by
      rw [hcm]
      refine mem_slitPlane_iff.mpr (Or.inr ?_)
      rw [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im]
      linarith
    simp only [Function.comp_apply]
    rw [hform _ h1 hsp, hform _ h2 hsm]
    ring)
  convert hlim using 2
  ring

/-! ## Cramér's theorem for the causal wave -/

/-- **Cramér's theorem for the Klein–Gordon causal wave.**  The causal wave
`Φ(z) = Σ_ρ m_ρ cos(z√(γ_ρ² + 2)) sech²(γ_ρ/2)`, holomorphic on `|Im z| < 1`, continues to a function
`F` holomorphic at every point whose segment `[0, z]` avoids the boundary singularities of the
massless wave.  On the boundary lines `|Im z| = 1` the singular points of `Φ` are exactly `±log n ± i`
with `n = 1` or `Λ(n) ≠ 0`.  At each prime point `q = s₁ log n + s₂ i` (`Λ(n) ≠ 0`), with
`L = s₂ (2i/π) Λ(n)/√n`,

`F(z) = L/(z − q) − L z B(2(z² − q²)) Log(1 − z/q) + H(z)`,   `H` holomorphic near `q`:

a simple pole carrying the von Mangoldt weight together with a logarithmic branch point, whose cut
runs along the ray through `q` and across which `F` jumps by `2πi L z B(2(z² − q²))`. -/
theorem kgZeroWave_cramer_branch :
    ∃ F : ℂ → ℂ,
      (∀ z : ℂ, |z.im| < 1 → kgZeroWave z = F z) ∧
      (∀ z : ℂ, LightConeRegular z → AnalyticAt ℂ F z) ∧
      {v : ℂ | |v.im| = 1 ∧ ¬ ∃ G : ℂ → ℂ, ContinuousAt G v ∧
          ∀ᶠ z in 𝓝 v, |z.im| < 1 → G z = kgZeroWave z} =
        {v : ℂ | |v.im| = 1 ∧ ∃ n : ℕ, (n = 1 ∨ chmdPrimeWeight n ≠ 0) ∧ |v.re| = Real.log n} ∧
      ∀ n : ℕ, chmdPrimeWeight n ≠ 0 → ∀ q : ℂ, |q.re| = Real.log n → |q.im| = 1 →
        (∃ r > 0, ∃ H : ℂ → ℂ, DifferentiableOn ℂ H (ball q r) ∧
          ∀ z ∈ ball q r, 1 - z / q ∈ slitPlane →
            F z = (q.im : ℂ) * (2 * I / π * chmdPrimeWeight n) / (z - q) -
              (q.im : ℂ) * (2 * I / π * chmdPrimeWeight n) * z *
                lightConeBessel (2 * (z ^ 2 - q ^ 2)) * Complex.log (1 - z / q) + H z) ∧
        ∃ s₀ > (1 : ℝ), ∀ s ∈ Ioo (1 : ℝ) s₀,
          Tendsto (fun ε : ℝ => F (s * q + ε * (I * q)) - F (s * q - ε * (I * q))) (𝓝[>] 0)
            (𝓝 (2 * π * I * ((q.im : ℂ) * (2 * I / π * chmdPrimeWeight n)) * (s * q) *
              lightConeBessel (2 * ((s * q) ^ 2 - q ^ 2)))) :=
  ⟨kgBoundaryWave, fun _ hz => kgZeroWave_eq_kgBoundaryWave hz,
    fun _ hz => analyticAt_kgBoundaryWave hz, kgZeroWave_boundary_singular_set,
    fun _ hw _ hre him => ⟨kgBoundaryWave_prime_branch hw hre him,
      tendsto_kgBoundaryWave_jump hw hre him⟩⟩

end RHTower.CHMDLightCone
