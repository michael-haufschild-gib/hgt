import GaloisForLFunctions.RHTower.WeightedEulerStripFourierAnalytic
import GaloisForLFunctions.RHTower.BoundedSupportFourierUncertainty

/-!
# Strip analyticity of the Fourier transform of an exponentially decaying function

The corpus already has this for *entire* functions with a two-ray Phragmen--Lindelof bound.  Here
the hypothesis is weakened to what the proof actually uses: a merely measurable function of a real
variable, dominated by `K exp (-eps |x|)`.  Its Fourier transform at a complex frequency is then
defined and analytic on the horizontal strip `|im w| < eps`, by differentiation under the integral.

This is the form needed when the decaying factor is analytic but the other factor is only square
integrable.
-/

open Complex Real MeasureTheory Set Filter Topology

noncomputable section

namespace RHTower

/-- Fourier transform of a real-variable function at a complex frequency. -/
def expFourier (g : ℝ → ℂ) (w : ℂ) : ℂ := ∫ x : ℝ, g x * Complex.exp (-(I * w * x))

theorem integrable_expFourier_kernel {g : ℝ → ℂ} (hmeas : AEStronglyMeasurable g volume)
    {K ε : ℝ} (hK0 : 0 ≤ K) (hbound : ∀ x : ℝ, ‖g x‖ ≤ K * Real.exp (-(ε * |x|)))
    {w : ℂ} (hw : |w.im| < ε) :
    Integrable fun x : ℝ => g x * Complex.exp (-(I * w * x)) := by
  have hc : 0 < ε - |w.im| := by linarith
  refine Integrable.mono' ((integrable_exp_neg_mul_abs hc).const_mul K) ?_ ?_
  · exact hmeas.mul (Complex.continuous_exp.comp (by fun_prop)).aestronglyMeasurable
  · refine ae_of_all _ fun x => ?_
    rw [norm_mul, Complex.norm_exp, re_neg_I_mul_mul_ofReal]
    calc ‖g x‖ * Real.exp (w.im * x)
        ≤ (K * Real.exp (-(ε * |x|))) * Real.exp (w.im * x) :=
          mul_le_mul_of_nonneg_right (hbound x) (Real.exp_nonneg _)
      _ = K * Real.exp (-(ε * |x|) + w.im * x) := by rw [mul_assoc, ← Real.exp_add]
      _ ≤ K * Real.exp (-((ε - |w.im|) * |x|)) := by
          refine mul_le_mul_of_nonneg_left ?_ hK0
          refine Real.exp_le_exp.2 ?_
          have h2 : w.im * x ≤ |w.im| * |x| := by
            calc w.im * x ≤ |w.im * x| := le_abs_self _
              _ = |w.im| * |x| := abs_mul _ _
          nlinarith [abs_nonneg x]
      _ = K * Real.exp (-((ε - |w.im|) * |x|)) := rfl

theorem hasDerivAt_expFourier {g : ℝ → ℂ} (hmeas : AEStronglyMeasurable g volume)
    {K ε : ℝ} (hK0 : 0 ≤ K) (hbound : ∀ x : ℝ, ‖g x‖ ≤ K * Real.exp (-(ε * |x|)))
    {w₀ : ℂ} (hw : |w₀.im| < ε) :
    HasDerivAt (expFourier g)
      (∫ x : ℝ, g x * (-(I * x)) * Complex.exp (-(I * w₀ * x))) w₀ := by
  set r : ℝ := (ε - |w₀.im|) / 2 with hr
  have hr0 : 0 < r := by rw [hr]; linarith
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun (w : ℂ) (x : ℝ) => g x * Complex.exp (-(I * w * x)))
    (F' := fun (w : ℂ) (x : ℝ) => g x * (-(I * x)) * Complex.exp (-(I * w * x)))
    (bound := fun x : ℝ => K * (|x| * Real.exp (-(r * |x|))))
    (Metric.ball_mem_nhds w₀ hr0) ?_ ?_ ?_ ?_ ?_ ?_).2
  · filter_upwards with w
    exact hmeas.mul (Complex.continuous_exp.comp (by fun_prop)).aestronglyMeasurable
  · exact integrable_expFourier_kernel hmeas hK0 hbound hw
  · exact (hmeas.mul (by fun_prop)).mul
      (Complex.continuous_exp.comp (by fun_prop)).aestronglyMeasurable
  · refine ae_of_all _ fun x w hwball => ?_
    have hwim : |w.im| ≤ |w₀.im| + r := by
      rw [Metric.mem_ball, Complex.dist_eq] at hwball
      have h1 : |w.im - w₀.im| ≤ ‖w - w₀‖ := by
        rw [← Complex.sub_im]
        exact Complex.abs_im_le_norm _
      calc |w.im| = |w₀.im + (w.im - w₀.im)| := by ring_nf
        _ ≤ |w₀.im| + |w.im - w₀.im| := abs_add_le _ _
        _ ≤ |w₀.im| + r := by linarith [le_of_lt hwball]
    rw [norm_mul, norm_mul, Complex.norm_exp, re_neg_I_mul_mul_ofReal]
    have hnormIx : ‖-(I * (x : ℂ))‖ = |x| := by
      rw [norm_neg, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
    rw [hnormIx]
    have hexp : Real.exp (w.im * x) ≤ Real.exp ((|w₀.im| + r) * |x|) := by
      refine Real.exp_le_exp.2 ?_
      calc w.im * x ≤ |w.im * x| := le_abs_self _
        _ = |w.im| * |x| := abs_mul _ _
        _ ≤ (|w₀.im| + r) * |x| := mul_le_mul_of_nonneg_right hwim (abs_nonneg x)
    calc ‖g x‖ * |x| * Real.exp (w.im * x)
        ≤ (K * Real.exp (-(ε * |x|))) * |x| * Real.exp ((|w₀.im| + r) * |x|) := by
          refine mul_le_mul (mul_le_mul_of_nonneg_right (hbound x) (abs_nonneg x)) hexp
            (Real.exp_nonneg _) ?_
          positivity
      _ = K * (|x| * Real.exp (-(ε * |x|) + (|w₀.im| + r) * |x|)) := by
          rw [show K * Real.exp (-(ε * |x|)) * |x| * Real.exp ((|w₀.im| + r) * |x|)
              = K * (|x| * (Real.exp (-(ε * |x|)) * Real.exp ((|w₀.im| + r) * |x|))) from by ring,
            ← Real.exp_add]
      _ ≤ K * (|x| * Real.exp (-(r * |x|))) := by
          refine mul_le_mul_of_nonneg_left ?_ hK0
          refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg x)
          refine Real.exp_le_exp.2 ?_
          have hεsplit : ε = |w₀.im| + 2 * r := by rw [hr]; ring
          nlinarith [abs_nonneg x]
  · exact (integrable_abs_mul_exp_neg_mul_abs hr0).const_mul K
  · refine ae_of_all _ fun x w _ => ?_
    have h1 : HasDerivAt (fun w : ℂ => -(I * (x : ℂ)) * w) (-(I * (x : ℂ))) w := by
      simpa using (hasDerivAt_id w).const_mul (-(I * (x : ℂ)))
    have h2 : HasDerivAt (fun w : ℂ => Complex.exp (-(I * (x : ℂ)) * w))
        (Complex.exp (-(I * (x : ℂ)) * w) * -(I * (x : ℂ))) w := h1.cexp
    have h3 : HasDerivAt (fun w : ℂ => g x * Complex.exp (-(I * (x : ℂ)) * w))
        (g x * (Complex.exp (-(I * (x : ℂ)) * w) * -(I * (x : ℂ)))) w := h2.const_mul (g x)
    have hfun : (fun w : ℂ => g x * Complex.exp (-(I * (x : ℂ)) * w))
        = fun w : ℂ => g x * Complex.exp (-(I * w * (x : ℂ))) := by
      funext w
      congr 2
      ring
    rw [hfun] at h3
    convert! h3 using 1
    ring

theorem analyticOnNhd_expFourier {g : ℝ → ℂ} (hmeas : AEStronglyMeasurable g volume)
    {K ε : ℝ} (hK0 : 0 ≤ K) (hbound : ∀ x : ℝ, ‖g x‖ ≤ K * Real.exp (-(ε * |x|))) :
    AnalyticOnNhd ℂ (expFourier g) {w : ℂ | |w.im| < ε} := by
  have hopen : IsOpen {w : ℂ | |w.im| < ε} :=
    isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const
  refine DifferentiableOn.analyticOnNhd (fun w hw => ?_) hopen
  exact ((hasDerivAt_expFourier hmeas hK0 hbound hw).differentiableAt).differentiableWithinAt


/-- A power is dominated by the factorial times a half-rate exponential. -/
theorem pow_abs_mul_exp_neg_le {a : ℝ} (ha : 0 < a) (n : ℕ) (x : ℝ) :
    |x| ^ n * Real.exp (-(a * |x|)) ≤
      (2 / a) ^ n * (n.factorial : ℝ) * Real.exp (-(a / 2 * |x|)) := by
  set s : ℝ := a / 2 * |x| with hs
  have hs0 : 0 ≤ s := by positivity
  have hkey : s ^ n ≤ (n.factorial : ℝ) * Real.exp s := by
    have h := Real.pow_div_factorial_le_exp s hs0 n
    have hfac : (0 : ℝ) < (n.factorial : ℝ) := by exact_mod_cast n.factorial_pos
    rw [div_le_iff₀ hfac] at h
    linarith [h]
  have hx : |x| ^ n = (2 / a) ^ n * s ^ n := by
    rw [hs, mul_pow, ← mul_assoc, ← mul_pow]
    rw [show (2 / a) * (a / 2) = 1 by field_simp]
    ring
  rw [hx]
  have hsplit : Real.exp (-(a * |x|)) = Real.exp (-s) * Real.exp (-(a / 2 * |x|)) := by
    rw [← Real.exp_add, hs]
    congr 1
    ring
  rw [hsplit]
  have hstep : s ^ n * Real.exp (-s) ≤ (n.factorial : ℝ) := by
    have hexp : Real.exp (-s) = (Real.exp s)⁻¹ := Real.exp_neg s
    rw [hexp, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos s)]
    linarith [hkey]
  calc (2 / a) ^ n * s ^ n * (Real.exp (-s) * Real.exp (-(a / 2 * |x|)))
      = (2 / a) ^ n * (s ^ n * Real.exp (-s)) * Real.exp (-(a / 2 * |x|)) := by ring
    _ ≤ (2 / a) ^ n * (n.factorial : ℝ) * Real.exp (-(a / 2 * |x|)) := by
        refine mul_le_mul_of_nonneg_right ?_ (Real.exp_nonneg _)
        exact mul_le_mul_of_nonneg_left hstep (by positivity)

/-- The exponentially weighted moment integrands are integrable. -/
theorem integrable_expDecay_mul_pow {g : ℝ → ℂ} (hmeas : AEStronglyMeasurable g volume)
    {K ε : ℝ} (hK0 : 0 ≤ K) (hε : 0 < ε)
    (hbound : ∀ x : ℝ, ‖g x‖ ≤ K * Real.exp (-(ε * |x|))) (n : ℕ) :
    Integrable (fun x : ℝ => g x * (x : ℂ) ^ n) := by
  have hhalf : 0 < ε / 2 := by linarith
  have hmaj : Integrable
      (fun x : ℝ => K * ((2 / ε) ^ n * (n.factorial : ℝ)) * Real.exp (-(ε / 2 * |x|))) := by
    exact (integrable_exp_neg_mul_abs hhalf).const_mul
      (K * ((2 / ε) ^ n * (n.factorial : ℝ)))
  refine Integrable.mono' hmaj (hmeas.mul (by fun_prop)) ?_
  refine Filter.Eventually.of_forall fun x => ?_
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
  calc ‖g x‖ * |x| ^ n
      ≤ (K * Real.exp (-(ε * |x|))) * |x| ^ n :=
        mul_le_mul_of_nonneg_right (hbound x) (by positivity)
    _ = K * (|x| ^ n * Real.exp (-(ε * |x|))) := by ring
    _ ≤ K * ((2 / ε) ^ n * (n.factorial : ℝ) * Real.exp (-(ε / 2 * |x|))) :=
        mul_le_mul_of_nonneg_left (pow_abs_mul_exp_neg_le hε n x) hK0
    _ = K * ((2 / ε) ^ n * (n.factorial : ℝ)) * Real.exp (-(ε / 2 * |x|)) := by ring


/-- The `n`-th term of the exponential series of the Fourier kernel, against `g`. -/
def expFourierSeriesTerm (g : ℝ → ℂ) (w : ℂ) (n : ℕ) (x : ℝ) : ℂ :=
  g x * ((-Complex.I * w * (x : ℂ)) ^ n / (n.factorial : ℂ))

theorem expFourierSeriesTerm_eq (g : ℝ → ℂ) (w : ℂ) (n : ℕ) (x : ℝ) :
    expFourierSeriesTerm g w n x =
      ((-Complex.I * w) ^ n / (n.factorial : ℂ)) * (g x * (x : ℂ) ^ n) := by
  rw [expFourierSeriesTerm, mul_pow]
  ring

theorem integrable_expFourierSeriesTerm {g : ℝ → ℂ} (hmeas : AEStronglyMeasurable g volume)
    {K ε : ℝ} (hK0 : 0 ≤ K) (hε : 0 < ε)
    (hbound : ∀ x : ℝ, ‖g x‖ ≤ K * Real.exp (-(ε * |x|))) (w : ℂ) (n : ℕ) :
    Integrable (expFourierSeriesTerm g w n) := by
  have hbase := integrable_expDecay_mul_pow hmeas hK0 hε hbound n
  refine (hbase.const_mul ((-Complex.I * w) ^ n / (n.factorial : ℂ))).congr
    (Filter.Eventually.of_forall fun x => ?_)
  exact (expFourierSeriesTerm_eq g w n x).symm

theorem integral_expFourierSeriesTerm_eq_zero {g : ℝ → ℂ}
    (hmom : ∀ n : ℕ, (∫ x : ℝ, g x * (x : ℂ) ^ n) = 0) (w : ℂ) (n : ℕ) :
    (∫ x : ℝ, expFourierSeriesTerm g w n x) = 0 := by
  have hrw : (∫ x : ℝ, expFourierSeriesTerm g w n x) =
      ((-Complex.I * w) ^ n / (n.factorial : ℂ)) * ∫ x : ℝ, g x * (x : ℂ) ^ n := by
    rw [← MeasureTheory.integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => expFourierSeriesTerm_eq g w n x)
  rw [hrw, hmom n, mul_zero]

theorem hasSum_expFourierSeriesTerm (g : ℝ → ℂ) (w : ℂ) (x : ℝ) :
    HasSum (fun n : ℕ => expFourierSeriesTerm g w n x)
      (g x * Complex.exp (-(Complex.I * w * (x : ℂ)))) := by
  have hexp : HasSum (fun n : ℕ => (-Complex.I * w * (x : ℂ)) ^ n / (n.factorial : ℂ))
      (Complex.exp (-(Complex.I * w * (x : ℂ)))) := by
    have h := NormedSpace.expSeries_div_hasSum_exp (-Complex.I * w * (x : ℂ))
    rw [← Complex.exp_eq_exp_ℂ] at h
    have heq : Complex.exp (-(Complex.I * w * (x : ℂ))) =
        Complex.exp (-Complex.I * w * (x : ℂ)) := by
      congr 1
      ring
    rw [heq]
    exact h
  have hmul := hexp.mul_left (g x)
  refine hmul.congr_fun fun n => ?_
  rw [expFourierSeriesTerm]


theorem norm_expFourierSeriesTerm (g : ℝ → ℂ) (w : ℂ) (n : ℕ) (x : ℝ) :
    ‖expFourierSeriesTerm g w n x‖ = ‖g x‖ * (‖w‖ ^ n * |x| ^ n) / (n.factorial : ℝ) := by
  rw [expFourierSeriesTerm, norm_mul, norm_div, norm_pow, norm_mul, norm_mul,
    Complex.norm_natCast, norm_neg, Complex.norm_I, one_mul, Complex.norm_real,
    Real.norm_eq_abs, mul_pow]
  ring

theorem integral_norm_expFourierSeriesTerm_le {g : ℝ → ℂ}
    (hmeas : AEStronglyMeasurable g volume) {K ε : ℝ} (hK0 : 0 ≤ K) (hε : 0 < ε)
    (hbound : ∀ x : ℝ, ‖g x‖ ≤ K * Real.exp (-(ε * |x|))) (w : ℂ) (n : ℕ) :
    (∫ x : ℝ, ‖expFourierSeriesTerm g w n x‖) ≤
      K * (∫ x : ℝ, Real.exp (-(ε / 2 * |x|))) * (2 * ‖w‖ / ε) ^ n := by
  have hhalf : 0 < ε / 2 := by linarith
  have hmaj : Integrable (fun x : ℝ => K * ((2 / ε) ^ n * (n.factorial : ℝ)) *
      Real.exp (-(ε / 2 * |x|))) :=
    (integrable_exp_neg_mul_abs hhalf).const_mul _
  have hfacpos : (0 : ℝ) < (n.factorial : ℝ) := by exact_mod_cast n.factorial_pos
  have hpt : ∀ x : ℝ, ‖expFourierSeriesTerm g w n x‖ ≤
      (‖w‖ ^ n / (n.factorial : ℝ)) *
        (K * ((2 / ε) ^ n * (n.factorial : ℝ)) * Real.exp (-(ε / 2 * |x|))) := by
    intro x
    rw [norm_expFourierSeriesTerm]
    have hstep : ‖g x‖ * |x| ^ n ≤
        K * ((2 / ε) ^ n * (n.factorial : ℝ) * Real.exp (-(ε / 2 * |x|))) := by
      calc ‖g x‖ * |x| ^ n
          ≤ (K * Real.exp (-(ε * |x|))) * |x| ^ n :=
            mul_le_mul_of_nonneg_right (hbound x) (by positivity)
        _ = K * (|x| ^ n * Real.exp (-(ε * |x|))) := by ring
        _ ≤ K * ((2 / ε) ^ n * (n.factorial : ℝ) * Real.exp (-(ε / 2 * |x|))) :=
            mul_le_mul_of_nonneg_left (pow_abs_mul_exp_neg_le hε n x) hK0
    have hrw : ‖g x‖ * (‖w‖ ^ n * |x| ^ n) / (n.factorial : ℝ) =
        (‖w‖ ^ n / (n.factorial : ℝ)) * (‖g x‖ * |x| ^ n) := by
      field_simp
    rw [hrw]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    calc ‖g x‖ * |x| ^ n
        ≤ K * ((2 / ε) ^ n * (n.factorial : ℝ) * Real.exp (-(ε / 2 * |x|))) := hstep
      _ = K * ((2 / ε) ^ n * (n.factorial : ℝ)) * Real.exp (-(ε / 2 * |x|)) := by ring
  have hint : Integrable (fun x : ℝ => ‖expFourierSeriesTerm g w n x‖) :=
    (integrable_expFourierSeriesTerm hmeas hK0 hε hbound w n).norm
  calc (∫ x : ℝ, ‖expFourierSeriesTerm g w n x‖)
      ≤ ∫ x : ℝ, (‖w‖ ^ n / (n.factorial : ℝ)) *
          (K * ((2 / ε) ^ n * (n.factorial : ℝ)) * Real.exp (-(ε / 2 * |x|))) :=
        integral_mono hint (hmaj.const_mul _) hpt
    _ = (‖w‖ ^ n / (n.factorial : ℝ)) * (K * ((2 / ε) ^ n * (n.factorial : ℝ))) *
          ∫ x : ℝ, Real.exp (-(ε / 2 * |x|)) := by
        rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
        ring
    _ = K * (∫ x : ℝ, Real.exp (-(ε / 2 * |x|))) * (2 * ‖w‖ / ε) ^ n := by
        have hpow : (2 * ‖w‖ / ε) ^ n = ‖w‖ ^ n * (2 / ε) ^ n := by
          rw [← mul_pow]
          congr 1
          ring
        rw [hpow]
        field_simp


/-- **Vanishing of the strip Fourier transform near the origin.**  If every polynomial moment of an
exponentially decaying function vanishes, its Fourier transform vanishes on the disc of radius half
the decay rate: the exponential series may be integrated term by term there. -/
theorem expFourier_eq_zero_of_moments {g : ℝ → ℂ} (hmeas : AEStronglyMeasurable g volume)
    {K ε : ℝ} (hK0 : 0 ≤ K) (hε : 0 < ε)
    (hbound : ∀ x : ℝ, ‖g x‖ ≤ K * Real.exp (-(ε * |x|)))
    (hmom : ∀ n : ℕ, (∫ x : ℝ, g x * (x : ℂ) ^ n) = 0)
    {w : ℂ} (hw : ‖w‖ < ε / 2) : expFourier g w = 0 := by
  have hlt : 2 * ‖w‖ / ε < 1 := by
    rw [div_lt_one hε]
    linarith
  have hgeo : Summable (fun n : ℕ =>
      K * (∫ x : ℝ, Real.exp (-(ε / 2 * |x|))) * (2 * ‖w‖ / ε) ^ n) :=
    (summable_geometric_of_lt_one (by positivity) hlt).mul_left _
  have hsum : Summable (fun n : ℕ => ∫ x : ℝ, ‖expFourierSeriesTerm g w n x‖) :=
    Summable.of_nonneg_of_le (fun n => integral_nonneg fun x => norm_nonneg _)
      (fun n => integral_norm_expFourierSeriesTerm_le hmeas hK0 hε hbound w n) hgeo
  have hHS := hasSum_integral_of_summable_integral_norm
    (fun n => integrable_expFourierSeriesTerm hmeas hK0 hε hbound w n) hsum
  have hsum0 : HasSum (fun n : ℕ => (∫ x : ℝ, expFourierSeriesTerm g w n x)) 0 := by
    have hz : (fun n : ℕ => (∫ x : ℝ, expFourierSeriesTerm g w n x)) = fun _ : ℕ => (0 : ℂ) := by
      funext n
      exact integral_expFourierSeriesTerm_eq_zero hmom w n
    rw [hz]
    exact hasSum_zero
  have heq : (∫ x : ℝ, ∑' n : ℕ, expFourierSeriesTerm g w n x) = 0 := (hHS.unique hsum0)
  rw [expFourier, ← heq]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  exact ((hasSum_expFourierSeriesTerm g w x).tsum_eq).symm


theorem integrable_of_expDecay {g : ℝ → ℂ} (hmeas : AEStronglyMeasurable g volume)
    {K ε : ℝ} (hε : 0 < ε) (hbound : ∀ x : ℝ, ‖g x‖ ≤ K * Real.exp (-(ε * |x|))) :
    Integrable g :=
  Integrable.mono' ((integrable_exp_neg_mul_abs hε).const_mul K) hmeas
    (Filter.Eventually.of_forall hbound)

theorem convex_imStrip (ε : ℝ) : Convex ℝ {w : ℂ | |w.im| < ε} := by
  have h : {w : ℂ | |w.im| < ε} = {w : ℂ | -ε < w.im} ∩ {w : ℂ | w.im < ε} := by
    ext w
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, abs_lt]
  rw [h]
  exact (convex_halfSpace_im_gt _).inter (convex_halfSpace_im_lt _)

/-- **Determinacy: an exponentially decaying function with all polynomial moments zero vanishes.**
The transform is analytic on the strip and zero on a disc, hence zero on the strip; on the real axis
it is the ordinary Fourier transform, and Fourier injectivity finishes. -/
theorem ae_eq_zero_of_moments_eq_zero {g : ℝ → ℂ} (hmeas : AEStronglyMeasurable g volume)
    {K ε : ℝ} (hK0 : 0 ≤ K) (hε : 0 < ε)
    (hbound : ∀ x : ℝ, ‖g x‖ ≤ K * Real.exp (-(ε * |x|)))
    (hmom : ∀ n : ℕ, (∫ x : ℝ, g x * (x : ℂ) ^ n) = 0) :
    g =ᵐ[volume] 0 := by
  have hzero : (0 : ℂ) ∈ {w : ℂ | |w.im| < ε} := by
    simp only [Set.mem_setOf_eq, Complex.zero_im, abs_zero]
    exact hε
  have hev : expFourier g =ᶠ[𝓝 (0 : ℂ)] 0 := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (by positivity : (0 : ℝ) < ε / 2)] with w hw
    have hnorm : ‖w‖ < ε / 2 := by
      rw [Metric.mem_ball, Complex.dist_eq, sub_zero] at hw
      exact hw
    exact expFourier_eq_zero_of_moments hmeas hK0 hε hbound hmom hnorm
  have hstrip : Set.EqOn (expFourier g) 0 {w : ℂ | |w.im| < ε} :=
    (analyticOnNhd_expFourier hmeas hK0 hbound).eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (convex_imStrip ε).isPreconnected hzero hev
  refine integrable_ae_eq_zero_of_fourier_eq_zero
    (integrable_of_expDecay hmeas hε hbound) (fun w => ?_)
  have hmem : (((2 * Real.pi * w : ℝ)) : ℂ) ∈ {w : ℂ | |w.im| < ε} := by
    simp only [Set.mem_setOf_eq, Complex.ofReal_im, abs_zero]
    exact hε
  have hval : expFourier g (((2 * Real.pi * w : ℝ)) : ℂ) = 0 := by
    simpa using hstrip hmem
  rw [Real.fourier_real_eq_integral_exp_smul]
  rw [expFourier] at hval
  rw [← hval]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [smul_eq_mul]
  rw [mul_comm]
  congr 1
  congr 1
  push_cast
  ring


/-- The exponential-weight integrability hypothesis: every weight strictly inside the rate. -/
def ExpWeightIntegrable (g : ℝ → ℂ) (ε : ℝ) : Prop :=
  ∀ a : ℝ, |a| < ε → Integrable (fun x : ℝ => ‖g x‖ * Real.exp (a * |x|))

theorem expWeightIntegrable_of_bound {g : ℝ → ℂ} (hmeas : AEStronglyMeasurable g volume)
    {K ε : ℝ} (hK0 : 0 ≤ K) (hbound : ∀ x : ℝ, ‖g x‖ ≤ K * Real.exp (-(ε * |x|))) :
    ExpWeightIntegrable g ε := by
  intro a ha
  have hc : 0 < ε - |a| := by linarith
  refine Integrable.mono' ((integrable_exp_neg_mul_abs hc).const_mul K)
    (hmeas.norm.mul (by fun_prop)) (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc ‖g x‖ * Real.exp (a * |x|)
      ≤ (K * Real.exp (-(ε * |x|))) * Real.exp (a * |x|) :=
        mul_le_mul_of_nonneg_right (hbound x) (Real.exp_nonneg _)
    _ = K * Real.exp (-(ε * |x|) + a * |x|) := by rw [mul_assoc, ← Real.exp_add]
    _ ≤ K * Real.exp (-((ε - |a|) * |x|)) := by
        refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hK0
        have : a * |x| ≤ |a| * |x| := mul_le_mul_of_nonneg_right (le_abs_self a) (abs_nonneg x)
        nlinarith [abs_nonneg x]

/-- Absolute-value weights are absorbed by an arbitrarily small exponential gain. -/
theorem abs_le_exp_mul {c : ℝ} (hc : 0 < c) (x : ℝ) : |x| ≤ (1 / c) * Real.exp (c * |x|) := by
  have h : c * |x| ≤ Real.exp (c * |x|) := by linarith [Real.add_one_le_exp (c * |x|)]
  rw [one_div, inv_mul_eq_div, le_div_iff₀ hc]
  linarith

theorem integrable_abs_mul_of_expWeightIntegrable {g : ℝ → ℂ}
    (hmeas : AEStronglyMeasurable g volume) {ε : ℝ}
    (hg : ExpWeightIntegrable g ε) {a : ℝ} (ha : |a| < ε) :
    Integrable (fun x : ℝ => ‖g x‖ * |x| * Real.exp (a * |x|)) := by
  obtain ⟨c, hc0, hnew⟩ : ∃ c : ℝ, 0 < c ∧ |a + c| < ε := by
    refine ⟨(ε - |a|) / 2, by linarith, ?_⟩
    have h1 : |a + (ε - |a|) / 2| ≤ |a| + |(ε - |a|) / 2| := abs_add_le _ _
    rw [abs_of_pos (by linarith : (0 : ℝ) < (ε - |a|) / 2)] at h1
    linarith
  have hbase := hg (a + c) hnew
  refine Integrable.mono' (hbase.const_mul (1 / c))
    ((hmeas.norm.mul (by fun_prop)).mul (by fun_prop))
    (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc ‖g x‖ * |x| * Real.exp (a * |x|)
      ≤ ‖g x‖ * ((1 / c) * Real.exp (c * |x|)) * Real.exp (a * |x|) := by
        refine mul_le_mul_of_nonneg_right ?_ (Real.exp_nonneg _)
        exact mul_le_mul_of_nonneg_left (abs_le_exp_mul hc0 x) (norm_nonneg _)
    _ = (1 / c) * (‖g x‖ * Real.exp ((a + c) * |x|)) := by
        rw [show (a + c) * |x| = c * |x| + a * |x| from by ring, Real.exp_add]
        ring


theorem integrable_expFourier_kernel' {g : ℝ → ℂ} (hmeas : AEStronglyMeasurable g volume)
    {ε : ℝ} (hg : ExpWeightIntegrable g ε) {w : ℂ} (hw : |w.im| < ε) :
    Integrable fun x : ℝ => g x * Complex.exp (-(I * w * x)) := by
  have habs : |(|w.im|)| < ε := by rwa [abs_abs]
  refine Integrable.mono' (hg |w.im| habs)
    (hmeas.mul (Complex.continuous_exp.comp (by fun_prop)).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun x => ?_)
  rw [norm_mul, Complex.norm_exp, re_neg_I_mul_mul_ofReal]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (norm_nonneg _)
  calc w.im * x ≤ |w.im * x| := le_abs_self _
    _ = |w.im| * |x| := abs_mul _ _

theorem hasDerivAt_expFourier' {g : ℝ → ℂ} (hmeas : AEStronglyMeasurable g volume)
    {ε : ℝ} (hg : ExpWeightIntegrable g ε) {w₀ : ℂ} (hw : |w₀.im| < ε) :
    HasDerivAt (expFourier g)
      (∫ x : ℝ, g x * (-(I * x)) * Complex.exp (-(I * w₀ * x))) w₀ := by
  set r : ℝ := (ε - |w₀.im|) / 2 with hr
  have hr0 : 0 < r := by rw [hr]; linarith
  have hsum : |(|w₀.im| + r)| < ε := by
    rw [abs_of_nonneg (by positivity)]
    rw [hr]
    linarith
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun (w : ℂ) (x : ℝ) => g x * Complex.exp (-(I * w * x)))
    (F' := fun (w : ℂ) (x : ℝ) => g x * (-(I * x)) * Complex.exp (-(I * w * x)))
    (bound := fun x : ℝ => ‖g x‖ * |x| * Real.exp ((|w₀.im| + r) * |x|))
    (Metric.ball_mem_nhds w₀ hr0) ?_ ?_ ?_ ?_ ?_ ?_).2
  · filter_upwards with w
    exact hmeas.mul (Complex.continuous_exp.comp (by fun_prop)).aestronglyMeasurable
  · exact integrable_expFourier_kernel' hmeas hg hw
  · exact (hmeas.mul (by fun_prop)).mul
      (Complex.continuous_exp.comp (by fun_prop)).aestronglyMeasurable
  · refine ae_of_all _ fun x w hwball => ?_
    have hwim : |w.im| ≤ |w₀.im| + r := by
      rw [Metric.mem_ball, Complex.dist_eq] at hwball
      have h1 : |w.im - w₀.im| ≤ ‖w - w₀‖ := by
        rw [← Complex.sub_im]
        exact Complex.abs_im_le_norm _
      calc |w.im| = |w₀.im + (w.im - w₀.im)| := by ring_nf
        _ ≤ |w₀.im| + |w.im - w₀.im| := abs_add_le _ _
        _ ≤ |w₀.im| + r := by linarith [le_of_lt hwball]
    rw [norm_mul, norm_mul, Complex.norm_exp, re_neg_I_mul_mul_ofReal]
    have hnormIx : ‖-(I * (x : ℂ))‖ = |x| := by
      rw [norm_neg, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
    rw [hnormIx]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by positivity)
    calc w.im * x ≤ |w.im * x| := le_abs_self _
      _ = |w.im| * |x| := abs_mul _ _
      _ ≤ (|w₀.im| + r) * |x| := mul_le_mul_of_nonneg_right hwim (abs_nonneg x)
  · exact integrable_abs_mul_of_expWeightIntegrable hmeas hg hsum
  · refine ae_of_all _ fun x w _ => ?_
    have h1 : HasDerivAt (fun w : ℂ => -(I * (x : ℂ)) * w) (-(I * (x : ℂ))) w := by
      simpa using (hasDerivAt_id w).const_mul (-(I * (x : ℂ)))
    have h2 : HasDerivAt (fun w : ℂ => Complex.exp (-(I * (x : ℂ)) * w))
        (Complex.exp (-(I * (x : ℂ)) * w) * -(I * (x : ℂ))) w := h1.cexp
    have h3 : HasDerivAt (fun w : ℂ => g x * Complex.exp (-(I * (x : ℂ)) * w))
        (g x * (Complex.exp (-(I * (x : ℂ)) * w) * -(I * (x : ℂ)))) w := h2.const_mul (g x)
    have hfun : (fun w : ℂ => g x * Complex.exp (-(I * (x : ℂ)) * w))
        = fun w : ℂ => g x * Complex.exp (-(I * w * (x : ℂ))) := by
      funext w
      congr 2
      ring
    rw [hfun] at h3
    convert! h3 using 1
    ring

theorem analyticOnNhd_expFourier' {g : ℝ → ℂ} (hmeas : AEStronglyMeasurable g volume)
    {ε : ℝ} (hg : ExpWeightIntegrable g ε) :
    AnalyticOnNhd ℂ (expFourier g) {w : ℂ | |w.im| < ε} := by
  have hopen : IsOpen {w : ℂ | |w.im| < ε} :=
    isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const
  refine DifferentiableOn.analyticOnNhd (fun w hw => ?_) hopen
  exact ((hasDerivAt_expFourier' hmeas hg hw).differentiableAt).differentiableWithinAt

/-- The power weight is dominated by a half-rate exponential gain. -/
theorem pow_abs_le_factorial_mul_exp {a : ℝ} (ha : 0 < a) (n : ℕ) (x : ℝ) :
    |x| ^ n ≤ (2 / a) ^ n * (n.factorial : ℝ) * Real.exp (a / 2 * |x|) := by
  have h := pow_abs_mul_exp_neg_le ha n x
  have hpos : (0 : ℝ) < Real.exp (-(a * |x|)) := Real.exp_pos _
  rw [← le_div_iff₀ hpos] at h
  refine le_trans h (le_of_eq ?_)
  have hcomb : Real.exp (a / 2 * |x|) * Real.exp (-(a * |x|)) = Real.exp (-(a / 2 * |x|)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [div_eq_iff (ne_of_gt hpos)]
  linear_combination (-((2 / a) ^ n * (n.factorial : ℝ))) * hcomb


theorem abs_half_lt {ε : ℝ} (hε : 0 < ε) : |ε / 2| < ε := by
  rw [abs_of_pos (by linarith)]
  linarith

theorem integrable_expDecay_mul_pow' {g : ℝ → ℂ} (hmeas : AEStronglyMeasurable g volume)
    {ε : ℝ} (hε : 0 < ε) (hg : ExpWeightIntegrable g ε) (n : ℕ) :
    Integrable (fun x : ℝ => g x * (x : ℂ) ^ n) := by
  have hbase := hg (ε / 2) (abs_half_lt hε)
  refine Integrable.mono' (hbase.const_mul ((2 / ε) ^ n * (n.factorial : ℝ)))
    (hmeas.mul (by fun_prop)) (Filter.Eventually.of_forall fun x => ?_)
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
  calc ‖g x‖ * |x| ^ n
      ≤ ‖g x‖ * ((2 / ε) ^ n * (n.factorial : ℝ) * Real.exp (ε / 2 * |x|)) :=
        mul_le_mul_of_nonneg_left (pow_abs_le_factorial_mul_exp hε n x) (norm_nonneg _)
    _ = (2 / ε) ^ n * (n.factorial : ℝ) * (‖g x‖ * Real.exp (ε / 2 * |x|)) := by ring

theorem integrable_expFourierSeriesTerm' {g : ℝ → ℂ} (hmeas : AEStronglyMeasurable g volume)
    {ε : ℝ} (hε : 0 < ε) (hg : ExpWeightIntegrable g ε) (w : ℂ) (n : ℕ) :
    Integrable (expFourierSeriesTerm g w n) := by
  have hbase := integrable_expDecay_mul_pow' hmeas hε hg n
  refine (hbase.const_mul ((-Complex.I * w) ^ n / (n.factorial : ℂ))).congr
    (Filter.Eventually.of_forall fun x => ?_)
  exact (expFourierSeriesTerm_eq g w n x).symm

theorem integral_norm_expFourierSeriesTerm_le' {g : ℝ → ℂ}
    (hmeas : AEStronglyMeasurable g volume) {ε : ℝ} (hε : 0 < ε)
    (hg : ExpWeightIntegrable g ε) (w : ℂ) (n : ℕ) :
    (∫ x : ℝ, ‖expFourierSeriesTerm g w n x‖) ≤
      (∫ x : ℝ, ‖g x‖ * Real.exp (ε / 2 * |x|)) * (2 * ‖w‖ / ε) ^ n := by
  have hbase := hg (ε / 2) (abs_half_lt hε)
  have hfacpos : (0 : ℝ) < (n.factorial : ℝ) := by exact_mod_cast n.factorial_pos
  have hint : Integrable (fun x : ℝ => ‖expFourierSeriesTerm g w n x‖) :=
    (integrable_expFourierSeriesTerm' hmeas hε hg w n).norm
  have hpt : ∀ x : ℝ, ‖expFourierSeriesTerm g w n x‖ ≤
      (‖w‖ ^ n * (2 / ε) ^ n) * (‖g x‖ * Real.exp (ε / 2 * |x|)) := by
    intro x
    rw [norm_expFourierSeriesTerm]
    have hstep : ‖g x‖ * |x| ^ n ≤
        (2 / ε) ^ n * (n.factorial : ℝ) * (‖g x‖ * Real.exp (ε / 2 * |x|)) := by
      calc ‖g x‖ * |x| ^ n
          ≤ ‖g x‖ * ((2 / ε) ^ n * (n.factorial : ℝ) * Real.exp (ε / 2 * |x|)) :=
            mul_le_mul_of_nonneg_left (pow_abs_le_factorial_mul_exp hε n x) (norm_nonneg _)
        _ = (2 / ε) ^ n * (n.factorial : ℝ) * (‖g x‖ * Real.exp (ε / 2 * |x|)) := by ring
    have hrw : ‖g x‖ * (‖w‖ ^ n * |x| ^ n) / (n.factorial : ℝ) =
        (‖w‖ ^ n / (n.factorial : ℝ)) * (‖g x‖ * |x| ^ n) := by
      field_simp
    rw [hrw]
    calc (‖w‖ ^ n / (n.factorial : ℝ)) * (‖g x‖ * |x| ^ n)
        ≤ (‖w‖ ^ n / (n.factorial : ℝ)) *
            ((2 / ε) ^ n * (n.factorial : ℝ) * (‖g x‖ * Real.exp (ε / 2 * |x|))) :=
          mul_le_mul_of_nonneg_left hstep (by positivity)
      _ = (‖w‖ ^ n * (2 / ε) ^ n) * (‖g x‖ * Real.exp (ε / 2 * |x|)) := by
          field_simp
  calc (∫ x : ℝ, ‖expFourierSeriesTerm g w n x‖)
      ≤ ∫ x : ℝ, (‖w‖ ^ n * (2 / ε) ^ n) * (‖g x‖ * Real.exp (ε / 2 * |x|)) :=
        integral_mono hint (hbase.const_mul _) hpt
    _ = (‖w‖ ^ n * (2 / ε) ^ n) * ∫ x : ℝ, ‖g x‖ * Real.exp (ε / 2 * |x|) :=
        MeasureTheory.integral_const_mul _ _
    _ = (∫ x : ℝ, ‖g x‖ * Real.exp (ε / 2 * |x|)) * (2 * ‖w‖ / ε) ^ n := by
        have hpow : (2 * ‖w‖ / ε) ^ n = ‖w‖ ^ n * (2 / ε) ^ n := by
          rw [← mul_pow]
          congr 1
          ring
        rw [hpow]
        ring


/-- **Vanishing near the origin, weighted form.** -/
theorem expFourier_eq_zero_of_moments' {g : ℝ → ℂ} (hmeas : AEStronglyMeasurable g volume)
    {ε : ℝ} (hε : 0 < ε) (hg : ExpWeightIntegrable g ε)
    (hmom : ∀ n : ℕ, (∫ x : ℝ, g x * (x : ℂ) ^ n) = 0)
    {w : ℂ} (hw : ‖w‖ < ε / 2) : expFourier g w = 0 := by
  have hlt : 2 * ‖w‖ / ε < 1 := by
    rw [div_lt_one hε]
    linarith
  have hBnn : 0 ≤ ∫ x : ℝ, ‖g x‖ * Real.exp (ε / 2 * |x|) :=
    integral_nonneg fun x => by positivity
  have hgeo : Summable (fun n : ℕ =>
      (∫ x : ℝ, ‖g x‖ * Real.exp (ε / 2 * |x|)) * (2 * ‖w‖ / ε) ^ n) :=
    (summable_geometric_of_lt_one (by positivity) hlt).mul_left _
  have hsum : Summable (fun n : ℕ => ∫ x : ℝ, ‖expFourierSeriesTerm g w n x‖) :=
    Summable.of_nonneg_of_le (fun n => integral_nonneg fun x => norm_nonneg _)
      (fun n => integral_norm_expFourierSeriesTerm_le' hmeas hε hg w n) hgeo
  have hHS := hasSum_integral_of_summable_integral_norm
    (fun n => integrable_expFourierSeriesTerm' hmeas hε hg w n) hsum
  have hsum0 : HasSum (fun n : ℕ => (∫ x : ℝ, expFourierSeriesTerm g w n x)) 0 := by
    have hz : (fun n : ℕ => (∫ x : ℝ, expFourierSeriesTerm g w n x)) = fun _ : ℕ => (0 : ℂ) := by
      funext n
      exact integral_expFourierSeriesTerm_eq_zero hmom w n
    rw [hz]
    exact hasSum_zero
  have heq : (∫ x : ℝ, ∑' n : ℕ, expFourierSeriesTerm g w n x) = 0 := hHS.unique hsum0
  rw [expFourier, ← heq]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  exact ((hasSum_expFourierSeriesTerm g w x).tsum_eq).symm

/-- **Determinacy, weighted form.**  A function with exponentially weighted integrability and all
polynomial moments zero vanishes almost everywhere. -/
theorem ae_eq_zero_of_moments_eq_zero' {g : ℝ → ℂ} (hmeas : AEStronglyMeasurable g volume)
    {ε : ℝ} (hε : 0 < ε) (hg : ExpWeightIntegrable g ε)
    (hmom : ∀ n : ℕ, (∫ x : ℝ, g x * (x : ℂ) ^ n) = 0) :
    g =ᵐ[volume] 0 := by
  have hzero : (0 : ℂ) ∈ {w : ℂ | |w.im| < ε} := by
    simp only [Set.mem_setOf_eq, Complex.zero_im, abs_zero]
    exact hε
  have hev : expFourier g =ᶠ[𝓝 (0 : ℂ)] 0 := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (by positivity : (0 : ℝ) < ε / 2)] with w hw
    have hnorm : ‖w‖ < ε / 2 := by
      rw [Metric.mem_ball, Complex.dist_eq, sub_zero] at hw
      exact hw
    exact expFourier_eq_zero_of_moments' hmeas hε hg hmom hnorm
  have hstrip : Set.EqOn (expFourier g) 0 {w : ℂ | |w.im| < ε} :=
    (analyticOnNhd_expFourier' hmeas hg).eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (convex_imStrip ε).isPreconnected hzero hev
  have hgint : Integrable g := by
    have h0 : |(0 : ℝ)| < ε := by simpa using hε
    have hb := hg 0 h0
    refine Integrable.mono' hb hmeas (Filter.Eventually.of_forall fun x => ?_)
    simp
  refine integrable_ae_eq_zero_of_fourier_eq_zero hgint (fun w => ?_)
  have hmem : (((2 * Real.pi * w : ℝ)) : ℂ) ∈ {w : ℂ | |w.im| < ε} := by
    simp only [Set.mem_setOf_eq, Complex.ofReal_im, abs_zero]
    exact hε
  have hval : expFourier g (((2 * Real.pi * w : ℝ)) : ℂ) = 0 := by
    simpa using hstrip hmem
  rw [Real.fourier_real_eq_integral_exp_smul]
  rw [expFourier] at hval
  rw [← hval]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [smul_eq_mul]
  rw [mul_comm]
  congr 1
  congr 1
  push_cast
  ring

end RHTower
