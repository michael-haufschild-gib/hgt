import GaloisForLFunctions.RHTower.PoissonAbelRadialInterchange

/-!
# The Abel-regularized radial primitive splits into channels

At a fixed Abel radius the sampled series converges absolutely and uniformly, so the growing
half-line primitive of the Abel-regularized radial sum is the Abel-weighted sum of the individual
channel primitives:

```text
integral_0^t exp(s/2) (sqrt a · AbelSum(f, a, r))_re ds
  = (1/sqrt lambda) sum_n r^(n+1) integral_0^t a · (Fourier f (a (n+1)))_re ds,     a = lambda e^s.
```

Every step is an absolutely convergent interchange: the Abel weight is geometric and the Fourier
samples are bounded by the source's total mass.
-/

noncomputable section

open Real MeasureTheory Set intervalIntegral Filter Topology
open scoped FourierTransform

namespace RHTower

variable {f : ℝ → ℝ}

/-- The sampled Abel series is absolutely summable at a fixed radius. -/
theorem summable_abelSample {a r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Summable fun n : ℕ =>
      (r : ℂ) ^ (n + 1) * 𝓕 (fun x : ℝ => (f x : ℂ)) (a * ((n : ℝ) + 1)) := by
  set C : ℝ := ∫ x : ℝ, ‖(f x : ℂ)‖ with hC
  have hCnn : (0 : ℝ) ≤ C := integral_nonneg fun x => norm_nonneg _
  have hgeo : Summable fun n : ℕ => r ^ (n + 1) * C := by
    refine ((summable_geometric_of_lt_one hr0 hr1).mul_left (r * C)).congr fun n => ?_
    rw [pow_succ]
    ring
  refine Summable.of_norm_bounded hgeo fun n => ?_
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0]
  exact mul_le_mul_of_nonneg_left (norm_fourier_le_integral_norm _) (by positivity)

/-- The real part of the Abel sum is the Abel-weighted sum of the sampled real parts. -/
theorem re_poissonMuntzAbelSum {a r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    (poissonMuntzAbelSum f a r).re
      = ∑' n : ℕ, r ^ (n + 1) *
          (𝓕 (fun x : ℝ => (f x : ℂ)) (a * ((n : ℝ) + 1))).re := by
  rw [poissonMuntzAbelSum]
  rw [show ((∑' n : ℕ, (r : ℂ) ^ (n + 1) *
      𝓕 (fun x : ℝ => (f x : ℂ)) (a * ((n : ℝ) + 1))).re)
      = Complex.reCLM (∑' n : ℕ, (r : ℂ) ^ (n + 1) *
        𝓕 (fun x : ℝ => (f x : ℂ)) (a * ((n : ℝ) + 1))) from rfl]
  rw [Complex.reCLM.map_tsum (summable_abelSample hr0 hr1)]
  refine tsum_congr fun n => ?_
  show ((r : ℂ) ^ (n + 1) * 𝓕 (fun x : ℝ => (f x : ℂ)) (a * ((n : ℝ) + 1))).re
    = r ^ (n + 1) * (𝓕 (fun x : ℝ => (f x : ℂ)) (a * ((n : ℝ) + 1))).re
  rw [show ((r : ℂ) ^ (n + 1)) = (((r ^ (n + 1) : ℝ)) : ℂ) by push_cast; ring]
  exact Complex.re_ofReal_mul _ _

/-- The growing branch of the Abel-regularized radial sum, channel by channel. -/
theorem expHalf_mul_sqrt_mul_poissonMuntzAbelSum_re {lam : ℝ}
    (hlam : 0 < lam) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (s : ℝ) :
    Real.exp (s / 2) * ((Real.sqrt (lam * Real.exp s) : ℂ) *
        poissonMuntzAbelSum f (lam * Real.exp s) r).re
      = (1 / Real.sqrt lam) * ∑' n : ℕ, r ^ (n + 1) *
          ((lam * Real.exp s) *
            (𝓕 (fun x : ℝ => (f x : ℂ)) ((lam * Real.exp s) * ((n : ℝ) + 1))).re) := by
  have hsl : (0 : ℝ) < Real.sqrt lam := Real.sqrt_pos.mpr hlam
  have hexp : (0 : ℝ) < Real.exp (s / 2) := Real.exp_pos _
  have hsq : Real.sqrt (lam * Real.exp s) = Real.sqrt lam * Real.exp (s / 2) :=
    HTGeometry.sqrt_mul_exp hlam.le s
  have hkey : Real.exp (s / 2) * Real.sqrt (lam * Real.exp s)
      = (1 / Real.sqrt lam) * (lam * Real.exp s) := by
    have hll : Real.sqrt lam * Real.sqrt lam = lam := Real.mul_self_sqrt hlam.le
    have hee : Real.exp (s / 2) * Real.exp (s / 2) = Real.exp s := by
      rw [← Real.exp_add]
      ring_nf
    rw [hsq, one_div, eq_comm, inv_mul_eq_div, div_eq_iff (ne_of_gt hsl)]
    calc lam * Real.exp s
        = (Real.sqrt lam * Real.sqrt lam) * (Real.exp (s / 2) * Real.exp (s / 2)) := by
          rw [hll, hee]
      _ = Real.exp (s / 2) * (Real.sqrt lam * Real.exp (s / 2)) * Real.sqrt lam := by ring
  rw [Complex.re_ofReal_mul, re_poissonMuntzAbelSum hr0 hr1, ← mul_assoc, hkey, mul_assoc]
  congr 1
  rw [← tsum_mul_left]
  refine tsum_congr fun n => ?_
  ring

/-- **The channel split of the Abel-regularized radial primitive.** -/
theorem intervalIntegral_expHalf_mul_sqrt_mul_poissonMuntzAbelSum_eq_tsum
    (hf : Integrable f) {lam : ℝ} (hlam : 0 < lam) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    {t : ℝ} (ht : 0 ≤ t) :
    (∫ s in (0 : ℝ)..t, Real.exp (s / 2) * ((Real.sqrt (lam * Real.exp s) : ℂ) *
        poissonMuntzAbelSum f (lam * Real.exp s) r).re)
      = (1 / Real.sqrt lam) * ∑' n : ℕ, r ^ (n + 1) *
          ∫ s in (0 : ℝ)..t, (lam * Real.exp s) *
            (𝓕 (fun x : ℝ => (f x : ℂ)) ((lam * Real.exp s) * ((n : ℝ) + 1))).re := by
  set g : ℝ → ℂ := fun x : ℝ => (f x : ℂ) with hg
  set C : ℝ := ∫ x : ℝ, ‖g x‖ with hC
  have hCnn : (0 : ℝ) ≤ C := integral_nonneg fun x => norm_nonneg _
  have hFc : Continuous (𝓕 g) :=
    GaloisForLFunctions.HTGeometry.continuous_fourier_of_integrable hf.ofReal
  set T : ℕ → ℝ → ℝ := fun n s => r ^ (n + 1) *
    ((lam * Real.exp s) * (𝓕 g ((lam * Real.exp s) * ((n : ℝ) + 1))).re) with hT
  have hTcont : ∀ n : ℕ, Continuous (T n) := by
    intro n
    refine continuous_const.mul ((continuous_const.mul Real.continuous_exp).mul ?_)
    exact Complex.continuous_re.comp
      (hFc.comp ((continuous_const.mul Real.continuous_exp).mul continuous_const))
  have hTint : ∀ n : ℕ, Integrable (T n) (volume.restrict (Ioc (0 : ℝ) t)) := by
    intro n
    exact ((hTcont n).integrableOn_Icc (a := 0) (b := t)).mono_set Ioc_subset_Icc_self
  have hTbound : ∀ n : ℕ, ∀ s ∈ Ioc (0 : ℝ) t,
      ‖T n s‖ ≤ r ^ (n + 1) * ((lam * Real.exp t) * C) := by
    intro n s hs
    have hs0 : (0 : ℝ) ≤ s := le_of_lt hs.1
    have hexp : Real.exp s ≤ Real.exp t := Real.exp_le_exp.mpr hs.2
    have hpos : (0 : ℝ) < lam * Real.exp s := by positivity
    rw [hT, Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ r ^ (n + 1))]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [abs_mul, abs_of_pos hpos]
    refine mul_le_mul ?_ ?_ (abs_nonneg _) (by positivity)
    · exact mul_le_mul_of_nonneg_left hexp hlam.le
    · exact le_trans (Complex.abs_re_le_norm _) (norm_fourier_le_integral_norm _)
  have hTnormSummable : Summable fun n : ℕ =>
      ∫ s in Ioc (0 : ℝ) t, ‖T n s‖ := by
    have hgeo : Summable fun n : ℕ =>
        r ^ (n + 1) * ((lam * Real.exp t) * C) * t := by
      refine ((summable_geometric_of_lt_one hr0 hr1).mul_left
        (r * ((lam * Real.exp t) * C) * t)).congr fun n => ?_
      rw [pow_succ]
      ring
    refine Summable.of_nonneg_of_le (fun n => integral_nonneg fun s => norm_nonneg _)
      (fun n => ?_) hgeo
    have hle : (∫ s in Ioc (0 : ℝ) t, ‖T n s‖)
        ≤ ∫ _s in Ioc (0 : ℝ) t, r ^ (n + 1) * ((lam * Real.exp t) * C) := by
      refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun s => norm_nonneg _)
        (integrableOn_const measure_Ioc_lt_top.ne enorm_ne_top) ?_
      refine (ae_restrict_iff' measurableSet_Ioc).mpr
        (Filter.Eventually.of_forall fun s hs => hTbound n s hs)
    refine hle.trans (le_of_eq ?_)
    rw [setIntegral_const, smul_eq_mul]
    rw [show (volume.real (Ioc (0 : ℝ) t)) = t by
      rw [MeasureTheory.measureReal_def, Real.volume_Ioc,
        ENNReal.toReal_ofReal (by linarith)]
      ring]
    ring
  rw [intervalIntegral.integral_of_le ht]
  have hsplit : (∫ s in Ioc (0 : ℝ) t, Real.exp (s / 2) *
      ((Real.sqrt (lam * Real.exp s) : ℂ) *
        poissonMuntzAbelSum f (lam * Real.exp s) r).re)
      = ∫ s in Ioc (0 : ℝ) t, (1 / Real.sqrt lam) * ∑' n : ℕ, T n s := by
    refine setIntegral_congr_fun measurableSet_Ioc fun s _ => ?_
    exact expHalf_mul_sqrt_mul_poissonMuntzAbelSum_re hlam hr0 hr1 s
  rw [hsplit, MeasureTheory.integral_const_mul]
  congr 1
  rw [← integral_tsum_of_summable_integral_norm hTint hTnormSummable]
  refine tsum_congr fun n => ?_
  rw [hT, intervalIntegral.integral_of_le ht, ← MeasureTheory.integral_const_mul]

/-! ### The transport -/

/-- The `n`-th channel primitive of the source's Fourier samples. -/
def channelPrimitive (f : ℝ → ℝ) (lam : ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..t, (lam * Real.exp s) *
    (𝓕 (fun x : ℝ => (f x : ℂ)) ((lam * Real.exp s) * ((n : ℝ) + 1))).re

/-- **The transport of the primitive bound.**  A bound on the summed channel primitives, uniform in
the endpoint, bounds the growing primitive of the radial source itself. -/
theorem abs_halfLineExpPrimitive_radialFullLogSource_le_of_channel_bound
    (hf : Integrable f) (heven : Function.Even f) (hcompact : HasCompactSupport f)
    {Cf : ℝ} (hbnd : ∀ y : ℝ, |f y| ≤ Cf) (hmean : ∫ x : ℝ, f x = 0)
    {lam : ℝ} (hlam : 0 < lam)
    (hleb : ∀ b : ℝ, 0 < b → Tendsto (fun s : ℝ => (∫ u in (0 : ℝ)..s,
        |poissonMuntzAngularDatum f b u - poissonMuntzAngularDatum f b 0| +
          |poissonMuntzAngularDatum f b (-u) - poissonMuntzAngularDatum f b 0|) / s)
      (𝓝[>] 0) (𝓝 0))
    {B : ℝ} {t : ℝ} (ht : 0 ≤ t)
    (hsum : Summable fun n : ℕ => |channelPrimitive f lam n t|)
    (hchan : ∑' n : ℕ, |channelPrimitive f lam n t| ≤ B) :
    |HTGeometry.halfLineExpPrimitive (HTGeometry.radialFullLogSource f lam) t|
      ≤ B / Real.sqrt lam := by
  have hsl : (0 : ℝ) < Real.sqrt lam := Real.sqrt_pos.mpr hlam
  have hlim := tendsto_intervalIntegral_sqrt_mul_poissonMuntzAbelSum
    hf heven hcompact hbnd hmean hlam hleb ht
  have habs := (continuous_abs.tendsto _).comp hlim
  simp only [Function.comp_def] at habs
  refine le_of_tendsto habs ?_
  have hev0 : ∀ᶠ r : ℝ in 𝓝[<] (1 : ℝ), 0 ≤ r ∧ r < 1 := by
    have h1 : ∀ᶠ r : ℝ in 𝓝[<] (1 : ℝ), (0 : ℝ) < r :=
      eventually_nhdsWithin_of_eventually_nhds (eventually_gt_nhds (by norm_num))
    have h2 : ∀ᶠ r : ℝ in 𝓝[<] (1 : ℝ), r < 1 := eventually_mem_nhdsWithin
    filter_upwards [h1, h2] with r hr1 hr2
    exact ⟨hr1.le, hr2⟩
  filter_upwards [hev0] with r hr
  rw [intervalIntegral_expHalf_mul_sqrt_mul_poissonMuntzAbelSum_eq_tsum hf hlam hr.1 hr.2 ht]
  have hrle : ∀ n : ℕ, r ^ (n + 1) ≤ 1 := fun n => pow_le_one₀ hr.1 hr.2.le
  have hterm : ∀ n : ℕ, ‖r ^ (n + 1) * channelPrimitive f lam n t‖
      ≤ |channelPrimitive f lam n t| := by
    intro n
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hr.1 (n + 1))]
    exact mul_le_of_le_one_left (abs_nonneg _) (hrle n)
  have hnorm : Summable fun n : ℕ => ‖r ^ (n + 1) * channelPrimitive f lam n t‖ :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hterm hsum
  have hbound : |∑' n : ℕ, r ^ (n + 1) * channelPrimitive f lam n t| ≤ B := by
    refine le_trans ?_ hchan
    have h1 : ‖∑' n : ℕ, r ^ (n + 1) * channelPrimitive f lam n t‖
        ≤ ∑' n : ℕ, ‖r ^ (n + 1) * channelPrimitive f lam n t‖ :=
      norm_tsum_le_tsum_norm hnorm
    have h2 : (∑' n : ℕ, ‖r ^ (n + 1) * channelPrimitive f lam n t‖)
        ≤ ∑' n : ℕ, |channelPrimitive f lam n t| := Summable.tsum_mono hnorm hsum hterm
    rw [Real.norm_eq_abs] at h1
    linarith
  rw [abs_mul, abs_of_nonneg (le_of_lt (by positivity : (0 : ℝ) < 1 / Real.sqrt lam))]
  calc (1 / Real.sqrt lam) * |∑' n : ℕ, r ^ (n + 1) * channelPrimitive f lam n t|
      ≤ (1 / Real.sqrt lam) * B := mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = B / Real.sqrt lam := by ring

/-- **The channel primitive in the radial variable.**  The exponential substitution turns the
logarithmic channel integral into the radial one the exterior estimate bounds. -/
theorem channelPrimitive_eq_integral (hf : Integrable f) {lam : ℝ} (n : ℕ) (t : ℝ) :
    channelPrimitive f lam n t
      = ∫ x in (1 : ℝ)..Real.exp t,
          lam * (𝓕 (fun y : ℝ => (f y : ℂ)) (lam * x * ((n : ℝ) + 1))).re := by
  have hFc : Continuous (𝓕 (fun y : ℝ => (f y : ℂ))) :=
    GaloisForLFunctions.HTGeometry.continuous_fourier_of_integrable hf.ofReal
  have hgc : Continuous fun u : ℝ =>
      lam * (𝓕 (fun y : ℝ => (f y : ℂ)) (lam * u * ((n : ℝ) + 1))).re := by
    refine continuous_const.mul (Complex.continuous_re.comp (hFc.comp ?_))
    exact (continuous_const.mul continuous_id).mul continuous_const
  have hsub := intervalIntegral.integral_deriv_smul_comp
    (f := Real.exp) (f' := Real.exp) (a := (0 : ℝ)) (b := t)
    (g := fun u : ℝ => lam * (𝓕 (fun y : ℝ => (f y : ℂ)) (lam * u * ((n : ℝ) + 1))).re)
    (fun x _ => Real.hasDerivAt_exp x) Real.continuous_exp.continuousOn hgc
  rw [Real.exp_zero] at hsub
  rw [channelPrimitive, ← hsub]
  refine intervalIntegral.integral_congr fun s _ => ?_
  show (lam * Real.exp s) *
      (𝓕 (fun y : ℝ => (f y : ℂ)) ((lam * Real.exp s) * ((n : ℝ) + 1))).re
    = Real.exp s • (lam * (𝓕 (fun y : ℝ => (f y : ℂ)) (lam * Real.exp s * ((n : ℝ) + 1))).re)
  rw [smul_eq_mul]
  ring

end RHTower
