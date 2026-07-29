import GaloisForLFunctions.RHTower.ObserverTemporalDimensionLaw
import GaloisForLFunctions.HTGeometry.ConvolutionAtomBounds
import Mathlib.Topology.ContinuousMap.Weierstrass

/-!
# Complete observer recurrence distribution

For an arbitrary probability energy spectrum, every power of survival
fidelity is itself a characteristic function: its spectral law is the
corresponding convolution power of the energy-difference measure.  Symmetric
time averaging therefore identifies every long-time fidelity moment with an
exact additive collision probability.

Polynomial approximation on `[0,1]` upgrades the moment hierarchy to a
complete distribution theorem: every continuous statistic of the fidelity
has a long-time mean.  No finiteness, discreteness, absolute continuity, or
finite-dimensional hypothesis is imposed.
-/

open Complex Filter MeasureTheory Set
open scoped MeasureTheory Topology Polynomial

noncomputable section

namespace RHTower

open GaloisForLFunctions.HTGeometry

/-- Symmetric-window normalized `n`-th fidelity moment. -/
def spectralReturnMomentMean
    (mu : Measure ℝ) (n : ℕ) (r : ℝ) : ℂ :=
  ((2 * r : ℝ) : ℂ)⁻¹ *
    ∫ t in -r..r,
      ((Complex.normSq (charFun mu t) ^ n : ℝ) : ℂ)

/-- Real form of the symmetric-window normalized fidelity moment. -/
def spectralReturnMomentMeanReal
    (mu : Measure ℝ) (n : ℕ) (r : ℝ) : ℝ :=
  (2 * r)⁻¹ *
    ∫ t in -r..r, Complex.normSq (charFun mu t) ^ n

lemma spectralReturnMomentMean_eq_ofReal
    (mu : Measure ℝ) (n : ℕ) (r : ℝ) :
    spectralReturnMomentMean mu n r =
      (spectralReturnMomentMeanReal mu n r : ℂ) := by
  rw [spectralReturnMomentMean, spectralReturnMomentMeanReal,
    intervalIntegral.integral_ofReal]
  push_cast
  rfl

/-- Characteristic function of an `n`-fold convolution power. -/
lemma charFun_convPow
    (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (n : ℕ) (t : ℝ) :
    charFun (convPow nu n) t = charFun nu t ^ n := by
  induction n with
  | zero =>
      simp [convPow, charFun_apply_real]
  | succ n ih =>
      haveI : IsProbabilityMeasure (convPow nu n) :=
        isProbabilityMeasure_convPow nu n
      rw [convPow, MeasureTheory.charFun_conv, ih, pow_succ']

/-- Every fidelity power is the characteristic function of the corresponding
convolution power of the projective energy-gap law. -/
lemma charFun_convPow_spectralDifferenceMeasure
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (n : ℕ) (t : ℝ) :
    charFun (convPow (spectralDifferenceMeasure mu) n) t =
      (Complex.normSq (charFun mu t) : ℂ) ^ n := by
  rw [charFun_convPow, charFun_spectralDifferenceMeasure]

/-- At every positive window radius, the `n`-th fidelity moment is the sinc
average of the `n`-fold additive gap-collision law. -/
lemma spectralReturnMomentMean_eq_integral_sinc
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (n : ℕ) {r : ℝ} (hr : 0 < r) :
    spectralReturnMomentMean mu n r =
      ∫ x, (Real.sinc (r * x) : ℂ)
        ∂convPow (spectralDifferenceMeasure mu) n := by
  haveI : IsProbabilityMeasure
      (convPow (spectralDifferenceMeasure mu) n) :=
    isProbabilityMeasure_convPow (spectralDifferenceMeasure mu) n
  rw [spectralReturnMomentMean]
  have hchar (t : ℝ) :
      (((Complex.normSq (charFun mu t) ^ n : ℝ) : ℂ)) =
        charFun (convPow (spectralDifferenceMeasure mu) n) t := by
    rw [charFun_convPow_spectralDifferenceMeasure]
    norm_cast
  simp_rw [hchar]
  rw [integral_charFun_Icc hr]
  have hne : ((2 * r : ℝ) : ℂ) ≠ 0 := by
    norm_cast
    positivity
  rw [integral_complex_ofReal]
  have hcast : (2 : ℂ) * (r : ℂ) = ((2 * r : ℝ) : ℂ) := by
    norm_num
  rw [hcast, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]

/-- Universal all-order recurrence law.  The long-time `n`-th fidelity
moment is exactly the probability that `n` independent visible energy gaps
sum to zero. -/
theorem spectralReturnMomentMean_tendsto_collisionHierarchy
    (mu : Measure ℝ) [IsProbabilityMeasure mu] (n : ℕ) :
    Tendsto (spectralReturnMomentMean mu n) atTop
      (𝓝 (((convPow (spectralDifferenceMeasure mu) n).real {0} : ℝ) : ℂ)) := by
  haveI : IsProbabilityMeasure
      (convPow (spectralDifferenceMeasure mu) n) :=
    isProbabilityMeasure_convPow (spectralDifferenceMeasure mu) n
  have h :=
    tendsto_integral_complex_sinc_mul
      (nu := convPow (spectralDifferenceMeasure mu) n)
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  exact (spectralReturnMomentMean_eq_integral_sinc mu n hr).symm

/-- Real form of the universal all-order recurrence law. -/
theorem spectralReturnMomentMeanReal_tendsto_collisionHierarchy
    (mu : Measure ℝ) [IsProbabilityMeasure mu] (n : ℕ) :
    Tendsto (spectralReturnMomentMeanReal mu n) atTop
      (𝓝 ((convPow (spectralDifferenceMeasure mu) n).real {0})) := by
  have h := (Complex.continuous_re.tendsto
    (((convPow (spectralDifferenceMeasure mu) n).real {0} : ℝ) : ℂ)).comp
      (spectralReturnMomentMean_tendsto_collisionHierarchy mu n)
  have heq :
      Complex.re ∘ spectralReturnMomentMean mu n =
        spectralReturnMomentMeanReal mu n := by
    funext r
    rw [Function.comp_apply, spectralReturnMomentMean_eq_ofReal,
      Complex.ofReal_re]
  rwa [heq] at h

/-- Convolution with an atomless right factor cannot create atoms. -/
lemma noAtoms_conv_of_right_noAtoms
    (mu nu : Measure ℝ) [NoAtoms nu] :
    NoAtoms (mu ∗ nu) := by
  rw [Measure.conv]
  apply noAtoms_map_prod_of_countable_fibers
    mu nu (fun p : ℝ × ℝ ↦ p.1 + p.2) (by fun_prop)
  intro a energy
  apply (Set.finite_singleton (energy - a)).countable.mono
  intro b hb
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff] at hb ⊢
  linarith

/-- Every positive convolution power of an atomless real measure is
atomless. -/
lemma noAtoms_convPow_of_noAtoms
    (nu : Measure ℝ) [SFinite nu] [NoAtoms nu]
    {n : ℕ} (hn : 0 < n) :
    NoAtoms (convPow nu n) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  rw [convPow, Measure.conv_comm]
  exact noAtoms_conv_of_right_noAtoms (convPow nu k) nu

/-- The difference of two independent samples from an atomless measure is
atomless. -/
lemma noAtoms_spectralDifferenceMeasure_of_noAtoms
    (mu : Measure ℝ) [NoAtoms mu] :
    NoAtoms (spectralDifferenceMeasure mu) := by
  rw [spectralDifferenceMeasure]
  apply noAtoms_map_prod_of_countable_fibers
    mu mu (fun p : ℝ × ℝ ↦ p.1 - p.2) (by fun_prop)
  intro a gap
  apply (Set.finite_singleton (a - gap)).countable.mono
  intro b hb
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff] at hb ⊢
  linarith

/-- In the atomless phase every positive-order additive collision moment is
zero. -/
theorem spectralCollisionHierarchy_eq_zero_of_noAtoms
    (mu : Measure ℝ) [IsProbabilityMeasure mu] [NoAtoms mu]
    {n : ℕ} (hn : 0 < n) :
    (convPow (spectralDifferenceMeasure mu) n).real {0} = 0 := by
  letI : NoAtoms (spectralDifferenceMeasure mu) :=
    noAtoms_spectralDifferenceMeasure_of_noAtoms mu
  letI : NoAtoms (convPow (spectralDifferenceMeasure mu) n) :=
    noAtoms_convPow_of_noAtoms (spectralDifferenceMeasure mu) hn
  rw [Measure.real, measure_singleton]
  simp

/-- Fidelity always belongs to the compact unit interval. -/
lemma normSq_charFun_mem_Icc
    (mu : Measure ℝ) [IsProbabilityMeasure mu] (t : ℝ) :
    Complex.normSq (charFun mu t) ∈ Icc (0 : ℝ) 1 := by
  constructor
  · exact Complex.normSq_nonneg _
  · rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg (charFun mu t),
      norm_charFun_le_one (μ := mu) t]

/-- Symmetric-window mean of an arbitrary real statistic of fidelity. -/
def spectralReturnStatisticMeanReal
    (mu : Measure ℝ) (g : ℝ → ℝ) (r : ℝ) : ℝ :=
  (2 * r)⁻¹ *
    ∫ t in -r..r, g (Complex.normSq (charFun mu t))

private lemma continuous_fidelity
    (mu : Measure ℝ) [IsProbabilityMeasure mu] :
    Continuous (fun t : ℝ ↦ Complex.normSq (charFun mu t)) :=
  Complex.continuous_normSq.comp continuous_charFun

private lemma continuous_polynomial_fidelity
    (mu : Measure ℝ) [IsProbabilityMeasure mu] (p : ℝ[X]) :
    Continuous
      (fun t : ℝ ↦ p.eval (Complex.normSq (charFun mu t))) := by
  have hp : Continuous (fun x : ℝ ↦ p.eval x) := by
    simpa only [Polynomial.eval₂_at_apply] using
      p.continuous_eval₂ (RingHom.id ℝ)
  exact hp.comp (continuous_fidelity mu)

/-- Exact collision-hierarchy evaluation of a polynomial fidelity
statistic. -/
def spectralCollisionPolynomialMean
    (mu : Measure ℝ) (p : ℝ[X]) : ℝ :=
  p.sum fun n a ↦
    a * (convPow (spectralDifferenceMeasure mu) n).real {0}

lemma spectralCollisionPolynomialMean_add
    (mu : Measure ℝ) (p q : ℝ[X]) :
    spectralCollisionPolynomialMean mu (p + q) =
      spectralCollisionPolynomialMean mu p +
        spectralCollisionPolynomialMean mu q := by
  refine Polynomial.sum_add_index p q _ (fun _ ↦ by ring)
    (fun _ _ _ ↦ by ring)

/-- Every polynomial fidelity statistic converges exactly to its
collision-hierarchy evaluation. -/
theorem spectralReturnStatisticMeanReal_polynomial_tendsto_collisionHierarchy
    (mu : Measure ℝ) [IsProbabilityMeasure mu] (p : ℝ[X]) :
    Tendsto
      (spectralReturnStatisticMeanReal mu (fun x ↦ p.eval x))
      atTop (𝓝 (spectralCollisionPolynomialMean mu p)) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      have hadd :
          spectralReturnStatisticMeanReal mu
              (fun x ↦ (p + q).eval x) =
            fun r ↦
              spectralReturnStatisticMeanReal mu (fun x ↦ p.eval x) r +
              spectralReturnStatisticMeanReal mu (fun x ↦ q.eval x) r := by
        funext r
        rw [spectralReturnStatisticMeanReal]
        simp_rw [Polynomial.eval_add]
        rw [intervalIntegral.integral_add
          ((continuous_polynomial_fidelity mu p).intervalIntegrable (-r) r)
          ((continuous_polynomial_fidelity mu q).intervalIntegrable (-r) r)]
        simp only [spectralReturnStatisticMeanReal]
        ring
      rw [hadd, spectralCollisionPolynomialMean_add]
      exact hp.add hq
  | monomial n a =>
      have hmono :
          spectralReturnStatisticMeanReal mu
              (fun x ↦ (Polynomial.monomial n a).eval x) =
            fun r ↦ a * spectralReturnMomentMeanReal mu n r := by
        funext r
        rw [spectralReturnStatisticMeanReal,
          spectralReturnMomentMeanReal]
        simp_rw [Polynomial.eval_monomial]
        rw [intervalIntegral.integral_const_mul]
        ring
      rw [hmono, spectralCollisionPolynomialMean]
      simp only [Polynomial.sum_monomial_index, zero_mul]
      exact
        (spectralReturnMomentMeanReal_tendsto_collisionHierarchy
          mu n).const_mul a

/-- Every polynomial fidelity statistic has a long-time mean. -/
lemma exists_tendsto_spectralReturnStatisticMeanReal_polynomial
    (mu : Measure ℝ) [IsProbabilityMeasure mu] (p : ℝ[X]) :
    ∃ L : ℝ,
      Tendsto
        (spectralReturnStatisticMeanReal mu (fun x ↦ p.eval x))
        atTop (𝓝 L) :=
  ⟨spectralCollisionPolynomialMean mu p,
    spectralReturnStatisticMeanReal_polynomial_tendsto_collisionHierarchy
      mu p⟩

/-- In the atomless phase, every polynomial statistic has the same
long-time mean as evaluation at zero fidelity. -/
lemma spectralReturnStatisticMeanReal_polynomial_tendsto_eval_zero_of_noAtoms
    (mu : Measure ℝ) [IsProbabilityMeasure mu] [NoAtoms mu]
    (p : ℝ[X]) :
    Tendsto
        (spectralReturnStatisticMeanReal mu (fun x ↦ p.eval x))
        atTop (𝓝 (p.eval 0)) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      have hadd :
          spectralReturnStatisticMeanReal mu
              (fun x ↦ (p + q).eval x) =
            fun r ↦
              spectralReturnStatisticMeanReal mu (fun x ↦ p.eval x) r +
              spectralReturnStatisticMeanReal mu (fun x ↦ q.eval x) r := by
        funext r
        rw [spectralReturnStatisticMeanReal]
        simp_rw [Polynomial.eval_add]
        rw [intervalIntegral.integral_add
          ((continuous_polynomial_fidelity mu p).intervalIntegrable (-r) r)
          ((continuous_polynomial_fidelity mu q).intervalIntegrable (-r) r)]
        simp only [spectralReturnStatisticMeanReal]
        ring
      rw [hadd, Polynomial.eval_add]
      exact hp.add hq
  | monomial n a =>
      have hmono :
          spectralReturnStatisticMeanReal mu
              (fun x ↦ (Polynomial.monomial n a).eval x) =
            fun r ↦ a * spectralReturnMomentMeanReal mu n r := by
        funext r
        rw [spectralReturnStatisticMeanReal,
          spectralReturnMomentMeanReal]
        simp_rw [Polynomial.eval_monomial]
        rw [intervalIntegral.integral_const_mul]
        ring
      rw [hmono, Polynomial.eval_monomial]
      by_cases hn : n = 0
      · subst n
        have hmoment :=
          spectralReturnMomentMeanReal_tendsto_collisionHierarchy mu 0
        have hzero :
            (convPow (spectralDifferenceMeasure mu) 0).real {0} = 1 := by
          rw [convPow, Measure.real,
            Measure.dirac_apply' 0 (measurableSet_singleton 0)]
          norm_num
        simpa [hzero] using hmoment.const_mul a
      · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
        have hmoment :=
          spectralReturnMomentMeanReal_tendsto_collisionHierarchy mu n
        have hzero :=
          spectralCollisionHierarchy_eq_zero_of_noAtoms mu hnpos
        simpa [hzero, hn] using hmoment.const_mul a

/-- Uniform approximation on the fidelity interval controls every positive
window mean with the same error. -/
lemma spectralReturnStatisticMeanReal_dist_le_of_uniform
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    {f g : ℝ → ℝ} (hf : ContinuousOn f (Icc (0 : ℝ) 1))
    (hg : ContinuousOn g (Icc (0 : ℝ) 1))
    {epsilon r : ℝ} (hr : 0 < r)
    (hfg : ∀ x ∈ Icc (0 : ℝ) 1, |f x - g x| ≤ epsilon) :
    dist (spectralReturnStatisticMeanReal mu f r)
        (spectralReturnStatisticMeanReal mu g r) ≤ epsilon := by
  let F : ℝ → ℝ := fun t ↦ Complex.normSq (charFun mu t)
  have hF : Continuous F := continuous_fidelity mu
  have hfi : IntervalIntegrable (fun t ↦ f (F t)) volume (-r) r :=
    (hf.comp hF.continuousOn
      (fun t _ ↦ normSq_charFun_mem_Icc mu t)).intervalIntegrable
  have hgi : IntervalIntegrable (fun t ↦ g (F t)) volume (-r) r :=
    (hg.comp hF.continuousOn
      (fun t _ ↦ normSq_charFun_mem_Icc mu t)).intervalIntegrable
  have hnorm :
      ‖∫ t in -r..r, (f (F t) - g (F t))‖ ≤
        epsilon * |r - (-r)| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro t _
    simpa [Real.norm_eq_abs] using
      hfg (F t) (normSq_charFun_mem_Icc mu t)
  rw [spectralReturnStatisticMeanReal,
    spectralReturnStatisticMeanReal, Real.dist_eq]
  have hscale : 0 ≤ (2 * r)⁻¹ := by positivity
  calc
    |(2 * r)⁻¹ * (∫ t in -r..r, f (F t)) -
        (2 * r)⁻¹ * (∫ t in -r..r, g (F t))| =
        (2 * r)⁻¹ *
          ‖(∫ t in -r..r, f (F t)) -
            (∫ t in -r..r, g (F t))‖ := by
          rw [← mul_sub, abs_mul, abs_of_nonneg hscale,
            Real.norm_eq_abs]
    _ = (2 * r)⁻¹ *
          ‖∫ t in -r..r, (f (F t) - g (F t))‖ := by
          rw [intervalIntegral.integral_sub hfi hgi]
    _ ≤ (2 * r)⁻¹ * (epsilon * |r - (-r)|) := by
          gcongr
    _ = epsilon := by
          rw [abs_of_pos (by linarith : 0 < r - (-r))]
          field_simp
          ring

/-- Complete recurrence-distribution law.  Every continuous real statistic
of survival fidelity has a symmetric-window long-time mean for every
probability energy spectrum, finite or infinite.  The polynomial moments
determining this mean are the exact additive collision hierarchy above. -/
theorem exists_tendsto_spectralReturnStatisticMeanReal
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (g : ℝ → ℝ) (hg : ContinuousOn g (Icc (0 : ℝ) 1)) :
    ∃ L : ℝ,
      Tendsto (spectralReturnStatisticMeanReal mu g) atTop (𝓝 L) := by
  apply cauchy_map_iff_exists_tendsto.mp
  rw [Metric.cauchy_iff]
  refine ⟨inferInstance, ?_⟩
  intro epsilon hepsilon
  obtain ⟨p, hp⟩ :=
    exists_polynomial_near_of_continuousOn
      0 1 g hg (epsilon / 8) (by positivity)
  obtain ⟨Lp, hLp⟩ :=
    exists_tendsto_spectralReturnStatisticMeanReal_polynomial mu p
  have hevent :
      ∀ᶠ r in atTop,
        dist
          (spectralReturnStatisticMeanReal mu (fun x ↦ p.eval x) r)
          Lp < epsilon / 4 :=
    (Metric.tendsto_nhds.mp hLp) (epsilon / 4) (by positivity)
  refine ⟨Metric.ball Lp (epsilon / 2), ?_, ?_⟩
  · rw [mem_map]
    filter_upwards [hevent, eventually_gt_atTop (0 : ℝ)] with r hrp hr
    change dist (spectralReturnStatisticMeanReal mu g r) Lp <
      epsilon / 2
    have happrox :
        dist (spectralReturnStatisticMeanReal mu g r)
          (spectralReturnStatisticMeanReal mu (fun x ↦ p.eval x) r) ≤
            epsilon / 8 := by
      apply spectralReturnStatisticMeanReal_dist_le_of_uniform
        mu hg
        (p.continuous_eval₂ (RingHom.id ℝ)).continuousOn
        hr
      intro x hx
      rw [abs_sub_comm]
      exact (hp x hx).le
    calc
      dist (spectralReturnStatisticMeanReal mu g r) Lp ≤
          dist (spectralReturnStatisticMeanReal mu g r)
              (spectralReturnStatisticMeanReal mu
                (fun x ↦ p.eval x) r) +
            dist (spectralReturnStatisticMeanReal mu
                (fun x ↦ p.eval x) r) Lp :=
        dist_triangle _ _ _
      _ < epsilon / 8 + epsilon / 4 :=
        add_lt_add_of_le_of_lt happrox hrp
      _ < epsilon / 2 := by linarith
  · intro x hx y hy
    rw [Metric.mem_ball] at hx hy
    refine (dist_triangle x Lp y).trans_lt ?_
    rw [dist_comm Lp y]
    linarith

/-- Atomless complete-distribution law.  For every continuous fidelity
statistic, the long-time mean is its value at zero.  Equivalently, the full
asymptotic fidelity distribution is the point mass at zero, even for
singular-continuous spectra whose pointwise fidelity need not decay. -/
theorem spectralReturnStatisticMeanReal_tendsto_eval_zero_of_noAtoms
    (mu : Measure ℝ) [IsProbabilityMeasure mu] [NoAtoms mu]
    (g : ℝ → ℝ) (hg : ContinuousOn g (Icc (0 : ℝ) 1)) :
    Tendsto (spectralReturnStatisticMeanReal mu g) atTop (𝓝 (g 0)) := by
  rw [Metric.tendsto_nhds]
  intro epsilon hepsilon
  obtain ⟨p, hp⟩ :=
    exists_polynomial_near_of_continuousOn
      0 1 g hg (epsilon / 4) (by positivity)
  have hpmean :=
    spectralReturnStatisticMeanReal_polynomial_tendsto_eval_zero_of_noAtoms
      mu p
  have hevent :
      ∀ᶠ r in atTop,
        dist
          (spectralReturnStatisticMeanReal mu (fun x ↦ p.eval x) r)
          (p.eval 0) < epsilon / 4 :=
    (Metric.tendsto_nhds.mp hpmean) (epsilon / 4) (by positivity)
  filter_upwards [hevent, eventually_gt_atTop (0 : ℝ)] with r hrp hr
  have happrox :
      dist (spectralReturnStatisticMeanReal mu g r)
          (spectralReturnStatisticMeanReal mu (fun x ↦ p.eval x) r) ≤
        epsilon / 4 := by
    apply spectralReturnStatisticMeanReal_dist_le_of_uniform
      mu hg (p.continuous_eval₂ (RingHom.id ℝ)).continuousOn hr
    intro x hx
    rw [abs_sub_comm]
    exact (hp x hx).le
  have hzero : dist (p.eval 0) (g 0) < epsilon / 4 := by
    rw [Real.dist_eq]
    exact hp 0 (by constructor <;> norm_num)
  calc
    dist (spectralReturnStatisticMeanReal mu g r) (g 0) ≤
        dist (spectralReturnStatisticMeanReal mu g r)
            (spectralReturnStatisticMeanReal mu (fun x ↦ p.eval x) r) +
          dist (spectralReturnStatisticMeanReal mu (fun x ↦ p.eval x) r)
            (g 0) :=
      dist_triangle _ _ _
    _ ≤ epsilon / 4 +
        (dist (spectralReturnStatisticMeanReal mu (fun x ↦ p.eval x) r)
            (p.eval 0) + dist (p.eval 0) (g 0)) := by
      gcongr
      exact dist_triangle _ _ _
    _ < epsilon := by linarith

end RHTower
