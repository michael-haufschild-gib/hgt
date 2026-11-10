import GaloisForLFunctions.ArithmeticWeightTheory.GaugeDeformations.AnalyticPrimeSmoothing
import GaloisForLFunctions.ArithmeticWeightTheory.GaugeDeformations.PrimeLogarithmRenormalization

/-!
# The moving branch of an arbitrary analytic smoothing profile

The first nonzero Taylor coefficient produces a shifted prime
logarithm. Its imaginary exponent prevents a joint holomorphic endpoint,
even when Euler agreement is required only on nearby real parameters.
-/

open Complex Filter Topology Metric Set
open GaloisForLFunctions.ArithmeticCorrelationGeometry
open GaloisForLFunctions.PrimeTorusTheory
open _root_.RHTower
noncomputable section
set_option autoImplicit false
namespace GaloisForLFunctions.ArithmeticWeightTheory.GaugeDeformations

private def imaginaryBranchApproach (b d : ℝ) (n : ℕ) : ℝ :=
  Real.exp (-Real.pi * (2 * (n : ℝ) + d) / |b|)

private theorem tendsto_imaginaryBranchApproach {b : ℝ} (hb : b ≠ 0) (d : ℝ) :
    Tendsto (imaginaryBranchApproach b d) atTop (𝓝[>] (0 : ℝ)) := by
  have hpos : 0 < 2 * Real.pi / |b| := div_pos (mul_pos (by norm_num) Real.pi_pos) (abs_pos.mpr hb)
  have hn : Tendsto (fun n : ℕ => -((2 * Real.pi / |b|) * (n : ℝ))) atTop atBot :=
    tendsto_neg_atTop_atBot.comp (Tendsto.const_mul_atTop hpos tendsto_natCast_atTop_atTop)
  have he := (Real.tendsto_exp_atBot.comp hn).mul_const (Real.exp (-Real.pi * d / |b|))
  have heq (n : ℕ) : imaginaryBranchApproach b d n =
      Real.exp (-((2 * Real.pi / |b|) * (n : ℝ))) * Real.exp (-Real.pi * d / |b|) := by
    rw [← Real.exp_add]
    unfold imaginaryBranchApproach
    congr 1
    ring
  have hzero : Tendsto (imaginaryBranchApproach b d) atTop (𝓝 (0 : ℝ)) := by
    rw [show imaginaryBranchApproach b d = _ from funext heq]
    simpa only [Function.comp_apply, zero_mul] using he
  exact tendsto_nhdsWithin_iff.mpr ⟨hzero, Eventually.of_forall (fun n => Real.exp_pos _)⟩

private theorem normalized_real_sign {b : ℝ} (hb : b ≠ 0) : b / |b| = 1 ∨ b / |b| = -1 := by
  rcases lt_or_gt_of_ne hb with hn | hp
  · right
    rw [abs_of_neg hn]
    apply (div_eq_iff (neg_ne_zero.mpr hb)).mpr
    ring
  · left
    rw [abs_of_pos hp, div_self hb]

private theorem imaginaryBranch_period {b : ℝ} (hb : b ≠ 0) :
    Complex.exp (((b / |b| : ℝ) : ℂ) * (2 * (Real.pi : ℂ) * I)) = 1 := by
  rcases normalized_real_sign hb with hp | hn
  · rw [hp, Complex.ofReal_one, one_mul, Complex.exp_two_pi_mul_I]
  · rw [hn]
    rw [show (((-1 : ℝ) : ℂ) * (2 * (Real.pi : ℂ) * I)) = -(2 * (Real.pi : ℂ) * I) by
      push_cast; ring, Complex.exp_neg, Complex.exp_two_pi_mul_I, inv_one]

private theorem imaginaryBranch_antiperiod {b : ℝ} (hb : b ≠ 0) :
    Complex.exp (((b / |b| : ℝ) : ℂ) * (Real.pi : ℂ) * I) = -1 := by
  rcases normalized_real_sign hb with hp | hn
  · rw [hp, Complex.ofReal_one, one_mul, Complex.exp_pi_mul_I]
  · rw [hn]
    rw [show (((-1 : ℝ) : ℂ) * (Real.pi : ℂ) * I) = -(Real.pi : ℂ) * I by push_cast; ring]
    simpa only [neg_mul] using Complex.exp_neg_pi_mul_I

private theorem exp_log_imaginaryBranchApproach {b : ℝ} (hb : b ≠ 0) (d : ℝ) (n : ℕ) :
    Complex.exp (-(b : ℂ) * I * Complex.log ((imaginaryBranchApproach b d n : ℝ) : ℂ)) =
      Complex.exp (((b / |b| : ℝ) : ℂ) * (Real.pi : ℂ) * I * (d : ℂ)) := by
  rw [imaginaryBranchApproach, ← Complex.ofReal_log (Real.exp_pos _).le, Real.log_exp]
  have he : -(b : ℂ) * I * ((-Real.pi * (2 * (n : ℝ) + d) / |b| : ℝ) : ℂ) =
      (n : ℂ) * (((b / |b| : ℝ) : ℂ) * (2 * (Real.pi : ℂ) * I)) +
        (((b / |b| : ℝ) : ℂ) * (Real.pi : ℂ) * I * (d : ℂ)) := by
    push_cast
    ring
  rw [he, Complex.exp_add, Complex.exp_nat_mul, imaginaryBranch_period hb, one_pow, one_mul]

/-- Every nonzero imaginary logarithmic exponent prevents continuous extension across its branch. -/
theorem imaginaryLogBranch_no_continuous_extension {c : ℂ} {b : ℝ} (hb : b ≠ 0) {A F : ℂ → ℂ}
    (hA : ContinuousAt A c) (hA0 : A c ≠ 0) (hF : ContinuousAt F c)
    (he : ∀ᶠ x : ℝ in 𝓝[>] 0, F (c + (x : ℂ)) =
      A (c + (x : ℂ)) * Complex.exp (-(b : ℂ) * I * Complex.log (x : ℂ))) : False := by
  have hvalue (d : ℝ) : F c = A c * Complex.exp (((b / |b| : ℝ) : ℂ) * (Real.pi : ℂ) * I * (d : ℂ)) := by
    have ht := tendsto_imaginaryBranchApproach hb d
    have hc : Tendsto (fun n : ℕ => c + ((imaginaryBranchApproach b d n : ℝ) : ℂ)) atTop (𝓝 c) := by
      have hcast := Complex.continuous_ofReal.continuousAt.tendsto.comp
        (ht.mono_right nhdsWithin_le_nhds)
      simpa only [Function.comp_apply, Complex.ofReal_zero, add_zero] using tendsto_const_nhds.add hcast
    have hleft : Tendsto (fun n => F (c + ((imaginaryBranchApproach b d n : ℝ) : ℂ))) atTop (𝓝 (F c)) :=
      hF.tendsto.comp hc
    have hright := (hA.tendsto.comp hc).mul_const
      (Complex.exp (((b / |b| : ℝ) : ℂ) * (Real.pi : ℂ) * I * (d : ℂ)))
    apply tendsto_nhds_unique hleft
    apply hright.congr'
    filter_upwards [ht.eventually he] with n hn
    simp only [Function.comp_apply, hn, exp_log_imaginaryBranchApproach hb]
  have h0 := hvalue 0
  have h1 := hvalue 1
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one] at h0
  simp only [Complex.ofReal_one, mul_one, imaginaryBranch_antiperiod hb, mul_neg_one] at h1
  have hz : A c = 0 := by linear_combination (h1 - h0) / 2
  exact hA0 hz


/-- The analytic exponent remaining after the first moving prime logarithm. -/
def analyticSmoothingBranchExponent (Φ : ℂ → ℂ) (m : ℕ) (a : ℂ) (t : ℝ) (s : ℂ) : ℂ :=
  a * primeLogRegularPart (s + (((m : ℝ) * t : ℝ) : ℂ)) +
    analyticSmoothingPrimeRemainder Φ m a t s + hullRem s (twist (analyticSmoothingGauge Φ t)) -
      hullRem s (twist 0)

/-- The regular factor accompanying the first moving prime logarithm. -/
def analyticSmoothingBranchUnit (Φ : ℂ → ℂ) (m : ℕ) (a : ℂ) (t : ℝ) (s : ℂ) : ℂ :=
  zetaResidueFactor s * Complex.exp (analyticSmoothingBranchExponent Φ m a t s)

private theorem smoothing_prime_decay_eq (p : Nat.Primes) (s : ℂ) :
    Complex.exp (-s * (Real.log (p : ℝ) : ℂ)) = (p : ℂ) ^ (-s) := by
  simpa only [primeFrequency, neg_mul] using prime_cexp_decay p s

/-- The normally convergent canonical logarithm agrees with the actual gauge exponent. -/
theorem jointExponent_analyticSmoothing_eq {Φ : ℂ → ℂ} {m : ℕ} {C : ℝ}
    (hunit : ∀ x : ℝ, x ∈ Icc 0 1 → ‖Φ (x : ℂ)‖ = 1)
    (hdecay : ∀ p : Nat.Primes, ∀ z : ℂ, 0 ≤ z.re →
      ‖analyticSmoothingPrimePhase Φ p z - 1‖ ≤ C * (p : ℝ) ^ (-((m : ℝ) * z.re)))
    {t : ℝ} (ht : 0 ≤ t) {s : ℂ} (hs : 1 < s.re + (m : ℝ) * t) (hhalf : 1 / 2 < s.re) :
    jointDeformationExponent (analyticSmoothingPrimePhase Φ) ((t : ℂ), s) =
      deformationExponent (analyticSmoothingGauge Φ t) s := by
  have hp : Summable (fun p : Nat.Primes => (twist (analyticSmoothingGauge Φ t) p - 1) *
      (p : ℂ) ^ (-s)) := by
    apply Summable.of_norm
    convert analyticSmoothing_prime_summability_of_decay hunit hdecay ht hs using 1
    funext p
    rw [norm_mul, Complex.norm_natCast_cpow_of_pos p.2.pos, Complex.neg_re]
  have hx := summable_localRem (s := s) (norm_twist_prime (analyticSmoothingGauge Φ t)) hhalf
  have hzero := summable_localRem (s := s) (norm_twist_prime 0) hhalf
  rw [jointDeformationExponent, deformationExponent, deformationPrimeSum, hullRem, hullRem,
    ← hp.tsum_add hx, ← (hp.add hx).tsum_sub hzero]
  apply tsum_congr
  intro p
  simp only [jointEulerChange, prime_cexp_decay, analyticSmoothingPrimePhase_eq_twist hunit ht,
    localRem, eulerVar, powCoeff, twist_trivial, mul_one]
  rw [mul_comm ((p : ℂ) ^ (-s)) (twist (analyticSmoothingGauge Φ t) p)]
  ring

/-- The leading Taylor coefficient multiplies the first shifted prime logarithm. -/
theorem deformationPrimeSum_analyticSmoothing_split {Φ : ℂ → ℂ} {m : ℕ} {a : ℂ} {C : ℝ}
    (hunit : ∀ x : ℝ, x ∈ Icc 0 1 → ‖Φ (x : ℂ)‖ = 1)
    (hrem : ∀ z : ℂ, ‖z‖ ≤ 1 → ‖Φ z - 1 - a * z ^ m‖ ≤ C * ‖z‖ ^ (m + 1))
    {t : ℝ} (ht : 0 ≤ t) {s : ℂ} (hs : 1 < s.re + (m : ℝ) * t) :
    deformationPrimeSum (analyticSmoothingGauge Φ t) s =
      a * coronaPrimeZeta (s + (((m : ℝ) * t : ℝ) : ℂ)) +
        analyticSmoothingPrimeRemainder Φ m a t s := by
  have hst : 1 < (s + (((m : ℝ) * t : ℝ) : ℂ)).re := by
    simpa only [Complex.add_re, Complex.ofReal_re] using hs
  have hf := (summable_coronaPrimeEigenvalue hst).mul_left a
  have hr := summable_analyticSmoothingPrimeRemainder hrem ht (s := s)
    (by nlinarith only [hs, ht])
  rw [deformationPrimeSum, analyticSmoothingPrimeRemainder, coronaPrimeZeta,
    ← tsum_mul_left, ← hf.tsum_add hr]
  apply tsum_congr
  intro p
  rw [← analyticSmoothingPrimePhase_eq_twist hunit ht]
  simp only [coronaPrimeEigenvalue]
  rw [← smoothing_prime_decay_eq p s,
    ← smoothing_prime_decay_eq p (s + (((m : ℝ) * t : ℝ) : ℂ))]
  rw [show -(s + (((m : ℝ) * t : ℝ) : ℂ)) * (Real.log (p : ℝ) : ℂ) =
    -((m : ℂ) * (t : ℂ)) * (Real.log (p : ℝ) : ℂ) + -s * (Real.log (p : ℝ) : ℂ) by
      push_cast; ring, Complex.exp_add]
  ring

/-- The remainder exponent is analytic at the first moving singularity. -/
theorem analyticAt_analyticSmoothingBranchExponent {Φ : ℂ → ℂ} {m : ℕ} {a : ℂ} {C : ℝ}
    (hC : 0 ≤ C)
    (hrem : ∀ z : ℂ, ‖z‖ ≤ 1 → ‖Φ z - 1 - a * z ^ m‖ ≤ C * ‖z‖ ^ (m + 1))
    {t : ℝ} (ht : 0 < t) (hmt : (m : ℝ) * t < 1 / 2) :
    AnalyticAt ℂ (analyticSmoothingBranchExponent Φ m a t) (1 - (((m : ℝ) * t : ℝ) : ℂ)) := by
  let q := (m : ℝ) * t
  have hreg : AnalyticAt ℂ primeLogRegularPart ((1 - (q : ℂ)) + (q : ℂ)) := by
    simpa only [sub_add_cancel] using analyticAt_primeLogRegularPart_one
  have hshift : AnalyticAt ℂ (fun s : ℂ => s + (q : ℂ)) (1 - (q : ℂ)) :=
    analyticAt_id.add analyticAt_const
  have hhalf : (1 : ℂ) - (q : ℂ) ∈ PrimeTorusTheory.rightHalf := by
    change 1 / 2 < (1 : ℂ).re - (q : ℂ).re
    simp only [Complex.one_re, Complex.ofReal_re]
    linarith only [hmt]
  have hr := analyticOnNhd_analyticSmoothingPrimeRemainder hC hrem ht.le (1 - (q : ℂ))
    (by change 1 < (1 : ℂ).re - (q : ℂ).re + ((m : ℝ) + 1) * t
        simp only [Complex.one_re, Complex.ofReal_re]
        dsimp only [q]
        nlinarith only [ht])
  exact (((analyticAt_const.mul (hreg.comp (f := fun z : ℂ => z + (q : ℂ)) hshift)).add hr).add
    (analyticOnNhd_hullRem (norm_twist_prime (analyticSmoothingGauge Φ t)) _ hhalf)).sub
      (analyticOnNhd_hullRem (norm_twist_prime 0) _ hhalf)

/-- One spectral radius gives the exact first-branch factorization for every positive parameter. -/
theorem analyticSmoothing_moving_branch_factorization {Φ : ℂ → ℂ} {m : ℕ} {a : ℂ} {C D : ℝ}
    (hunit : ∀ x : ℝ, x ∈ Icc 0 1 → ‖Φ (x : ℂ)‖ = 1)
    (hdecay : ∀ p : Nat.Primes, ∀ z : ℂ, 0 ≤ z.re →
      ‖analyticSmoothingPrimePhase Φ p z - 1‖ ≤ D * (p : ℝ) ^ (-((m : ℝ) * z.re)))
    (hrem : ∀ z : ℂ, ‖z‖ ≤ 1 → ‖Φ z - 1 - a * z ^ m‖ ≤ C * ‖z‖ ^ (m + 1)) :
    ∃ r : ℝ, 0 < r ∧ ∀ t : ℝ, 0 ≤ t → ∀ s : ℂ,
      ‖s - (1 - (((m : ℝ) * t : ℝ) : ℂ))‖ < r →
      1 < s.re + (m : ℝ) * t → 1 / 2 < s.re →
        jointGaugeRegularization (analyticSmoothingPrimePhase Φ) ((t : ℂ), s) =
          analyticSmoothingBranchUnit Φ m a t s *
            Complex.exp (-a * Complex.log (s - (1 - (((m : ℝ) * t : ℝ) : ℂ)))) := by
  obtain ⟨r, hr, _, hprime⟩ := exists_primeLogRegularPart_germ
  refine ⟨r, hr, ?_⟩
  intro t ht s hsr hs hhalf
  let q := (m : ℝ) * t
  have harg : s + (q : ℂ) - 1 = s - (1 - (q : ℂ)) := by ring
  have hball : s + (q : ℂ) ∈ ball 1 r := by
    simpa only [mem_ball, dist_eq_norm, harg] using hsr
  have hp := hprime (s + (q : ℂ)) hball
    (by simpa only [Complex.add_re, Complex.ofReal_re] using hs)
  have hH : deformationExponent (analyticSmoothingGauge Φ t) s =
      analyticSmoothingBranchExponent Φ m a t s - a * Complex.log (s - (1 - (q : ℂ))) := by
    rw [deformationExponent, deformationPrimeSum_analyticSmoothing_split hunit hrem ht hs,
      analyticSmoothingBranchExponent]
    rw [harg] at hp
    linear_combination a * hp
  rw [jointGaugeRegularization, jointExponent_analyticSmoothing_eq hunit hdecay ht hs hhalf, hH,
    sub_eq_add_neg, ← neg_mul, Complex.exp_add, analyticSmoothingBranchUnit]
  ring

/-- The regular branch factor is an analytic unit for all sufficiently small positive parameters. -/
theorem analyticSmoothing_moving_branch_unit {Φ : ℂ → ℂ} {m : ℕ} {a : ℂ} {C : ℝ}
    (hC : 0 ≤ C)
    (hrem : ∀ z : ℂ, ‖z‖ ≤ 1 → ‖Φ z - 1 - a * z ^ m‖ ≤ C * ‖z‖ ^ (m + 1)) :
    ∃ T : ℝ, 0 < T ∧ ∀ t : ℝ, 0 < t → t < T →
      AnalyticAt ℂ (analyticSmoothingBranchUnit Φ m a t) (1 - (((m : ℝ) * t : ℝ) : ℂ)) ∧
        analyticSmoothingBranchUnit Φ m a t (1 - (((m : ℝ) * t : ℝ) : ℂ)) ≠ 0 := by
  have hZ : ∀ᶠ s in 𝓝 (1 : ℂ), zetaResidueFactor s ≠ 0 :=
    (differentiable_zetaResidueFactor.continuous.continuousAt).eventually_ne
      (by rw [zetaResidueFactor_one]; exact one_ne_zero)
  obtain ⟨ε, hε, hb⟩ := Metric.mem_nhds_iff.mp hZ
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hm1 : (0 : ℝ) < m + 1 := by positivity
  refine ⟨min ε (1 / 2) / ((m : ℝ) + 1), div_pos (lt_min hε (by norm_num)) hm1, ?_⟩
  intro t ht htT
  have htm : t * ((m : ℝ) + 1) < min ε (1 / 2) := (lt_div_iff₀ hm1).mp htT
  have hmtε : (m : ℝ) * t < ε := by
    have hh := htm.trans_le (min_le_left _ _)
    nlinarith only [hh, ht]
  have hmt2 : (m : ℝ) * t < 1 / 2 := by
    have hh := htm.trans_le (min_le_right _ _)
    nlinarith only [hh, ht]
  refine ⟨(differentiable_zetaResidueFactor.analyticAt _).mul
    (analyticAt_analyticSmoothingBranchExponent hC hrem ht hmt2).cexp, ?_⟩
  have hdist : dist (1 - (((m : ℝ) * t : ℝ) : ℂ)) 1 < ε := by
    rw [dist_eq_norm, sub_sub_cancel_left, norm_neg, norm_real,
      Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hm0 ht.le)]
    exact hmtε
  exact mul_ne_zero (hb hdist) (Complex.exp_ne_zero _)

/-- A nonzero imaginary leading coefficient excludes continuous extension across its moving branch. -/
theorem analyticSmoothing_branch_no_extension_of_jet {Φ : ℂ → ℂ} {m : ℕ} {b C D : ℝ}
    (hb : b ≠ 0) (hC : 0 ≤ C)
    (hunit : ∀ x : ℝ, x ∈ Icc 0 1 → ‖Φ (x : ℂ)‖ = 1)
    (hdecay : ∀ p : Nat.Primes, ∀ z : ℂ, 0 ≤ z.re →
      ‖analyticSmoothingPrimePhase Φ p z - 1‖ ≤ D * (p : ℝ) ^ (-((m : ℝ) * z.re)))
    (hrem : ∀ z : ℂ, ‖z‖ ≤ 1 → ‖Φ z - 1 - (b : ℂ) * I * z ^ m‖ ≤ C * ‖z‖ ^ (m + 1)) :
    ∃ T : ℝ, 0 < T ∧ ∀ t : ℝ, 0 < t → t < T →
      ¬ ∃ F : ℂ → ℂ, ContinuousAt F (1 - (((m : ℝ) * t : ℝ) : ℂ)) ∧
        ∀ᶠ x : ℝ in 𝓝[>] 0,
          F (1 - (((m : ℝ) * t : ℝ) : ℂ) + (x : ℂ)) =
            jointGaugeRegularization (analyticSmoothingPrimePhase Φ)
              ((t : ℂ), 1 - (((m : ℝ) * t : ℝ) : ℂ) + (x : ℂ)) := by
  obtain ⟨T, hT, hbranch⟩ := analyticSmoothing_moving_branch_unit hC hrem
  obtain ⟨r, hr, hfac⟩ := analyticSmoothing_moving_branch_factorization hunit hdecay hrem
  have hm1 : (0 : ℝ) < m + 1 := by positivity
  refine ⟨min T ((1 / 2) / ((m : ℝ) + 1)), lt_min hT (div_pos (by norm_num) hm1), ?_⟩
  intro t ht htT
  have htT' : t < T := lt_of_lt_of_le htT (min_le_left _ _)
  have ht2 := (lt_div_iff₀ hm1).mp (lt_of_lt_of_le htT (min_le_right _ _))
  have hmt2 : (m : ℝ) * t < 1 / 2 := by nlinarith only [ht2, ht]
  obtain ⟨ha, hne⟩ := hbranch t ht htT'
  rintro ⟨F, hF, he⟩
  apply imaginaryLogBranch_no_continuous_extension hb ha.continuousAt hne hF
  filter_upwards [he, self_mem_nhdsWithin, nhdsWithin_le_nhds (gt_mem_nhds hr)] with x hx hx0 hxr
  change 0 < x at hx0
  rw [hx, hfac t ht.le]
  · simp only [add_sub_cancel_left, neg_mul]
  · rw [add_sub_cancel_left, norm_real, Real.norm_eq_abs, abs_of_pos hx0]
    exact hxr
  · simp only [Complex.add_re, Complex.sub_re, Complex.one_re, Complex.ofReal_re]
    linarith only [hx0]
  · simp only [Complex.add_re, Complex.sub_re, Complex.one_re, Complex.ofReal_re]
    linarith only [hx0, hmt2]

private theorem analyticAt_analyticSmoothing_spectral_regularization {Φ : ℂ → ℂ} {m : ℕ} {C : ℝ}
    (hunit : ∀ x : ℝ, x ∈ Icc 0 1 → ‖Φ (x : ℂ)‖ = 1)
    (hdecay : ∀ p : Nat.Primes, ∀ z : ℂ, 0 ≤ z.re →
      ‖analyticSmoothingPrimePhase Φ p z - 1‖ ≤ C * (p : ℝ) ^ (-((m : ℝ) * z.re)))
    {t : ℝ} (ht : 0 ≤ t) {s : ℂ} (hh : 1 / 2 < s.re) (hs : 1 < s.re + (m : ℝ) * t) :
    AnalyticAt ℂ (fun z => zetaResidueFactor z *
      Complex.exp (deformationExponent (analyticSmoothingGauge Φ t) z)) s := by
  have hmax : max (1 / 2) (1 - (m : ℝ) * t) < s.re :=
    max_lt hh (by linarith only [hs])
  obtain ⟨σ, hσ, hσs⟩ := exists_between hmax
  have hσhalf : 1 / 2 < σ := (le_max_left _ _).trans_lt hσ
  have hσt : 1 < σ + (m : ℝ) * t := by
    have h := (le_max_right (1 / 2) (1 - (m : ℝ) * t)).trans_lt hσ
    linarith only [h]
  have hH := (exists_isozeric hσhalf.le
    (analyticSmoothing_prime_summability_of_decay hunit hdecay ht hσt)).1 s hσs
  exact (differentiable_zetaResidueFactor.analyticAt s).mul hH.cexp

/-- Every nonconstant analytic profile has a first moving oscillatory branch, with its exact unit. -/
theorem analyticSmoothing_branch_rigidity {Φ : ℂ → ℂ} {R : NNReal}
    (hR : 1 < (R : ℝ)) (hΦ : AnalyticOnNhd ℂ Φ (closedBall 0 R))
    (h0 : Φ 0 = 1) (h1 : Φ 1 = -1)
    (hunit : ∀ x : ℝ, x ∈ Icc 0 1 → ‖Φ (x : ℂ)‖ = 1) :
    ∃ m : ℕ, 0 < m ∧ ∃ b : ℝ, b ≠ 0 ∧
      smoothingTaylorCoefficient Φ m = (b : ℂ) * I ∧
      (∀ k < m, smoothingTaylorCoefficient Φ k = 0) ∧
      (∃ r : ℝ, 0 < r ∧ ∀ t : ℝ, 0 ≤ t → ∀ s : ℂ,
        ‖s - (1 - (((m : ℝ) * t : ℝ) : ℂ))‖ < r →
        1 < s.re + (m : ℝ) * t → 1 / 2 < s.re →
          jointGaugeRegularization (analyticSmoothingPrimePhase Φ) ((t : ℂ), s) =
            analyticSmoothingBranchUnit Φ m ((b : ℂ) * I) t s *
              Complex.exp (-(b : ℂ) * I * Complex.log (s - (1 - (((m : ℝ) * t : ℝ) : ℂ))))) ∧
      (∃ T : ℝ, 0 < T ∧ ∀ t : ℝ, 0 < t → t < T →
        AnalyticAt ℂ (analyticSmoothingBranchUnit Φ m ((b : ℂ) * I) t)
          (1 - (((m : ℝ) * t : ℝ) : ℂ)) ∧
        analyticSmoothingBranchUnit Φ m ((b : ℂ) * I) t (1 - (((m : ℝ) * t : ℝ) : ℂ)) ≠ 0) ∧
      ∃ T : ℝ, 0 < T ∧ ∀ t : ℝ, 0 < t → t < T →
        ¬ ∃ F : ℂ → ℂ, ContinuousAt F (1 - (((m : ℝ) * t : ℝ) : ℂ)) ∧
          ∀ᶠ x : ℝ in 𝓝[>] 0,
            F (1 - (((m : ℝ) * t : ℝ) : ℂ) + (x : ℂ)) =
              jointGaugeRegularization (analyticSmoothingPrimePhase Φ)
                ((t : ℂ), 1 - (((m : ℝ) * t : ℝ) : ℂ) + (x : ℂ)) := by
  obtain ⟨m, hm, b, hb, G, hG, hG0, hfac, hcoeff, hbelow, C, hC, hrem⟩ :=
    analyticPhase_first_jet hR hΦ h0 h1 hunit
  obtain ⟨D, hD, hdecay⟩ := analyticSmoothingPrimePhase_decay_of_factor hR hG hfac
  refine ⟨m, hm, b, hb, hcoeff, hbelow, ?_,
    analyticSmoothing_moving_branch_unit hC hrem,
    analyticSmoothing_branch_no_extension_of_jet hb hC hunit hdecay hrem⟩
  simpa only [neg_mul] using analyticSmoothing_moving_branch_factorization hunit hdecay hrem

/-- Real Euler agreement alone excludes a joint holomorphic endpoint for every such analytic profile. -/
theorem analyticSmoothing_no_joint_endpoint_regularization {Φ : ℂ → ℂ} {R : NNReal}
    (hR : 1 < (R : ℝ)) (hΦ : AnalyticOnNhd ℂ Φ (closedBall 0 R))
    (h0 : Φ 0 = 1) (h1 : Φ 1 = -1)
    (hunit : ∀ x : ℝ, x ∈ Icc 0 1 → ‖Φ (x : ℂ)‖ = 1) :
    ¬ ∃ U : ℂ × ℂ → ℂ, AnalyticAt ℂ U (0, 1) ∧
      ∀ᶠ t : ℝ in 𝓝[>] 0, ∀ᶠ σ : ℝ in 𝓝[>] 1,
        U ((t : ℂ), (σ : ℂ)) =
          ((σ : ℂ) - 1) * gaugeFibre (analyticSmoothingGauge Φ t) (σ : ℂ) := by
  obtain ⟨m, hm, b, hb, G, hG, hG0, hfac, hcoeff, hbelow, C, hC, hrem⟩ :=
    analyticPhase_first_jet hR hΦ h0 h1 hunit
  obtain ⟨D', hD', hdecay⟩ := analyticSmoothingPrimePhase_decay_of_factor hR hG hfac
  rintro ⟨U, hU, hagree⟩
  obtain ⟨ρ, hρ, hUa⟩ := hU.exists_ball_analyticOnNhd
  obtain ⟨T, hT, hno⟩ := analyticSmoothing_branch_no_extension_of_jet hb hC hunit hdecay hrem
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hm1 : (0 : ℝ) < m + 1 := by positivity
  have hmin : 0 < min T (min (ρ / ((m : ℝ) + 1)) ((1 / 2) / ((m : ℝ) + 1))) :=
    lt_min hT (lt_min (div_pos hρ hm1) (div_pos (by norm_num) hm1))
  have hpos : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t := self_mem_nhdsWithin
  have hsmall : ∀ᶠ t : ℝ in 𝓝[>] 0,
      t < min T (min (ρ / ((m : ℝ) + 1)) ((1 / 2) / ((m : ℝ) + 1))) :=
    nhdsWithin_le_nhds (gt_mem_nhds hmin)
  obtain ⟨t, ht, ha, htmax⟩ := (hpos.and (hagree.and hsmall)).exists
  have htT : t < T := lt_of_lt_of_le htmax (min_le_left _ _)
  have htρ := (lt_div_iff₀ hm1).mp
    (lt_of_lt_of_le htmax ((min_le_right _ _).trans (min_le_left _ _)))
  have ht2 := (lt_div_iff₀ hm1).mp
    (lt_of_lt_of_le htmax ((min_le_right _ _).trans (min_le_right _ _)))
  let q := (m : ℝ) * t
  have hq : 0 < q := mul_pos hm0 ht
  have hqρ : q < ρ := by dsimp only [q]; nlinarith only [htρ, ht]
  have hq2 : q < 1 / 2 := by dsimp only [q]; nlinarith only [ht2, ht]
  have htρ' : t < ρ := by nlinarith only [htρ, hq]
  let F : ℂ → ℂ := fun s => U ((t : ℂ), s)
  let K : ℂ → ℂ := fun s => zetaResidueFactor s *
    Complex.exp (deformationExponent (analyticSmoothingGauge Φ t) s)
  have hFa : AnalyticOnNhd ℂ F (ball 1 ρ) := by
    intro s hs
    have hpair : ((t : ℂ), s) ∈ ball ((0 : ℂ), (1 : ℂ)) ρ := by
      rw [mem_ball, Prod.dist_eq, max_lt_iff]
      refine ⟨?_, hs⟩
      simpa only [dist_zero_right, norm_real, Real.norm_eq_abs, abs_of_pos ht] using htρ'
    exact (hUa _ hpair).comp (g := U) (f := fun z : ℂ => ((t : ℂ), z))
      (analyticAt_const.prod analyticAt_id)
  let D : Set ℂ := (ball 1 ρ ∩ {s | 1 - q < s.re}) ∩ {s | 1 / 2 < s.re}
  have hKa : AnalyticOnNhd ℂ K D := by
    intro s hs
    have hst : 1 - q < s.re := hs.1.2
    exact analyticAt_analyticSmoothing_spectral_regularization hunit hdecay ht.le hs.2
      (by linarith only [hst])
  have hFKa : AnalyticOnNhd ℂ F D := hFa.mono (fun s hs => hs.1.1)
  have hD : IsPreconnected D :=
    (((convex_ball (1 : ℂ) ρ).inter (convex_halfSpace_re_gt (1 - q))).inter
      (convex_halfSpace_re_gt (1 / 2))).isPreconnected
  have h1D : (1 : ℂ) ∈ D := by
    exact ⟨⟨mem_ball_self hρ, by change 1 - q < 1; linarith only [hq]⟩, by norm_num⟩
  have he : ∀ᶠ σ : ℝ in 𝓝[>] 1, F (σ : ℂ) = K (σ : ℂ) := by
    filter_upwards [ha, self_mem_nhdsWithin] with σ hσ hσ1
    change 1 < σ at hσ1
    have hse : 1 < (σ : ℂ).re := hσ1
    have hs1 : (σ : ℂ) ≠ 1 := by exact_mod_cast hσ1.ne'
    dsimp [F, K]
    rw [hσ, gaugeFibre_eq_zeta_mul_exp _ hse, zetaResidueFactor_of_ne hs1]
    ring
  have hmap : Tendsto (fun σ : ℝ => (σ : ℂ)) (𝓝[>] 1) (𝓝[≠] (1 : ℂ)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · simpa only [Complex.ofReal_one] using
        (Complex.continuous_ofReal.tendsto (1 : ℝ)).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with σ hσ
      exact fun hh => (ne_of_gt hσ) (Complex.ofReal_eq_one.mp hh)
  have hid := hFKa.eqOn_of_preconnected_of_frequently_eq hKa hD h1D
    (hmap.frequently he.frequently)
  apply hno t ht htT
  have hs0 : 1 - (q : ℂ) ∈ ball 1 ρ := by
    rw [mem_ball, dist_eq_norm, sub_sub_cancel_left, norm_neg, norm_real,
      Real.norm_eq_abs, abs_of_pos hq]
    exact hqρ
  refine ⟨F, (hFa _ hs0).continuousAt, ?_⟩
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (gt_mem_nhds hq)] with x hx hxq
  change 0 < x at hx
  have hpoint : 1 - (q : ℂ) + (x : ℂ) ∈ D := by
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [mem_ball, dist_eq_norm]
      have heq : 1 - (q : ℂ) + (x : ℂ) - 1 = ((x - q : ℝ) : ℂ) := by push_cast; ring
      rw [heq, norm_real, Real.norm_eq_abs, abs_of_neg (sub_neg.mpr hxq)]
      linarith only [hx, hqρ]
    · simp only [mem_setOf_eq, Complex.add_re, Complex.sub_re, Complex.one_re, Complex.ofReal_re]
      linarith only [hx]
    · simp only [mem_setOf_eq, Complex.add_re, Complex.sub_re, Complex.one_re, Complex.ofReal_re]
      linarith only [hx, hq2]
  rw [hid hpoint, jointGaugeRegularization,
    jointExponent_analyticSmoothing_eq hunit hdecay ht.le (by
      simp only [Complex.add_re, Complex.sub_re, Complex.one_re, Complex.ofReal_re]
      linarith only [hx]) hpoint.2]

#print axioms analyticSmoothing_branch_rigidity
#print axioms analyticSmoothing_no_joint_endpoint_regularization

end GaloisForLFunctions.ArithmeticWeightTheory.GaugeDeformations
