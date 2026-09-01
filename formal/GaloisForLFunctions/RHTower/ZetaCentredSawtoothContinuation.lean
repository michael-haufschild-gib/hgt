import GaloisForLFunctions.RHTower.ZetaTruncatedExtension
import GaloisForLFunctions.RHTower.SawtoothSum

/-!
# The centred additive discrepancy of `ℕ` continues `ζ` to `Re s > -1`

The truncated representation `ζ(s) = Σ_{n ≤ N} n^{-s} + N^{1-s}/(s-1) - s ∫_N^∞ {u} u^{-s-1} du`
holds on `Re s > 0`.  Centring the sawtooth, `{u} = 1/2 + ({u} - 1/2)`, and integrating the centred
part by parts against the periodic second Bernoulli kernel `B₂({u}) = ({u}² - {u})/2` gives

`ζ(s) = Σ_{n ≤ N} n^{-s} + N^{1-s}/(s-1) - N^{-s}/2 - s (s+1) ∫_N^∞ B₂({u}) u^{-s-2} du`.

The kernel `B₂` is bounded by `1/8`, so the last integral converges absolutely and is holomorphic on
`Re s > -1`.  By the identity theorem the representation holds on the whole punctured half-plane
`Re s > -1`, `s ≠ 1`: the additive discrepancy of the integers carries `ζ` across `Re s = 0` with no
singularity other than the pole at `s = 1`.  As a consistency check, evaluating at `s = 0` with
`N = 1` recovers `ζ(0) = -1/2` from the additive side alone.
-/

noncomputable section

namespace RHTower

open MeasureTheory Set Filter Metric Complex intervalIntegral

/-! ## The periodic second Bernoulli kernel -/

/-- The periodic second Bernoulli kernel `({x}² - {x})/2`. -/
def bernoulliPeriodic (x : ℝ) : ℝ := ((Int.fract x) ^ 2 - Int.fract x) / 2

/-- The periodic second Bernoulli kernel is bounded by `1/8`. -/
theorem abs_bernoulliPeriodic_le (x : ℝ) : |bernoulliPeriodic x| ≤ 1 / 8 := by
  unfold bernoulliPeriodic
  have h0 := Int.fract_nonneg x
  have h1 := (Int.fract_lt_one x).le
  rw [abs_le]
  constructor
  · nlinarith [sq_nonneg (Int.fract x - 1 / 2)]
  · nlinarith

theorem abs_bernoulliPeriodic_le_one (x : ℝ) : |bernoulliPeriodic x| ≤ 1 :=
  le_trans (abs_bernoulliPeriodic_le x) (by norm_num)

theorem measurable_bernoulliPeriodic : Measurable bernoulliPeriodic := by
  unfold bernoulliPeriodic
  exact ((measurable_fract.pow_const 2).sub measurable_fract).div_const 2

/-- The `B₂`-form tail `∫_N^∞ B₂({u}) u^{-s-2} du`. -/
def zetaBernoulliTail (N : ℕ) (s : ℂ) : ℂ :=
  ∫ u in Set.Ioi (N : ℝ), ((bernoulliPeriodic u : ℝ) : ℂ) * (u : ℂ) ^ (-s - 1 - 1)

variable {N : ℕ}

/-- Measurability of the `B₂` integrand at every parameter. -/
theorem aestronglyMeasurable_bernoulli (hN : 1 ≤ N) (z : ℂ) :
    AEStronglyMeasurable
      (fun u : ℝ => ((bernoulliPeriodic u : ℝ) : ℂ) * (u : ℂ) ^ (-z - 1 - 1))
      (volume.restrict (Set.Ioi (N : ℝ))) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  apply AEStronglyMeasurable.mul
  · exact (Complex.measurable_ofReal.comp measurable_bernoulliPeriodic).aestronglyMeasurable
  · apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi
    intro u hu
    have hu0 : (0 : ℝ) < u := lt_trans hN0 hu
    have h2 : Continuous fun v : ℝ => (v, (-z - 1 - 1 : ℂ)) := by fun_prop
    exact ((Complex.continuousAt_ofReal_cpow u (-z - 1 - 1)
      (Or.inr (ne_of_gt hu0))).comp
        (f := fun v : ℝ => (v, (-z - 1 - 1 : ℂ)))
        h2.continuousAt).continuousWithinAt

/-- Absolute integrability of the `B₂` integrand on `(N, ∞)` for `Re s > -1`. -/
theorem integrableOn_bernoulli_cpow {s : ℂ} (hs : -1 < s.re) (hN : 1 ≤ N) :
    IntegrableOn (fun u : ℝ => ((bernoulliPeriodic u : ℝ) : ℂ) * (u : ℂ) ^ (-s - 1 - 1))
      (Set.Ioi (N : ℝ)) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hcomp : IntegrableOn (fun u : ℝ => u ^ (-s.re - 2)) (Set.Ioi (N : ℝ)) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) hN0
  refine Integrable.mono hcomp (aestronglyMeasurable_bernoulli hN s) ?_
  rw [ae_restrict_iff' measurableSet_Ioi]
  filter_upwards with u hu
  have hu0 : (0 : ℝ) < u := lt_trans hN0 hu
  have hre : (-s - 1 - 1).re = -s.re - 2 := by
    simp only [Complex.sub_re, Complex.neg_re, Complex.one_re]
    ring
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hu0, hre, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hu0.le _)]
  have hb := abs_bernoulliPeriodic_le_one u
  have hpow : 0 ≤ u ^ (-s.re - 2) := Real.rpow_nonneg hu0.le _
  exact mul_le_of_le_one_left hpow hb

set_option maxHeartbeats 1600000 in
/-- **Holomorphy of the `B₂` tail** on `Re s > -1`: differentiation under the integral, with the
dominating bound `log u · u^{-(Re s₀ + 3)/2}` on the ball of radius `(Re s₀ + 1)/2`. -/
theorem differentiableAt_zetaBernoulliTail (hN : 1 ≤ N) {s₀ : ℂ}
    (hs : -1 < s₀.re) :
    DifferentiableAt ℂ (zetaBernoulliTail N) s₀ := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hNR1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hr : (0 : ℝ) < (s₀.re + 1) / 2 := by linarith
  -- the real-part floor on the ball
  have hball : ∀ z ∈ ball s₀ ((s₀.re + 1) / 2), (s₀.re - 1) / 2 ≤ z.re := by
    intro z hz
    rw [mem_ball, dist_eq_norm] at hz
    have h1 : |(z - s₀).re| ≤ ‖z - s₀‖ := Complex.abs_re_le_norm _
    have h2 : (z - s₀).re = z.re - s₀.re := by simp [Complex.sub_re]
    rw [h2] at h1
    have h3 := abs_le.1 h1
    linarith [h3.1]
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun z : ℂ => fun u : ℝ =>
      ((bernoulliPeriodic u : ℝ) : ℂ) * (u : ℂ) ^ (-z - 1 - 1))
    (F' := fun z : ℂ => fun u : ℝ =>
      ((bernoulliPeriodic u : ℝ) : ℂ)
        * (-(Complex.log u) * (u : ℂ) ^ (-z - 1 - 1)))
    (x₀ := s₀)
    (bound := fun u : ℝ => Real.log u * u ^ (-(s₀.re + 3) / 2))
    (μ := volume.restrict (Set.Ioi (N : ℝ)))
    (ball_mem_nhds s₀ hr)
    (Eventually.of_forall fun z => aestronglyMeasurable_bernoulli hN z)
    (integrableOn_bernoulli_cpow hs hN)
    ?_ ?_ ?_ ?_
  · exact key.2.differentiableAt
  · -- measurability of the derivative integrand
    apply AEStronglyMeasurable.mul
    · exact (Complex.measurable_ofReal.comp measurable_bernoulliPeriodic).aestronglyMeasurable
    · apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi
      intro u hu
      have hu0 : (0 : ℝ) < u := lt_trans hN0 hu
      apply ContinuousWithinAt.mul
      · apply ContinuousWithinAt.congr
          (f := fun v : ℝ => -((Real.log v : ℝ) : ℂ))
        · apply ContinuousWithinAt.neg
          exact (Complex.continuous_ofReal.continuousAt.comp
            (Real.continuousAt_log (ne_of_gt hu0))).continuousWithinAt
        · intro v hv
          have hv0 : (0 : ℝ) < v := lt_trans hN0 hv
          rw [Complex.ofReal_log hv0.le]
        · rw [Complex.ofReal_log hu0.le]
      · have h2 : Continuous fun v : ℝ => (v, (-s₀ - 1 - 1 : ℂ)) := by fun_prop
        exact ((Complex.continuousAt_ofReal_cpow u (-s₀ - 1 - 1)
          (Or.inr (ne_of_gt hu0))).comp
            (f := fun v : ℝ => (v, (-s₀ - 1 - 1 : ℂ)))
            h2.continuousAt).continuousWithinAt
  · -- the uniform bound on the ball
    rw [ae_restrict_iff' measurableSet_Ioi]
    filter_upwards with u hu
    intro z hz
    have hu0 : (0 : ℝ) < u := lt_trans hN0 hu
    have hu1 : (1 : ℝ) ≤ u := le_trans hNR1 (le_of_lt hu)
    have hlog0 : 0 ≤ Real.log u := Real.log_nonneg hu1
    have hzre := hball z hz
    have h1 : ‖((bernoulliPeriodic u : ℝ) : ℂ)
        * (-(Complex.log u) * (u : ℂ) ^ (-z - 1 - 1))‖
        = |bernoulliPeriodic u| * (Real.log u * u ^ ((-z - 1 - 1).re)) := by
      rw [norm_mul, norm_mul, norm_neg,
        Complex.norm_cpow_eq_rpow_re_of_pos hu0,
        ← Complex.ofReal_log hu0.le, Complex.norm_real,
        Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg hlog0]
    rw [h1]
    have h2 : u ^ ((-z - 1 - 1).re) ≤ u ^ (-(s₀.re + 3) / 2) := by
      apply Real.rpow_le_rpow_of_exponent_le hu1
      simp only [Complex.sub_re, Complex.neg_re, Complex.one_re]
      linarith
    have h4 : (0 : ℝ) ≤ u ^ ((-z - 1 - 1).re) := Real.rpow_nonneg hu0.le _
    have h5 : |bernoulliPeriodic u| * (Real.log u * u ^ ((-z - 1 - 1).re))
        ≤ Real.log u * u ^ ((-z - 1 - 1).re) :=
      mul_le_of_le_one_left (mul_nonneg hlog0 h4) (abs_bernoulliPeriodic_le_one u)
    have h6 : Real.log u * u ^ ((-z - 1 - 1).re)
        ≤ Real.log u * u ^ (-(s₀.re + 3) / 2) :=
      mul_le_mul_of_nonneg_left h2 hlog0
    linarith
  · -- integrability of the dominating bound
    have hε : (0 : ℝ) < (s₀.re + 1) / 4 := by linarith
    have hexp : (s₀.re + 1) / 4 + -(s₀.re + 3) / 2 < -1 := by linarith
    have hcomp : IntegrableOn
        (fun u : ℝ => (4 / (s₀.re + 1)) * u ^ ((s₀.re + 1) / 4 + -(s₀.re + 3) / 2))
        (Set.Ioi (N : ℝ)) :=
      (integrableOn_Ioi_rpow_of_lt hexp hN0).const_mul _
    apply Integrable.mono hcomp
    · apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi
      intro u hu
      have hu0 : (0 : ℝ) < u := lt_trans hN0 hu
      apply ContinuousWithinAt.mul
      · exact (Real.continuousAt_log (ne_of_gt hu0)).continuousWithinAt
      · exact (Real.continuousAt_rpow_const u _
          (Or.inl (ne_of_gt hu0))).continuousWithinAt
    · rw [ae_restrict_iff' measurableSet_Ioi]
      filter_upwards with u hu
      have hu0 : (0 : ℝ) < u := lt_trans hN0 hu
      have hu1 : (1 : ℝ) ≤ u := le_trans hNR1 (le_of_lt hu)
      have hlog0 : 0 ≤ Real.log u := Real.log_nonneg hu1
      have h1 : Real.log u ≤ u ^ ((s₀.re + 1) / 4) / ((s₀.re + 1) / 4) :=
        Real.log_le_rpow_div hu0.le hε
      have h2 : ‖Real.log u * u ^ (-(s₀.re + 3) / 2)‖
          = Real.log u * u ^ (-(s₀.re + 3) / 2) := by
        rw [Real.norm_eq_abs, abs_of_nonneg
          (mul_nonneg hlog0 (Real.rpow_nonneg hu0.le _))]
      have h3 : ‖(4 / (s₀.re + 1)) * u ^ ((s₀.re + 1) / 4 + -(s₀.re + 3) / 2)‖
          = (4 / (s₀.re + 1)) * u ^ ((s₀.re + 1) / 4 + -(s₀.re + 3) / 2) := by
        rw [Real.norm_eq_abs, abs_of_nonneg
          (mul_nonneg (div_nonneg (by norm_num) (by linarith)) (Real.rpow_nonneg hu0.le _))]
      rw [h2, h3]
      have h5 : (0 : ℝ) ≤ u ^ (-(s₀.re + 3) / 2) := Real.rpow_nonneg hu0.le _
      have h6 := mul_le_mul_of_nonneg_right h1 h5
      have h7 : u ^ ((s₀.re + 1) / 4) / ((s₀.re + 1) / 4) * u ^ (-(s₀.re + 3) / 2)
          = (4 / (s₀.re + 1)) * u ^ ((s₀.re + 1) / 4 + -(s₀.re + 3) / 2) := by
        rw [Real.rpow_add hu0]
        field_simp
      rw [h7] at h6
      exact h6
  · -- pointwise differentiability in the parameter
    rw [ae_restrict_iff' measurableSet_Ioi]
    filter_upwards with u hu
    intro z _
    have hu0 : (0 : ℝ) < u := lt_trans hN0 hu
    have hg : HasDerivAt (fun w : ℂ => -w - 1 - 1) (-1) z := by
      simpa using (((hasDerivAt_id z).neg.sub_const 1).sub_const 1)
    have hpow := hg.const_cpow (c := (u : ℂ))
      (Or.inl (by exact_mod_cast ne_of_gt hu0))
    have hmul := hpow.const_mul ((bernoulliPeriodic u : ℝ) : ℂ)
    exact hmul.congr_deriv (by ring)

/-! ## The per-cell integration by parts, summed from `N` -/

/-- The centred sawtooth integrates by parts against the `B₂` kernel on `[N, M]`, with no
boundary terms: the per-cell identity `sawtooth_ibp_unit` chained over the cells `[m, m+1]`,
`N ≤ m < M`. -/
theorem sawtooth_ibp_sum_from {N M : ℕ} (hN : 1 ≤ N) (hNM : N ≤ M) (s : ℂ) :
    (∫ x in (N : ℝ)..(M : ℝ), ((Int.fract x - 1 / 2 : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1))
      = -∫ x in (N : ℝ)..(M : ℝ),
          ((((Int.fract x) ^ 2 - Int.fract x) / 2 : ℝ) : ℂ)
            * ((-s - 1) * (x : ℂ) ^ (-s - 1 - 1)) := by
  have hintL : ∀ m : ℕ, 1 ≤ m → IntervalIntegrable
      (fun x : ℝ => ((Int.fract x - 1 / 2 : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1))
      volume (m : ℝ) ((m : ℝ) + 1) := by
    intro m hm
    have hle : (m : ℝ) ≤ (m : ℝ) + 1 := by linarith
    have hpos : ∀ y ∈ Set.uIcc (m : ℝ) ((m : ℝ) + 1), 0 < y := by
      intro y hy
      rw [Set.uIcc_of_le hle] at hy
      have : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
      linarith [hy.1]
    have hG : IntervalIntegrable (fun x => ((x - m - 1 / 2 : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1))
        volume (m : ℝ) ((m : ℝ) + 1) :=
      (ContinuousOn.mul (by fun_prop)
        (ContinuousOn.cpow_const (by fun_prop)
          (fun y hy => Or.inl (by simpa using hpos y hy)))).intervalIntegrable
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hle] at hG ⊢
    refine hG.congr ?_
    have hae := (ae_restrict_iff' measurableSet_Ioc).mpr (fract_ae_sub m)
    filter_upwards [hae] with x hx
    rw [hx]
  have hintR : ∀ m : ℕ, 1 ≤ m → IntervalIntegrable
      (fun x : ℝ => ((((Int.fract x) ^ 2 - Int.fract x) / 2 : ℝ) : ℂ)
        * ((-s - 1) * (x : ℂ) ^ (-s - 1 - 1)))
      volume (m : ℝ) ((m : ℝ) + 1) := by
    intro m hm
    have hle : (m : ℝ) ≤ (m : ℝ) + 1 := by linarith
    have hpos : ∀ y ∈ Set.uIcc (m : ℝ) ((m : ℝ) + 1), 0 < y := by
      intro y hy
      rw [Set.uIcc_of_le hle] at hy
      have : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
      linarith [hy.1]
    have hG : IntervalIntegrable
        (fun x => ((((x - m) ^ 2 - (x - m)) / 2 : ℝ) : ℂ) * ((-s - 1) * (x : ℂ) ^ (-s - 1 - 1)))
        volume (m : ℝ) ((m : ℝ) + 1) :=
      (ContinuousOn.mul (by fun_prop)
        (continuousOn_const.mul (ContinuousOn.cpow_const (by fun_prop)
          (fun y hy => Or.inl (by simpa using hpos y hy))))).intervalIntegrable
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hle] at hG ⊢
    refine hG.congr ?_
    have hae := (ae_restrict_iff' measurableSet_Ioc).mpr (fract_ae_sub m)
    filter_upwards [hae] with x hx
    rw [hx]
  set a : ℕ → ℝ := fun k => (N : ℝ) + k with ha
  have hak : ∀ k : ℕ, a k = ((N + k : ℕ) : ℝ) := fun k => by simp [ha]
  have hak1 : ∀ k : ℕ, a (k + 1) = ((N + k : ℕ) : ℝ) + 1 := fun k => by
    simp only [ha]
    push_cast
    ring
  have hperk : ∀ k : ℕ, k < M - N →
      (∫ x in a k..a (k + 1), ((Int.fract x - 1 / 2 : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1))
        = -∫ x in a k..a (k + 1),
            ((((Int.fract x) ^ 2 - Int.fract x) / 2 : ℝ) : ℂ)
              * ((-s - 1) * (x : ℂ) ^ (-s - 1 - 1)) := by
    intro k _
    have hm1 : 1 ≤ N + k := le_add_right hN
    rw [hak k, hak1 k]
    have hle : ((N + k : ℕ) : ℝ) ≤ ((N + k : ℕ) : ℝ) + 1 := by linarith
    have hcL : (∫ x in ((N + k : ℕ) : ℝ)..(((N + k : ℕ) : ℝ) + 1),
          ((Int.fract x - 1 / 2 : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1))
        = ∫ x in ((N + k : ℕ) : ℝ)..(((N + k : ℕ) : ℝ) + 1),
            ((x - ((N + k : ℕ) : ℝ) - 1 / 2 : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1) := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [fract_ae_sub (N + k)] with x hx
      intro hxu
      rw [Set.uIoc_of_le hle] at hxu
      rw [hx hxu]
    have hcR : (∫ x in ((N + k : ℕ) : ℝ)..(((N + k : ℕ) : ℝ) + 1),
          ((((Int.fract x) ^ 2 - Int.fract x) / 2 : ℝ) : ℂ)
            * ((-s - 1) * (x : ℂ) ^ (-s - 1 - 1)))
        = ∫ x in ((N + k : ℕ) : ℝ)..(((N + k : ℕ) : ℝ) + 1),
            ((((x - ((N + k : ℕ) : ℝ)) ^ 2 - (x - ((N + k : ℕ) : ℝ))) / 2 : ℝ) : ℂ)
              * ((-s - 1) * (x : ℂ) ^ (-s - 1 - 1)) := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [fract_ae_sub (N + k)] with x hx
      intro hxu
      rw [Set.uIoc_of_le hle] at hxu
      rw [hx hxu]
    rw [hcL, hcR]
    exact sawtooth_ibp_unit hm1 s
  have hsL := intervalIntegral.sum_integral_adjacent_intervals
    (f := fun x : ℝ => ((Int.fract x - 1 / 2 : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1))
    (a := a) (n := M - N)
    (fun k _ => by
      rw [hak k, hak1 k]
      exact hintL (N + k) (le_add_right hN))
  have hsR := intervalIntegral.sum_integral_adjacent_intervals
    (f := fun x : ℝ => ((((Int.fract x) ^ 2 - Int.fract x) / 2 : ℝ) : ℂ)
        * ((-s - 1) * (x : ℂ) ^ (-s - 1 - 1)))
    (a := a) (n := M - N)
    (fun k _ => by
      rw [hak k, hak1 k]
      exact hintR (N + k) (le_add_right hN))
  have hstart : a 0 = (N : ℝ) := by simp only [ha]; simp
  have hend : a (M - N) = (M : ℝ) := by
    simp only [ha]
    rw [Nat.cast_sub hNM]
    ring
  rw [hstart, hend] at hsL hsR
  rw [← hsL, ← hsR, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl (fun k hk => hperk k (Finset.mem_range.mp hk))

/-! ## The centred representation on `Re s > 0` -/

/-- **Centring the sawtooth tail.**  On `Re s > 0`,
`∫_N^∞ {u} u^{-s-1} du = N^{-s}/(2s) + (s+1) ∫_N^∞ B₂({u}) u^{-s-2} du`. -/
theorem zetaSawtoothTail_eq_half_add_bernoulli (hN : 1 ≤ N) {s : ℂ} (hs : 0 < s.re) :
    zetaSawtoothTail N s = (N : ℂ) ^ (-s) / (2 * s) + (s + 1) * zetaBernoulliTail N s := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hs0 : s ≠ 0 := by
    intro h
    rw [h] at hs
    simp at hs
  have hre : (-s - 1).re < -1 := by
    simp only [Complex.sub_re, Complex.neg_re, Complex.one_re]
    linarith
  have hf1 := integrableOn_sawtooth_cpow hs hN
  have hcpow : IntegrableOn (fun u : ℝ => (u : ℂ) ^ (-s - 1)) (Set.Ioi (N : ℝ)) :=
    integrableOn_Ioi_cpow_of_lt hre hN0
  have hc : IntegrableOn (fun u : ℝ => (1 / 2 : ℂ) * (u : ℂ) ^ (-s - 1)) (Set.Ioi (N : ℝ)) :=
    hcpow.const_mul _
  have hgint : IntegrableOn
      (fun u : ℝ => ((Int.fract u - 1 / 2 : ℝ) : ℂ) * (u : ℂ) ^ (-s - 1)) (Set.Ioi (N : ℝ)) := by
    refine (hf1.sub hc).congr_fun ?_ measurableSet_Ioi
    intro u _
    simp only [Pi.sub_apply]
    push_cast
    ring
  have hbint := integrableOn_bernoulli_cpow (s := s) (by linarith) hN
  have hsplit : zetaSawtoothTail N s
      = (∫ u in Set.Ioi (N : ℝ), (1 / 2 : ℂ) * (u : ℂ) ^ (-s - 1))
        + ∫ u in Set.Ioi (N : ℝ), ((Int.fract u - 1 / 2 : ℝ) : ℂ) * (u : ℂ) ^ (-s - 1) := by
    unfold zetaSawtoothTail
    rw [← integral_add hc hgint]
    refine setIntegral_congr_fun measurableSet_Ioi ?_
    intro u _
    push_cast
    ring
  have hconst : (∫ u in Set.Ioi (N : ℝ), (1 / 2 : ℂ) * (u : ℂ) ^ (-s - 1))
      = (N : ℂ) ^ (-s) / (2 * s) := by
    rw [MeasureTheory.integral_const_mul, integral_Ioi_cpow_of_lt hre hN0]
    have h1 : (-s - 1 + 1) = -s := by ring
    rw [h1]
    push_cast
    field_simp
  have hlim : (∫ u in Set.Ioi (N : ℝ), ((Int.fract u - 1 / 2 : ℝ) : ℂ) * (u : ℂ) ^ (-s - 1))
      = (s + 1) * zetaBernoulliTail N s := by
    have hL : Tendsto
        (fun M : ℕ => ∫ x in (N : ℝ)..(M : ℝ),
          ((Int.fract x - 1 / 2 : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1))
        atTop (nhds (∫ u in Set.Ioi (N : ℝ),
          ((Int.fract u - 1 / 2 : ℝ) : ℂ) * (u : ℂ) ^ (-s - 1))) :=
      intervalIntegral_tendsto_integral_Ioi (N : ℝ) hgint tendsto_natCast_atTop_atTop
    have hR : Tendsto
        (fun M : ℕ => (s + 1) * ∫ x in (N : ℝ)..(M : ℝ),
          ((bernoulliPeriodic x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1 - 1))
        atTop (nhds ((s + 1) * zetaBernoulliTail N s)) :=
      (intervalIntegral_tendsto_integral_Ioi (N : ℝ) hbint
        tendsto_natCast_atTop_atTop).const_mul (s + 1)
    have heq : ∀ᶠ M : ℕ in atTop,
        (s + 1) * (∫ x in (N : ℝ)..(M : ℝ),
          ((bernoulliPeriodic x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1 - 1))
        = ∫ x in (N : ℝ)..(M : ℝ), ((Int.fract x - 1 / 2 : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1) := by
      filter_upwards [Filter.eventually_ge_atTop N] with M hM
      rw [sawtooth_ibp_sum_from hN hM s, ← intervalIntegral.integral_const_mul,
        ← intervalIntegral.integral_neg]
      refine intervalIntegral.integral_congr (fun x _ => ?_)
      simp only [bernoulliPeriodic]
      push_cast
      ring
    exact tendsto_nhds_unique hL (hR.congr' heq)
  rw [hsplit, hconst, hlim]

/-- The centred truncated representation
`Σ_{n ≤ N} n^{-s} + N^{1-s}/(s-1) - N^{-s}/2 - s(s+1) ∫_N^∞ B₂({u}) u^{-s-2} du`. -/
def zetaCentredTruncated (N : ℕ) (s : ℂ) : ℂ :=
  (∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s))
    + (N : ℂ) ^ (1 - s) / (s - 1) - (N : ℂ) ^ (-s) / 2
    - s * (s + 1) * zetaBernoulliTail N s

/-- The centred representation agrees with `ζ` on `Re s > 0`, `s ≠ 1`. -/
theorem zeta_eq_centredTruncated_of_re_pos (hN : 1 ≤ N) {s : ℂ}
    (hs0 : 0 < s.re) (hs1 : s ≠ 1) :
    riemannZeta s = zetaCentredTruncated N s := by
  have hs : s ≠ 0 := by
    intro h
    rw [h] at hs0
    simp at hs0
  rw [zeta_eq_truncated_of_re_pos hN hs0 hs1, zetaTruncated, zetaCentredTruncated,
    zetaSawtoothTail_eq_half_add_bernoulli hN hs0]
  field_simp
  ring

/-! ## Continuation to `Re s > -1` -/

/-- The centred representation is differentiable on `Re s > -1`, `s ≠ 1`. -/
theorem differentiableAt_zetaCentredTruncated (hN : 1 ≤ N) {z : ℂ}
    (hz0 : -1 < z.re) (hz1 : z ≠ 1) :
    DifferentiableAt ℂ (zetaCentredTruncated N) z := by
  have hNne : (N : ℂ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  have hsum : DifferentiableAt ℂ
      (fun s : ℂ => ∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s)) z := by
    apply DifferentiableAt.fun_sum
    intro n hn
    rw [Finset.mem_Icc] at hn
    exact DifferentiableAt.const_cpow (differentiable_id.neg).differentiableAt
      (Or.inl (by exact_mod_cast (by omega : n ≠ 0)))
  have hpole : DifferentiableAt ℂ
      (fun s : ℂ => (N : ℂ) ^ (1 - s) / (s - 1)) z := by
    apply DifferentiableAt.div
    · exact DifferentiableAt.const_cpow
        ((differentiable_const 1).sub differentiable_id).differentiableAt (Or.inl hNne)
    · exact (differentiable_id.sub_const 1).differentiableAt
    · exact sub_ne_zero.2 hz1
  have hhalf : DifferentiableAt ℂ (fun s : ℂ => (N : ℂ) ^ (-s) / 2) z :=
    (DifferentiableAt.const_cpow (differentiable_id.neg).differentiableAt
      (Or.inl hNne)).div_const 2
  have htail : DifferentiableAt ℂ
      (fun s : ℂ => s * (s + 1) * zetaBernoulliTail N s) z :=
    (differentiableAt_id.mul (differentiableAt_id.add_const 1)).mul
      (differentiableAt_zetaBernoulliTail hN hz0)
  exact ((hsum.add hpole).sub hhalf).sub htail

/-- The punctured half-plane `Re s > -1`, `s ≠ 1` is preconnected. -/
theorem isPreconnected_halfplane_neg_one_punctured :
    IsPreconnected ({z : ℂ | -1 < z.re} \ {1}) := by
  have hre : IsLinearMap ℝ Complex.re :=
    ⟨fun a b => Complex.add_re a b, fun r z => Complex.smul_re r z⟩
  have him : IsLinearMap ℝ Complex.im :=
    ⟨fun a b => Complex.add_im a b, fun r z => Complex.smul_im r z⟩
  have hA : Convex ℝ {z : ℂ | 1 < z.re} := convex_halfSpace_gt hre 1
  have hB : Convex ℝ ({z : ℂ | -1 < z.re} ∩ {z : ℂ | 0 < z.im}) :=
    (convex_halfSpace_gt hre (-1)).inter (convex_halfSpace_gt him 0)
  have hC : Convex ℝ ({z : ℂ | -1 < z.re} ∩ {z : ℂ | z.im < 0}) :=
    (convex_halfSpace_gt hre (-1)).inter (convex_halfSpace_lt him 0)
  have hD : Convex ℝ ({z : ℂ | -1 < z.re} ∩ {z : ℂ | z.re < 1}) :=
    (convex_halfSpace_gt hre (-1)).inter (convex_halfSpace_lt hre 1)
  have hcover : ({z : ℂ | -1 < z.re} \ {1})
      = (({z : ℂ | 1 < z.re}
          ∪ ({z : ℂ | -1 < z.re} ∩ {z : ℂ | 0 < z.im}))
        ∪ ({z : ℂ | -1 < z.re} ∩ {z : ℂ | z.im < 0}))
        ∪ ({z : ℂ | -1 < z.re} ∩ {z : ℂ | z.re < 1}) := by
    ext z
    simp only [Set.mem_sdiff, Set.mem_setOf_eq, Set.mem_singleton_iff,
      Set.mem_union, Set.mem_inter_iff]
    constructor
    · rintro ⟨hre0, hne1⟩
      rcases lt_trichotomy z.im 0 with him | him | him
      · exact Or.inl (Or.inr ⟨hre0, him⟩)
      · rcases lt_trichotomy z.re 1 with hre1 | hre1 | hre1
        · exact Or.inr ⟨hre0, hre1⟩
        · exfalso
          apply hne1
          apply Complex.ext
          · simpa using hre1
          · simpa using him
        · exact Or.inl (Or.inl (Or.inl hre1))
      · exact Or.inl (Or.inl (Or.inr ⟨hre0, him⟩))
    · rintro (((h | ⟨h1, h2⟩) | ⟨h1, h2⟩) | ⟨h1, h2⟩)
      · refine ⟨by linarith, fun he => ?_⟩
        rw [he] at h
        simp at h
      · refine ⟨h1, fun he => ?_⟩
        rw [he] at h2
        simp at h2
      · refine ⟨h1, fun he => ?_⟩
        rw [he] at h2
        simp at h2
      · refine ⟨h1, fun he => ?_⟩
        rw [he] at h2
        simp at h2
  rw [hcover]
  have hx₁ : (2 + Complex.I) ∈ {z : ℂ | 1 < z.re}
      ∩ ({z : ℂ | -1 < z.re} ∩ {z : ℂ | 0 < z.im}) := by
    refine ⟨?_, ?_, ?_⟩ <;>
      norm_num [Complex.add_re, Complex.add_im, Complex.I_re, Complex.I_im]
  have hAB := IsPreconnected.union (2 + Complex.I) hx₁.1 hx₁.2
    hA.isPreconnected hB.isPreconnected
  have hx₂ : (2 - Complex.I) ∈ ({z : ℂ | 1 < z.re}
        ∪ ({z : ℂ | -1 < z.re} ∩ {z : ℂ | 0 < z.im}))
      ∩ ({z : ℂ | -1 < z.re} ∩ {z : ℂ | z.im < 0}) := by
    refine ⟨Or.inl ?_, ⟨?_, ?_⟩⟩ <;>
      norm_num [Complex.sub_re, Complex.sub_im, Complex.I_re, Complex.I_im]
  have hABC := IsPreconnected.union (2 - Complex.I) hx₂.1 hx₂.2
    hAB hC.isPreconnected
  have hx₃ : ((1 / 2 : ℝ) + Complex.I) ∈ (({z : ℂ | 1 < z.re}
        ∪ ({z : ℂ | -1 < z.re} ∩ {z : ℂ | 0 < z.im}))
        ∪ ({z : ℂ | -1 < z.re} ∩ {z : ℂ | z.im < 0}))
      ∩ ({z : ℂ | -1 < z.re} ∩ {z : ℂ | z.re < 1}) := by
    refine ⟨Or.inl (Or.inr ⟨?_, ?_⟩), ⟨?_, ?_⟩⟩ <;>
      norm_num [Complex.add_re, Complex.add_im, Complex.I_re, Complex.I_im]
  exact IsPreconnected.union ((1 / 2 : ℝ) + Complex.I) hx₃.1 hx₃.2
    hABC hD.isPreconnected

set_option maxHeartbeats 800000 in
/-- **The centred representation continues `ζ` to `Re s > -1`, `s ≠ 1`.**  Both sides are analytic
on the punctured half-plane, agree on `Re s > 0`, and the punctured half-plane is preconnected. -/
theorem zeta_eq_centredTruncated_of_re_gt_neg_one (hN : 1 ≤ N) {s : ℂ}
    (hs0 : -1 < s.re) (hs1 : s ≠ 1) :
    riemannZeta s = zetaCentredTruncated N s := by
  have hU : IsOpen ({z : ℂ | -1 < z.re} \ {1}) :=
    (isOpen_lt continuous_const Complex.continuous_re).sdiff isClosed_singleton
  have hζ : AnalyticOnNhd ℂ riemannZeta ({z : ℂ | -1 < z.re} \ {1}) := by
    apply DifferentiableOn.analyticOnNhd _ hU
    intro z hz
    exact (differentiableAt_riemannZeta hz.2).differentiableWithinAt
  have htr : AnalyticOnNhd ℂ (zetaCentredTruncated N) ({z : ℂ | -1 < z.re} \ {1}) := by
    apply DifferentiableOn.analyticOnNhd _ hU
    intro z hz
    exact (differentiableAt_zetaCentredTruncated hN hz.1 hz.2).differentiableWithinAt
  have h2mem : (2 : ℂ) ∈ ({z : ℂ | -1 < z.re} \ {1}) := by
    constructor
    · norm_num
    · simp only [Set.mem_singleton_iff]
      intro h
      have := congrArg Complex.re h
      simp at this
  have hev : riemannZeta =ᶠ[nhds (2 : ℂ)] zetaCentredTruncated N := by
    have hmem : ({z : ℂ | 0 < z.re} \ {1}) ∈ nhds (2 : ℂ) := by
      apply IsOpen.mem_nhds
        ((isOpen_lt continuous_const Complex.continuous_re).sdiff isClosed_singleton)
      constructor
      · simp
      · simp only [Set.mem_singleton_iff]
        intro h
        have := congrArg Complex.re h
        simp at this
    filter_upwards [hmem] with z hz
    exact zeta_eq_centredTruncated_of_re_pos hN hz.1 hz.2
  exact hζ.eqOn_of_preconnected_of_eventuallyEq htr
    isPreconnected_halfplane_neg_one_punctured h2mem hev
    ⟨hs0, by simpa using hs1⟩

/-! ## The additive boundary value at `s = 0` -/

/-- At `s = 0` with `N = 1` the centred representation is `1 - 1 - 1/2 = -1/2`. -/
theorem zetaCentredTruncated_one_zero : zetaCentredTruncated 1 0 = -1 / 2 := by
  unfold zetaCentredTruncated
  simp
  norm_num

/-- `ζ(0) = -1/2`, recovered from the additive side: the constant `-1/2 = -B₁` is the value of the
centred sawtooth representation at `s = 0`. -/
theorem riemannZeta_zero_of_centred : riemannZeta 0 = -1 / 2 := by
  rw [zeta_eq_centredTruncated_of_re_gt_neg_one (N := 1) le_rfl (by simp) (by norm_num),
    zetaCentredTruncated_one_zero]

end RHTower
