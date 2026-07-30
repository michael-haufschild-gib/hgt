import GaloisForLFunctions.RHTower.HighExponentShellClockMoments
import GaloisForLFunctions.RHTower.MobiusIncidenceClockGiniFisherFourUnit

/-!
# The critical clock law of a high-exponent shell

The shell Gibbs law `P_{m,σ}(n) = a_m(n) n^{-σ} / S_m(σ)` is a genuine probability mass function
on `ℕ` for `σ > 1`, and its rescaled logarithmic clock `(σ-1)·log n` converges weakly, as
`σ ↓ 1`, to the unit-rate exponential law:

* `RHTower.charFun_shellClockProbabilityMeasure` — the characteristic function of the shell clock
  is the shell-source ratio `S_m(σ - i t(σ-1)) / S_m(σ)`;
* `RHTower.tendsto_charFun_shellClockProbabilityMeasure` — it converges to `(1 - it)⁻¹`, the
  characteristic function of `Exp(1)`, because `S_m = U_m·(z-1)⁻¹` with `U_m` analytic and nonzero
  at the pole;
* `RHTower.tendsto_shellClockProbabilityMeasure` — hence weak convergence to the same unit-rate
  exponential law that the squarefree Möbius source selects;
* `RHTower.tendsto_shellGapProbabilityMeasure` — the oriented gap of two independent shell clocks
  converges weakly to the universal Laplace gap law.

The shell supports are pairwise disjoint, so this is an infinite orthogonal family of positive
arithmetic sources with one common critical clock.
-/

noncomputable section

namespace RHTower

open Complex MeasureTheory Set Filter
open scoped BigOperators Topology ENNReal NNReal LSeries.notation

/-! ## The shell Gibbs mass -/

/-- The unnormalised shell Gibbs mass `a_m(n) n^{-σ}`. -/
def shellMass (m : ℕ) (σ : ℝ) (n : ℕ) : ℝ := (shellIndicator m n : ℝ) * (((n : ℝ)) ^ σ)⁻¹

theorem shellMass_nonneg (m : ℕ) (σ : ℝ) (n : ℕ) : 0 ≤ shellMass m σ n := by
  have hInd : (0 : ℝ) ≤ (shellIndicator m n : ℝ) := by
    rcases shellIndicator_eq_zero_or_one m n with h | h <;> rw [h] <;> norm_num
  have hpow : (0 : ℝ) ≤ (((n : ℝ)) ^ σ)⁻¹ := by positivity
  exact mul_nonneg hInd hpow

theorem summable_shellMass (m : ℕ) {σ : ℝ} (hσ : 1 < σ) : Summable (shellMass m σ) := by
  have hmaj : Summable (fun n : ℕ => |Real.log n| ^ 0 * (n : ℝ) ^ (-σ)) :=
    summable_abs_log_natCast_pow_mul_rpow_neg 0 σ hσ
  refine Summable.of_nonneg_of_le (shellMass_nonneg m σ) (fun n => ?_) hmaj
  have hrw : |Real.log n| ^ 0 * (n : ℝ) ^ (-σ) = (((n : ℝ)) ^ σ)⁻¹ := by
    rw [pow_zero, one_mul, Real.rpow_neg (Nat.cast_nonneg n)]
  rw [hrw, shellMass]
  have hInd : (shellIndicator m n : ℝ) ≤ 1 := by
    rcases shellIndicator_eq_zero_or_one m n with h | h <;> rw [h] <;> norm_num
  have hpow : (0 : ℝ) ≤ (((n : ℝ)) ^ σ)⁻¹ := by positivity
  nlinarith

theorem tsum_shellMass {m : ℕ} (hm : m ≠ 0) {σ : ℝ} (hσ : 1 < σ) :
    ∑' n : ℕ, shellMass m σ n = shellMellin m σ := (shellMellin_eq_tsum hm hσ).symm

/-- The smallest member of the `m`-th shell is `2^m`. -/
theorem shellIndicator_two_pow (m : ℕ) : shellIndicator m (2 ^ m) = 1 := by
  rw [shellIndicator_eq_one_iff]
  refine ⟨?_, ?_⟩
  · intro p hp hdvd
    have hpdvd : p ∣ 2 ^ m := (dvd_pow_self p (Nat.succ_ne_zero m)).trans hdvd
    have hp2 : p = 2 :=
      (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hpdvd)
    subst hp2
    have hle : m + 1 ≤ m :=
      (Nat.pow_dvd_pow_iff_le_right (by norm_num : (1 : ℕ) < 2)).mp hdvd
    omega
  · intro h
    exact h 2 Nat.prime_two dvd_rfl

theorem shellMellin_pos {m : ℕ} (hm : m ≠ 0) {σ : ℝ} (hσ : 1 < σ) : 0 < shellMellin m σ := by
  rw [← tsum_shellMass hm hσ]
  refine Summable.tsum_pos (summable_shellMass m hσ) (shellMass_nonneg m σ) (2 ^ m) ?_
  rw [shellMass, shellIndicator_two_pow m]
  push_cast
  positivity

/-- The normalised shell Gibbs probability. -/
def shellProbability (m : ℕ) (σ : ℝ) (n : ℕ) : ℝ := shellMass m σ n / shellMellin m σ

theorem shellProbability_nonneg {m : ℕ} (hm : m ≠ 0) {σ : ℝ} (hσ : 1 < σ) (n : ℕ) :
    0 ≤ shellProbability m σ n :=
  div_nonneg (shellMass_nonneg m σ n) (shellMellin_pos hm hσ).le

theorem hasSum_shellProbability {m : ℕ} (hm : m ≠ 0) {σ : ℝ} (hσ : 1 < σ) :
    HasSum (shellProbability m σ) 1 := by
  have hsum := (summable_shellMass m hσ).hasSum.div_const (shellMellin m σ)
  rw [tsum_shellMass hm hσ, div_self (shellMellin_pos hm hσ).ne'] at hsum
  exact hsum

/-! ## The shell clock as a probability measure -/

private def shellCriticalPMFOf (m : ℕ) (hm : m ≠ 0) (σ : ℝ) (hσ : 1 < σ) : PMF ℕ := by
  refine ⟨fun n => ENNReal.ofReal (shellProbability m σ n), ?_⟩
  apply ENNReal.hasSum_coe.mpr
  rw [← ENNReal.toNNReal_one]
  simpa using (hasSum_shellProbability hm hσ).toNNReal (shellProbability_nonneg hm hσ)

/-- The shell probability mass function, extended harmlessly off its natural half-plane so it can
be used as a filter-indexed family. -/
def shellCriticalPMF (m : ℕ) (σ : ℝ) : PMF ℕ :=
  if h : m ≠ 0 ∧ 1 < σ then shellCriticalPMFOf m h.1 σ h.2 else PMF.pure 1

theorem shellCriticalPMF_toReal {m : ℕ} (hm : m ≠ 0) {σ : ℝ} (hσ : 1 < σ) (n : ℕ) :
    (shellCriticalPMF m σ n).toReal = shellProbability m σ n := by
  rw [shellCriticalPMF, dif_pos ⟨hm, hσ⟩]
  change (ENNReal.ofReal (shellProbability m σ n)).toReal = _
  rw [ENNReal.toReal_ofReal (shellProbability_nonneg hm hσ n)]

/-- The shell index law as a probability measure on `ℕ`. -/
def shellIndexProbabilityMeasure (m : ℕ) (σ : ℝ) : ProbabilityMeasure ℕ :=
  ⟨(shellCriticalPMF m σ).toMeasure, inferInstance⟩

/-- The rescaled logarithmic shell clock. -/
def shellClock (σ : ℝ) (n : ℕ) : ℝ := (σ - 1) * Real.log n

/-- The shell clock as a Borel probability measure on `ℝ`. -/
def shellClockProbabilityMeasure (m : ℕ) (σ : ℝ) : ProbabilityMeasure ℝ :=
  ProbabilityMeasure.map (shellIndexProbabilityMeasure m σ)
    (Measurable.of_discrete.aemeasurable :
      AEMeasurable (shellClock σ) (shellCriticalPMF m σ).toMeasure)

/-! ## The characteristic function -/

private theorem integrable_shellClock_char (m : ℕ) (σ t : ℝ) :
    Integrable (fun n : ℕ => Complex.exp (((t * shellClock σ n : ℝ) : ℂ) * Complex.I))
      (shellCriticalPMF m σ).toMeasure := by
  refine (integrable_const (1 : ℝ)).mono' Measurable.of_discrete.aestronglyMeasurable ?_
  filter_upwards with n
  rw [Complex.norm_exp]
  simp [Complex.mul_re]

theorem charFun_shellClockProbabilityMeasure_eq_tsum {m : ℕ} (hm : m ≠ 0) {σ : ℝ} (hσ : 1 < σ)
    (t : ℝ) :
    charFun (shellClockProbabilityMeasure m σ : Measure ℝ) t =
      ∑' n : ℕ, (shellProbability m σ n : ℂ) *
        Complex.exp (((t * shellClock σ n : ℝ) : ℂ) * Complex.I) := by
  rw [charFun_apply_real]
  unfold shellClockProbabilityMeasure shellIndexProbabilityMeasure ProbabilityMeasure.map
  simp only [ProbabilityMeasure.coe_mk]
  rw [integral_map Measurable.of_discrete.aemeasurable (by fun_prop)]
  have hint : Integrable
      (fun n : ℕ => Complex.exp ((t : ℂ) * (shellClock σ n : ℂ) * Complex.I))
      (shellCriticalPMF m σ).toMeasure := by
    convert integrable_shellClock_char m σ t using 1
    funext n
    push_cast
    rfl
  rw [PMF.integral_eq_tsum _ _ hint]
  apply tsum_congr
  intro n
  rw [shellCriticalPMF_toReal hm hσ]
  change (shellProbability m σ n : ℂ) * _ = _
  congr 2
  push_cast
  rfl

private theorem rpow_inv_mul_exp_eq_cpow_inv {σ t : ℝ} {n : ℕ} (hn : n ≠ 0) :
    (((((n : ℝ)) ^ σ)⁻¹ : ℝ) : ℂ) *
        Complex.exp (((t * shellClock σ n : ℝ) : ℂ) * Complex.I)
      = ((n : ℂ) ^ (squarefreeMobiusCriticalClockParameter σ t))⁻¹ := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  have hlog : Complex.log (n : ℂ) = ((Real.log n : ℝ) : ℂ) := by
    rw [← Complex.ofReal_natCast n, ← Complex.ofReal_log hnpos.le]
  have hleft : ((((n : ℝ)) ^ σ)⁻¹ : ℝ) = Real.exp (-(Real.log n * σ)) := by
    rw [Real.rpow_def_of_pos hnpos, ← Real.exp_neg]
  rw [hleft, Complex.ofReal_exp, Complex.cpow_def_of_ne_zero hnC, hlog, ← Complex.exp_neg,
    ← Complex.exp_add]
  congr 1
  unfold squarefreeMobiusCriticalClockParameter shellClock
  push_cast
  ring

/-- **The shell clock characteristic function is a shell-source ratio.** -/
theorem charFun_shellClockProbabilityMeasure {m : ℕ} (hm : m ≠ 0) {σ : ℝ} (hσ : 1 < σ) (t : ℝ) :
    charFun (shellClockProbabilityMeasure m σ : Measure ℝ) t =
      shellSource m (squarefreeMobiusCriticalClockParameter σ t) / (shellMellin m σ : ℂ) := by
  have hparam : 1 < (squarefreeMobiusCriticalClockParameter σ t).re := by
    rw [squarefreeMobiusCriticalClockParameter_re]; exact hσ
  rw [charFun_shellClockProbabilityMeasure_eq_tsum hm hσ]
  have hterm : ∀ n : ℕ,
      (shellProbability m σ n : ℂ) *
          Complex.exp (((t * shellClock σ n : ℝ) : ℂ) * Complex.I) =
        LSeries.term ↗(shellIndicator m) (squarefreeMobiusCriticalClockParameter σ t) n /
          (shellMellin m σ : ℂ) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [LSeries.term, shellProbability, shellMass]
    · rw [LSeries.term_of_ne_zero hn.ne', shellProbability, shellMass, Complex.ofReal_div,
        Complex.ofReal_mul, div_mul_eq_mul_div]
      congr 1
      rw [mul_assoc, rpow_inv_mul_exp_eq_cpow_inv hn.ne', div_eq_mul_inv]
      norm_cast
  rw [tsum_congr hterm, tsum_div_const]
  congr 1
  have hfold : ∑' n : ℕ,
      LSeries.term ↗(shellIndicator m) (squarefreeMobiusCriticalClockParameter σ t) n
      = LSeries ↗(shellIndicator m) (squarefreeMobiusCriticalClockParameter σ t) := rfl
  rw [hfold, LSeries_shellIndicator hm hparam, shellSource]

/-! ## The critical limit -/

/-- **The shell clock has the unit-rate exponential characteristic function in the limit.** -/
theorem tendsto_charFun_shellClockProbabilityMeasure {m : ℕ} (hm : 12 ≤ m) (t : ℝ) :
    Tendsto (fun σ : ℝ => charFun (shellClockProbabilityMeasure m σ : Measure ℝ) t)
      (𝓝[>] (1 : ℝ)) (𝓝 ((1 - (t : ℂ) * Complex.I)⁻¹)) := by
  have hhalf : (1 : ℝ) / 2 < ((1 : ℂ)).re := by norm_num
  have hUana := analyticAt_shellResidueUnit hm hhalf
  have hU1 := shellResidueUnit_one_ne_zero (m := m) (by omega)
  have hq : (1 - (t : ℂ) * Complex.I) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp [Complex.mul_re] at this
  have hofReal : Tendsto (fun σ : ℝ => (σ : ℂ)) (𝓝[>] (1 : ℝ)) (𝓝 (1 : ℂ)) := by
    have h : Tendsto (fun σ : ℝ => (σ : ℂ)) (𝓝 (1 : ℝ)) (𝓝 ((1 : ℝ) : ℂ)) :=
      (Complex.continuous_ofReal.continuousAt).tendsto
    rw [Complex.ofReal_one] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hparam : Tendsto (fun σ : ℝ => squarefreeMobiusCriticalClockParameter σ t)
      (𝓝[>] (1 : ℝ)) (𝓝 (1 : ℂ)) := by
    have hcont : ContinuousAt
        (fun σ : ℝ => squarefreeMobiusCriticalClockParameter σ t) 1 := by
      unfold squarefreeMobiusCriticalClockParameter
      fun_prop
    simpa [squarefreeMobiusCriticalClockParameter] using
      hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hUparam : Tendsto (fun σ : ℝ =>
      shellResidueUnit m (squarefreeMobiusCriticalClockParameter σ t))
      (𝓝[>] (1 : ℝ)) (𝓝 (shellResidueUnit m 1)) :=
    hUana.continuousAt.tendsto.comp hparam
  have hUsigma : Tendsto (fun σ : ℝ => shellResidueUnit m (σ : ℂ))
      (𝓝[>] (1 : ℝ)) (𝓝 (shellResidueUnit m 1)) :=
    hUana.continuousAt.tendsto.comp hofReal
  have hmodel : Tendsto (fun σ : ℝ =>
      shellResidueUnit m (squarefreeMobiusCriticalClockParameter σ t) /
        shellResidueUnit m (σ : ℂ) * (1 - (t : ℂ) * Complex.I)⁻¹)
      (𝓝[>] (1 : ℝ)) (𝓝 ((1 - (t : ℂ) * Complex.I)⁻¹)) := by
    have h := (hUparam.div hUsigma hU1).mul
      (tendsto_const_nhds (x := (1 - (t : ℂ) * Complex.I)⁻¹) (f := 𝓝[>] (1 : ℝ)))
    rw [div_self hU1, one_mul] at h
    exact h
  have hUneEv : ∀ᶠ σ : ℝ in 𝓝[>] (1 : ℝ), shellResidueUnit m (σ : ℂ) ≠ 0 :=
    hofReal.eventually (hUana.continuousAt.eventually_ne hU1)
  refine hmodel.congr' ?_
  filter_upwards [self_mem_nhdsWithin, hUneEv] with σ hσmem hUne
  have hσ : 1 < σ := Set.mem_Ioi.mp hσmem
  have hσ1 : (σ : ℂ) ≠ 1 := by
    intro h
    have : σ = 1 := by simpa using congrArg Complex.re h
    rw [this] at hσ
    exact lt_irrefl 1 hσ
  have hparamOne : squarefreeMobiusCriticalClockParameter σ t ≠ 1 := by
    intro h
    have : σ = 1 := by
      have := congrArg Complex.re h
      rwa [squarefreeMobiusCriticalClockParameter_re, Complex.one_re] at this
    rw [this] at hσ
    exact lt_irrefl 1 hσ
  have hsub : ((σ : ℂ)) - 1 ≠ 0 := sub_ne_zero.mpr hσ1
  have hfactor : squarefreeMobiusCriticalClockParameter σ t - 1
      = ((σ : ℂ) - 1) * (1 - (t : ℂ) * Complex.I) := by
    unfold squarefreeMobiusCriticalClockParameter
    push_cast
    ring
  rw [charFun_shellClockProbabilityMeasure (by omega) hσ, ofReal_shellMellin (by omega) hσ,
    shellSource_eq_of_ne_one hparamOne, shellSource_eq_of_ne_one hσ1, hfactor]
  field_simp

/-- **Unconditional shell critical clock law.**  The rescaled logarithmic shell probability
measures converge weakly to the unit-rate exponential law as `σ → 1+`. -/
theorem tendsto_shellClockProbabilityMeasure {m : ℕ} (hm : 12 ≤ m) :
    Tendsto (shellClockProbabilityMeasure m) (𝓝[>] (1 : ℝ))
      (𝓝 mobiusCriticalExponentialProbabilityMeasure) := by
  rw [tendsto_iff_seq_tendsto]
  intro σ hσ
  apply ProbabilityMeasure.tendsto_of_tendsto_charFun
  intro t
  have hchar := (tendsto_charFun_shellClockProbabilityMeasure hm t).comp hσ
  rw [charFun_mobiusCriticalExponentialProbabilityMeasure]
  simpa only [Function.comp_apply] using! hchar

/-! ## The oriented gap of two independent shell clocks -/

/-- Oriented difference of two independent shell critical clocks. -/
def shellGapProbabilityMeasure (m : ℕ) (σ : ℝ) : ProbabilityMeasure ℝ :=
  ProbabilityMeasure.map
    ((shellClockProbabilityMeasure m σ).prod (shellClockProbabilityMeasure m σ))
    ((continuous_fst.sub continuous_snd).measurable.aemeasurable)

/-- **The shell gap law converges weakly to the universal Laplace gap law.** -/
theorem tendsto_shellGapProbabilityMeasure {m : ℕ} (hm : 12 ≤ m) :
    Tendsto (shellGapProbabilityMeasure m) (𝓝[>] (1 : ℝ))
      (𝓝 mobiusCriticalExponentialGapProbabilityMeasure) := by
  have hclock := tendsto_shellClockProbabilityMeasure hm
  have hpair : Tendsto
      (fun σ : ℝ => (shellClockProbabilityMeasure m σ, shellClockProbabilityMeasure m σ))
      (𝓝[>] (1 : ℝ))
      (𝓝 (mobiusCriticalExponentialProbabilityMeasure,
        mobiusCriticalExponentialProbabilityMeasure)) :=
    hclock.prodMk_nhds hclock
  have hprod : Tendsto
      (fun σ : ℝ =>
        (shellClockProbabilityMeasure m σ).prod (shellClockProbabilityMeasure m σ))
      (𝓝[>] (1 : ℝ))
      (𝓝 (mobiusCriticalExponentialProbabilityMeasure.prod
        mobiusCriticalExponentialProbabilityMeasure)) :=
    ProbabilityMeasure.continuous_prod.continuousAt.tendsto.comp hpair
  exact (ProbabilityMeasure.continuous_map
    (continuous_fst.sub continuous_snd)).continuousAt.tendsto |>.comp hprod

end RHTower
