import GaloisForLFunctions.BlackHoleRingdown.TailEnergy.FixedStepContractionFalsification

/-!
# The return that the other scattering paths must cancel

In the Gram expansion of Gabet, Ferreira Da Costa and Lee
(arXiv:2611.18900, §4), discarding cross terms retains the individual
path intensities. At the modular cusp, the same prime-power path recurs
at arbitrarily late times with unchanged amplitude. After subtracting
the exact mean, the other paths must converge to its negative.
-/

noncomputable section
open Complex MeasureTheory Set Filter Topology Finset
namespace GaloisForLFunctions.BlackHoleRingdown.ReturnCancellation

/-- Response to a single unit-weight bounce at time zero. -/
def bounce (h : CompactPulse) (u : ℝ) : ℂ :=
  ∫ v in Ioi (0 : ℝ), h (u-v)*((bounceKernel v : ℝ) : ℂ)

/-- Individual summand in the physical field. -/
def path (h : CompactPulse) (c : ℕ) (t : ℝ) : ℂ :=
  (echoWeight c : ℂ) * bounce h (t-echoDelay c)

/-- Every compact pulse, including pulses with nonzero mean, has an exact
finite return expansion after the explicit growing term is restored. -/
theorem finite_return_sum (h : CompactPulse) {S B t : ℝ}
    (hs : ∀ s : ℝ, S < |s| → h s = 0) (ht : t ≤ B) :
    ∑ c ∈ Icc 1 (pathReturnCutoff (B+S)), path h c t =
      pulseReflected h t + meanCoefficient h * cexp ((t : ℂ)/2) := by
  rw [← h.pulseEcho_eq, pulseEcho]
  let F := Finset.Icc 1 (pathReturnCutoff (B+S))
  have hpt (w : ℝ) : h (t-w) * (echoKernel w : ℂ) =
      ∑ c ∈ F, h (t-w) * (echoTerm c w : ℂ) := by
    by_cases hw : w ≤ B+S
    · rw [echoKernel_eq_finset_sum_of_le hw, Complex.ofReal_sum, Finset.mul_sum]
    · have hh : S < |t-w| := by
        rw [abs_sub_comm]
        exact (by linarith : S < w-t).trans_le (le_abs_self _)
      simp [hs _ hh]
  simp_rw [hpt]
  rw [integral_finsetSum F fun c _ => integrable_pulse_mul_echoTerm h c t]
  exact sum_congr rfl fun c _ => (integral_pulse_mul_echoTerm_eq_bounce h c t).symm

/-- A cutoff containing the selected denominator even when the sampled
bounce time is negative. -/
def denominators (S u : ℝ) (c : ℕ) : Finset ℕ :=
  Icc 1 (pathReturnCutoff (echoDelay c+max u 0+S))

private theorem mem_denominators {c : ℕ} (hc : 0 < c) (u : ℝ) {S : ℝ} (hS : 0 ≤ S) :
    c ∈ denominators S u c := by
  refine mem_Icc.mpr ⟨hc, ?_⟩
  have hc' : (0 : ℝ) < c := Nat.cast_pos.mpr hc
  have he : (c : ℝ) ≤ Real.exp ((echoDelay c+max u 0+S)/2) := by
    calc (c : ℝ) = Real.exp (Real.log c) := (Real.exp_log hc').symm
         _ ≤ _ := Real.exp_le_exp.mpr (by unfold echoDelay; linarith only [le_max_right u 0,hS])
  exact Nat.cast_le.mp (he.trans (Nat.le_ceil _))

/-- All other paths at the selected arrival, after removing the mean. -/
def others (h : CompactPulse) (S u : ℝ) (c : ℕ) : ℂ :=
  (∑ m ∈ (denominators S u c).erase c, path h m (echoDelay c+u)) -
    meanCoefficient h * cexp (((echoDelay c+u : ℝ) : ℂ)/2)

/-- Exact cancellation error, before taking a limit or bounding the field. -/
theorem erase_one_return (h : CompactPulse) {S : ℝ} (hS : 0 ≤ S)
    (hs : ∀ s : ℝ, S < |s| → h s = 0) (u : ℝ) {c : ℕ} (hc : 0 < c) :
    others h S u c + (echoWeight c : ℂ)*bounce h u = pulseReflected h (echoDelay c+u) := by
  have he := finite_return_sum h hs (by linarith only [le_max_left u 0] :
    echoDelay c+u ≤ echoDelay c+max u 0)
  change (∑ m ∈ denominators S u c, path h m (echoDelay c+u)) = _ at he
  rw [← sum_erase_add _ _ (mem_denominators hc u hS)] at he
  have hpath : path h c (echoDelay c+u) = (echoWeight c : ℂ)*bounce h u := by
    rw [path, add_sub_cancel_left]
  rw [hpath] at he
  unfold others
  linear_combination he

/-- Each prime furnishes an infinite geometric sequence of tests. At every
known decay rate the remaining signed paths cancel the *same* wave with
geometrically decreasing error in the prime-power index. -/
theorem prime_power_cancellation_rate (h : CompactPulse) {σ : ℝ} (hσ : 0 < σ)
    (hσ' : σ < 3001/48000) {S : ℝ} (hS : 0 ≤ S)
    (hs : ∀ s : ℝ, S < |s| → h s = 0) {p : ℕ} (hp : p.Prime) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : ℝ) (k : ℕ), 1 ≤ k → 0 ≤ echoDelay (p^k)+u →
      ‖others h S u (p^k) + ((1-1/(p : ℝ) : ℝ) : ℂ)*bounce h u‖ ≤
        C * Real.exp (-σ*u) * (Real.exp (-2*σ*Real.log p))^k := by
  obtain ⟨C,hC,hfield,_⟩ := (unconditional_cusp_escape_sub_seven_eighths hσ hσ' h).2
  refine ⟨C,hC,fun u k hk ht => ?_⟩
  obtain ⟨hd,hw⟩ := echoDelay_and_weight_prime_pow hp hk
  rw [← hw, erase_one_return h hS hs u (pow_pos hp.pos _)]
  refine (hfield _ ht).trans_eq ?_
  rw [hd, ← Real.exp_nat_mul, mul_assoc, ← Real.exp_add]
  congr 2
  ring

/-- A nonzero mean-zero pulse has a nonzero single-bounce waveform.
Hence the forced cancellation is nontrivial for every such pulse. -/
theorem exists_nonzero_bounce (h : CompactPulse) (hm : meanCoefficient h = 0)
    (hne : ∃ s : ℝ, h s ≠ 0) : ∃ u : ℝ, bounce h u ≠ 0 := by
  by_contra! hall
  obtain ⟨S,_,hs⟩ := h.exists_support_bound
  have hz (t : ℝ) : pulseReflected h t = 0 := by
    have he := finite_return_sum (B := t) h hs le_rfl
    simpa [path, hall, hm] using he.symm
  have he := tailEnergy_pos h hne 0
  simp [tailEnergy, hz] at he

/-- Along every prime-power tower the remaining paths converge to the
negative of the individual path. The same base time works for every prime. -/
theorem prime_power_cancellation_limit (h : CompactPulse) {S : ℝ} (hS : 0 ≤ S)
    (hs : ∀ s : ℝ, S < |s| → h s = 0) {p : ℕ} (hp : p.Prime) (u : ℝ) :
    Tendsto (fun k : ℕ => others h S u (p^k)) atTop
      (𝓝 (-(((1-1/(p : ℝ) : ℝ) : ℂ)*bounce h u))) := by
  let σ : ℝ := 1/32
  have hσ : 0 < σ := by norm_num [σ]
  obtain ⟨C,_,hC⟩ := prime_power_cancellation_rate h hσ (by norm_num [σ]) hS hs hp
  have hlog : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  let a := Real.exp (-2*σ*Real.log p)
  have ha : a < 1 := Real.exp_lt_one_iff.mpr (by nlinarith only [mul_pos hσ hlog])
  have hpow := tendsto_pow_atTop_nhds_zero_of_lt_one (Real.exp_pos _).le ha
  have htime : Tendsto (fun k : ℕ => (k : ℝ)*(2*Real.log p)+u) atTop atTop :=
    tendsto_atTop_add_const_right _ _ ((tendsto_mul_const_atTop_of_pos (by positivity)).mpr
      tendsto_natCast_atTop_atTop)
  have hb : Tendsto (fun k : ℕ => C*Real.exp (-σ*u)*a^k) atTop (𝓝 0) := by
    simpa using hpow.const_mul (C*Real.exp (-σ*u))
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [hb.eventually_lt_const hε, eventually_ge_atTop 1,
    htime.eventually_ge_atTop 0] with k hk hk1 hlate
  have ht : 0 ≤ echoDelay (p^k)+u := by
    rw [(echoDelay_and_weight_prime_pow hp hk1).1]
    linarith only [hlate]
  rw [dist_eq_norm, sub_neg_eq_add]
  exact (hC u k hk1 ht).trans_lt hk

#print axioms finite_return_sum
#print axioms erase_one_return
#print axioms prime_power_cancellation_rate
#print axioms exists_nonzero_bounce
#print axioms prime_power_cancellation_limit
end GaloisForLFunctions.BlackHoleRingdown.ReturnCancellation
