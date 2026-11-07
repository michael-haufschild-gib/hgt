import GaloisForLFunctions.TailArithmeticOfThePrimeOrbit.TheFirstReturn
import GaloisForLFunctions.RHTower.Sieve.PrimeCosineSum
import GaloisForLFunctions.RHTower.Sieve.ZetaStripPrimeSum
import GaloisForLFunctions.RHTower.Sieve.MertensSecond
import GaloisForLFunctions.RHTower.ZetaVerticalLineBound
import GaloisForLFunctions.SignedSuccessorArithmetic.TheSignedPrimeDivisorEndpointAtHalfDamping

/-!
# The first return is an extreme value

At the weights `1/p`, where the Euler product sees the pole, alignment of the head is the size of `ζ` just right of the
`1`-line. Let `A_t(N) = Σ_{p≤N} (1 − cos(t log p))/p` be the *harmonic defect* (the squared pretentious distance of `n^{it}`
to `1` up to `N`) and `s_N(t) = 1 + 1/log N + it`.

* **The dictionary** (`abs_harmonicDefect_sub_le`). `|A_t(N) − (log log N − log|ζ(s_N(t))|)| ≤ K` with an absolute
  explicit constant `K`. It combines Mertens' second theorem with the Euler comparison of `Σ_p Re p^{−s}` and `log|ζ(s)|`.
  So a *weak return* (`A_t(N) ≤ C`) at height `t` is the same event as a spike `|ζ(s_N(t))| ≍ log N`, and the first weak
  return is the inverse of the extreme-value function of `ζ` next to the `1`-line.
* **Extreme values from Dirichlet** (`exists_spike_le_pow`). Simultaneous approximation of the primes up to `N` at precision
  `≍ 1/log log N` gives a height `t ≤ Q^{π(N)}`, `Q ≍ √(log log N)`, with `|ζ(s_N(t))| ≥ e^{−1−K} log N`. In `log t` this is
  `log N ≍ log log t`: Littlewood's `Ω`-theorem for `ζ(1 + it)`, read as an upper bound for the first weak return.
* **The pole's price** (`log_log_le_of_isWeakReturn`, `firstReturn_lower`). `|ζ(s)| ≤ M + log(|t| + 1)` on `1 ≤ Re s ≤ 2`,
  `|t| ≥ 1`. So a weak return up to `N` needs `log N ≤ e^{C+K}(M + log(t + 1))`, and a return at precision `η` needs
  `(1 − η) log log N ≤ log(M + log(t + 1)) + O(1)`: `R(N, η) ≥ exp(c(log N)^{1−η})`.
* **Returns escape** (`tendsto_firstReturn_primes`). For `η < 1` the first return on the primes up to `N` tends to infinity
  with `N`. Rank-one flows (`firstReturn_le_of_rankOne`) have it bounded: the primes are not a periodic flow.

The upper bracket `R ≤ exp(C y/log y)` and this lower bracket `exp(c(log y)^{1−η})` are what is proved here. A bound
`|ζ(1 + it)| ≪ (log t)^{2/3}(log log t)^{1/3}` (Vinogradov–Korobov) would raise the lower bracket to
`exp(c(log y)^{3/2}/(log log y)^{1/2})` at bounded harmonic defect through the same dictionary.
-/

open Real Finset Filter Topology

namespace GaloisForLFunctions.TailArithmeticOfThePrimeOrbit

noncomputable section

/-- The harmonic defect `A_t(N) = Σ_{p≤N} (1 − cos(t log p))/p`. -/
def harmonicDefect (N : ℕ) (t : ℝ) : ℝ := ∑ p ∈ Nat.primesLE N, (1 - cos (t * Real.log p)) / (p : ℝ)

/-- A weak return up to `N`: the harmonic defect is at most `C`. -/
def IsWeakReturn (N : ℕ) (C t : ℝ) : Prop := harmonicDefect N t ≤ C

/-- The point `1 + 1/log N + it` next to the `1`-line. -/
def spikePoint (N : ℕ) (t : ℝ) : ℂ := (((1 + 1 / Real.log (N : ℝ) : ℝ) : ℂ) + (t : ℂ) * Complex.I)

/-- The constant of the Euler comparison at the weights `1/p`. -/
def eulerCompConst : ℝ :=
  π ^ 2 / 6 + 2 * (Real.log 2 + 2 * (2 * RHTower.Sieve.mertensFirstConst + 1 / 2)) / Real.log 2 +
    (1 + Real.log 4)

/-- The constant of the dictionary. -/
def harmonicConst : ℝ :=
  |RHTower.Sieve.mertensSecondUpperConst| + |RHTower.Sieve.mertensSecondLowerConst| + eulerCompConst

theorem eulerCompConst_nonneg : 0 ≤ eulerCompConst := by
  have hm := RHTower.Sieve.mertensFirstConst_nonneg
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  unfold eulerCompConst
  positivity

theorem harmonicConst_nonneg : 0 ≤ harmonicConst := by
  have := eulerCompConst_nonneg
  unfold harmonicConst
  positivity

theorem harmonicDefect_eq (N : ℕ) (t : ℝ) :
    harmonicDefect N t = RHTower.Sieve.mertensS N - ∑ p ∈ Nat.primesLE N, cos (t * Real.log p) / (p : ℝ) := by
  unfold harmonicDefect RHTower.Sieve.mertensS
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun p _ => by ring

theorem harmonicDefect_nonneg (N : ℕ) (t : ℝ) : 0 ≤ harmonicDefect N t :=
  Finset.sum_nonneg fun p _ => div_nonneg (by linarith [cos_le_one (t * Real.log p)]) (Nat.cast_nonneg p)

/-- **The dictionary.** The harmonic defect is `log log N − log|ζ(1 + 1/log N + it)|` up to an absolute constant. -/
theorem abs_harmonicDefect_sub_le {N : ℕ} (hN : 3 ≤ N) (t : ℝ) :
    |harmonicDefect N t - (RHTower.Sieve.logLog N - Real.log ‖riemannZeta (spikePoint N t)‖)| ≤
      harmonicConst := by
  have hN3 : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hlogN : 1 ≤ Real.log (N : ℝ) := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    linarith [Real.exp_one_lt_d9]
  have hσ : (1 : ℝ) < 1 + 1 / Real.log (N : ℝ) := by
    have : 0 < 1 / Real.log (N : ℝ) := by positivity
    linarith
  set L := Real.log ‖riemannZeta (spikePoint N t)‖ with hL
  -- Lower comparison: the cosine sum is at least `log |ζ| − C`.
  have htsum := RHTower.Sieve.le_tsum_re_prime_cpow_of_log_le (σ := 1 + 1 / Real.log (N : ℝ)) (t := t)
    (L := L) hσ le_rfl
  have hlo := RHTower.Sieve.sum_cos_div_prime_ge_of_le hN htsum
  -- Upper comparison: the cosine sum is at most `log |ζ| + C`.
  have hhi := SignedSuccessorArithmetic.sum_cos_div_prime_le_of_zeta_upper (z := N) (u := t)
    (B := ‖riemannZeta (spikePoint N t)‖) hN le_rfl
  have hMu := RHTower.Sieve.mertensS_le (N := N) (by omega)
  have hMl := RHTower.Sieve.le_mertensS (N := N) (by omega)
  rw [harmonicDefect_eq, abs_le]
  have hU := le_abs_self RHTower.Sieve.mertensSecondUpperConst
  have hLc := le_abs_self RHTower.Sieve.mertensSecondLowerConst
  have hU0 := abs_nonneg RHTower.Sieve.mertensSecondUpperConst
  have hLc0 := abs_nonneg RHTower.Sieve.mertensSecondLowerConst
  unfold harmonicConst eulerCompConst
  constructor <;> linarith

/-- A weak return is a spike. -/
theorem log_norm_zeta_ge_of_isWeakReturn {N : ℕ} (hN : 3 ≤ N) {C t : ℝ} (h : IsWeakReturn N C t) :
    RHTower.Sieve.logLog N - C - harmonicConst ≤ Real.log ‖riemannZeta (spikePoint N t)‖ := by
  have := (abs_le.mp (abs_harmonicDefect_sub_le hN t)).1
  unfold IsWeakReturn at h
  linarith

/-- A spike is a weak return. -/
theorem isWeakReturn_of_log_norm_zeta_ge {N : ℕ} (hN : 3 ≤ N) {C t : ℝ}
    (h : RHTower.Sieve.logLog N - C ≤ Real.log ‖riemannZeta (spikePoint N t)‖) :
    IsWeakReturn N (C + harmonicConst) t := by
  have := (abs_le.mp (abs_harmonicDefect_sub_le hN t)).2
  unfold IsWeakReturn
  linarith

/-- A return at precision `η` has harmonic defect at most `η Σ 1/p`. -/
theorem harmonicDefect_le_of_isReturn {N : ℕ} {η t : ℝ} (h : IsReturn (Nat.primesLE N) logStep η t) :
    harmonicDefect N t ≤ η * RHTower.Sieve.mertensS N := by
  unfold harmonicDefect RHTower.Sieve.mertensS
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun p hp => ?_
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  rw [mul_one_div]
  exact div_le_div_of_nonneg_right (h p hp) hp0

/-- **A return at precision `η` is a spike of exponent `1 − η`.** -/
theorem log_norm_zeta_ge_of_isReturn {N : ℕ} (hN : 3 ≤ N) {η t : ℝ} (hη : 0 ≤ η)
    (h : IsReturn (Nat.primesLE N) logStep η t) :
    (1 - η) * RHTower.Sieve.logLog N - η * |RHTower.Sieve.mertensSecondUpperConst| - harmonicConst ≤
      Real.log ‖riemannZeta (spikePoint N t)‖ := by
  have h1 := harmonicDefect_le_of_isReturn h
  have h2 := RHTower.Sieve.mertensS_le (N := N) (by omega)
  have h3 : η * RHTower.Sieve.mertensS N ≤
      η * (RHTower.Sieve.logLog N + |RHTower.Sieve.mertensSecondUpperConst|) :=
    mul_le_mul_of_nonneg_left (by linarith [le_abs_self RHTower.Sieve.mertensSecondUpperConst]) hη
  have h4 := log_norm_zeta_ge_of_isWeakReturn (C := harmonicDefect N t) hN (le_refl _)
  nlinarith

/-! ## Extreme values from Dirichlet -/

/-- **Extreme values.** For every `N ≥ 3` some height `t ≤ Q^{π(N)}`, `Q = ⌈π √(2(log log N + |c| + 1))⌉ + 1`, carries a
spike `log|ζ(s_N(t))| ≥ log log N − 1 − K`. -/
theorem exists_spike_le_pow {N : ℕ} (hN : 3 ≤ N) :
    ∃ t : ℝ, 1 ≤ t ∧
      t ≤ ((⌈π * √(2 * (RHTower.Sieve.logLog N + |RHTower.Sieve.mertensSecondUpperConst| + 1))⌉₊ + 1 : ℕ) : ℝ) ^
        (Nat.primesLE N).card ∧
      RHTower.Sieve.logLog N - 1 - harmonicConst ≤ Real.log ‖riemannZeta (spikePoint N t)‖ := by
  set U := |RHTower.Sieve.mertensSecondUpperConst| with hU
  set B := RHTower.Sieve.logLog N + U + 1 with hB
  have hN3 : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hll : 0 ≤ RHTower.Sieve.logLog N := by
    unfold RHTower.Sieve.logLog
    have h1 : 1 ≤ Real.log (N : ℝ) := by
      rw [Real.le_log_iff_exp_le (by linarith)]
      linarith [Real.exp_one_lt_d9]
    exact Real.log_nonneg h1
  have hB1 : 1 ≤ B := by rw [hB]; linarith [abs_nonneg RHTower.Sieve.mertensSecondUpperConst]
  set Q : ℕ := ⌈π * √(2 * B)⌉₊ + 1 with hQ
  have hQ1 : 1 ≤ Q := by omega
  set η : ℝ := 1 / B with hη
  have hη0 : 0 < η := by positivity
  have hηQ : 2 * π ^ 2 ≤ η * (Q : ℝ) ^ 2 := by
    have h0 : 0 ≤ π * √(2 * B) := by positivity
    have h1 : π * √(2 * B) ≤ (Q : ℝ) := by
      rw [hQ]
      push_cast
      linarith [Nat.le_ceil (π * √(2 * B))]
    have h2 : (π * √(2 * B)) ^ 2 ≤ (Q : ℝ) ^ 2 := pow_le_pow_left₀ h0 h1 2
    rw [mul_pow, sq_sqrt (by positivity)] at h2
    rw [hη, div_mul_eq_mul_div, one_mul, le_div_iff₀ (by positivity)]
    nlinarith
  obtain ⟨t, ht1, htQ, ht⟩ := exists_isReturn_le_pow (Nat.primesLE N) logStep hQ1 hηQ
  refine ⟨t, ht1, htQ, ?_⟩
  have h1 := harmonicDefect_le_of_isReturn ht
  have h2 := RHTower.Sieve.mertensS_le (N := N) (by omega)
  have h3 : η * RHTower.Sieve.mertensS N ≤ 1 := by
    have : RHTower.Sieve.mertensS N ≤ B := by
      rw [hB]; linarith [le_abs_self RHTower.Sieve.mertensSecondUpperConst]
    calc η * RHTower.Sieve.mertensS N ≤ η * B := mul_le_mul_of_nonneg_left this hη0.le
      _ = 1 := by rw [hη]; field_simp
  exact log_norm_zeta_ge_of_isWeakReturn hN (h1.trans h3)

/-! ## The pole's price -/

/-- `ζ` is at most `M + log(|t| + 1)` on `1 ≤ Re s ≤ 2`, `|Im s| ≥ 1`. -/
theorem exists_norm_zeta_le_log : ∃ M : ℝ, 5 ≤ M ∧ ∀ s : ℂ, 1 ≤ s.re → s.re ≤ 2 → 1 ≤ |s.im| →
    ‖riemannZeta s‖ ≤ M + Real.log (|s.im| + 1) := by
  set K : Set ℂ := {s | 1 ≤ s.re ∧ s.re ≤ 2 ∧ 1 ≤ |s.im| ∧ |s.im| ≤ 2} with hKdef
  have hKc : IsCompact K := by
    refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
    · refine (isClosed_le continuous_const Complex.continuous_re).inter
        ((isClosed_le Complex.continuous_re continuous_const).inter
        ((isClosed_le continuous_const Complex.continuous_im.abs).inter
          (isClosed_le Complex.continuous_im.abs continuous_const)))
    · refine (Metric.isBounded_iff_subset_closedBall 0).mpr ⟨4, fun s hs => ?_⟩
      rw [Metric.mem_closedBall, dist_zero_right]
      obtain ⟨h1, h2, _, h4⟩ := hs
      have := Complex.norm_le_abs_re_add_abs_im s
      have h5 : |s.re| ≤ 2 := abs_le.mpr ⟨by linarith, h2⟩
      linarith
  have hcont : ContinuousOn riemannZeta K := fun s hs => by
    have hs1 : s ≠ 1 := by
      intro h
      have := hs.2.2.1
      rw [h] at this
      simp at this
    exact (differentiableAt_riemannZeta hs1).continuousAt.continuousWithinAt
  obtain ⟨M₁, hM₁⟩ := hKc.exists_bound_of_continuousOn hcont
  refine ⟨max M₁ 5, le_max_right _ _, fun s h1 h2 h3 => ?_⟩
  have hlog0 : 0 ≤ Real.log (|s.im| + 1) := Real.log_nonneg (by linarith [abs_nonneg s.im])
  rcases le_or_gt |s.im| 2 with h4 | h4
  · have := hM₁ s ⟨h1, h2, h3, h4⟩
    linarith [le_max_left M₁ 5]
  · have := RHTower.norm_riemannZeta_le_log_add h1 h2 h4.le
    have h5 : Real.log |s.im| ≤ Real.log (|s.im| + 1) :=
      Real.log_le_log (by linarith) (by linarith)
    linarith [le_max_right M₁ 5]

theorem spikePoint_re (N : ℕ) (t : ℝ) : (spikePoint N t).re = 1 + 1 / Real.log (N : ℝ) := by
  simp [spikePoint]

theorem spikePoint_im (N : ℕ) (t : ℝ) : (spikePoint N t).im = t := by
  simp [spikePoint]

/-- The spike is at most `M + log(|t| + 1)` for `|t| ≥ 1`. -/
theorem norm_zeta_spikePoint_le {M : ℝ}
    (hM : ∀ s : ℂ, 1 ≤ s.re → s.re ≤ 2 → 1 ≤ |s.im| → ‖riemannZeta s‖ ≤ M + Real.log (|s.im| + 1))
    {N : ℕ} (hN : 3 ≤ N) {t : ℝ} (ht : 1 ≤ |t|) :
    ‖riemannZeta (spikePoint N t)‖ ≤ M + Real.log (|t| + 1) := by
  have hN3 : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hlogN : 1 ≤ Real.log (N : ℝ) := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    linarith [Real.exp_one_lt_d9]
  have h1 : 0 < 1 / Real.log (N : ℝ) := by positivity
  have h2 : 1 / Real.log (N : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; exact hlogN
  have := hM (spikePoint N t) (by rw [spikePoint_re]; linarith) (by rw [spikePoint_re]; linarith)
    (by rw [spikePoint_im]; exact ht)
  rwa [spikePoint_im] at this

/-- **The pole's price for a weak return.** -/
theorem log_log_le_of_isWeakReturn {M : ℝ} (hM5 : 5 ≤ M)
    (hM : ∀ s : ℂ, 1 ≤ s.re → s.re ≤ 2 → 1 ≤ |s.im| → ‖riemannZeta s‖ ≤ M + Real.log (|s.im| + 1))
    {N : ℕ} (hN : 3 ≤ N) {C t : ℝ} (ht : 1 ≤ |t|) (h : IsWeakReturn N C t) :
    RHTower.Sieve.logLog N - C - harmonicConst ≤ Real.log (M + Real.log (|t| + 1)) := by
  have h1 := log_norm_zeta_ge_of_isWeakReturn hN h
  have h2 := norm_zeta_spikePoint_le hM hN ht
  have hlog0 : 0 ≤ Real.log (|t| + 1) := Real.log_nonneg (by linarith [abs_nonneg t])
  rcases eq_or_lt_of_le (norm_nonneg (riemannZeta (spikePoint N t))) with h0 | h0
  · rw [← h0, Real.log_zero] at h1
    have : 0 ≤ Real.log (M + Real.log (|t| + 1)) := Real.log_nonneg (by linarith)
    linarith
  · exact h1.trans (Real.log_le_log h0 h2)

/-- **The pole's price for a return at precision `η`.** -/
theorem firstReturn_lower {M : ℝ} (hM5 : 5 ≤ M)
    (hM : ∀ s : ℂ, 1 ≤ s.re → s.re ≤ 2 → 1 ≤ |s.im| → ‖riemannZeta s‖ ≤ M + Real.log (|s.im| + 1))
    {N : ℕ} (hN : 3 ≤ N) {η t : ℝ} (hη : 0 ≤ η) (ht : 1 ≤ t) (h : IsReturn (Nat.primesLE N) logStep η t) :
    (1 - η) * RHTower.Sieve.logLog N - η * |RHTower.Sieve.mertensSecondUpperConst| - harmonicConst ≤
      Real.log (M + Real.log (t + 1)) := by
  have h1 := log_norm_zeta_ge_of_isReturn hN hη h
  have ht' : 1 ≤ |t| := by rw [abs_of_nonneg (by linarith)]; exact ht
  have h2 := norm_zeta_spikePoint_le hM hN ht'
  rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ t)] at h2
  have hlog0 : 0 ≤ Real.log (t + 1) := Real.log_nonneg (by linarith)
  rcases eq_or_lt_of_le (norm_nonneg (riemannZeta (spikePoint N t))) with h0 | h0
  · rw [← h0, Real.log_zero] at h1
    have : 0 ≤ Real.log (M + Real.log (t + 1)) := Real.log_nonneg (by linarith)
    linarith
  · exact h1.trans (Real.log_le_log h0 h2)

theorem tendsto_logLog : Tendsto (fun N : ℕ => RHTower.Sieve.logLog N) atTop atTop := by
  unfold RHTower.Sieve.logLog
  exact Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)

/-- **Returns escape with the length.** For `η < 1` the first return on the primes up to `N` tends to infinity. -/
theorem tendsto_firstReturn_primes {η : ℝ} (hη0 : 0 < η) (hη1 : η < 1) :
    Tendsto (fun N : ℕ => firstReturn (Nat.primesLE N) logStep η) atTop atTop := by
  obtain ⟨M, hM5, hM⟩ := exists_norm_zeta_le_log
  refine tendsto_atTop.mpr fun T => ?_
  set c := η * |RHTower.Sieve.mertensSecondUpperConst| + harmonicConst with hc
  have hlim : Tendsto (fun N : ℕ => (1 - η) * RHTower.Sieve.logLog N - c) atTop atTop :=
    tendsto_atTop_add_const_right _ _ (tendsto_logLog.const_mul_atTop (by linarith))
  filter_upwards [hlim.eventually_gt_atTop (Real.log (M + Real.log (max T 1 + 1))),
    eventually_ge_atTop 3] with N hN hN3
  by_contra hlt
  push Not at hlt
  have hR := firstReturn_mem (Nat.primesLE N) logStep hη0
  have h := firstReturn_lower hM5 hM hN3 hη0.le hR.1 hR.2
  have hR1 := hR.1
  have hmono : Real.log (M + Real.log (firstReturn (Nat.primesLE N) logStep η + 1)) ≤
      Real.log (M + Real.log (max T 1 + 1)) := by
    have hx : 0 < firstReturn (Nat.primesLE N) logStep η + 1 := by linarith
    have hlog0 : 0 ≤ Real.log (firstReturn (Nat.primesLE N) logStep η + 1) := Real.log_nonneg (by linarith)
    refine Real.log_le_log (by linarith) ?_
    have := Real.log_le_log hx (by linarith [le_max_left T 1] : firstReturn (Nat.primesLE N) logStep η + 1 ≤
      max T 1 + 1)
    linarith
  linarith

end

end GaloisForLFunctions.TailArithmeticOfThePrimeOrbit
