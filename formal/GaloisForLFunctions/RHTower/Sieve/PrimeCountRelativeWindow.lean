import GaloisForLFunctions.RHTower.PrimeHigherMertensRate

/-!
# Primes in windows of relative length `θ ≥ exp(-c√log Z)`

From the prime number theorem with the classical error `|θ(t) - t| ≤ D t exp(-c√log t)`
(`RHTower.exists_pntErrorEnvelope`), the number of primes in `(Z, Z(1+θ)]` is
`(1 + o(1)) θ Z / log Z`, uniformly for `exp(-(c/2)√log Z) ≤ θ ≤ 1`.
-/

namespace RHTower.Sieve

open Real Filter Topology Finset

noncomputable section

/-- The primes in `(Z, W]`. -/
def primesIn (Z W : ℝ) : Finset ℕ := (Finset.Ioc ⌊Z⌋₊ ⌊W⌋₊).filter Nat.Prime

theorem theta_sub_theta_eq_sum_primesIn {Z W : ℝ} (hZW : Z ≤ W) :
    Chebyshev.theta W - Chebyshev.theta Z = ∑ p ∈ primesIn Z W, log (p : ℝ) := by
  unfold Chebyshev.theta primesIn
  rw [sub_eq_iff_eq_add', Finset.sum_filter, Finset.sum_filter, Finset.sum_filter,
    Finset.sum_Ioc_consecutive _ (Nat.zero_le _) (Nat.floor_le_floor hZW)]

theorem mem_primesIn {Z W : ℝ} {p : ℕ} (hZ : 0 ≤ Z) (hp : p ∈ primesIn Z W) :
    p.Prime ∧ Z < p ∧ (p : ℝ) ≤ W := by
  simp only [primesIn, Finset.mem_filter, Finset.mem_Ioc] at hp
  refine ⟨hp.2, ?_, ?_⟩
  · exact (Nat.floor_lt hZ).1 hp.1.1
  · have hW : 0 ≤ W := by
      by_contra h
      have : ⌊W⌋₊ = 0 := Nat.floor_eq_zero.2 (by linarith)
      omega
    exact (Nat.le_floor_iff hW).1 hp.1.2

/-- **Primes in relative windows.** There is `c > 0` such that for every `η > 0`, eventually in
`Z`, for all `exp(-c√log Z) ≤ θ ≤ 1` the window `(Z, Z(1+θ)]` has between `(1-η)θZ/log Z` and
`(1+η)θZ/log Z` primes. -/
theorem exists_card_primesIn_window :
    ∃ c > 0, ∀ η > 0, ∀ᶠ Z : ℝ in atTop, ∀ θ : ℝ, exp (-c * sqrt (log Z)) ≤ θ → θ ≤ 1 →
      (1 - η) * (θ * Z / log Z) ≤ ((primesIn Z (Z * (1 + θ))).card : ℝ) ∧
      ((primesIn Z (Z * (1 + θ))).card : ℝ) ≤ (1 + η) * (θ * Z / log Z) := by
  obtain ⟨D, c, T, hc, hD, hT4, hθ, -⟩ := RHTower.exists_pntErrorEnvelope
  refine ⟨c / 2, by positivity, fun η hη => ?_⟩
  -- the error ratio `4D exp(-(c/2)√log Z)` tends to zero
  have hsmall : ∀ᶠ Z : ℝ in atTop, 4 * D * exp (-(c / 2) * sqrt (log Z)) ≤ η / 4 := by
    have hlim : Tendsto (fun Z : ℝ => 4 * D * exp (-(c / 2) * sqrt (log Z))) atTop (𝓝 0) := by
      have h1 : Tendsto (fun Z : ℝ => sqrt (log Z)) atTop atTop :=
        tendsto_sqrt_atTop.comp tendsto_log_atTop
      have h2 : Tendsto (fun Z : ℝ => -(c / 2) * sqrt (log Z)) atTop atBot :=
        (tendsto_neg_atTop_atBot.comp (h1.const_mul_atTop (by positivity : (0 : ℝ) < c / 2))).congr
          (fun Z => by simp only [Function.comp]; ring)
      simpa using (tendsto_exp_atBot.comp h2).const_mul (4 * D)
    exact hlim.eventually (ge_mem_nhds (by linarith))
  have hlogratio : ∀ᶠ Z : ℝ in atTop, log (2 * Z) ≤ (1 + η / 4) * log Z := by
    have hlim : ∀ᶠ Z : ℝ in atTop, log 2 ≤ η / 4 * log Z :=
      (tendsto_log_atTop.const_mul_atTop (by positivity)).eventually_ge_atTop (log 2)
    filter_upwards [hlim, eventually_gt_atTop (0 : ℝ)] with Z hZ hZ0
    rw [Real.log_mul (by norm_num) hZ0.ne']
    linarith
  filter_upwards [hsmall, hlogratio, eventually_ge_atTop T, eventually_gt_atTop (1 : ℝ)]
    with Z hZs hZr hZT hZ1
  intro θ hθlo hθ1
  have hZ0 : 0 < Z := by linarith
  have hlogZ : 0 < log Z := Real.log_pos hZ1
  have hθ0 : 0 < θ := (exp_pos _).trans_le hθlo
  set W := Z * (1 + θ) with hW
  have hZW : Z ≤ W := by rw [hW]; nlinarith
  have hW2 : W ≤ 2 * Z := by rw [hW]; nlinarith
  have hWT : T ≤ W := hZT.trans hZW
  -- the error at both ends
  have heZ := hθ Z hZT
  have heW := hθ W hWT
  have hexpW : exp (-c * sqrt (log W)) ≤ exp (-c * sqrt (log Z)) := by
    apply Real.exp_le_exp.2
    have : sqrt (log Z) ≤ sqrt (log W) := Real.sqrt_le_sqrt (Real.log_le_log hZ0 hZW)
    nlinarith
  have hsum := theta_sub_theta_eq_sum_primesIn hZW
  have hdiff : |Chebyshev.theta W - Chebyshev.theta Z - θ * Z| ≤ 3 * D * Z * exp (-c * sqrt (log Z)) := by
    have e : Chebyshev.theta W - Chebyshev.theta Z - θ * Z
        = (Chebyshev.theta W - W) - (Chebyshev.theta Z - Z) := by rw [hW]; ring
    rw [e]
    refine (abs_sub _ _).trans ?_
    have h1 : D * W * exp (-c * sqrt (log W)) ≤ 2 * D * Z * exp (-c * sqrt (log Z)) := by
      have := mul_le_mul hW2 hexpW (exp_pos _).le (by linarith)
      nlinarith
    linarith
  -- the relative error is at most η/4 · θ Z
  have hrel : 3 * D * Z * exp (-c * sqrt (log Z)) ≤ η / 4 * (θ * Z) := by
    have hsplit : exp (-c * sqrt (log Z)) = exp (-(c / 2) * sqrt (log Z)) * exp (-(c / 2) * sqrt (log Z)) := by
      rw [← Real.exp_add]; ring_nf
    rw [hsplit]
    have h1 : exp (-(c / 2) * sqrt (log Z)) ≤ θ := hθlo
    have h2 : 4 * D * exp (-(c / 2) * sqrt (log Z)) ≤ η / 4 := hZs
    have h3 : 0 ≤ exp (-(c / 2) * sqrt (log Z)) := (exp_pos _).le
    nlinarith [mul_le_mul_of_nonneg_left h1 (by positivity : 0 ≤ 3 * D * Z * exp (-(c / 2) * sqrt (log Z)))]
  have hlogp : ∀ p ∈ primesIn Z W, log Z ≤ log (p : ℝ) ∧ log (p : ℝ) ≤ log (2 * Z) := by
    intro p hp
    obtain ⟨-, h1, h2⟩ := mem_primesIn hZ0.le hp
    exact ⟨Real.log_le_log hZ0 h1.le, Real.log_le_log (hZ0.trans h1) (h2.trans hW2)⟩
  have hup : (primesIn Z W).card * log Z ≤ ∑ p ∈ primesIn Z W, log (p : ℝ) := by
    rw [← nsmul_eq_mul, ← Finset.sum_const]
    exact Finset.sum_le_sum (fun p hp => (hlogp p hp).1)
  have hlo : ∑ p ∈ primesIn Z W, log (p : ℝ) ≤ (primesIn Z W).card * log (2 * Z) := by
    rw [← nsmul_eq_mul, ← Finset.sum_const]
    exact Finset.sum_le_sum (fun p hp => (hlogp p hp).2)
  rw [← hsum] at hup hlo
  have hdiff' := abs_le.mp hdiff
  have hc0 : (0 : ℝ) ≤ (primesIn Z W).card := Nat.cast_nonneg _
  have hθZ : 0 < θ * Z := by positivity
  constructor
  · -- lower bound
    have hcard : (1 - η / 4) * (θ * Z) ≤ (primesIn Z W).card * log (2 * Z) := by linarith
    have hA : (1 - η / 4) * (θ * Z) ≤ (1 + η / 4) * ((primesIn Z W).card * log Z) := by
      have := mul_le_mul_of_nonneg_left hZr hc0
      nlinarith
    have key : (1 - η) * (θ * Z) * (1 + η / 4) ≤ (1 - η / 4) * (θ * Z) := by nlinarith
    have hB : (1 - η) * (θ * Z) ≤ (primesIn Z W).card * log Z := by
      have h := key.trans hA
      have hp : 0 < 1 + η / 4 := by positivity
      nlinarith
    rw [← mul_div_assoc, div_le_iff₀ hlogZ]
    exact hB
  · -- upper bound
    have hcard : (primesIn Z W).card * log Z ≤ (1 + η / 4) * (θ * Z) := by linarith
    rw [← mul_div_assoc, le_div_iff₀ hlogZ]
    nlinarith

end

end RHTower.Sieve
