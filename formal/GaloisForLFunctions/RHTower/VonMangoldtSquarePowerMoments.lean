import GaloisForLFunctions.RHTower.PNTTailLogMoment
import GaloisForLFunctions.RHTower.XiMassShellPrimeMass
import GaloisForLFunctions.RHTower.ChebyshevPsiScaling
import GaloisForLFunctions.RHTower.PrimeRpowAbelSummation

/-!
# Power moments of `Λ(n)²` from the prime number theorem

`Σ_{n ≤ x} Λ(n)² n / (x² log x) → 1/2` and `(x^{k+1}/log x) Σ_{n > x} Λ(n)²/n^{k+2} → 1/(k+1)`.

`Λ(n)²` is squeezed between `log²p` on the primes and `Λ(n) log n`; both bounds have partial
sums `θ` and `ψ`, asymptotic to `x` by the prime number theorem, so the two Abel-summation
limits of `PNTFirstLogMoment` and `PNTTailLogMoment` apply to both and pinch `Λ(n)²`.
-/

open Filter Topology Set
open ArithmeticFunction (vonMangoldt)

namespace RHTower

/-! ## The two partial-sum functions -/

theorem partialSumReal_vonMangoldt (t : ℝ) :
    partialSumReal (fun n : ℕ => (vonMangoldt n : ℝ)) t = chebyshevPsiReal t := by
  rw [partialSumReal, chebyshevPsiReal_eq_sum_range]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext n; simp only [Finset.mem_Icc, Finset.mem_range]; omega

theorem tendsto_partialSumReal_vonMangoldt_div :
    Tendsto (fun t : ℝ => partialSumReal (fun n : ℕ => (vonMangoldt n : ℝ)) t / t) atTop (𝓝 1) := by
  simp_rw [partialSumReal_vonMangoldt]
  exact tendsto_chebyshevPsiReal_div

theorem partialSumReal_primeLogWeight (t : ℝ) :
    partialSumReal primeLogWeight t = Chebyshev.theta t :=
  sum_primeLogWeight_eq_theta t

theorem tendsto_partialSumReal_primeLogWeight_div :
    Tendsto (fun t : ℝ => partialSumReal primeLogWeight t / t) atTop (𝓝 1) := by
  simp_rw [partialSumReal_primeLogWeight]
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.mp (chebyshevTheta_eventually_relative (ε := ε / 2)
    (by positivity))
  refine ⟨max x₀ 1, fun x hx => ?_⟩
  have hx1 : (1 : ℝ) ≤ x := (le_max_right _ _).trans hx
  have hx0 : 0 < x := by linarith
  have h := hx₀ x ((le_max_left _ _).trans hx)
  rw [Real.dist_eq, show Chebyshev.theta x / x - 1 = (Chebyshev.theta x - x) / x by field_simp,
    abs_div, abs_of_pos hx0, div_lt_iff₀ hx0]
  nlinarith

theorem primeLogWeight_nonneg (n : ℕ) : 0 ≤ primeLogWeight n := by
  unfold primeLogWeight
  split_ifs with h
  · exact Real.log_nonneg (by exact_mod_cast h.one_lt.le)
  · exact le_rfl

theorem primeLogWeight_zero : primeLogWeight 0 = 0 := by simp [primeLogWeight]

/-- The squeeze `log n · primeLogWeight n ≤ Λ(n)² ≤ Λ(n) log n`. -/
theorem log_mul_primeLogWeight_le_vonMangoldt_sq (n : ℕ) :
    Real.log n * primeLogWeight n ≤ vonMangoldt n ^ 2 := by
  unfold primeLogWeight
  split_ifs with h
  · rw [ArithmeticFunction.vonMangoldt_apply_prime h]; ring_nf; exact le_rfl
  · rw [mul_zero]; positivity

theorem vonMangoldt_sq_le_log_mul (n : ℕ) :
    vonMangoldt n ^ 2 ≤ Real.log n * vonMangoldt n := by
  have := ArithmeticFunction.vonMangoldt_le_log (n := n)
  have h0 := ArithmeticFunction.vonMangoldt_nonneg (n := n)
  nlinarith

/-! ## The finite moment `Σ_{n≤x} Λ(n)² n ~ ½ x² log x` -/

/-- **`Σ_{n ≤ x} Λ(n)² n / (x² log x) → 1/2`.** -/
theorem tendsto_sum_vonMangoldt_sq_mul_div :
    Tendsto (fun x : ℝ => (∑ n ∈ Finset.Icc 0 ⌊x⌋₊, vonMangoldt n ^ 2 * n) / (x ^ 2 * Real.log x))
      atTop (𝓝 (1 / 2)) := by
  have hΛ := tendsto_sum_mul_log_div_sq_log (c := fun n : ℕ => (vonMangoldt n : ℝ)) (by simp)
    (fun n => ArithmeticFunction.vonMangoldt_nonneg) tendsto_partialSumReal_vonMangoldt_div
  have hθ := tendsto_sum_mul_log_div_sq_log (c := primeLogWeight) primeLogWeight_zero
    primeLogWeight_nonneg tendsto_partialSumReal_primeLogWeight_div
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hθ hΛ ?_ ?_
  · filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
    have hpos : 0 < x ^ 2 * Real.log x := by
      have := Real.log_pos (by linarith : (1 : ℝ) < x); positivity
    apply div_le_div_of_nonneg_right _ hpos.le
    refine Finset.sum_le_sum fun n _ => ?_
    have := log_mul_primeLogWeight_le_vonMangoldt_sq n
    have hn := Nat.cast_nonneg (α := ℝ) n
    nlinarith
  · filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
    have hpos : 0 < x ^ 2 * Real.log x := by
      have := Real.log_pos (by linarith : (1 : ℝ) < x); positivity
    apply div_le_div_of_nonneg_right _ hpos.le
    refine Finset.sum_le_sum fun n _ => ?_
    have := vonMangoldt_sq_le_log_mul n
    have hn := Nat.cast_nonneg (α := ℝ) n
    nlinarith

/-! ## The tail moments `Σ_{n>x} Λ(n)²/n^{k+2}` -/

theorem log_sq_le_rpow_half {n : ℕ} : Real.log n ^ 2 ≤ 16 * (n : ℝ) ^ ((1 / 2 : ℝ)) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hlog : Real.log n ≤ 4 * (n : ℝ) ^ ((1 / 4 : ℝ)) := by
    have := Real.log_le_rpow_div hn'.le (show (0 : ℝ) < 1 / 4 by norm_num)
    rw [div_eq_mul_inv, show ((1 / 4 : ℝ))⁻¹ = 4 by norm_num] at this
    linarith
  have hlog0 : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
  have h4 : ((n : ℝ) ^ ((1 / 4 : ℝ))) ^ 2 = (n : ℝ) ^ ((1 / 2 : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hn'.le]; norm_num
  calc Real.log n ^ 2 ≤ (4 * (n : ℝ) ^ ((1 / 4 : ℝ))) ^ 2 := by gcongr
    _ = 16 * (n : ℝ) ^ ((1 / 2 : ℝ)) := by rw [mul_pow, h4]; norm_num

/-- `Λ(n) log n / n^{k+2} ≤ 16 n^{−3/2}`. -/
theorem vonMangoldt_mul_log_div_pow_le (k n : ℕ) :
    vonMangoldt n * Real.log n / (n : ℝ) ^ (k + 2) ≤ 16 * ((n : ℝ) ^ ((3 / 2 : ℝ)))⁻¹ := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h1 : vonMangoldt n * Real.log n ≤ Real.log n ^ 2 := by
    have := ArithmeticFunction.vonMangoldt_le_log (n := n)
    have hlog0 : 0 ≤ Real.log n := Real.log_nonneg hn1
    nlinarith
  have h2 := log_sq_le_rpow_half (n := n)
  have hpow : (n : ℝ) ^ 2 ≤ (n : ℝ) ^ (k + 2) := pow_le_pow_right₀ hn1 (by omega)
  rw [div_le_iff₀ (by positivity)]
  calc vonMangoldt n * Real.log n ≤ 16 * (n : ℝ) ^ ((1 / 2 : ℝ)) := h1.trans h2
    _ = 16 * ((n : ℝ) ^ ((3 / 2 : ℝ)))⁻¹ * (n : ℝ) ^ 2 := by
        rw [← Real.rpow_neg hn'.le, ← Real.rpow_two, mul_assoc, ← Real.rpow_add hn']; norm_num
    _ ≤ 16 * ((n : ℝ) ^ ((3 / 2 : ℝ)))⁻¹ * (n : ℝ) ^ (k + 2) := by gcongr

theorem summable_vonMangoldt_tail (k : ℕ) (x : ℝ) :
    Summable (fun n : ℕ => if x < (n : ℝ) then vonMangoldt n * Real.log n / (n : ℝ) ^ (k + 2) else 0) := by
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_)
    ((Real.summable_nat_rpow_inv.mpr (by norm_num : (1 : ℝ) < 3 / 2)).mul_left 16)
  · split_ifs with h
    · exact div_nonneg (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
        (Real.log_natCast_nonneg n)) (by positivity)
    · exact le_rfl
  · split_ifs with h
    · exact vonMangoldt_mul_log_div_pow_le k n
    · positivity

/-- **`(x^{k+1}/log x) Σ_{n > x} Λ(n)²/n^{k+2} → 1/(k+1)`.** -/
theorem tendsto_tail_vonMangoldt_sq (k : ℕ) :
    Tendsto (fun x : ℝ => x ^ (k + 1) / Real.log x *
        ∑' n : ℕ, (if x < (n : ℝ) then vonMangoldt n ^ 2 / (n : ℝ) ^ (k + 2) else 0))
      atTop (𝓝 (1 / ((k : ℝ) + 1))) := by
  have hΛ := tendsto_tail_log_moment (c := fun n : ℕ => (vonMangoldt n : ℝ)) (by simp)
    (fun n => ArithmeticFunction.vonMangoldt_nonneg) tendsto_partialSumReal_vonMangoldt_div k
  have hθ := tendsto_tail_log_moment (c := primeLogWeight) primeLogWeight_zero
    primeLogWeight_nonneg tendsto_partialSumReal_primeLogWeight_div k
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hθ hΛ ?_ ?_
  · filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
    have hpos : 0 ≤ x ^ (k + 1) / Real.log x := by
      have := Real.log_pos (by linarith : (1 : ℝ) < x); positivity
    refine mul_le_mul_of_nonneg_left ?_ hpos
    have hsumΛ : Summable (fun n : ℕ => if x < (n : ℝ) then vonMangoldt n ^ 2 / (n : ℝ) ^ (k + 2)
        else 0) := by
      refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) (summable_vonMangoldt_tail k x)
      · split_ifs <;> positivity
      · split_ifs with h
        · apply div_le_div_of_nonneg_right _ (by positivity)
          have := vonMangoldt_sq_le_log_mul n; linarith
        · exact le_rfl
    refine Summable.tsum_le_tsum (fun n => ?_) ?_ hsumΛ
    · split_ifs with h
      · apply div_le_div_of_nonneg_right _ (by positivity)
        have := log_mul_primeLogWeight_le_vonMangoldt_sq n; linarith
      · exact le_rfl
    · refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hsumΛ
      · split_ifs with h
        · exact div_nonneg (mul_nonneg (primeLogWeight_nonneg n)
            (Real.log_natCast_nonneg n)) (by positivity)
        · exact le_rfl
      · split_ifs with h
        · apply div_le_div_of_nonneg_right _ (by positivity)
          have := log_mul_primeLogWeight_le_vonMangoldt_sq n; linarith
        · exact le_rfl
  · filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
    have hpos : 0 ≤ x ^ (k + 1) / Real.log x := by
      have := Real.log_pos (by linarith : (1 : ℝ) < x); positivity
    refine mul_le_mul_of_nonneg_left ?_ hpos
    refine Summable.tsum_le_tsum (fun n => ?_) ?_ (summable_vonMangoldt_tail k x)
    · split_ifs with h
      · apply div_le_div_of_nonneg_right _ (by positivity)
        have := vonMangoldt_sq_le_log_mul n; linarith
      · exact le_rfl
    · refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) (summable_vonMangoldt_tail k x)
      · split_ifs <;> positivity
      · split_ifs with h
        · apply div_le_div_of_nonneg_right _ (by positivity)
          have := vonMangoldt_sq_le_log_mul n; linarith
        · exact le_rfl

end RHTower
