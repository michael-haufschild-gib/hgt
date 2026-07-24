import Mathlib
import GaloisForLFunctions.RHTower.SquaredXiRadialJetSourceAlignment

/-!
# Reverse-Bessel radial jets are blind to every fixed Euler frequency

The order-`n` reverse-Bessel radial polynomial `B_n(x) = ∑_{j=0}^n b(n,j) x^j`, built from the
radial-jet magnitudes `b(n,j) = squaredRadialJetWeight n j`, satisfies after normalisation by its
constant coefficient `b(n,0)`:

* `B_n(x)/b(n,0) ≤ exp x` for `x ≥ 0` (dominated by the exponential series);
* `B_n(x)/b(n,0) → exp x` as `n → ∞` at every fixed `x ≥ 0`.

Both rest on the normalised-coefficient domination `b(n,j)/b(n,0) ≤ 1/j!` with the pointwise limit
`b(n,j)/b(n,0) → 1/j!`, which follow from the exact reverse-Bessel closed form via the ratio
recurrence `b(n,j+1)·(2n−j)·(j+1) = b(n,j)·2(n−j)`.  The growing-order sum limit is obtained from
Tannery's theorem.  Consequently every fixed prime-power atom loses its Euler damping as the order
grows, so no finite set of primes can dominate the growing-order squared-Xi source.
-/

open scoped BigOperators
open RHTower

namespace RHTower

noncomputable section

/-- The order-`n` reverse-Bessel radial polynomial `B_n(x) = ∑_{j=0}^n b(n,j) x^j`. -/
def reverseBesselPoly (n : ℕ) (x : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (n + 1), (squaredRadialJetWeight n j : ℝ) * x ^ j

/-- Ratio recurrence in `ℚ` from the closed form: `b(n,j+1)·(2n−j)·(j+1) = b(n,j)·2(n−j)`. -/
private theorem weight_ratio_rec_rat {n j : ℕ} (hjn : j < n) :
    (squaredRadialJetWeight n (j + 1) : ℚ) * ((2 * n - j : ℕ) : ℚ) * ((j + 1 : ℕ) : ℚ)
      = (squaredRadialJetWeight n j : ℚ) * (2 * ((n - j : ℕ) : ℚ)) := by
  rw [squaredRadialJetWeight_eq_closedForm n (j + 1) (by omega),
      squaredRadialJetWeight_eq_closedForm n j (by omega)]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + j + 1 := ⟨n - j - 1, by omega⟩
  unfold squaredRadialJetWeightClosedForm
  have e1 : 2 * (m + j + 1) - (j + 1) = 2 * m + j + 1 := by omega
  have e2 : (m + j + 1) - (j + 1) = m := by omega
  have e3 : 2 * (m + j + 1) - j = 2 * m + j + 2 := by omega
  have e4 : (m + j + 1) - j = m + 1 := by omega
  rw [e1, e2, e3, e4]
  push_cast
  rw [show (2 * m + j + 2).factorial = (2 * m + j + 2) * (2 * m + j + 1).factorial from by
        rw [show 2 * m + j + 2 = (2 * m + j + 1) + 1 from rfl, Nat.factorial_succ],
      show (m + 1).factorial = (m + 1) * m.factorial from Nat.factorial_succ m,
      show (j + 1).factorial = (j + 1) * j.factorial from Nat.factorial_succ j]
  have hm : (m.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero m
  have hj : (j.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
  have hf : ((2 * m + j + 1).factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  push_cast; field_simp; ring

/-- Ratio recurrence in `ℕ`. -/
private theorem weight_ratio_rec_nat {n j : ℕ} (hjn : j < n) :
    squaredRadialJetWeight n (j + 1) * (2 * n - j) * (j + 1)
      = squaredRadialJetWeight n j * (2 * (n - j)) := by
  have := weight_ratio_rec_rat hjn
  exact_mod_cast this

/-- Normalised-coefficient domination, integer form: `b(n,j)·j! ≤ b(n,0)` on the triangular
range. -/
private theorem weight_mul_factorial_le (n : ℕ) :
    ∀ j, j ≤ n → squaredRadialJetWeight n j * j.factorial ≤ squaredRadialJetWeight n 0 := by
  intro j
  induction j with
  | zero => intro _; simp
  | succ k ih =>
      intro hk
      have hkn : k < n := hk
      have hrec := weight_ratio_rec_nat hkn
      have h2npos : 0 < 2 * n - k := by omega
      have step : squaredRadialJetWeight n (k + 1) * (k + 1) ≤ squaredRadialJetWeight n k := by
        apply Nat.le_of_mul_le_mul_right _ h2npos
        calc squaredRadialJetWeight n (k + 1) * (k + 1) * (2 * n - k)
            = squaredRadialJetWeight n (k + 1) * (2 * n - k) * (k + 1) := by ring
          _ = squaredRadialJetWeight n k * (2 * (n - k)) := hrec
          _ ≤ squaredRadialJetWeight n k * (2 * n - k) := by
                apply Nat.mul_le_mul_left; omega
      calc squaredRadialJetWeight n (k + 1) * (k + 1).factorial
          = squaredRadialJetWeight n (k + 1) * (k + 1) * k.factorial := by
              rw [Nat.factorial_succ]; ring
        _ ≤ squaredRadialJetWeight n k * k.factorial := by
              apply Nat.mul_le_mul_right; exact step
        _ ≤ squaredRadialJetWeight n 0 := ih (by omega)

/-- Normalised-coefficient domination, real form: `b(n,j) ≤ b(n,0)/j!`. -/
theorem weight_le_div {n j : ℕ} (hj : j ≤ n) :
    (squaredRadialJetWeight n j : ℝ)
      ≤ (squaredRadialJetWeight n 0 : ℝ) / (j.factorial : ℝ) := by
  have h := weight_mul_factorial_le n j hj
  have hR : (squaredRadialJetWeight n j : ℝ) * (j.factorial : ℝ)
      ≤ (squaredRadialJetWeight n 0 : ℝ) := by exact_mod_cast h
  rw [le_div_iff₀ (by positivity : (0 : ℝ) < (j.factorial : ℝ))]
  exact hR

/-- Positivity of the constant coefficient. -/
theorem weight_zero_pos (n : ℕ) : 0 < (squaredRadialJetWeight n 0 : ℝ) := by
  exact_mod_cast squaredRadialJetWeight_pos n 0 (Nat.zero_le n)

/-- **The normalised reverse-Bessel polynomial is dominated by the exponential.**  For `x ≥ 0`,
`B_n(x)/b(n,0) ≤ exp x`. -/
theorem reverseBesselPoly_div_le_exp (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    reverseBesselPoly n x / (squaredRadialJetWeight n 0 : ℝ) ≤ Real.exp x := by
  have hb0 := weight_zero_pos n
  have key : reverseBesselPoly n x ≤ (squaredRadialJetWeight n 0 : ℝ) * Real.exp x := by
    unfold reverseBesselPoly
    calc ∑ j ∈ Finset.range (n + 1), (squaredRadialJetWeight n j : ℝ) * x ^ j
        ≤ ∑ j ∈ Finset.range (n + 1), ((squaredRadialJetWeight n 0 : ℝ) / (j.factorial : ℝ)) * x ^ j := by
          apply Finset.sum_le_sum
          intro j hj
          have hjn : j ≤ n := by
            simpa [Nat.lt_succ_iff] using Finset.mem_range.mp hj
          gcongr
          exact weight_le_div hjn
      _ = (squaredRadialJetWeight n 0 : ℝ) * ∑ j ∈ Finset.range (n + 1), x ^ j / (j.factorial : ℝ) := by
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; ring
      _ ≤ (squaredRadialJetWeight n 0 : ℝ) * Real.exp x := by
          apply mul_le_mul_of_nonneg_left _ hb0.le
          rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
          exact Summable.sum_le_tsum (Finset.range (n + 1)) (fun j _ => by positivity)
            (Real.summable_pow_div_factorial x)
  rw [div_le_iff₀ hb0]
  linarith [key]

/-- The normalised coefficient `b(n,j)/b(n,0)`. -/
def reverseBesselRatio (n j : ℕ) : ℝ :=
  (squaredRadialJetWeight n j : ℝ) / (squaredRadialJetWeight n 0 : ℝ)

private theorem reverseBesselRatio_nonneg (n j : ℕ) : 0 ≤ reverseBesselRatio n j :=
  div_nonneg (by positivity) (weight_zero_pos n).le

/-- `b(n,j)/b(n,0) ≤ 1/j!` for every `j` (the excess `j > n` terms vanish). -/
private theorem reverseBesselRatio_le (n j : ℕ) : reverseBesselRatio n j ≤ 1 / (j.factorial : ℝ) := by
  rcases le_or_gt j n with hj | hj
  · unfold reverseBesselRatio
    rw [div_le_iff₀ (weight_zero_pos n)]
    have hle := weight_le_div (n := n) (j := j) hj
    rw [show (1:ℝ) / (j.factorial : ℝ) * (squaredRadialJetWeight n 0 : ℝ)
        = (squaredRadialJetWeight n 0 : ℝ) / (j.factorial : ℝ) from by ring]
    exact hle
  · unfold reverseBesselRatio
    rw [squaredRadialJetWeight_eq_zero_of_lt n j hj]
    simp only [Nat.cast_zero, zero_div]
    positivity

/-- Ratio recurrence in `ℝ`: `b(n,j+1)/b(n,0) = (b(n,j)/b(n,0))·2(n−j)/((2n−j)(j+1))`. -/
private theorem reverseBesselRatio_succ {n j : ℕ} (hjn : j < n) :
    reverseBesselRatio n (j + 1)
      = reverseBesselRatio n j * (2 * ((n:ℝ) - j) / ((2 * (n:ℝ) - j) * ((j:ℝ) + 1))) := by
  have hcast2n : ((2 * n - j : ℕ) : ℝ) = 2 * (n:ℝ) - j := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  have hcastn : ((n - j : ℕ) : ℝ) = (n:ℝ) - j := by rw [Nat.cast_sub (by omega)]
  have hrec : (squaredRadialJetWeight n (j + 1) : ℝ) * (2 * (n:ℝ) - j) * ((j:ℝ) + 1)
      = (squaredRadialJetWeight n j : ℝ) * (2 * ((n:ℝ) - j)) := by
    have h := weight_ratio_rec_nat hjn
    have hR : (squaredRadialJetWeight n (j + 1) : ℝ) * ((2 * n - j : ℕ) : ℝ) * ((j + 1 : ℕ) : ℝ)
        = (squaredRadialJetWeight n j : ℝ) * (2 * ((n - j : ℕ) : ℝ)) := by exact_mod_cast h
    rw [hcast2n, hcastn] at hR
    push_cast at hR
    linear_combination hR
  have h2n : 2 * (n:ℝ) - j ≠ 0 := by
    have : (j:ℝ) < n := by exact_mod_cast hjn
    have : (0:ℝ) < 2 * (n:ℝ) - j := by nlinarith
    exact this.ne'
  have hj1 : ((j:ℝ) + 1) ≠ 0 := by positivity
  have key : (squaredRadialJetWeight n (j + 1) : ℝ)
      = (squaredRadialJetWeight n j : ℝ) * (2 * ((n:ℝ) - j)) / ((2 * (n:ℝ) - j) * ((j:ℝ) + 1)) := by
    rw [eq_div_iff (mul_ne_zero h2n hj1)]
    linear_combination hrec
  unfold reverseBesselRatio
  rw [key]; ring

/-- **Termwise limit**: `b(n,j)/b(n,0) → 1/j!` as `n → ∞`, for each fixed `j`. -/
theorem reverseBesselRatio_tendsto (j : ℕ) :
    Filter.Tendsto (fun n : ℕ => reverseBesselRatio n j) Filter.atTop
      (nhds (1 / (j.factorial : ℝ))) := by
  induction j with
  | zero =>
      have hfun : (fun n : ℕ => reverseBesselRatio n 0) = fun _ => (1 : ℝ) := by
        funext n; unfold reverseBesselRatio; rw [div_self (weight_zero_pos n).ne']
      rw [hfun]
      simp only [Nat.factorial_zero, Nat.cast_one, div_one]
      exact tendsto_const_nhds
  | succ j ih =>
      have hfac : Filter.Tendsto
          (fun n : ℕ => 2 * ((n:ℝ) - j) / ((2 * (n:ℝ) - j) * ((j:ℝ) + 1))) Filter.atTop
          (nhds (1 / ((j:ℝ) + 1))) := by
        have hj0 : Filter.Tendsto (fun n : ℕ => (j:ℝ) / (n:ℝ)) Filter.atTop (nhds 0) :=
          tendsto_const_div_atTop_nhds_zero_nat (j:ℝ)
        have hnum : Filter.Tendsto (fun n : ℕ => 2 - 2 * ((j:ℝ) / (n:ℝ))) Filter.atTop (nhds 2) := by
          have h1 : Filter.Tendsto (fun n : ℕ => 2 * ((j:ℝ) / (n:ℝ))) Filter.atTop (nhds 0) := by
            simpa using hj0.const_mul (2:ℝ)
          simpa using h1.const_sub (2:ℝ)
        have hden : Filter.Tendsto (fun n : ℕ => (2 - (j:ℝ) / (n:ℝ)) * ((j:ℝ) + 1)) Filter.atTop
            (nhds (2 * ((j:ℝ) + 1))) := by
          have h2 : Filter.Tendsto (fun n : ℕ => 2 - (j:ℝ) / (n:ℝ)) Filter.atTop (nhds 2) := by
            simpa using hj0.const_sub (2:ℝ)
          simpa using h2.mul_const ((j:ℝ) + 1)
        have hlim : Filter.Tendsto
            (fun n : ℕ => (2 - 2 * ((j:ℝ) / (n:ℝ))) / ((2 - (j:ℝ) / (n:ℝ)) * ((j:ℝ) + 1)))
            Filter.atTop (nhds (1 / ((j:ℝ) + 1))) := by
          have hquot := hnum.div hden (by positivity)
          have heq : (2:ℝ) / (2 * ((j:ℝ) + 1)) = 1 / ((j:ℝ) + 1) := by
            rw [div_eq_div_iff (by positivity) (by positivity)]; ring
          rw [heq] at hquot; exact hquot
        refine hlim.congr' ?_
        filter_upwards [Filter.eventually_ge_atTop (j + 1)] with n hn
        have hnpos : (j:ℝ) + 1 ≤ (n:ℝ) := by exact_mod_cast hn
        have hn0 : (n:ℝ) ≠ 0 := by
          have : (0:ℝ) < (n:ℝ) := by nlinarith
          exact this.ne'
        have hd : 2 * (n:ℝ) - j ≠ 0 := by
          have : (0:ℝ) < 2 * (n:ℝ) - j := by nlinarith
          exact this.ne'
        field_simp
      have hmul := ih.mul hfac
      have htarget : Filter.Tendsto (fun n : ℕ => reverseBesselRatio n (j + 1)) Filter.atTop
          (nhds (1 / (j.factorial : ℝ) * (1 / ((j:ℝ) + 1)))) := by
        refine hmul.congr' ?_
        filter_upwards [Filter.eventually_gt_atTop j] with n hn
        exact (reverseBesselRatio_succ hn).symm
      have heq : (1 / (j.factorial : ℝ)) * (1 / ((j:ℝ) + 1)) = 1 / ((j + 1).factorial : ℝ) := by
        rw [Nat.factorial_succ]; push_cast; field_simp
      rwa [heq] at htarget

/-- **Fixed-frequency limit** (`(3)`): for `x ≥ 0`, the normalised reverse-Bessel polynomial
converges to the exponential, `B_n(x)/b(n,0) → exp x`.  Consequently every fixed prime-power atom
loses its Euler damping as the order grows. -/
theorem reverseBesselPoly_div_tendsto_exp {x : ℝ} (hx : 0 ≤ x) :
    Filter.Tendsto (fun n : ℕ => reverseBesselPoly n x / (squaredRadialJetWeight n 0 : ℝ))
      Filter.atTop (nhds (Real.exp x)) := by
  have hFtsum : ∀ n, reverseBesselPoly n x / (squaredRadialJetWeight n 0 : ℝ)
      = ∑' k, reverseBesselRatio n k * x ^ k := by
    intro n
    have hsum_eq : reverseBesselPoly n x / (squaredRadialJetWeight n 0 : ℝ)
        = ∑ k ∈ Finset.range (n + 1), reverseBesselRatio n k * x ^ k := by
      unfold reverseBesselPoly
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro k _; unfold reverseBesselRatio; ring
    rw [hsum_eq, tsum_eq_sum (s := Finset.range (n + 1))]
    intro k hk
    have hkn : n < k := by simpa [Nat.lt_succ_iff] using hk
    unfold reverseBesselRatio
    rw [squaredRadialJetWeight_eq_zero_of_lt n k hkn]; simp
  have hlim_g : ∀ k : ℕ, Filter.Tendsto (fun n => reverseBesselRatio n k * x ^ k) Filter.atTop
      (nhds (x ^ k / (k.factorial : ℝ))) := by
    intro k
    have := (reverseBesselRatio_tendsto k).mul_const (x ^ k)
    rwa [show (1 / (k.factorial : ℝ)) * x ^ k = x ^ k / (k.factorial : ℝ) from by ring] at this
  have hbound : ∀ n : ℕ, ∀ k : ℕ,
      ‖reverseBesselRatio n k * x ^ k‖ ≤ x ^ k / (k.factorial : ℝ) := by
    intro n k
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (reverseBesselRatio_nonneg n k),
        abs_of_nonneg (by positivity : (0:ℝ) ≤ x ^ k)]
    calc reverseBesselRatio n k * x ^ k
        ≤ (1 / (k.factorial : ℝ)) * x ^ k := by
          gcongr; exact reverseBesselRatio_le n k
      _ = x ^ k / (k.factorial : ℝ) := by ring
  have hsummable : Summable (fun k : ℕ => x ^ k / (k.factorial : ℝ)) :=
    Real.summable_pow_div_factorial x
  have htan := tendsto_tsum_of_dominated_convergence hsummable hlim_g
    (Filter.Eventually.of_forall hbound)
  have hexp : (∑' k : ℕ, x ^ k / (k.factorial : ℝ)) = Real.exp x := by
    rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
  rw [hexp] at htan
  exact htan.congr' (Filter.Eventually.of_forall (fun n => (hFtsum n).symm))

/-- **Fixed Euler-frequency blindness** (`(4)`): at any fixed `w > 0` and integer `m ≥ 2`, the
Euler-damped normalised jet atom `m^{-1/2-w} B_n(w log m)/b(n,0)` loses its damping and converges to
`m^{-1/2}` as the order grows. -/
theorem reverseBessel_fixed_frequency_blind {w : ℝ} (hw : 0 < w) {m : ℕ} (hm : 2 ≤ m) :
    Filter.Tendsto
      (fun n : ℕ => (m:ℝ) ^ (-(1/2 : ℝ) - w)
        * (reverseBesselPoly n (w * Real.log m) / (squaredRadialJetWeight n 0 : ℝ)))
      Filter.atTop (nhds ((m:ℝ) ^ (-(1/2 : ℝ)))) := by
  have hm1 : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast (by omega : 1 ≤ m)
  have hmpos : (0:ℝ) < (m:ℝ) := by exact_mod_cast (by omega : 0 < m)
  have hlognn : 0 ≤ w * Real.log m := mul_nonneg hw.le (Real.log_nonneg hm1)
  have h3 := reverseBesselPoly_div_tendsto_exp (x := w * Real.log m) hlognn
  have hexp : Real.exp (w * Real.log m) = (m:ℝ) ^ w := by
    rw [Real.rpow_def_of_pos hmpos, mul_comm]
  rw [hexp] at h3
  have hmul := h3.const_mul ((m:ℝ) ^ (-(1/2 : ℝ) - w))
  have hpow : (m:ℝ) ^ (-(1/2 : ℝ) - w) * (m:ℝ) ^ w = (m:ℝ) ^ (-(1/2 : ℝ)) := by
    rw [← Real.rpow_add hmpos]; congr 1; ring
  rwa [hpow] at hmul

end

end RHTower
