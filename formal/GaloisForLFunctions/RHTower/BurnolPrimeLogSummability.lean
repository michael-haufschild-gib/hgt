import Mathlib

/-!
# Prime-log summability thresholds

The all-prime Burnol entrance walls separate two elementary series over the primes:
`∑ 1 / (p (log p)²)` converges, while `∑ 1 / p` diverges.  The convergent side is proved by a
telescoping comparison with `1/log n - 1/log (n+1)`, the divergent side is Euler's theorem.

Two auxiliary growth facts are recorded here as well: every power of `log` is eventually dominated
by every positive power of the variable, and every power of the variable is dominated by an
exponential of its square root.  Together they place the critical exponent of the inverse-completion
wall at `Re ρ = 1/2`.
-/

open Real Filter Topology Asymptotics

noncomputable section

namespace RHTower

/-! ## The convergent side -/

/-- One telescoping step: the reciprocal of `n (log n)²` is dominated by the decrement of
`1/log n`.  The mechanism is `log (1 + 1/a) ≥ 1/(a+1)` together with `log a ≤ log (a+1)`. -/
theorem burnolLogTelescopeStep (n : ℕ) :
    1 / (((n : ℝ) + 3) * Real.log ((n : ℝ) + 3) ^ 2) ≤
      1 / Real.log ((n : ℝ) + 2) - 1 / Real.log ((n : ℝ) + 3) := by
  set a : ℝ := (n : ℝ) + 2 with ha
  set b : ℝ := (n : ℝ) + 3 with hb
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have ha2 : (2 : ℝ) ≤ a := by simp only [ha]; linarith
  have hab : b = a + 1 := by simp only [ha, hb]; ring
  have hapos : (0 : ℝ) < a := by linarith
  have hbpos : (0 : ℝ) < b := by rw [hab]; linarith
  have hloga : 0 < Real.log a := Real.log_pos (by linarith)
  have hlogb : 0 < Real.log b := Real.log_pos (by rw [hab]; linarith)
  have hmono : Real.log a ≤ Real.log b := Real.log_le_log hapos (by rw [hab]; linarith)
  -- `log b - log a = log (b/a) ≥ 1 - a/b = 1/b`
  have hkey : 1 / b ≤ Real.log b - Real.log a := by
    have hdiv : Real.log (b / a) = Real.log b - Real.log a :=
      Real.log_div (ne_of_gt hbpos) (ne_of_gt hapos)
    have hlow : 1 - (b / a)⁻¹ ≤ Real.log (b / a) := by
      have h := Real.log_le_sub_one_of_pos (x := (b / a)⁻¹) (by positivity)
      rw [Real.log_inv] at h
      linarith
    have hinv : (b / a)⁻¹ = a / b := by
      rw [inv_div]
    rw [hinv] at hlow
    have hba : b - a = 1 := by rw [hab]; ring
    have hval : 1 - a / b = 1 / b := by
      field_simp
      linarith
    rw [hval] at hlow
    linarith [hdiv ▸ hlow]
  -- assemble
  have hrhs : 1 / Real.log a - 1 / Real.log b = (Real.log b - Real.log a) /
      (Real.log a * Real.log b) := by
    field_simp
  rw [hrhs, div_le_div_iff₀ (by positivity) (by positivity)]
  have h1 : Real.log a * Real.log b ≤ Real.log b ^ 2 := by nlinarith
  have hkey' : 1 ≤ b * (Real.log b - Real.log a) := by
    have h := mul_le_mul_of_nonneg_left hkey hbpos.le
    rwa [mul_one_div, div_self (ne_of_gt hbpos)] at h
  nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ b * (Real.log b - Real.log a) - 1)
    (sq_nonneg (Real.log b))]

/-- Convergence of `∑ 1 / (n (log n)²)` over the shifted index. -/
theorem burnolSummable_shifted_one_div_mul_log_sq :
    Summable (fun n : ℕ => 1 / (((n : ℝ) + 3) * Real.log ((n : ℝ) + 3) ^ 2)) := by
  refine summable_of_sum_range_le (c := 1 / Real.log 2) (fun n => by positivity) ?_
  intro N
  have hstep : ∀ i ∈ Finset.range N,
      1 / (((i : ℝ) + 3) * Real.log ((i : ℝ) + 3) ^ 2) ≤
        (fun k : ℕ => 1 / Real.log ((k : ℝ) + 2)) i -
          (fun k : ℕ => 1 / Real.log ((k : ℝ) + 2)) (i + 1) := by
    intro i _
    have := burnolLogTelescopeStep i
    simpa only [Nat.cast_add, Nat.cast_one] using by
      simpa [show ((i : ℝ) + 1 + 2) = (i : ℝ) + 3 by ring] using this
  refine (Finset.sum_le_sum hstep).trans ?_
  rw [Finset.sum_range_sub' (fun k : ℕ => 1 / Real.log ((k : ℝ) + 2))]
  have hpos : 0 ≤ 1 / Real.log ((N : ℝ) + 2) := by
    have : (0 : ℝ) < Real.log ((N : ℝ) + 2) :=
      Real.log_pos (by have := Nat.cast_nonneg (α := ℝ) N; linarith)
    positivity
  simp only [Nat.cast_zero, zero_add]
  linarith

/-- **Convergence of the critical integer series.** -/
theorem burnolSummable_one_div_mul_log_sq :
    Summable (fun n : ℕ => 1 / ((n : ℝ) * Real.log (n : ℝ) ^ 2)) := by
  rw [← summable_nat_add_iff 3]
  refine burnolSummable_shifted_one_div_mul_log_sq.congr (fun n => ?_)
  push_cast
  ring_nf

/-- **Convergence over the primes.** -/
theorem burnolSummable_prime_one_div_mul_log_sq :
    Summable (fun p : Nat.Primes => 1 / ((p : ℝ) * Real.log (p : ℝ) ^ 2)) :=
  burnolSummable_one_div_mul_log_sq.subtype _

/-- **Euler's divergence, on the prime subtype.** -/
theorem burnolNotSummable_prime_one_div : ¬ Summable (fun p : Nat.Primes => 1 / (p : ℝ)) := by
  intro h
  exact not_summable_one_div_on_primes (summable_subtype_iff_indicator.mp h)

/-- Square-summability of the prime reciprocals. -/
theorem burnolSummable_prime_one_div_sq :
    Summable (fun p : Nat.Primes => 1 / ((p : ℝ) ^ 2)) :=
  (Real.summable_one_div_nat_pow.mpr one_lt_two).subtype _

/-! ## Growth comparisons -/

/-- Every power of `log` is eventually dominated by every positive power of the variable. -/
theorem burnolEventually_log_pow_le_rpow {δ : ℝ} (hδ : 0 < δ) (k : ℕ) :
    ∀ᶠ x : ℝ in atTop, Real.log x ^ k ≤ x ^ δ := by
  have h := _root_.isLittleO_log_rpow_rpow_atTop (s := δ) (k : ℝ) hδ
  have h1 := h.bound (c := 1) one_pos
  filter_upwards [h1, eventually_ge_atTop (1 : ℝ)] with x hx hx1
  have hlognn : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hxpos : (0 : ℝ) < x := lt_of_lt_of_le one_pos hx1
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity), one_mul] at hx
  calc Real.log x ^ k = Real.log x ^ (k : ℝ) := by
        rw [Real.rpow_natCast]
    _ ≤ x ^ δ := hx

/-- The prime-log tail with subexponential damping is dominated by the critical series:
`u^k e^{-2y√u} ≤ C / u²` for every `u > 0`. -/
theorem burnolPow_mul_exp_neg_sqrt_le {y : ℝ} (hy : 0 < y) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : ℝ, 0 < u →
      u ^ k * Real.exp (-(2 * y * Real.sqrt u)) ≤ C / u ^ 2 := by
  classical
  set m : ℕ := 2 * k + 4 with hm
  set C₀ : ℝ := (m.factorial : ℝ) / (2 * y) ^ m with hC₀
  have hC₀pos : 0 < C₀ := by positivity
  have hbig : ∀ u : ℝ, 1 ≤ u → u ^ k * Real.exp (-(2 * y * Real.sqrt u)) ≤ C₀ / u ^ 2 := by
    intro u hu
    have hupos : (0 : ℝ) < u := lt_of_lt_of_le one_pos hu
    set v : ℝ := Real.sqrt u with hv
    have hvpos : (0 : ℝ) < v := Real.sqrt_pos.mpr hupos
    have hv2 : v ^ 2 = u := Real.sq_sqrt hupos.le
    have h2y : (0 : ℝ) < 2 * y := by positivity
    have hfac : (0 : ℝ) < (m.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos m
    have hE : (0 : ℝ) < Real.exp (2 * y * v) := Real.exp_pos _
    have hexp : (2 * y * v) ^ m / (m.factorial : ℝ) ≤ Real.exp (2 * y * v) := by
      have hnn : (0 : ℝ) ≤ 2 * y * v := by positivity
      have hsum := Real.sum_le_exp_of_nonneg hnn (m + 1)
      have hmem : (2 * y * v) ^ m / (m.factorial : ℝ) ≤
          ∑ i ∈ Finset.range (m + 1), (2 * y * v) ^ i / (i.factorial : ℝ) :=
        Finset.single_le_sum (f := fun i : ℕ => (2 * y * v) ^ i / (i.factorial : ℝ))
          (fun i _ => by positivity) (Finset.self_mem_range_succ m)
      linarith
    have hkey : v ^ m ≤ C₀ * Real.exp (2 * y * v) := by
      have hexpand : (2 * y * v) ^ m = (2 * y) ^ m * v ^ m := by rw [mul_pow]
      rw [hexpand, div_le_iff₀ hfac] at hexp
      have hform : C₀ * Real.exp (2 * y * v) =
          (Real.exp (2 * y * v) * (m.factorial : ℝ)) / (2 * y) ^ m := by
        rw [hC₀]
        ring
      rw [hform, le_div_iff₀ (by positivity : (0 : ℝ) < (2 * y) ^ m), mul_comm]
      exact hexp
    have hrewrite : u ^ k * Real.exp (-(2 * y * v)) = v ^ m / (v ^ 4 * Real.exp (2 * y * v)) := by
      have hmsplit : v ^ m = v ^ (2 * k) * v ^ 4 := by rw [hm, ← pow_add]
      rw [Real.exp_neg, hmsplit, pow_mul, hv2]
      field_simp
    rw [hrewrite]
    have hu2 : u ^ 2 = v ^ 4 := by rw [← hv2]; ring
    rw [hu2, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_right hkey (by positivity : (0 : ℝ) ≤ v ^ 4), hE,
      pow_nonneg hvpos.le 4]
  refine ⟨max 1 C₀, lt_of_lt_of_le one_pos (le_max_left _ _), ?_⟩
  intro u hu
  rcases le_or_gt 1 u with hge | hlt
  · refine (hbig u hge).trans ?_
    exact div_le_div_of_nonneg_right (le_max_right 1 C₀) (by positivity) |>.trans_eq rfl
  · have hsmall : u ^ k * Real.exp (-(2 * y * Real.sqrt u)) ≤ 1 := by
      have h1 : u ^ k ≤ 1 := pow_le_one₀ hu.le hlt.le
      have h2 : Real.exp (-(2 * y * Real.sqrt u)) ≤ 1 := by
        refine Real.exp_le_one_iff.mpr ?_
        have : 0 ≤ 2 * y * Real.sqrt u := by positivity
        linarith
      nlinarith [Real.exp_pos (-(2 * y * Real.sqrt u)), pow_nonneg hu.le k]
    refine hsmall.trans ?_
    rw [le_div_iff₀ (by positivity)]
    have hu2 : u ^ 2 ≤ 1 := by nlinarith
    have hCge : (1 : ℝ) ≤ max 1 C₀ := le_max_left _ _
    nlinarith

end RHTower
