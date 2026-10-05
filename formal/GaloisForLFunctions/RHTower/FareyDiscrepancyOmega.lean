import GaloisForLFunctions.RHTower.FareyDiscrepancyFranelSquareLaw
import GaloisForLFunctions.RHTower.MertensSquareRootOmega

/-!
# Ω-theorems for the Farey discrepancy

Unconditionally, `Σ_ν |f_ν - ν/L| > c√n` and `Σ_ν (f_ν - ν/L)² > c/n` for infinitely many `n`.
Landau's inequality `|M(n)| ≤ 2π Σ_ν |δ_ν|` transports `M(x) = Ω(√x)`, and
`(Σ|δ_ν|)² ≤ L Σ δ_ν² ≤ n² Σ δ_ν²` passes to the square discrepancy.  The exponents `½` and `-1`
of the Franel–Landau criteria are therefore attained.
-/

open Finset Filter

open RHTower.Sieve (fareySet mem_fareySet)

namespace RHTower

noncomputable section

theorem norm_mobiusMertensPartialSum_eq_abs_mertensFunctionReal (n : ℕ) :
    ‖mobiusMertensPartialSum n‖ = |mertensFunctionReal n| := by
  rw [mobiusMertensPartialSum_eq_mertensIoc, Complex.norm_intCast, mertensFunctionReal,
    Nat.floor_natCast, mertensIoc]
  congr 1
  push_cast
  refine sum_congr ?_ fun k _ => rfl
  ext k; simp only [mem_Ioc, mem_Icc]; omega

/-- **`Σ_ν |δ_ν|` is not `o(√n)`.**  For some `c > 0`, `Σ_ν |f_ν - ν/L| > c√n` for infinitely
many `n`. -/
theorem exists_frequently_sqrt_lt_fareyL1Discrepancy :
    ∃ c : ℝ, 0 < c ∧ ∃ᶠ n : ℕ in atTop, c * Real.sqrt n < fareyL1Discrepancy n := by
  obtain ⟨c, hc, hfreq, _⟩ := mertens_omega_pm_sqrt
  refine ⟨c / (2 * Real.pi), by positivity, ?_⟩
  rw [Nat.frequently_atTop_iff_infinite]
  intro hfin
  obtain ⟨N, hN⟩ := hfin.bddAbove
  obtain ⟨x, hxc, hx⟩ := (hfreq.and_eventually (eventually_ge_atTop ((N : ℝ) + 2))).exists
  set n := ⌊x⌋₊ with hn
  have hx0 : 0 ≤ x := by linarith
  have hnx : (n : ℝ) ≤ x := Nat.floor_le hx0
  have hnN : N + 1 < n := by
    have := Nat.lt_floor_add_one x
    have h2 : (N : ℝ) + 1 < n := by
      have := Nat.floor_le hx0
      have h3 : x - 1 < n := by linarith [Nat.lt_floor_add_one x]
      linarith
    exact_mod_cast h2
  have hM : mertensFunctionReal x = mertensFunctionReal n := by
    simp [mertensFunctionReal, hn]
  have hn2 : 2 ≤ n := by omega
  have hL := norm_mobiusMertensPartialSum_le_fareyL1Discrepancy hn2
  rw [norm_mobiusMertensPartialSum_eq_abs_mertensFunctionReal] at hL
  have hsq : c * Real.sqrt n ≤ c * Real.sqrt x :=
    mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hnx) hc.le
  have hmem : n ∈ {n : ℕ | c / (2 * Real.pi) * Real.sqrt n < fareyL1Discrepancy n} := by
    show c / (2 * Real.pi) * Real.sqrt n < fareyL1Discrepancy n
    have hπ : 0 < 2 * Real.pi := by positivity
    have h1 : c * Real.sqrt n < |mertensFunctionReal n| := by
      rw [← hM]; exact lt_of_le_of_lt hsq (lt_of_lt_of_le hxc (le_abs_self _))
    rw [div_mul_eq_mul_div, div_lt_iff₀ hπ]
    linarith
  have := hN hmem
  omega

/-- **`Σ_ν δ_ν²` is not `o(1/n)`.**  For some `c > 0`, `Σ_ν (f_ν - ν/L)² > c/n` for infinitely
many `n`. -/
theorem exists_frequently_inv_lt_fareyL2Discrepancy :
    ∃ c : ℝ, 0 < c ∧ ∃ᶠ n : ℕ in atTop, c / n < fareyL2Discrepancy n := by
  obtain ⟨c, hc, hfreq⟩ := exists_frequently_sqrt_lt_fareyL1Discrepancy
  refine ⟨c ^ 2, by positivity, ?_⟩
  refine (hfreq.and_eventually (eventually_ge_atTop 1)).mono fun n ⟨hn, hn1⟩ => ?_
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hsq := sq_fareyL1Discrepancy_le n
  have hL : ((fareySet n).card : ℝ) ≤ (n : ℝ) ^ 2 := by exact_mod_cast card_fareySet_le n
  have h1 : (c * Real.sqrt n) ^ 2 < fareyL1Discrepancy n ^ 2 :=
    pow_lt_pow_left₀ hn (by positivity) two_ne_zero
  rw [mul_pow, Real.sq_sqrt hn0.le] at h1
  have h2 : fareyL1Discrepancy n ^ 2 ≤ (n : ℝ) ^ 2 * fareyL2Discrepancy n :=
    hsq.trans (mul_le_mul_of_nonneg_right hL (fareyL2Discrepancy_nonneg n))
  rw [div_lt_iff₀ hn0]
  nlinarith

end

end RHTower
