import GaloisForLFunctions.RHTower.Sieve.PerronFiniteSum
import GaloisForLFunctions.RHTower.Sieve.HarmonicLogBound

/-!
# The truncation error of the sharp Perron formula at a half-integer cutoff

Placing the cutoff at `x = N + 1/2` separates it from every integer by at least `1/2`, and the
logarithmic separation is then bounded below uniformly:

`|log((N + 1/2)/n)| ≥ 1/(2N+2)`   for every integer `n ≥ 1`,

because `log y ≥ 1 − 1/y` on both sides of `1`.  With a uniform bound `B` on the coefficients and a
support inside `[1, M]`, the Perron error is therefore

`∑_n ‖c_n‖(x/n)^σ/(πT|log(x/n)|) ≤ 2(N+1)·B·x^σ·(1 + log M)/(πT)`,

the harmonic sum `∑_{n ≤ M} n^{-σ} ≤ 1 + log M` absorbing the whole support.

The factor `N` this costs is bought back by the height: at `T = N²` the error is
`O(B·x^{σ−1}(1 + log M))`, polylogarithmic for polylogarithmic coefficients, while the height enters
the main term only through the *number* of dyadic blocks, `log₂ T`.  The near-diagonal harmonic
analysis that a truncation at `T = N` would require is thus unnecessary: raising the height is
cheaper than sharpening the separation.
-/

noncomputable section
namespace RHTower.Sieve
open Complex MeasureTheory Set

/-- `log y ≥ 1 − 1/y` for positive `y`, the reflection of `log y ≤ y − 1`. -/
theorem one_sub_inv_le_log {y : ℝ} (hy : 0 < y) : 1 - 1 / y ≤ Real.log y := by
  have hinv : (0 : ℝ) < 1 / y := by positivity
  have h := Real.log_le_sub_one_of_pos hinv
  rw [one_div, Real.log_inv] at h
  have hy' : (1 : ℝ) / y = y⁻¹ := one_div y
  rw [hy']
  linarith

/-- **The logarithmic separation at a half-integer cutoff.**  Every integer `n ≥ 1` is separated from
`N + 1/2` by `|log((N+1/2)/n)| ≥ 1/(2N+2)`. -/
theorem inv_le_abs_log_div_half_integer {N n : ℕ} (hN : 1 ≤ N) (hn : 1 ≤ n) :
    1 / (2 * ((N : ℝ) + 1)) ≤ |Real.log (((N : ℝ) + 1 / 2) / n)| := by
  have hN0 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hn0 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hx : (0 : ℝ) < (N : ℝ) + 1 / 2 := by linarith
  set x : ℝ := (N : ℝ) + 1 / 2 with hxdef
  by_cases hle : n ≤ N
  · -- below the cutoff: `x/n ≥ x/N`
    have hnN : (n : ℝ) ≤ (N : ℝ) := by exact_mod_cast hle
    have hratio : (1 : ℝ) < x / n := by
      rw [lt_div_iff₀ (by linarith)]
      rw [hxdef]
      linarith
    have hlog : 1 - (n : ℝ) / x ≤ Real.log (x / n) := by
      have h := one_sub_inv_le_log (y := x / n) (by positivity)
      have hinv : 1 / (x / n) = (n : ℝ) / x := by
        rw [one_div_div]
      rw [hinv] at h
      exact h
    have hlower : 1 / (2 * ((N : ℝ) + 1)) ≤ 1 - (n : ℝ) / x := by
      have hstep : (n : ℝ) / x ≤ (N : ℝ) / x := by
        exact div_le_div_of_nonneg_right hnN hx.le
      have hval : 1 - (N : ℝ) / x = (1 / 2) / x := by
        rw [hxdef]
        field_simp
        ring
      have hx2 : (1 / 2) / x ≥ 1 / (2 * ((N : ℝ) + 1)) := by
        rw [ge_iff_le, div_le_div_iff₀ (by positivity) (by positivity)]
        rw [hxdef]
        linarith
      linarith
    rw [abs_of_nonneg (Real.log_nonneg hratio.le)]
    linarith
  · -- above the cutoff: `n/x ≥ (N+1)/x`
    have hnN : (N : ℝ) + 1 ≤ (n : ℝ) := by
      have : N + 1 ≤ n := by omega
      exact_mod_cast this
    have hratio : x / n < 1 := by
      rw [div_lt_one (by linarith)]
      rw [hxdef]
      linarith
    have hlog : 1 - x / n ≤ Real.log ((n : ℝ) / x) := by
      have h := one_sub_inv_le_log (y := (n : ℝ) / x) (by positivity)
      have hinv : 1 / ((n : ℝ) / x) = x / n := by rw [one_div_div]
      rw [hinv] at h
      exact h
    have hneg : Real.log (x / n) = -Real.log ((n : ℝ) / x) := by
      rw [← Real.log_inv, inv_div]
    have hlower : 1 / (2 * ((N : ℝ) + 1)) ≤ 1 - x / n := by
      have hstep : x / n ≤ x / ((N : ℝ) + 1) :=
        div_le_div_of_nonneg_left hx.le (by linarith) hnN
      have hval : 1 - x / ((N : ℝ) + 1) = (1 / 2) / ((N : ℝ) + 1) := by
        rw [hxdef]
        field_simp
        ring
      have hx2 : (1 / 2) / ((N : ℝ) + 1) = 1 / (2 * ((N : ℝ) + 1)) := by
        rw [div_div]
      linarith
    rw [hneg, abs_neg, abs_of_nonneg (le_trans (by linarith) hlog)]
    linarith

/-- **The Perron truncation error at a half-integer cutoff.**  A uniform coefficient bound and a
support inside `[1, M]` give an error `2(N+1)·B·x^σ·(1 + log M)/(πT)`. -/
theorem perron_truncation_error_le {c : ℕ → ℂ} {s : Finset ℕ} {M : ℕ} (hs : s ⊆ Finset.Icc 1 M)
    {B : ℝ} (hB : ∀ n, ‖c n‖ ≤ B) {N : ℕ} (hN : 1 ≤ N) {σ T : ℝ} (hσ : 1 ≤ σ) (hT : 0 < T) :
    (∑ n ∈ s, ‖c n‖ * ((((N : ℝ) + 1 / 2) / n) ^ σ
        / (Real.pi * T * |Real.log (((N : ℝ) + 1 / 2) / n)|)))
      ≤ 2 * ((N : ℝ) + 1) * B * (((N : ℝ) + 1 / 2)) ^ σ * (1 + Real.log M) / (Real.pi * T) := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hN0 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hx : (0 : ℝ) < (N : ℝ) + 1 / 2 := by linarith
  have hB0 : (0 : ℝ) ≤ B := le_trans (norm_nonneg (c 1)) (hB 1)
  set x : ℝ := (N : ℝ) + 1 / 2 with hxdef
  set K : ℝ := 2 * ((N : ℝ) + 1) * B * x ^ σ / (Real.pi * T) with hK
  have hK0 : (0 : ℝ) ≤ K := by
    rw [hK]
    have : (0 : ℝ) ≤ x ^ σ := Real.rpow_nonneg hx.le σ
    positivity
  -- each term is at most `K/n`
  have hterm : ∀ n ∈ s, ‖c n‖ * ((x / n) ^ σ / (Real.pi * T * |Real.log (x / n)|))
      ≤ K * (1 / (n : ℝ)) := by
    intro n hn
    have hn1 : 1 ≤ n := (Finset.mem_Icc.1 (hs hn)).1
    have hn0 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
    have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
    have hsep : 1 / (2 * ((N : ℝ) + 1)) ≤ |Real.log (x / n)| :=
      inv_le_abs_log_div_half_integer hN hn1
    have hsep0 : (0 : ℝ) < |Real.log (x / n)| :=
      lt_of_lt_of_le (by positivity) hsep
    -- replace the logarithm by its lower bound
    have hden : Real.pi * T * (1 / (2 * ((N : ℝ) + 1))) ≤ Real.pi * T * |Real.log (x / n)| :=
      mul_le_mul_of_nonneg_left hsep (by positivity)
    have hnum0 : (0 : ℝ) ≤ (x / n) ^ σ := Real.rpow_nonneg (by positivity) σ
    have hstep1 : (x / n) ^ σ / (Real.pi * T * |Real.log (x / n)|)
        ≤ (x / n) ^ σ / (Real.pi * T * (1 / (2 * ((N : ℝ) + 1)))) :=
      div_le_div_of_nonneg_left hnum0 (by positivity) hden
    -- the power splits and the exponent drops to one
    have hpow : (x / n) ^ σ ≤ x ^ σ * (1 / (n : ℝ)) := by
      have hge : (n : ℝ) ≤ (n : ℝ) ^ σ := by
        have h1 : ((n : ℝ)) ^ (1 : ℝ) ≤ ((n : ℝ)) ^ σ :=
          Real.rpow_le_rpow_of_exponent_le hn0 hσ
        rwa [Real.rpow_one] at h1
      have hxσ : (0 : ℝ) ≤ x ^ σ := Real.rpow_nonneg hx.le σ
      rw [Real.div_rpow hx.le (by positivity), mul_one_div]
      exact div_le_div_of_nonneg_left hxσ hnpos hge
    have hfrac : Real.pi * T * (1 / (2 * ((N : ℝ) + 1))) = Real.pi * T / (2 * ((N : ℝ) + 1)) := by
      field_simp
    calc ‖c n‖ * ((x / n) ^ σ / (Real.pi * T * |Real.log (x / n)|))
        ≤ B * ((x / n) ^ σ / (Real.pi * T * (1 / (2 * ((N : ℝ) + 1))))) := by
          refine mul_le_mul (hB n) hstep1 (by positivity) hB0
      _ = B * (2 * ((N : ℝ) + 1)) * (x / n) ^ σ / (Real.pi * T) := by
          rw [hfrac]
          field_simp
      _ ≤ B * (2 * ((N : ℝ) + 1)) * (x ^ σ * (1 / (n : ℝ))) / (Real.pi * T) := by
          refine div_le_div_of_nonneg_right ?_ (by positivity)
          exact mul_le_mul_of_nonneg_left hpow (by positivity)
      _ = K * (1 / (n : ℝ)) := by
          rw [hK]
          field_simp
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [← Finset.mul_sum]
  have hsum : ∑ n ∈ s, (1 : ℝ) / (n : ℝ) ≤ 1 + Real.log M := by
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hs ?_) (sum_Icc_one_div_le_one_add_log M)
    intro n _ _
    positivity
  refine le_trans (mul_le_mul_of_nonneg_left hsum hK0) (le_of_eq ?_)
  rw [hK]
  field_simp

/-- The cutoff at `N + 1/2` selects exactly the integers up to `N`. -/
theorem filter_lt_half_integer (M N : ℕ) :
    Finset.filter (fun n : ℕ => ((n : ℝ) < (N : ℝ) + 1 / 2)) (Finset.Icc 1 M)
      = Finset.Icc 1 (min M N) := by
  ext n
  simp only [Finset.mem_filter, Finset.mem_Icc, le_min_iff]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨h1, h2, ?_⟩
    by_contra hcon
    have hge : N + 1 ≤ n := by omega
    have : ((N : ℝ) + 1) ≤ (n : ℝ) := by exact_mod_cast hge
    linarith
  · rintro ⟨h1, h2, h3⟩
    refine ⟨⟨h1, h2⟩, ?_⟩
    have : (n : ℝ) ≤ (N : ℝ) := by exact_mod_cast h3
    linarith

/-- **The truncated Perron formula at a cutoff anywhere.**  For coefficients supported in `[1, M]` and
bounded by `B`, the partial sum below `N + 1/2` — that is, over `[1, min M N]`, the cutoff being free to
fall inside or beyond the support — is the truncated vertical integral of the Dirichlet polynomial
against `x^s/s`, with error `2(N+1)·B·x^σ·(1 + log M)/(πT)`. -/
theorem norm_sum_Icc_sub_perron_integral_le {c : ℕ → ℂ} {M N : ℕ} (hN : 1 ≤ N)
    {B : ℝ} (hB : ∀ n, ‖c n‖ ≤ B) {σ T : ℝ} (hσ : 1 ≤ σ) (hT : 0 < T) :
    ‖(∑ n ∈ Finset.Icc 1 (min M N), c n)
        - ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ t in (-T)..T,
            (∑ n ∈ Finset.Icc 1 M, c n * ((n : ℂ) ^ (-((σ : ℂ) + (t : ℝ) * I))))
              * (((((N : ℝ) + 1 / 2) : ℝ) : ℂ) ^ ((σ : ℂ) + (t : ℝ) * I)
                  / ((σ : ℂ) + (t : ℝ) * I))‖
      ≤ 2 * ((N : ℝ) + 1) * B * (((N : ℝ) + 1 / 2)) ^ σ * (1 + Real.log M) / (Real.pi * T) := by
  have hN0 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hx : (0 : ℝ) < (N : ℝ) + 1 / 2 := by linarith
  have hs0 : (0 : ℕ) ∉ Finset.Icc 1 M := by simp
  have hne : ∀ n ∈ Finset.Icc 1 M, (n : ℝ) ≠ (N : ℝ) + 1 / 2 := by
    intro n _ h
    have h2 : (2 : ℝ) * (n : ℝ) = 2 * (N : ℝ) + 1 := by linarith
    have h2' : (2 * n : ℕ) = 2 * N + 1 := by
      have : ((2 * n : ℕ) : ℝ) = ((2 * N + 1 : ℕ) : ℝ) := by push_cast; linarith
      exact_mod_cast this
    omega
  have hmain := norm_sum_lt_sub_perron_integral_le (c := c) (s := Finset.Icc 1 M) hs0 hx hne
    (σ := σ) (T := T) (by linarith) hT
  rw [filter_lt_half_integer M N] at hmain
  refine le_trans hmain ?_
  exact perron_truncation_error_le (le_refl _) hB hN hσ hT

end RHTower.Sieve
end
