import GaloisForLFunctions.LogarithmicChowla.TwistVarLimit
import GaloisForLFunctions.LogarithmicChowla.PrimeKernelBound

/-!
# Logarithmic two-point Chowla

For every `h ≥ 1` (`tendsto_logAvg_liouville_shift`):

`(1/log x) Σ_{n ≤ x} λ(n)λ(n+h)/n → 0`.

For an ultrafilter `U ≤ atTop` and `c(h) = L_U(λ(n)λ(n+h))` (`corr_eq_zero`): §4 gives scales `k`
with `|c(h) − avg_{p∈𝐏_k} c(ph)| ≤ 6ε` arbitrarily far out (`exists_scale_corr_close`); §5–§6 give
`|avg_{p∈𝐏_k} c(ph)| ≤ η + 4Σ_{s ≤ hQ₀}Σ_{b<s} V(b/s, T)` for `4TW ≤ 2^k`
(`exists_abs_avg_corr_le`); and `V(b/s, T) → 0` (`tendsto_twistVar_zero`).  With `T = ⌊2^k/(4W)⌋`,
`|c(h)| ≤ 8ε` for every `ε`.  Bounded sequences whose limit functionals all vanish have vanishing
logarithmic averages (`tendsto_logAvg_of_forall_limAvg_eq_zero`).
-/

namespace GaloisForLFunctions.LogarithmicChowla

open Finset Filter Topology

noncomputable section
set_option autoImplicit false

variable {U : Ultrafilter ℝ}

/-- The arc sums of the circle method tend to zero. -/
theorem tendsto_sum_twistVar_zero (hU : (U : Filter ℝ) ≤ atTop) (h Q₀ : ℕ) :
    Tendsto (fun T : ℕ => ∑ s ∈ Icc 1 (h * Q₀), ∑ b ∈ range s, twistVar U ((b : ℝ) / s) T)
      atTop (𝓝 0) := by
  have := tendsto_finsetSum
    (f := fun (s : ℕ) (T : ℕ) => ∑ b ∈ range s, twistVar U ((b : ℝ) / s) T)
    (a := fun _ => (0 : ℝ)) (x := atTop) (Icc 1 (h * Q₀)) fun s hs => by
      have := tendsto_finsetSum (f := fun (b : ℕ) (T : ℕ) => twistVar U ((b : ℝ) / s) T)
        (a := fun _ => (0 : ℝ)) (x := atTop) (range s)
        fun b _ => tendsto_twistVar_zero hU (mem_Icc.mp hs).1 b
      rw [sum_const_zero] at this
      exact this
  rw [sum_const_zero] at this
  exact this

/-- **The two-point correlation of `λ` vanishes under every limit functional.** -/
theorem corr_eq_zero (hU : (U : Filter ℝ) ≤ atTop) {h : ℕ} (hh : 0 < h) : corr U h = 0 := by
  have key : ∀ ε : ℝ, 0 < ε → ε ≤ 1 → |corr U h| ≤ 8 * ε := by
    intro ε hε hε1
    obtain ⟨Q₀, W, hW, k₁, hK⟩ := exists_abs_avg_corr_le hU h hh hε hε1
    obtain ⟨T₁, hT₁⟩ := eventually_atTop.mp
      ((tendsto_sum_twistVar_zero hU h Q₀).eventually (ge_mem_nhds (by linarith : (0 : ℝ) < ε / 4)))
    obtain ⟨k₂, hk₂⟩ := pow_unbounded_of_one_lt (4 * W * ((T₁ : ℝ) + 1)) (by norm_num : (1 : ℝ) < 2)
    obtain ⟨k, hkK, hclose⟩ := exists_scale_corr_close hU h hε hε1 (max k₁ k₂)
    have hk1 : k₁ ≤ k := le_trans (le_max_left _ _) hkK
    have hk2 : k₂ ≤ k := le_trans (le_max_right _ _) hkK
    have h2k : (2 : ℝ) ^ k₂ ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) hk2
    have hW4 : (0 : ℝ) < 4 * W := by linarith
    set T := ⌊(2 : ℝ) ^ k / (4 * W)⌋₊ with hTdef
    have hTT₁ : T₁ + 1 ≤ T := by
      rw [hTdef]
      refine Nat.le_floor ?_
      rw [le_div_iff₀ hW4]
      push_cast
      nlinarith
    have hT0 : 0 < T := by omega
    have hTW : 4 * (T : ℝ) * W ≤ 2 ^ k := by
      have h1 : (T : ℝ) ≤ (2 : ℝ) ^ k / (4 * W) := Nat.floor_le (by positivity)
      rw [le_div_iff₀ hW4] at h1
      linarith
    have havg := hK k hk1 T hT0 hTW
    have hS := hT₁ T (by omega)
    have h1 : |(∑ p : primesAt k, corr U ((p : ℕ) * h)) / (primesAt k).card| ≤ 2 * ε := by
      linarith
    calc |corr U h|
        = |(corr U h - (∑ p : primesAt k, corr U ((p : ℕ) * h)) / (primesAt k).card)
            + (∑ p : primesAt k, corr U ((p : ℕ) * h)) / (primesAt k).card| := by
          rw [sub_add_cancel]
      _ ≤ |corr U h - (∑ p : primesAt k, corr U ((p : ℕ) * h)) / (primesAt k).card|
            + |(∑ p : primesAt k, corr U ((p : ℕ) * h)) / (primesAt k).card| := abs_add_le _ _
      _ ≤ 6 * ε + 2 * ε := add_le_add hclose h1
      _ = 8 * ε := by ring
  have h0 : |corr U h| ≤ 0 := by
    refine le_of_forall_pos_le_add fun δ hδ => ?_
    have := key (min (δ / 8) 1) (by positivity) (min_le_right _ _)
    have : 8 * min (δ / 8) 1 ≤ δ := by
      have := min_le_left (δ / 8) 1; linarith
    linarith
  exact abs_nonpos_iff.mp h0

/-- **Logarithmic two-point Chowla.**  For every `h ≥ 1`,
`(1/log x) Σ_{n ≤ x} λ(n)λ(n+h)/n → 0`. -/
theorem tendsto_logAvg_liouville_shift {h : ℕ} (hh : 0 < h) :
    Tendsto (logAvg fun n => lam n * lam (n + h)) atTop (𝓝 0) :=
  tendsto_logAvg_of_forall_limAvg_eq_zero ((bdd_lam_comp id).mul (bdd_lam_comp (· + h)))
    fun _ hU => corr_eq_zero hU hh

end

end GaloisForLFunctions.LogarithmicChowla
