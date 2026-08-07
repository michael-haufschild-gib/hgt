import GaloisForLFunctions.RHTower.Sieve.PartialSumVsTripleConvolution
import GaloisForLFunctions.RHTower.Sieve.GhsStepFour
import GaloisForLFunctions.HTGeometry.SmoothWeightWindow
/-!
# The master bound for the partial sums of a bounded multiplicative function

The whole Granville–Harper–Soundararajan chain, in one inequality.  For totally multiplicative `f` with
`f(1) = 1` and `‖f‖ ≤ 1`, every `N ≥ 2`, every smoothing width `H > 0`, every `σ > 1` and every admissible
sieve level `Y ≤ z`:

`‖∑_{n ≤ N} f(n)‖·log N ≤ (recursion errors) + (smoothing error) + (1/2π)·(Euler)·(kernel)·√(sieve a)·√(sieve b)`.

The three groups are:

* the recursion errors `(9+c)N + N log 4 + (9+c)N(B/log 2)(1 + log log₂ N)`, all `O(N log log N)`;
* the smoothing error `(H+1)·(log⌊N+H⌋)⁴/(log 2)³`, the window length times the polylogarithmic size of the
  coefficients of the triple convolution;
* the analytic term, the three-factor Cauchy–Schwarz bound of the vertical integral, with `C` the
  quadratic-decay constant of the smoothing kernel and the two sieve quantities the Selberg-sieve
  mean-square majorants of the two prime weights.

Nothing is assumed anywhere in the chain, and no term is left implicit.  What the bound still awaits is the
arithmetic evaluation of the two sieve sums, which is where a saving in `N` — as opposed to the trivial
bound — is created.
-/

noncomputable section
namespace RHTower.Sieve
open Finset MeasureTheory Complex

variable {f : ℕ → ℂ}

/-- A convolution vanishes at `0`, so its partial sum over `range (M+1)` is its partial sum over
`Icc 1 M`. -/
theorem sum_range_convolution_eq_sum_Icc (a b : ℕ → ℂ) (M : ℕ) :
    (∑ n ∈ Finset.range (M + 1), (LSeries.convolution a b) n)
      = ∑ n ∈ Finset.Icc 1 M, (LSeries.convolution a b) n := by
  classical
  have hzero : (LSeries.convolution a b) 0 = 0 := LSeries.convolution_map_zero a b
  rw [show Finset.range (M + 1) = insert 0 (Finset.Icc 1 M) by
    ext n
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc, Nat.lt_succ_iff]
    omega]
  rw [Finset.sum_insert (by simp), hzero, zero_add]

/-- **The smoothing error for the triple convolution at a natural cutoff.**  The window carries at most
`H + 1` integers and the coefficients there are at most `(log⌊N+H⌋)⁴/(log 2)³`. -/
theorem norm_tsum_ghs_smoothWeight_sub_sum_Icc_le (hbdd : ∀ n : ℕ, ‖f n‖ ≤ 1) (N : ℕ)
    {H : ℝ} (hH : 0 < H) :
    ‖(∑' n : ℕ,
          (LSeries.convolution (ghsOuter f N) (LSeries.convolution (ghsInner f N) f)) n
            * ((GaloisForLFunctions.HTGeometry.smoothWeight (N : ℝ) H (n : ℝ) : ℝ) : ℂ))
        - ∑ n ∈ Finset.Icc 1 N,
            (LSeries.convolution (ghsOuter f N) (LSeries.convolution (ghsInner f N) f)) n‖
      ≤ (H + 1) * ((Real.log ((⌊(N : ℝ) + H⌋₊ : ℕ) : ℝ)) ^ 4 / (Real.log 2) ^ 3) := by
  classical
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hfloor : ⌊(N : ℝ)⌋₊ = N := Nat.floor_natCast N
  have hC0 : (0 : ℝ) ≤ (Real.log ((⌊(N : ℝ) + H⌋₊ : ℕ) : ℝ)) ^ 4 / (Real.log 2) ^ 3 := by
    positivity
  have hC : ∀ n : ℕ, ⌊(N : ℝ)⌋₊ < n → n ≤ ⌊(N : ℝ) + H⌋₊ →
      ‖(LSeries.convolution (ghsOuter f N) (LSeries.convolution (ghsInner f N) f)) n‖
        ≤ (Real.log ((⌊(N : ℝ) + H⌋₊ : ℕ) : ℝ)) ^ 4 / (Real.log 2) ^ 3 := by
    intro n hn hnle
    rw [hfloor] at hn
    have hn1 : 1 ≤ n := by omega
    refine (norm_ghsTriple_le hbdd N N hn1).trans ?_
    have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
    have hlogn : (0 : ℝ) ≤ Real.log n := Real.log_nonneg hnR
    have hle : Real.log (n : ℝ) ≤ Real.log ((⌊(N : ℝ) + H⌋₊ : ℕ) : ℝ) := by
      refine Real.log_le_log (by linarith) ?_
      exact_mod_cast hnle
    exact div_le_div_of_nonneg_right (pow_le_pow_left₀ hlogn hle 4) (by positivity)
  have hmain := GaloisForLFunctions.HTGeometry.norm_tsum_mul_smoothWeight_sub_partialSum_le_width
    (a := LSeries.convolution (ghsOuter f N) (LSeries.convolution (ghsInner f N) f))
    (N := (N : ℝ)) (H := H) (C := (Real.log ((⌊(N : ℝ) + H⌋₊ : ℕ) : ℝ)) ^ 4 / (Real.log 2) ^ 3)
    (Nat.cast_nonneg N) hH hC0 hC
  rw [hfloor, sum_range_convolution_eq_sum_Icc] at hmain
  exact hmain

/-- **The master bound.**  For a totally multiplicative `f` with `‖f‖ ≤ 1`, the partial sum obeys

`‖∑_{n ≤ N} f(n)‖·log N ≤ (recursion errors) + (smoothing error) + (1/2π)·(Euler)·(kernel)·√(sieve)·√(sieve)`,

with every term explicit: the recursion errors are `O(N log log N)`, the smoothing error is
`(H+1)(log⌊N+H⌋)⁴/(log 2)³`, and the analytic term is the three-factor Cauchy–Schwarz bound of the vertical
integral.  Nothing is assumed: the whole Granville–Harper–Soundararajan chain is discharged. -/
theorem exists_norm_sum_Icc_mul_log_le (hf1 : f 1 = 1)
    (hfmul : ∀ a b : ℕ, f (a * b) = f a * f b) (hbdd : ∀ n : ℕ, ‖f n‖ ≤ 1)
    (N : ℕ) (hN : 2 ≤ N) {H : ℝ} (hH : 0 < H) {σ : ℝ} (hσ : 1 < σ)
    (z Y : ℕ) (hY : 1 ≤ Y) (hYz : Y ≤ z) (hz : 2 ≤ z) (hlog : 0 < Real.log Y) :
    ∃ C : ℝ, 0 ≤ C ∧
      ‖∑ n ∈ Finset.Icc 1 N, f n‖ * Real.log (N : ℝ)
        ≤ ((9 + RHTower.Mertens.mertensTail) * (N : ℝ) + (N : ℝ) * Real.log 4
            + (9 + RHTower.Mertens.mertensTail)
                * ((N : ℝ)
                    * (((Real.log 3 + 2 * ((Real.log 4 + 4) + (8 + RHTower.Mertens.mertensTail)))
                          / Real.log 2)
                        * (1 + Real.log ((Nat.log 2 N : ℕ) : ℝ)))))
          + (H + 1) * ((Real.log ((⌊(N : ℝ) + H⌋₊ : ℕ) : ℝ)) ^ 4 / (Real.log 2) ^ 3)
          + (1 / (2 * Real.pi))
              * (((1 + 1 / (σ - 1)) * Real.exp (7 / 2)) * C
                  * (Real.sqrt
                        (25 * Real.pi ^ 2 * sieveMeanSquare (ghsOuter f N) (Finset.Icc 1 N) σ z Y)
                      * Real.sqrt
                          (25 * Real.pi ^ 2
                            * sieveMeanSquare (ghsInner f N) (Finset.Icc 1 N) σ z Y))) := by
  classical
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hNR : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
  have hlogN : (0 : ℝ) ≤ Real.log (N : ℝ) := Real.log_nonneg (by linarith)
  have hmul : ∀ {m n : ℕ}, Nat.Coprime m n → f (m * n) = f m * f n := fun {m n} _ => hfmul m n
  obtain ⟨C, hC0, hstep4⟩ :=
    exists_norm_tsum_ghs_smoothWeight_le hf1 hmul hbdd N N hNpos hH hσ z Y hY hYz hz hlog
  refine ⟨C, hC0, ?_⟩
  set d : ℕ → ℂ :=
    LSeries.convolution (ghsOuter f N) (LSeries.convolution (ghsInner f N) f) with hd
  set Sconv : ℂ := ∑ n ∈ Finset.Icc 1 N, d n with hSconv
  set Tsm : ℂ := ∑' n : ℕ,
    d n * ((GaloisForLFunctions.HTGeometry.smoothWeight (N : ℝ) H (n : ℝ) : ℝ) : ℂ) with hTsm
  -- the paper half
  have hpaper := norm_sum_Icc_mul_log_sub_ghsTriple_le hfmul hbdd N hN
  -- the smoothing error
  have hsmooth := norm_tsum_ghs_smoothWeight_sub_sum_Icc_le hbdd N hH
  -- the analytic half, divided by 2π
  have hanalytic : ‖Tsm‖
      ≤ (1 / (2 * Real.pi))
          * (((1 + 1 / (σ - 1)) * Real.exp (7 / 2)) * C
              * (Real.sqrt
                    (25 * Real.pi ^ 2 * sieveMeanSquare (ghsOuter f N) (Finset.Icc 1 N) σ z Y)
                  * Real.sqrt
                      (25 * Real.pi ^ 2 * sieveMeanSquare (ghsInner f N) (Finset.Icc 1 N) σ z Y))) := by
    rw [one_div, inv_mul_eq_div, le_div_iff₀ hpi, mul_comm]
    exact hstep4
  -- assemble
  have hnorm : ‖∑ n ∈ Finset.Icc 1 N, f n‖ * Real.log (N : ℝ)
      = ‖(∑ n ∈ Finset.Icc 1 N, f n) * ((Real.log (N : ℝ) : ℝ) : ℂ)‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlogN]
  rw [hnorm]
  have hchain : (∑ n ∈ Finset.Icc 1 N, f n) * ((Real.log (N : ℝ) : ℝ) : ℂ)
      = ((∑ n ∈ Finset.Icc 1 N, f n) * ((Real.log (N : ℝ) : ℝ) : ℂ) - Sconv)
          + (Sconv - Tsm) + Tsm := by ring
  rw [hchain]
  have ht1 := norm_add_le
    (((∑ n ∈ Finset.Icc 1 N, f n) * ((Real.log (N : ℝ) : ℝ) : ℂ) - Sconv) + (Sconv - Tsm)) Tsm
  have ht2 := norm_add_le
    ((∑ n ∈ Finset.Icc 1 N, f n) * ((Real.log (N : ℝ) : ℝ) : ℂ) - Sconv) (Sconv - Tsm)
  have hrev : ‖Sconv - Tsm‖ = ‖Tsm - Sconv‖ := norm_sub_rev _ _
  have hsmooth' : ‖Sconv - Tsm‖
      ≤ (H + 1) * ((Real.log ((⌊(N : ℝ) + H⌋₊ : ℕ) : ℝ)) ^ 4 / (Real.log 2) ^ 3) := by
    rw [hrev, hTsm, hSconv]
    exact hsmooth
  have hpaper' : ‖(∑ n ∈ Finset.Icc 1 N, f n) * ((Real.log (N : ℝ) : ℝ) : ℂ) - Sconv‖
      ≤ (9 + RHTower.Mertens.mertensTail) * (N : ℝ) + (N : ℝ) * Real.log 4
        + (9 + RHTower.Mertens.mertensTail)
            * ((N : ℝ)
                * (((Real.log 3 + 2 * ((Real.log 4 + 4) + (8 + RHTower.Mertens.mertensTail)))
                      / Real.log 2)
                    * (1 + Real.log ((Nat.log 2 N : ℕ) : ℝ)))) := by
    rw [hSconv, hd]
    exact hpaper
  linarith [ht1, ht2, hpaper', hsmooth', hanalytic]

end RHTower.Sieve
end
