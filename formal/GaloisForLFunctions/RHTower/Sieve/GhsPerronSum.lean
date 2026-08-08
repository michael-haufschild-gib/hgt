import GaloisForLFunctions.RHTower.Sieve.TripleConvolutionPerronSum
import GaloisForLFunctions.RHTower.Sieve.GhsCoefficients
import GaloisForLFunctions.RHTower.Sieve.HarmonicLogBound

/-!
# The Granville–Harper–Soundararajan convolution through the sharp Perron formula

Instantiating the Perron step at the coefficients the logarithmic recursion produces: the outer prime
weight `f(p)log p/log⌊N₀/p⌋`, the inner prime weight `f(q)log q` truncated at `M`, and `f` itself
truncated at `L`.  All three inputs the general theorem asks for are then closed by results already in
the corpus:

* the two prime weights are supported on primes in `[1, N₀]` and `[1, M]`;
* the coefficients of the triple convolution are bounded by `(log n)^4/(log 2)^3`, hence uniformly by
  `(log(N₀ML))^4/(log 2)^3` on the support;
* the third factor's size on the line is its damped `ℓ¹` mass, at most `1 + log L`.

So the Perron step of the recursion is an unconditional inequality in which the only free parameters are
the abscissa, the truncation height, the cutoff, and the two sieve pairs.
-/

noncomputable section
namespace RHTower.Sieve
open Complex MeasureTheory Set

/-- A sequence truncated to `[1, L]`. -/
def truncSeq (f : ℕ → ℂ) (L : ℕ) : ℕ → ℂ := fun n => if n ∈ Finset.Icc 1 L then f n else 0

theorem truncSeq_support {f : ℕ → ℂ} {L n : ℕ} (h : truncSeq f L n ≠ 0) :
    n ∈ Finset.Icc 1 L := by
  rw [truncSeq] at h
  by_cases hn : n ∈ Finset.Icc 1 L
  · exact hn
  · rw [if_neg hn] at h
    exact absurd rfl h

theorem norm_truncSeq_le {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1) (L n : ℕ) :
    ‖truncSeq f L n‖ ≤ 1 := by
  rw [truncSeq]
  by_cases hn : n ∈ Finset.Icc 1 L
  · rw [if_pos hn]
    exact hf n
  · rw [if_neg hn, norm_zero]
    norm_num

/-- **The size of a truncated bounded sequence on a vertical line.**  Its damped `ℓ¹` mass is at most the
harmonic sum, hence `1 + log L`. -/
theorem norm_LSeries_truncSeq_line_le {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1) (L : ℕ) {σ : ℝ} (hσ : 1 ≤ σ)
    (t : ℝ) :
    ‖LSeries (truncSeq f L) ((σ : ℂ) + (t : ℝ) * I)‖ ≤ 1 + Real.log L := by
  have hs0 : (0 : ℕ) ∉ Finset.Icc 1 L := by simp
  refine le_trans (norm_LSeries_line_le_l1 hs0 (fun n hn => truncSeq_support hn) σ t) ?_
  refine le_trans (Finset.sum_le_sum ?_) (sum_Icc_one_div_le_one_add_log L)
  intro n hn
  have hn1 : 1 ≤ n := (Finset.mem_Icc.1 hn).1
  have hn0 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hge : (n : ℝ) ≤ ((n : ℝ)) ^ σ := by
    have h1 : ((n : ℝ)) ^ (1 : ℝ) ≤ ((n : ℝ)) ^ σ := Real.rpow_le_rpow_of_exponent_le hn0 hσ
    rwa [Real.rpow_one] at h1
  have hpow : ((n : ℝ)) ^ (-σ) ≤ 1 / (n : ℝ) := by
    rw [Real.rpow_neg hnpos.le, one_div]
    exact inv_anti₀ hnpos hge
  calc ‖truncSeq f L n‖ * ((n : ℝ)) ^ (-σ) ≤ 1 * (1 / (n : ℝ)) := by
        refine mul_le_mul (norm_truncSeq_le hf L n) hpow (by positivity) zero_le_one
    _ = 1 / (n : ℝ) := one_mul _

/-- **A uniform bound for the coefficients of the truncated GHS convolution.**  The polylogarithmic
coefficient bound at its largest point of the support, and zero beyond it. -/
theorem norm_ghsTriple_trunc_le_uniform {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1) {N₀ M L : ℕ}
    (hprod : 1 ≤ N₀ * (M * L)) (n : ℕ) :
    ‖(LSeries.convolution (ghsOuter f N₀)
        (LSeries.convolution (ghsInner f M) (truncSeq f L))) n‖
      ≤ (Real.log ((N₀ * (M * L) : ℕ) : ℝ)) ^ 4 / (Real.log 2) ^ 3 := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hprodR : (1 : ℝ) ≤ ((N₀ * (M * L) : ℕ) : ℝ) := by exact_mod_cast hprod
  have hlogprod : (0 : ℝ) ≤ Real.log ((N₀ * (M * L) : ℕ) : ℝ) := Real.log_nonneg hprodR
  have hsupp : ∀ k : ℕ, (LSeries.convolution (ghsOuter f N₀)
      (LSeries.convolution (ghsInner f M) (truncSeq f L))) k ≠ 0 →
      k ∈ Finset.Icc 1 (N₀ * (M * L)) := by
    intro k hk
    refine convolution_mem_Icc_of_support_mul (fun j hj => ghsOuter_mem_Icc hj) ?_ hk
    intro j hj
    exact convolution_mem_Icc_of_support_mul (fun i hi => ghsInner_mem_Icc hi)
      (fun i hi => truncSeq_support hi) hj
  by_cases hzero : (LSeries.convolution (ghsOuter f N₀)
      (LSeries.convolution (ghsInner f M) (truncSeq f L))) n = 0
  · rw [hzero, norm_zero]
    positivity
  · have hmem := Finset.mem_Icc.1 (hsupp n hzero)
    have hn1 : 1 ≤ n := hmem.1
    have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
    have hlogn : (0 : ℝ) ≤ Real.log n := Real.log_nonneg hnR
    have hmono : Real.log n ≤ Real.log ((N₀ * (M * L) : ℕ) : ℝ) := by
      refine Real.log_le_log (by linarith) ?_
      exact_mod_cast hmem.2
    have hbase := norm_convolution_triple_le_log_pow_const
      (A := 1 / Real.log 2) (B := 1) (by positivity) zero_le_one
      (fun p hp => ghsOuter_support hp) (norm_ghsOuter_le hf N₀)
      (fun q hq => ghsInner_support hq) (by simpa using norm_ghsInner_le hf M)
      (norm_truncSeq_le hf L) hn1
    refine le_trans hbase ?_
    have hpow : (Real.log n) ^ 4 ≤ (Real.log ((N₀ * (M * L) : ℕ) : ℝ)) ^ 4 :=
      pow_le_pow_left₀ hlogn hmono 4
    rw [show (1 / Real.log 2) * 1 * ((Real.log n) ^ 4 / (Real.log 2) ^ 2)
        = (Real.log n) ^ 4 / (Real.log 2) ^ 3 by field_simp]
    exact div_le_div_of_nonneg_right hpow (by positivity)

/-- **The Perron step of the Granville–Harper–Soundararajan recursion, with the third factor's size
free.**  Supports, primality and the coefficient bound are discharged from the corpus; the only input
left open is a bound `V` on the size of the truncated third factor on the range of integration. -/
theorem norm_sum_Icc_ghsTriple_of_bound_le {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1) {N₀ M L N : ℕ}
    (hprod : 1 ≤ N₀ * (M * L)) (hN : 1 ≤ N)
    {V σ t₀ : ℝ} (hV : 0 ≤ V) (hσ : 1 ≤ σ) (ht₀ : 1 ≤ t₀)
    (zA YA zB YB : ℕ) (hYA : 1 ≤ YA) (hYzA : YA ≤ zA) (hzA : 2 ≤ zA) (hlogA : 0 < Real.log YA)
    (hYB : 1 ≤ YB) (hYzB : YB ≤ zB) (hzB : 2 ≤ zB) (hlogB : 0 < Real.log YB) (K : ℕ)
    (hgV : ∀ t : ℝ, |t| ≤ t₀ * 2 ^ K →
      ‖LSeries (truncSeq f L) ((σ : ℂ) + (t : ℝ) * I)‖ ≤ V) :
    ‖∑ n ∈ Finset.Icc 1 (min (N₀ * (M * L)) N),
        (LSeries.convolution (ghsOuter f N₀)
          (LSeries.convolution (ghsInner f M) (truncSeq f L))) n‖
      ≤ 2 * ((N : ℝ) + 1) * ((Real.log ((N₀ * (M * L) : ℕ) : ℝ)) ^ 4 / (Real.log 2) ^ 3)
              * (((N : ℝ) + 1 / 2)) ^ σ
              * (1 + Real.log ((N₀ * (M * L) : ℕ) : ℝ)) / (Real.pi * (t₀ * 2 ^ K))
          + (1 / (2 * Real.pi))
              * (2 * perronVerticalProductBound (ghsOuter f N₀) (ghsInner f M)
                    (Finset.Icc 1 N₀) (Finset.Icc 1 M) σ ((N : ℝ) + 1 / 2) t₀ V
                    zA YA zB YB K
                  + (V * ((N : ℝ) + 1 / 2) ^ σ / σ)
                      * (Real.sqrt (sieveMeanSquareConst (ghsOuter f N₀) (Finset.Icc 1 N₀) σ YA
                            + sieveMeanSquareRate (ghsOuter f N₀) (Finset.Icc 1 N₀) σ zA YA * t₀)
                          * Real.sqrt (sieveMeanSquareConst (ghsInner f M) (Finset.Icc 1 M) σ YB
                            + sieveMeanSquareRate (ghsInner f M) (Finset.Icc 1 M) σ zB YB
                                * t₀))) :=
  norm_sum_Icc_triple_le (A := ghsOuter f N₀) (B := ghsInner f M) (g := truncSeq f L)
    (fun _ hn => ghsOuter_mem_Icc hn) (fun _ _ hn => ghsOuter_support hn)
    (fun _ hn => ghsInner_mem_Icc hn) (fun _ _ hn => ghsInner_support hn)
    (fun _ hn => truncSeq_support hn) hN
    (norm_ghsTriple_trunc_le_uniform hf hprod) hV hσ ht₀
    zA YA zB YB hYA hYzA hzA hlogA hYB hYzB hzB hlogB K hgV

/-- **The Perron step with the third factor at its `ℓ¹` size.**  The damped `ℓ¹` mass `1 + log L` needs no
hypothesis on `f` beyond boundedness. -/
theorem norm_sum_Icc_ghsTriple_le {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1) {N₀ M L N : ℕ}
    (hprod : 1 ≤ N₀ * (M * L)) (hN : 1 ≤ N)
    {σ t₀ : ℝ} (hσ : 1 ≤ σ) (ht₀ : 1 ≤ t₀)
    (zA YA zB YB : ℕ) (hYA : 1 ≤ YA) (hYzA : YA ≤ zA) (hzA : 2 ≤ zA) (hlogA : 0 < Real.log YA)
    (hYB : 1 ≤ YB) (hYzB : YB ≤ zB) (hzB : 2 ≤ zB) (hlogB : 0 < Real.log YB) (K : ℕ) :
    ‖∑ n ∈ Finset.Icc 1 (min (N₀ * (M * L)) N),
        (LSeries.convolution (ghsOuter f N₀)
          (LSeries.convolution (ghsInner f M) (truncSeq f L))) n‖
      ≤ 2 * ((N : ℝ) + 1) * ((Real.log ((N₀ * (M * L) : ℕ) : ℝ)) ^ 4 / (Real.log 2) ^ 3)
              * (((N : ℝ) + 1 / 2)) ^ σ
              * (1 + Real.log ((N₀ * (M * L) : ℕ) : ℝ)) / (Real.pi * (t₀ * 2 ^ K))
          + (1 / (2 * Real.pi))
              * (2 * perronVerticalProductBound (ghsOuter f N₀) (ghsInner f M)
                    (Finset.Icc 1 N₀) (Finset.Icc 1 M) σ ((N : ℝ) + 1 / 2) t₀ (1 + Real.log L)
                    zA YA zB YB K
                  + ((1 + Real.log L) * ((N : ℝ) + 1 / 2) ^ σ / σ)
                      * (Real.sqrt (sieveMeanSquareConst (ghsOuter f N₀) (Finset.Icc 1 N₀) σ YA
                            + sieveMeanSquareRate (ghsOuter f N₀) (Finset.Icc 1 N₀) σ zA YA * t₀)
                          * Real.sqrt (sieveMeanSquareConst (ghsInner f M) (Finset.Icc 1 M) σ YB
                            + sieveMeanSquareRate (ghsInner f M) (Finset.Icc 1 M) σ zB YB
                                * t₀))) := by
  have hL0 : (0 : ℝ) ≤ Real.log L := by
    rcases Nat.eq_zero_or_pos L with rfl | hL
    · simp
    · exact Real.log_nonneg (by exact_mod_cast hL)
  exact norm_sum_Icc_ghsTriple_of_bound_le hf hprod hN (by linarith) hσ ht₀
    zA YA zB YB hYA hYzA hzA hlogA hYB hYzB hzB hlogB K
    (fun t _ => norm_LSeries_truncSeq_line_le hf L hσ t)

/-- **The Perron step of the recursion at the near-diagonal truncation error, with the third factor's
size free.**  The same inputs, with the truncation error freed of its factor `N`. -/
theorem norm_sum_Icc_ghsTriple_of_bound_near_le {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1) {N₀ M L N : ℕ}
    (hprod : 1 ≤ N₀ * (M * L))
    {V σ t₀ : ℝ} (hV : 0 ≤ V) (hσ : 1 ≤ σ) (ht₀ : 1 ≤ t₀)
    (zA YA zB YB : ℕ) (hYA : 1 ≤ YA) (hYzA : YA ≤ zA) (hzA : 2 ≤ zA) (hlogA : 0 < Real.log YA)
    (hYB : 1 ≤ YB) (hYzB : YB ≤ zB) (hzB : 2 ≤ zB) (hlogB : 0 < Real.log YB) (K : ℕ)
    (hgV : ∀ t : ℝ, |t| ≤ t₀ * 2 ^ K →
      ‖LSeries (truncSeq f L) ((σ : ℂ) + (t : ℝ) * I)‖ ≤ V) :
    ‖∑ n ∈ Finset.Icc 1 (min (N₀ * (M * L)) N),
        (LSeries.convolution (ghsOuter f N₀)
          (LSeries.convolution (ghsInner f M) (truncSeq f L))) n‖
      ≤ ((Real.log ((N₀ * (M * L) : ℕ) : ℝ)) ^ 4 / (Real.log 2) ^ 3)
              * (((N : ℝ) + 1 / 2)) ^ σ
              * (5 * (1 + Real.log ((N₀ * (M * L) : ℕ) : ℝ)) + 4 * (1 + Real.log N))
              / (Real.pi * (t₀ * 2 ^ K))
          + (1 / (2 * Real.pi))
              * (2 * perronVerticalProductBound (ghsOuter f N₀) (ghsInner f M)
                    (Finset.Icc 1 N₀) (Finset.Icc 1 M) σ ((N : ℝ) + 1 / 2) t₀ V
                    zA YA zB YB K
                  + (V * ((N : ℝ) + 1 / 2) ^ σ / σ)
                      * (Real.sqrt (sieveMeanSquareConst (ghsOuter f N₀) (Finset.Icc 1 N₀) σ YA
                            + sieveMeanSquareRate (ghsOuter f N₀) (Finset.Icc 1 N₀) σ zA YA * t₀)
                          * Real.sqrt (sieveMeanSquareConst (ghsInner f M) (Finset.Icc 1 M) σ YB
                            + sieveMeanSquareRate (ghsInner f M) (Finset.Icc 1 M) σ zB YB
                                * t₀))) :=
  norm_sum_Icc_triple_near_le (A := ghsOuter f N₀) (B := ghsInner f M) (g := truncSeq f L)
    (fun _ hn => ghsOuter_mem_Icc hn) (fun _ _ hn => ghsOuter_support hn)
    (fun _ hn => ghsInner_mem_Icc hn) (fun _ _ hn => ghsInner_support hn)
    (fun _ hn => truncSeq_support hn)
    (norm_ghsTriple_trunc_le_uniform hf hprod) hV hσ ht₀
    zA YA zB YB hYA hYzA hzA hlogA hYB hYzB hzB hlogB K hgV

/-- **The Perron step at the near-diagonal error with the third factor at its `ℓ¹` size.** -/
theorem norm_sum_Icc_ghsTriple_near_le {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1) {N₀ M L N : ℕ}
    (hprod : 1 ≤ N₀ * (M * L))
    {σ t₀ : ℝ} (hσ : 1 ≤ σ) (ht₀ : 1 ≤ t₀)
    (zA YA zB YB : ℕ) (hYA : 1 ≤ YA) (hYzA : YA ≤ zA) (hzA : 2 ≤ zA) (hlogA : 0 < Real.log YA)
    (hYB : 1 ≤ YB) (hYzB : YB ≤ zB) (hzB : 2 ≤ zB) (hlogB : 0 < Real.log YB) (K : ℕ) :
    ‖∑ n ∈ Finset.Icc 1 (min (N₀ * (M * L)) N),
        (LSeries.convolution (ghsOuter f N₀)
          (LSeries.convolution (ghsInner f M) (truncSeq f L))) n‖
      ≤ ((Real.log ((N₀ * (M * L) : ℕ) : ℝ)) ^ 4 / (Real.log 2) ^ 3)
              * (((N : ℝ) + 1 / 2)) ^ σ
              * (5 * (1 + Real.log ((N₀ * (M * L) : ℕ) : ℝ)) + 4 * (1 + Real.log N))
              / (Real.pi * (t₀ * 2 ^ K))
          + (1 / (2 * Real.pi))
              * (2 * perronVerticalProductBound (ghsOuter f N₀) (ghsInner f M)
                    (Finset.Icc 1 N₀) (Finset.Icc 1 M) σ ((N : ℝ) + 1 / 2) t₀ (1 + Real.log L)
                    zA YA zB YB K
                  + ((1 + Real.log L) * ((N : ℝ) + 1 / 2) ^ σ / σ)
                      * (Real.sqrt (sieveMeanSquareConst (ghsOuter f N₀) (Finset.Icc 1 N₀) σ YA
                            + sieveMeanSquareRate (ghsOuter f N₀) (Finset.Icc 1 N₀) σ zA YA * t₀)
                          * Real.sqrt (sieveMeanSquareConst (ghsInner f M) (Finset.Icc 1 M) σ YB
                            + sieveMeanSquareRate (ghsInner f M) (Finset.Icc 1 M) σ zB YB
                                * t₀))) := by
  have hL0 : (0 : ℝ) ≤ Real.log L := by
    rcases Nat.eq_zero_or_pos L with rfl | hL
    · simp
    · exact Real.log_nonneg (by exact_mod_cast hL)
  exact norm_sum_Icc_ghsTriple_of_bound_near_le hf hprod (by linarith) hσ ht₀
    zA YA zB YB hYA hYzA hzA hlogA hYB hYzB hzB hlogB K
    (fun t _ => norm_LSeries_truncSeq_line_le hf L hσ t)

/-- **The Perron step of the recursion at per-block sieve levels and the near-diagonal truncation
error, with the third factor's size free.** -/
theorem norm_sum_Icc_ghsTriple_of_bound_block_near_le {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1)
    {N₀ M L N : ℕ} (hprod : 1 ≤ N₀ * (M * L))
    {V σ t₀ : ℝ} (hV : 0 ≤ V) (hσ : 1 ≤ σ) (ht₀ : 1 ≤ t₀)
    (ZA YlA ZB YlB : ℕ → ℕ)
    (hYA : ∀ j, 1 ≤ YlA j) (hYzA : ∀ j, YlA j ≤ ZA j) (hzA : ∀ j, 2 ≤ ZA j)
    (hlogA : ∀ j, 0 < Real.log (YlA j))
    (hYB : ∀ j, 1 ≤ YlB j) (hYzB : ∀ j, YlB j ≤ ZB j) (hzB : ∀ j, 2 ≤ ZB j)
    (hlogB : ∀ j, 0 < Real.log (YlB j)) (K : ℕ)
    (hgV : ∀ t : ℝ, |t| ≤ t₀ * 2 ^ K →
      ‖LSeries (truncSeq f L) ((σ : ℂ) + (t : ℝ) * I)‖ ≤ V) :
    ‖∑ n ∈ Finset.Icc 1 (min (N₀ * (M * L)) N),
        (LSeries.convolution (ghsOuter f N₀)
          (LSeries.convolution (ghsInner f M) (truncSeq f L))) n‖
      ≤ ((Real.log ((N₀ * (M * L) : ℕ) : ℝ)) ^ 4 / (Real.log 2) ^ 3)
              * (((N : ℝ) + 1 / 2)) ^ σ
              * (5 * (1 + Real.log ((N₀ * (M * L) : ℕ) : ℝ)) + 4 * (1 + Real.log N))
              / (Real.pi * (t₀ * 2 ^ K))
          + (1 / (2 * Real.pi))
              * (2 * perronVerticalAffineProductBound σ ((N : ℝ) + 1 / 2) t₀ V
                    (blockAffineConst (ghsOuter f N₀) N₀ σ ZA YlA)
                    (blockAffineRate (ghsOuter f N₀) N₀ σ ZA YlA)
                    (blockAffineConst (ghsInner f M) M σ ZB YlB)
                    (blockAffineRate (ghsInner f M) M σ ZB YlB) K
                  + (V * ((N : ℝ) + 1 / 2) ^ σ / σ)
                      * (Real.sqrt (blockAffineConst (ghsOuter f N₀) N₀ σ ZA YlA
                            + blockAffineRate (ghsOuter f N₀) N₀ σ ZA YlA * t₀)
                          * Real.sqrt (blockAffineConst (ghsInner f M) M σ ZB YlB
                            + blockAffineRate (ghsInner f M) M σ ZB YlB * t₀))) :=
  norm_sum_Icc_triple_block_near_le (A := ghsOuter f N₀) (B := ghsInner f M) (g := truncSeq f L)
    (fun _ hn => ghsOuter_mem_Icc hn) (fun _ _ hn => ghsOuter_support hn)
    (fun _ hn => ghsInner_mem_Icc hn) (fun _ _ hn => ghsInner_support hn)
    (fun _ hn => truncSeq_support hn)
    (norm_ghsTriple_trunc_le_uniform hf hprod) hV hσ ht₀
    ZA YlA ZB YlB hYA hYzA hzA hlogA hYB hYzB hzB hlogB K hgV

/-- **The Perron step at per-block sieve levels and the near-diagonal error, with the third factor at
its `ℓ¹` size.** -/
theorem norm_sum_Icc_ghsTriple_block_near_le {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1)
    {N₀ M L N : ℕ} (hprod : 1 ≤ N₀ * (M * L))
    {σ t₀ : ℝ} (hσ : 1 ≤ σ) (ht₀ : 1 ≤ t₀)
    (ZA YlA ZB YlB : ℕ → ℕ)
    (hYA : ∀ j, 1 ≤ YlA j) (hYzA : ∀ j, YlA j ≤ ZA j) (hzA : ∀ j, 2 ≤ ZA j)
    (hlogA : ∀ j, 0 < Real.log (YlA j))
    (hYB : ∀ j, 1 ≤ YlB j) (hYzB : ∀ j, YlB j ≤ ZB j) (hzB : ∀ j, 2 ≤ ZB j)
    (hlogB : ∀ j, 0 < Real.log (YlB j)) (K : ℕ) :
    ‖∑ n ∈ Finset.Icc 1 (min (N₀ * (M * L)) N),
        (LSeries.convolution (ghsOuter f N₀)
          (LSeries.convolution (ghsInner f M) (truncSeq f L))) n‖
      ≤ ((Real.log ((N₀ * (M * L) : ℕ) : ℝ)) ^ 4 / (Real.log 2) ^ 3)
              * (((N : ℝ) + 1 / 2)) ^ σ
              * (5 * (1 + Real.log ((N₀ * (M * L) : ℕ) : ℝ)) + 4 * (1 + Real.log N))
              / (Real.pi * (t₀ * 2 ^ K))
          + (1 / (2 * Real.pi))
              * (2 * perronVerticalAffineProductBound σ ((N : ℝ) + 1 / 2) t₀ (1 + Real.log L)
                    (blockAffineConst (ghsOuter f N₀) N₀ σ ZA YlA)
                    (blockAffineRate (ghsOuter f N₀) N₀ σ ZA YlA)
                    (blockAffineConst (ghsInner f M) M σ ZB YlB)
                    (blockAffineRate (ghsInner f M) M σ ZB YlB) K
                  + ((1 + Real.log L) * ((N : ℝ) + 1 / 2) ^ σ / σ)
                      * (Real.sqrt (blockAffineConst (ghsOuter f N₀) N₀ σ ZA YlA
                            + blockAffineRate (ghsOuter f N₀) N₀ σ ZA YlA * t₀)
                          * Real.sqrt (blockAffineConst (ghsInner f M) M σ ZB YlB
                            + blockAffineRate (ghsInner f M) M σ ZB YlB * t₀))) := by
  have hL0 : (0 : ℝ) ≤ Real.log L := by
    rcases Nat.eq_zero_or_pos L with rfl | hL
    · simp
    · exact Real.log_nonneg (by exact_mod_cast hL)
  exact norm_sum_Icc_ghsTriple_of_bound_block_near_le hf hprod (by linarith) hσ ht₀
    ZA YlA ZB YlB hYA hYzA hzA hlogA hYB hYzB hzB hlogB K
    (fun t _ => norm_LSeries_truncSeq_line_le hf L hσ t)

end RHTower.Sieve
end
