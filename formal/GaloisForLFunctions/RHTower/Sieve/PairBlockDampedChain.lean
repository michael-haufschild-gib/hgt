import GaloisForLFunctions.RHTower.Sieve.PerronVerticalPairBlockBound
import GaloisForLFunctions.RHTower.Sieve.PairConvolutionPerronSum
import GaloisForLFunctions.RHTower.Sieve.LogWeightVonMangoldtPair
import GaloisForLFunctions.RHTower.Sieve.GhsPerronDamped

/-!
# The pair chain with the damped factor charged block by block

The damped Euler bound is *pointwise* in the frequency: the corpus's `norm_tsum_twistedSummand_le_of_far`
asks only for the distance at the single point `s.im`, and the uniform version packages that.  So the
truncated factor may be charged one damped size per dyadic block,

`‖L(f_{≤L}, σ+it)‖ ≤ dampedSize σ (δ_m) z L`   for `t₀2^m ≤ |t| ≤ t₀2^{m+1}`,

and the block-constant dyadic split then charges the `m`-th block the weight
`(√Q√2/√t₀)(√2/2)^m + 2√κ`.  A distance `δ_m` growing in `m` therefore *converges* against the `2√κ`
part of the weight, where a single uniform `δ` pays `M·2√κ` — the block count.  This is the mechanism
behind Halász's `(1 + m)e^{−m}`: `M·e^{−m}` is replaced by `∑_m e^{−δ_m²}`.
-/

noncomputable section
namespace RHTower.Sieve
open Complex Finset

/-- **The damped size of the truncated factor at a single frequency.**  The pointwise form of
`norm_LSeries_truncSeq_line_le_damped`: only the distance at `t` is used. -/
theorem norm_LSeries_truncSeq_line_le_damped_at {f : ℕ → ℂ} (hf1 : f 1 = 1)
    (hmul : ∀ {m n : ℕ}, Nat.Coprime m n → f (m * n) = f m * f n) (hbdd : ∀ n, ‖f n‖ ≤ 1)
    {σ : ℝ} (hσ : 1 < σ) {z : ℕ} (hz : 1 ≤ z) {δ : ℝ} (hδ : 0 ≤ δ)
    {L : ℕ} (hL : 1 ≤ L) {t : ℝ}
    (hfar : δ ≤ Real.sqrt (mulDistSqPair f (charFn t) (Nat.primesLE z))) :
    ‖LSeries (truncSeq f L) ((σ : ℂ) + (t : ℝ) * I)‖ ≤ dampedSize σ δ z L := by
  rw [dampedSize]
  have hre : ((σ : ℂ) + (t : ℝ) * I).re = σ := by simp
  have hs : ((σ : ℂ) + (t : ℝ) * I) ≠ 0 := by
    intro h
    rw [h] at hre
    simp only [Complex.zero_re] at hre
    exact absurd hre.symm (by linarith : σ ≠ 0)
  have hsre : (1 : ℝ) < ((σ : ℂ) + (t : ℝ) * I).re := by rw [hre]; exact hσ
  have him : ((σ : ℂ) + (t : ℝ) * I).im = t := by simp
  have hdamp := norm_tsum_twistedSummand_le_of_far (f := f) hf1 hmul hbdd hsre hz hδ
    (by rw [him]; exact hfar)
  rw [hre] at hdamp
  have htail := norm_tsum_sub_sum_range_le_pow (f := f) hbdd
    (s := (σ : ℂ) + (t : ℝ) * I) (by rw [hre]; exact hσ) hL
  rw [hre] at htail
  rw [LSeries_truncSeq_eq_sum_range hs]
  have hsplit : (∑ n ∈ Finset.range (L + 1), twistedSummand f ((σ : ℂ) + (t : ℝ) * I) n)
      = (∑' n : ℕ, twistedSummand f ((σ : ℂ) + (t : ℝ) * I) n)
        - ((∑' n : ℕ, twistedSummand f ((σ : ℂ) + (t : ℝ) * I) n)
            - ∑ n ∈ Finset.range (L + 1), twistedSummand f ((σ : ℂ) + (t : ℝ) * I) n) := by
    ring
  rw [hsplit]
  exact le_trans (norm_sub_le _ _) (add_le_add hdamp htail)

/-- **The Perron step of a pair convolution with the second factor charged block by block.** -/
theorem norm_sum_Icc_pair_block_near_le {c g : ℕ → ℂ} {Mc Mg N : ℕ}
    (hcsupp : ∀ n : ℕ, c n ≠ 0 → n ∈ Finset.Icc 1 Mc)
    (hgsupp : ∀ n : ℕ, g n ≠ 0 → n ∈ Finset.Icc 1 Mg)
    {Bc V₀ σ t₀ : ℝ} {V : ℕ → ℝ} (hBc : ∀ n, ‖(LSeries.convolution c g) n‖ ≤ Bc)
    (hV : ∀ m, 0 ≤ V m) (hV₀ : 0 ≤ V₀) (hσ : 1 ≤ σ) (ht₀ : 1 ≤ t₀) (K : ℕ)
    (hgV : ∀ m, m < K → ∀ t : ℝ, t₀ * 2 ^ m ≤ |t| → |t| ≤ t₀ * 2 ^ (m + 1) →
      ‖LSeries g ((σ : ℂ) + (t : ℝ) * I)‖ ≤ V m)
    (hgV₀ : ∀ t : ℝ, |t| ≤ t₀ → ‖LSeries g ((σ : ℂ) + (t : ℝ) * I)‖ ≤ V₀) :
    ‖∑ n ∈ Finset.Icc 1 (min (Mc * Mg) N), (LSeries.convolution c g) n‖
      ≤ Bc * (((N : ℝ) + 1 / 2)) ^ σ
              * (5 * (1 + Real.log ((Mc * Mg : ℕ) : ℝ)) + 4 * (1 + Real.log N))
              / (Real.pi * (t₀ * 2 ^ K))
          + (1 / (2 * Real.pi))
              * perronVerticalPairBlockBound σ ((N : ℝ) + 1 / 2) t₀ V₀
                  (generalMeanSquareConst c (Finset.Icc 1 Mc) σ)
                  (generalMeanSquareRate c (Finset.Icc 1 Mc) σ) V K := by
  have ht₀0 : (0 : ℝ) < t₀ := by linarith
  have hT : (0 : ℝ) < t₀ * 2 ^ K := by positivity
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have hx : (0 : ℝ) < (N : ℝ) + 1 / 2 := by linarith
  have hc0 : (0 : ℕ) ∉ Finset.Icc 1 Mc := by simp
  have hg0 : (0 : ℕ) ∉ Finset.Icc 1 Mg := by simp
  refine norm_sum_Icc_pair_of_error_and_analytic_le (σ := σ) (t₀ := t₀) hcsupp hgsupp
    (by linarith) K ?_ ?_
  · exact norm_sum_Icc_sub_perron_integral_near_le (c := LSeries.convolution c g)
      (M := Mc * Mg) (N := N) hBc (σ := σ) (T := t₀ * 2 ^ K) hσ hT
  · exact integral_symm_norm_perron_pair_block_le hc0 hcsupp (by linarith) hx ht₀ hV hV₀
      (generalMeanSquareConst_nonneg c (Finset.Icc 1 Mc) σ)
      (generalMeanSquareRate_nonneg c (Finset.Icc 1 Mc) σ)
      (continuous_LSeries_line_of_support hg0 hgsupp σ)
      (fun _ hU => integral_Icc_normSq_LSeries_le_general_affine hc0 hcsupp σ hU) K hgV hgV₀

/-- **A Halász-type mean value bound with the damped factor charged block by block.**  The distance is
supplied per dyadic block, so a distance growing with the height is charged a *convergent* weighted sum
in place of the block count. -/
theorem norm_sum_Icc_mul_log_le_pair_block_damped {f : ℕ → ℂ}
    (hf : ∀ a b : ℕ, f (a * b) = f a * f b) (hbdd : ∀ n : ℕ, ‖f n‖ ≤ 1) (hf1 : f 1 = 1)
    {N : ℕ} (hN : 1 ≤ N) {σ t₀ δ₀ : ℝ} {δ : ℕ → ℝ} (hσ : 1 < σ) (ht₀ : 1 ≤ t₀)
    (hδ : ∀ m, 0 ≤ δ m) (hδ₀ : 0 ≤ δ₀) {z : ℕ} (hz : 1 ≤ z) (K : ℕ)
    (hfar : ∀ m, m < K → ∀ t : ℝ, t₀ * 2 ^ m ≤ |t| → |t| ≤ t₀ * 2 ^ (m + 1) →
      δ m ≤ Real.sqrt (mulDistSqPair f (charFn t) (Nat.primesLE z)))
    (hfar₀ : ∀ t : ℝ, |t| ≤ t₀ →
      δ₀ ≤ Real.sqrt (mulDistSqPair f (charFn t) (Nat.primesLE z))) :
    ‖∑ n ∈ Finset.Icc 1 N, f n‖ * Real.log (N : ℝ)
      ≤ (N : ℝ)
        + (Real.log ((N * N : ℕ) : ℝ) * (((N : ℝ) + 1 / 2)) ^ σ
              * (5 * (1 + Real.log ((N * N : ℕ) : ℝ)) + 4 * (1 + Real.log N))
              / (Real.pi * (t₀ * 2 ^ K))
            + (1 / (2 * Real.pi))
              * perronVerticalPairBlockBound σ ((N : ℝ) + 1 / 2) t₀
                  (dampedSize σ δ₀ z N)
                  (generalMeanSquareConst (vonMangoldtSeq (truncSeq f N)) (Finset.Icc 1 N) σ)
                  (generalMeanSquareRate (vonMangoldtSeq (truncSeq f N)) (Finset.Icc 1 N) σ)
                  (fun m => dampedSize σ (δ m) z N) K) := by
  have hmul : ∀ {m n : ℕ}, Nat.Coprime m n → f (m * n) = f m * f n := fun {m n} _ => hf m n
  have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hlogN : (0 : ℝ) ≤ Real.log (N : ℝ) := Real.log_nonneg hNR
  have hNsq : N ≤ N * N := by
    calc N = N * 1 := by ring
      _ ≤ N * N := Nat.mul_le_mul_left N hN
  have hpair := norm_sum_Icc_pair_block_near_le
    (c := vonMangoldtSeq (truncSeq f N)) (g := truncSeq f N) (Mc := N) (Mg := N) (N := N)
    (fun _ hm => vonMangoldtSeq_support hm) (fun _ hm => truncSeq_support hm)
    (norm_convolution_vonMangoldtSeq_le_uniform hbdd hN)
    (fun m => dampedSize_nonneg hσ z N) (dampedSize_nonneg hσ z N) hσ.le ht₀ K
    (fun m hm t ht htop =>
      norm_LSeries_truncSeq_line_le_damped_at hf1 hmul hbdd hσ hz (hδ m) hN
        (hfar m hm t ht htop))
    (fun t ht => norm_LSeries_truncSeq_line_le_damped_at hf1 hmul hbdd hσ hz hδ₀ hN (hfar₀ t ht))
  rw [min_eq_right hNsq, ← sum_Icc_convolution_vonMangoldtSeq_eq hf] at hpair
  have hweight := norm_sum_Icc_mul_log_sub_le (f := f) hbdd N
  have hsplit : ‖(∑ n ∈ Finset.Icc 1 N, f n) * ((Real.log (N : ℝ) : ℝ) : ℂ)‖
      ≤ ‖(∑ n ∈ Finset.Icc 1 N, f n) * ((Real.log (N : ℝ) : ℝ) : ℂ)
            - ∑ n ∈ Finset.Icc 1 N, f n * ((Real.log (n : ℝ) : ℝ) : ℂ)‖
          + ‖∑ n ∈ Finset.Icc 1 N, f n * ((Real.log (n : ℝ) : ℝ) : ℂ)‖ := by
    have := norm_add_le ((∑ n ∈ Finset.Icc 1 N, f n) * ((Real.log (N : ℝ) : ℝ) : ℂ)
        - ∑ n ∈ Finset.Icc 1 N, f n * ((Real.log (n : ℝ) : ℝ) : ℂ))
      (∑ n ∈ Finset.Icc 1 N, f n * ((Real.log (n : ℝ) : ℝ) : ℂ))
    simpa using this
  have hnorm : ‖(∑ n ∈ Finset.Icc 1 N, f n) * ((Real.log (N : ℝ) : ℝ) : ℂ)‖
      = ‖∑ n ∈ Finset.Icc 1 N, f n‖ * Real.log (N : ℝ) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlogN]
  rw [hnorm] at hsplit
  linarith [hsplit, hweight, hpair]

end RHTower.Sieve
end
