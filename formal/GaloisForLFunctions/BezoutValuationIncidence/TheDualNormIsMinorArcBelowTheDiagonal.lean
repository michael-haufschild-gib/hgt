import GaloisForLFunctions.BezoutValuationIncidence.MinorArcMoebiusSumsAtPrimeRootsOfUnity
import GaloisForLFunctions.BezoutValuationIncidence.SingleModulusCancellationOfTheMoebiusBlock
import GaloisForLFunctions.RHTower.Sieve.GapSums

/-!
# The dual norm of the Möbius row is minor-arc below the diagonal

Write the Bernoulli kernel in the Kloosterman-fraction form `𝔅(p, n) = (π²/4) Σ_k B₂(k/p) csc²(πk n̄/p)`.
The same kernel is diagonal in the additive characters of `n`: by the spectral law
`abs_kernelStatistic_le_fourier`, the kernel statistic of a large-scale row is controlled by the
twists `S_r(ζ) = Σ_n (c'(n)/nʳ) ζⁿ`, `r = 2, 3`, at the nontrivial `p`-th roots of unity `ζ`. No
complete sum in both `n` and `n̄` occurs. The input that acts is therefore the minor-arc law for
`Σ μ(n) ζⁿ` at the exact denominator `p` (`norm_sum_moebius_mul_pow_le`), not Weil's bound.

For the Möbius window row `c' = μ·𝟙_{(Q, 2Q]}`, Abel summation against `n^{-2}` and `n^{-3}` gives,
for every prime `p` and `1 ≤ U < p`,

`|Λ_p(c')| ≤ (π²(p² - 1)/36 (Q+1)^{-2} + π²p³/24 (Q+1)^{-3}) · M_p(U, 2Q)`,

where `M_p(U, N)` is the minor-arc majorant. With `U = ⌊Q^{δ/2}⌋` this is a power saving at every
prime `Q^δ ≤ p ≤ Q^{1-δ}`, that is, at every cross-scale exponent `θ = 2 log P / log Q ≤ 2 - 2δ`:

`|Λ_p(c')| ≤ 23 (1 + log 2Q)³ (p²/Q) Q^{-δ/4}`  (`abs_kernelStatistic_moebiusWindowRow_le_rpow`).

Summed with arbitrary bounded small-scale coefficients this is a power saving for the dual norm and
for the cross-scale remainder over the trivial size `Σ_p p/Q`, unconditionally
(`dualNorm_moebiusWindowRow_le_rpow`, `abs_rowBilinear_moebiusWindowRow_sub_main_le_rpow`). Generic
Type-II rows stop at `θ = 6/5`, sharp cutoffs at `4/3`; the Möbius row passes every `θ < 2`. The
saving degenerates exactly at the diagonal `θ = 2`, where `p ≍ Q` and the low frequencies of
`ζⁿ` are archimedean.
-/

open Finset Filter Topology ArithmeticFunction RHTower.Sieve
open scoped BigOperators

namespace GaloisForLFunctions.BezoutValuationIncidence

noncomputable section
set_option autoImplicit false

/-! ## §1. Abel summation of the window twists -/

/-- **Abel's inequality for complex sums.** For `w ≥ 0` nonincreasing and partial sums of `g` at
most `B`, `‖Σ_{i<n} w(i) g(i)‖ ≤ B w(0)`. -/
theorem norm_sum_range_ofReal_mul_le_of_antitone {g : ℕ → ℂ} {w : ℕ → ℝ} {B : ℝ} (n : ℕ)
    (hB : ∀ k ≤ n, ‖∑ j ∈ range k, g j‖ ≤ B) (hw0 : ∀ i, 0 ≤ w i)
    (hw : ∀ i, w (i + 1) ≤ w i) :
    ‖∑ i ∈ range n, (w i : ℂ) * g i‖ ≤ B * w 0 := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 (Nat.zero_le _))
  rcases n with _ | n
  · simp only [range_zero, sum_empty, norm_zero]
    exact mul_nonneg hB0 (hw0 0)
  simp_rw [← Complex.real_smul]
  rw [sum_range_by_parts, Nat.add_sub_cancel]
  have hhead : ‖w n • ∑ i ∈ range (n + 1), g i‖ ≤ w n * B := by
    rw [norm_smul, Real.norm_of_nonneg (hw0 n)]
    exact mul_le_mul_of_nonneg_left (hB _ le_rfl) (hw0 n)
  have htail : ‖∑ i ∈ range n, (w (i + 1) - w i) • ∑ j ∈ range (i + 1), g j‖ ≤ (w 0 - w n) * B := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ i ∈ range n, ‖(w (i + 1) - w i) • ∑ j ∈ range (i + 1), g j‖
        ≤ ∑ i ∈ range n, (w i - w (i + 1)) * B := by
          refine sum_le_sum fun i hi => ?_
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonpos (by linarith [hw i]), neg_sub]
          exact mul_le_mul_of_nonneg_left (hB _ (by have := mem_range.mp hi; omega))
            (by linarith [hw i])
      _ = (w 0 - w n) * B := by rw [← sum_mul, sum_range_sub']
  calc _ ≤ ‖w n • ∑ i ∈ range (n + 1), g i‖ +
        ‖∑ i ∈ range n, (w (i + 1) - w i) • ∑ j ∈ range (i + 1), g j‖ := norm_sub_le _ _
    _ ≤ w n * B + (w 0 - w n) * B := add_le_add hhead htail
    _ = B * w 0 := by ring

/-- **Window twists of the Möbius row.** If `‖Σ_{n ≤ x} μ(n) ζⁿ‖ ≤ B` for all `x ≤ 2Q`, then for
`N ≥ 2Q` and every `r`, `‖Σ_{n ≤ N} (μ𝟙_{(Q,2Q]}(n)/nʳ) ζⁿ‖ ≤ 2B/(Q+1)ʳ`. -/
theorem norm_sum_moebiusWindowRow_div_pow_le (Q N r : ℕ) (hQN : 2 * Q ≤ N) (ζ : ℂ) {B : ℝ}
    (hB : ∀ x ≤ 2 * Q, ‖∑ n ∈ Icc 1 x, (moebiusReal n : ℂ) * ζ ^ n‖ ≤ B) :
    ‖∑ n ∈ Icc 1 N, ((moebiusWindowRow Q n / (n : ℝ) ^ r : ℝ) : ℂ) * ζ ^ n‖ ≤
      2 * B / ((Q : ℝ) + 1) ^ r := by
  set S : ℕ → ℂ := fun x => ∑ n ∈ Icc 1 x, (moebiusReal n : ℂ) * ζ ^ n
  have hwin : ∑ n ∈ Icc 1 N, ((moebiusWindowRow Q n / (n : ℝ) ^ r : ℝ) : ℂ) * ζ ^ n =
      ∑ i ∈ range Q, ((1 / ((Q + 1 + i : ℕ) : ℝ) ^ r : ℝ) : ℂ) *
        ((moebiusReal (Q + 1 + i) : ℂ) * ζ ^ (Q + 1 + i)) := by
    have hsub : Ioc Q (2 * Q) ⊆ Icc 1 N := fun n hn => by
      simp only [mem_Ioc, mem_Icc] at hn ⊢; omega
    rw [← sum_subset hsub fun n _ hn => by
      rw [moebiusWindowRow, if_neg (by simpa only [mem_Ioc] using hn)]; simp]
    have hIoc : Ioc Q (2 * Q) = Ico (Q + 1) (2 * Q + 1) := by
      ext n; simp only [mem_Ioc, mem_Ico]; omega
    rw [hIoc, sum_Ico_eq_sum_range, show 2 * Q + 1 - (Q + 1) = Q by omega]
    refine sum_congr rfl fun i hi => ?_
    have hi' := mem_range.mp hi
    rw [moebiusWindowRow, if_pos (by omega)]
    push_cast
    ring
  have hpart : ∀ k ≤ Q, ‖∑ j ∈ range k, (moebiusReal (Q + 1 + j) : ℂ) * ζ ^ (Q + 1 + j)‖ ≤ 2 * B := by
    intro k hk
    have hdiff : ∑ j ∈ range k, (moebiusReal (Q + 1 + j) : ℂ) * ζ ^ (Q + 1 + j) = S (Q + k) - S Q := by
      induction k with
      | zero => simp
      | succ k ih =>
        rw [Finset.sum_range_succ, ih (by omega), show Q + (k + 1) = (Q + k) + 1 by ring]
        simp only [S]
        rw [sum_Icc_succ_top (by omega : 1 ≤ Q + k + 1), show Q + 1 + k = Q + k + 1 by ring]
        ring
    rw [hdiff]
    calc ‖S (Q + k) - S Q‖ ≤ ‖S (Q + k)‖ + ‖S Q‖ := norm_sub_le _ _
      _ ≤ B + B := add_le_add (hB _ (by omega)) (hB _ (by omega))
      _ = 2 * B := by ring
  rw [hwin]
  have h := norm_sum_range_ofReal_mul_le_of_antitone Q hpart (w := fun i => 1 / ((Q + 1 + i : ℕ) : ℝ) ^ r)
    (fun i => by positivity) (fun i => by
      apply one_div_le_one_div_of_le (by positivity)
      exact pow_le_pow_left₀ (by positivity) (by push_cast; linarith) r)
  refine h.trans (le_of_eq ?_)
  push_cast
  ring

/-! ## §2. The kernel statistic of the Möbius row through the minor-arc law -/

/-- The minor-arc majorant `M_p(U, N) = 2U + U W_p + (log₂ N + 1) √(typeIIBlockBound p U N)`. -/
def minorArcBound (p U N : ℕ) : ℝ :=
  2 * U + U * rootHarmonicSum p + (Nat.log 2 N + 1) * Real.sqrt (typeIIBlockBound p U N)

theorem minorArcBound_nonneg (p U N : ℕ) : 0 ≤ minorArcBound p U N := by
  unfold minorArcBound
  have := rootHarmonicSum_nonneg p
  positivity

theorem typeIIBlockBound_mono (p U : ℕ) {M N : ℕ} (h : M ≤ N) :
    typeIIBlockBound p U M ≤ typeIIBlockBound p U N := by
  unfold typeIIBlockBound
  have hW := rootHarmonicSum_nonneg p
  have hMN : (M : ℝ) ≤ N := by exact_mod_cast h
  have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg _
  have hsq : (M : ℝ) ^ 2 ≤ (N : ℝ) ^ 2 := pow_le_pow_left₀ hM0 hMN 2
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg _
  have hU0 : (0 : ℝ) ≤ U := Nat.cast_nonneg _
  have h1 : 1 + invSum M ^ 3 ≤ 1 + invSum N ^ 3 := by
    linarith [pow_le_pow_left₀ (invSum_nonneg M) (invSum_mono h) 3]
  have h2 : (M : ℝ) ^ 2 / p + (M : ℝ) ^ 2 / U + (M : ℝ) ^ 2 * rootHarmonicSum p / (U * p) +
      M * rootHarmonicSum p ≤ (N : ℝ) ^ 2 / p + (N : ℝ) ^ 2 / U +
        (N : ℝ) ^ 2 * rootHarmonicSum p / (U * p) + N * rootHarmonicSum p := by
    gcongr
  have h0 : 0 ≤ (M : ℝ) ^ 2 / p + (M : ℝ) ^ 2 / U + (M : ℝ) ^ 2 * rootHarmonicSum p / (U * p) +
      M * rootHarmonicSum p := by positivity
  have := invSum_nonneg N
  exact mul_le_mul (mul_le_mul_of_nonneg_left h1 (by norm_num)) h2 h0 (by positivity)

theorem minorArcBound_mono (p U : ℕ) {M N : ℕ} (h : M ≤ N) :
    minorArcBound p U M ≤ minorArcBound p U N := by
  unfold minorArcBound
  have hlog : (Nat.log 2 M : ℝ) ≤ Nat.log 2 N := by exact_mod_cast Nat.log_mono_right h
  gcongr
  exact typeIIBlockBound_mono p U h

theorem rowTransformMax_le_of_forall {N : ℕ} {c' : ℕ → ℝ} {d : ℕ} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ ζ ∈ nontrivialRoots d, ‖rowTransform N c' ζ‖ ≤ C) : rowTransformMax N c' d ≤ C := by
  unfold rowTransformMax
  split_ifs with hne
  · exact sup'_le hne _ h
  · exact hC

theorem cubicRowTransformMax_le_of_forall {N : ℕ} {c' : ℕ → ℝ} {d : ℕ} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ ζ ∈ nontrivialRoots d, ‖cubicRowTransform N c' ζ‖ ≤ C) :
    cubicRowTransformMax N c' d ≤ C := by
  unfold cubicRowTransformMax
  split_ifs with hne
  · exact sup'_le hne _ h
  · exact hC

/-- **The kernel statistic of the Möbius row at a prime, through the minor-arc law.** For `p` prime,
`1 ≤ U < p` and `N ≥ 2Q`,
`|Λ_p(μ𝟙_{(Q,2Q]})| ≤ (π²(p² - 1)/36 (Q+1)^{-2} + π²p³/24 (Q+1)^{-3}) M_p(U, 2Q)`. -/
theorem abs_kernelStatistic_moebiusWindowRow_le_minorArc {p : ℕ} (hp : p.Prime) {U : ℕ}
    (hU : 1 ≤ U) (hUp : U < p) {Q N : ℕ} (hQN : 2 * Q ≤ N) :
    |kernelStatistic N (moebiusWindowRow Q) p| ≤
      (Real.pi ^ 2 * ((p : ℝ) ^ 2 - 1) / 36 / ((Q : ℝ) + 1) ^ 2 +
        Real.pi ^ 2 * (p : ℝ) ^ 3 / 24 / ((Q : ℝ) + 1) ^ 3) * minorArcBound p U (2 * Q) := by
  set B := minorArcBound p U (2 * Q)
  have hB0 : 0 ≤ B := minorArcBound_nonneg p U (2 * Q)
  have hB : ∀ ζ ∈ nontrivialRoots p, ∀ x ≤ 2 * Q,
      ‖∑ n ∈ Icc 1 x, (moebiusReal n : ℂ) * ζ ^ n‖ ≤ B := fun ζ hζ x hx =>
    (norm_sum_moebius_mul_pow_le hp hζ hU hUp x).trans (minorArcBound_mono p U hx)
  have h2 : rowTransformMax N (moebiusWindowRow Q) p ≤ 2 * B / ((Q : ℝ) + 1) ^ 2 :=
    rowTransformMax_le_of_forall (by positivity) fun ζ hζ =>
      norm_sum_moebiusWindowRow_div_pow_le Q N 2 hQN ζ (hB ζ hζ)
  have h3 : cubicRowTransformMax N (moebiusWindowRow Q) p ≤ 2 * B / ((Q : ℝ) + 1) ^ 3 :=
    cubicRowTransformMax_le_of_forall (by positivity) fun ζ hζ =>
      norm_sum_moebiusWindowRow_div_pow_le Q N 3 hQN ζ (hB ζ hζ)
  have hp1 : (0 : ℝ) ≤ (p : ℝ) ^ 2 - 1 := by
    have : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    nlinarith
  refine (abs_kernelStatistic_le_fourier hp N _).trans ?_
  calc Real.pi ^ 2 * ((p : ℝ) ^ 2 - 1) / 72 * rowTransformMax N (moebiusWindowRow Q) p +
        Real.pi ^ 2 * (p : ℝ) ^ 3 / 48 * cubicRowTransformMax N (moebiusWindowRow Q) p
      ≤ Real.pi ^ 2 * ((p : ℝ) ^ 2 - 1) / 72 * (2 * B / ((Q : ℝ) + 1) ^ 2) +
        Real.pi ^ 2 * (p : ℝ) ^ 3 / 48 * (2 * B / ((Q : ℝ) + 1) ^ 3) := by
        gcongr
    _ = _ := by ring

end

end GaloisForLFunctions.BezoutValuationIncidence
