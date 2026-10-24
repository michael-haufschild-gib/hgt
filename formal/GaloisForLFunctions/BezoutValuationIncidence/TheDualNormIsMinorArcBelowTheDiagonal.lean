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

open Finset Filter Topology ArithmeticFunction RHTower RHTower.Sieve
open GaloisForLFunctions.BiScaleUncertainty
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

/-- **Window twists.** Let `c'` live on `(Q, 2Q]` with twisted partial sums
`‖Σ_{i<k} c'(Q+1+i) ζ^{Q+1+i}‖ ≤ B'` for `k ≤ Q`. Then for `N ≥ 2Q` and every `r`,
`‖Σ_{n ≤ N} (c'(n)/nʳ) ζⁿ‖ ≤ B'/(Q+1)ʳ`. -/
theorem norm_sum_window_div_pow_le_of_twisted (Q N r : ℕ) (hQN : 2 * Q ≤ N) {c' : ℕ → ℝ}
    (hsupp : ∀ n, c' n ≠ 0 → Q < n ∧ n ≤ 2 * Q) (ζ : ℂ) {B' : ℝ}
    (hB : ∀ k ≤ Q, ‖∑ i ∈ range k, (c' (Q + 1 + i) : ℂ) * ζ ^ (Q + 1 + i)‖ ≤ B') :
    ‖∑ n ∈ Icc 1 N, ((c' n / (n : ℝ) ^ r : ℝ) : ℂ) * ζ ^ n‖ ≤ B' / ((Q : ℝ) + 1) ^ r := by
  have hwin : ∑ n ∈ Icc 1 N, ((c' n / (n : ℝ) ^ r : ℝ) : ℂ) * ζ ^ n =
      ∑ i ∈ range Q, ((1 / ((Q + 1 + i : ℕ) : ℝ) ^ r : ℝ) : ℂ) *
        ((c' (Q + 1 + i) : ℂ) * ζ ^ (Q + 1 + i)) := by
    have hsub : Ioc Q (2 * Q) ⊆ Icc 1 N := fun n hn => by
      simp only [mem_Ioc, mem_Icc] at hn ⊢; omega
    rw [← sum_subset hsub fun n _ hn => by
      have : c' n = 0 := by
        by_contra h
        exact hn (mem_Ioc.mpr (hsupp n h))
      rw [this]; simp]
    have hIoc : Ioc Q (2 * Q) = Ico (Q + 1) (2 * Q + 1) := by
      ext n; simp only [mem_Ioc, mem_Ico]; omega
    rw [hIoc, sum_Ico_eq_sum_range, show 2 * Q + 1 - (Q + 1) = Q by omega]
    refine sum_congr rfl fun i _ => ?_
    push_cast
    ring
  rw [hwin]
  have h := norm_sum_range_ofReal_mul_le_of_antitone Q hB
    (w := fun i => 1 / ((Q + 1 + i : ℕ) : ℝ) ^ r)
    (fun i => by positivity) (fun i => by
      apply one_div_le_one_div_of_le (by positivity)
      exact pow_le_pow_left₀ (by positivity) (by push_cast; linarith) r)
  refine h.trans (le_of_eq ?_)
  push_cast
  ring

/-- **Window twists of the Möbius row.** If `‖Σ_{n ≤ x} μ(n) ζⁿ‖ ≤ B` for all `x ≤ 2Q`, then for
`N ≥ 2Q` and every `r`, `‖Σ_{n ≤ N} (μ𝟙_{(Q,2Q]}(n)/nʳ) ζⁿ‖ ≤ 2B/(Q+1)ʳ`. -/
theorem norm_sum_moebiusWindowRow_div_pow_le (Q N r : ℕ) (hQN : 2 * Q ≤ N) (ζ : ℂ) {B : ℝ}
    (hB : ∀ x ≤ 2 * Q, ‖∑ n ∈ Icc 1 x, (moebiusReal n : ℂ) * ζ ^ n‖ ≤ B) :
    ‖∑ n ∈ Icc 1 N, ((moebiusWindowRow Q n / (n : ℝ) ^ r : ℝ) : ℂ) * ζ ^ n‖ ≤
      2 * B / ((Q : ℝ) + 1) ^ r := by
  set S : ℕ → ℂ := fun x => ∑ n ∈ Icc 1 x, (moebiusReal n : ℂ) * ζ ^ n
  refine norm_sum_window_div_pow_le_of_twisted Q N r hQN (fun n h => ?_) ζ fun k hk => ?_
  · unfold moebiusWindowRow at h
    split_ifs at h with hn
    · exact hn
    · exact absurd rfl h
  have hdiff : ∑ i ∈ range k, ((moebiusWindowRow Q (Q + 1 + i) : ℝ) : ℂ) * ζ ^ (Q + 1 + i) =
      S (Q + k) - S Q := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ, ih (by omega), show Q + (k + 1) = (Q + k) + 1 by ring]
      simp only [S]
      rw [sum_Icc_succ_top (by omega : 1 ≤ Q + k + 1), show Q + 1 + k = Q + k + 1 by ring,
        moebiusWindowRow, if_pos (by omega)]
      ring
  rw [hdiff]
  calc ‖S (Q + k) - S Q‖ ≤ ‖S (Q + k)‖ + ‖S Q‖ := norm_sub_le _ _
    _ ≤ B + B := add_le_add (hB _ (by omega)) (hB _ (by omega))
    _ = 2 * B := by ring

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

/-! ## §3. The power saving at every cross-scale exponent below the diagonal -/

/-- `⌊x⌋₊ ≥ x/2` for `x ≥ 1`. -/
theorem half_le_natFloor {x : ℝ} (hx : 1 ≤ x) : x / 2 ≤ ⌊x⌋₊ := by
  have h1 : (1 : ℝ) ≤ ⌊x⌋₊ := by exact_mod_cast Nat.le_floor (by exact_mod_cast hx)
  have h2 := Nat.lt_floor_add_one x
  by_cases hx2 : 2 ≤ x
  · linarith
  · linarith

/-- `log₂ n + 1 ≤ 3 (1 + log n)`. -/
theorem natLog_two_add_one_le (n : ℕ) (hn : 1 ≤ n) :
    (Nat.log 2 n : ℝ) + 1 ≤ 3 * (1 + Real.log n) := by
  have hpow : ((2 : ℝ) ^ Nat.log 2 n) ≤ n := by exact_mod_cast Nat.pow_log_le_self 2 (by omega)
  have hlog : (Nat.log 2 n : ℝ) * Real.log 2 ≤ Real.log n := by
    rw [← Real.log_pow]
    exact Real.log_le_log (by positivity) hpow
  have h2 := Real.log_two_gt_d9
  have hl0 : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
  have hk0 : (0 : ℝ) ≤ Nat.log 2 n := Nat.cast_nonneg _
  have hprod := mul_le_mul_of_nonneg_left h2.le hk0
  linarith

/-- The constant factor of the spectral law: for `p ≤ q`,
`π²(p² - 1)/36 (q+1)^{-2} + π²p³/24 (q+1)^{-3} ≤ 0.69 p²/q²`. -/
theorem spectralFactor_le {p q : ℝ} (hp : 1 ≤ p) (hq : 0 < q) (hpq : p ≤ q) :
    Real.pi ^ 2 * (p ^ 2 - 1) / 36 / (q + 1) ^ 2 + Real.pi ^ 2 * p ^ 3 / 24 / (q + 1) ^ 3 ≤
      0.69 * (p ^ 2 / q ^ 2) := by
  have hpi : Real.pi ^ 2 < 9.87 := by nlinarith [Real.pi_pos, Real.pi_lt_d4]
  have hpi0 : 0 ≤ Real.pi ^ 2 := sq_nonneg _
  have t1 : (p ^ 2 - 1) / (q + 1) ^ 2 ≤ p ^ 2 / q ^ 2 := by
    calc (p ^ 2 - 1) / (q + 1) ^ 2 ≤ p ^ 2 / (q + 1) ^ 2 :=
          div_le_div_of_nonneg_right (by linarith) (by positivity)
      _ ≤ p ^ 2 / q ^ 2 := div_le_div_of_nonneg_left (by positivity) (by positivity)
          (pow_le_pow_left₀ hq.le (by linarith) 2)
  have t2 : p ^ 3 / (q + 1) ^ 3 ≤ p ^ 2 / q ^ 2 := by
    calc p ^ 3 / (q + 1) ^ 3 ≤ p ^ 3 / q ^ 3 :=
          div_le_div_of_nonneg_left (by positivity) (by positivity)
            (pow_le_pow_left₀ hq.le (by linarith) 3)
      _ = p ^ 2 / q ^ 2 * (p / q) := by field_simp
      _ ≤ p ^ 2 / q ^ 2 * 1 :=
          mul_le_mul_of_nonneg_left ((div_le_one hq).mpr hpq) (by positivity)
      _ = p ^ 2 / q ^ 2 := mul_one _
  have h0 : 0 ≤ p ^ 2 / q ^ 2 := by positivity
  calc Real.pi ^ 2 * (p ^ 2 - 1) / 36 / (q + 1) ^ 2 + Real.pi ^ 2 * p ^ 3 / 24 / (q + 1) ^ 3
      = Real.pi ^ 2 / 36 * ((p ^ 2 - 1) / (q + 1) ^ 2) +
          Real.pi ^ 2 / 24 * (p ^ 3 / (q + 1) ^ 3) := by ring
    _ ≤ Real.pi ^ 2 / 36 * (p ^ 2 / q ^ 2) + Real.pi ^ 2 / 24 * (p ^ 2 / q ^ 2) := by gcongr
    _ ≤ 0.69 * (p ^ 2 / q ^ 2) := by nlinarith

/-- **The cutoff `U = ⌊Q^{δ/2}⌋`.** For `Q ≥ 2`, `0 < δ < 1` and a prime `Q^δ ≤ p ≤ Q^{1-δ}`, with
`L = 1 + log 2Q` and `T = Q · Q^{-δ/4}`: `1 ≤ U < p`, `U ≤ T`, `log U ≤ L`, `W_p ≤ L T`,
`U W_p ≤ L T`, `p ≤ T` and `(log₂ 2Q + 1) √(typeIIBlockBound p U 2Q) ≤ 30 L³ T`. -/
theorem exists_minorArc_cutoff {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) {Q : ℕ} (hQ : 2 ≤ Q) {p : ℕ}
    (hp : p.Prime) (hpl : (Q : ℝ) ^ δ ≤ p) (hpu : (p : ℝ) ≤ (Q : ℝ) ^ (1 - δ)) :
    ∃ U : ℕ, 1 ≤ U ∧ U < p ∧ (U : ℝ) ≤ Q * (Q : ℝ) ^ (-(δ / 4)) ∧
      Real.log U ≤ 1 + Real.log (2 * Q) ∧
      rootHarmonicSum p ≤ (1 + Real.log (2 * Q)) * (Q * (Q : ℝ) ^ (-(δ / 4))) ∧
      (U : ℝ) * rootHarmonicSum p ≤ (1 + Real.log (2 * Q)) * (Q * (Q : ℝ) ^ (-(δ / 4))) ∧
      (p : ℝ) ≤ Q * (Q : ℝ) ^ (-(δ / 4)) ∧
      ((Nat.log 2 (2 * Q) : ℝ) + 1) * Real.sqrt (typeIIBlockBound p U (2 * Q)) ≤
        30 * (1 + Real.log (2 * Q)) ^ 3 * (Q * (Q : ℝ) ^ (-(δ / 4))) := by
  have hq2 : (2 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hq0 : (0 : ℝ) < Q := by linarith
  have hq1 : (1 : ℝ) < Q := by linarith
  set q : ℝ := (Q : ℝ)
  set y : ℝ := q ^ (δ / 4) with hydef
  have hy1 : 1 < y := Real.one_lt_rpow hq1 (by positivity)
  have hy0 : 0 < y := by linarith
  have hpowy : ∀ (k : ℕ), y ^ k = q ^ (δ / 4 * k) := fun k => by
    rw [hydef, ← Real.rpow_natCast, ← Real.rpow_mul hq0.le]
  have hy4 : y ^ 4 = q ^ δ := by rw [hpowy]; congr 1; push_cast; ring
  have hq1δ : q ^ (1 - δ) = q / y ^ 4 := by rw [Real.rpow_sub hq0, Real.rpow_one, hy4]
  have hT : q * q ^ (-(δ / 4)) = q / y := by rw [Real.rpow_neg hq0.le, ← hydef, div_eq_mul_inv]
  rw [hT]
  have hy3 : y ^ 3 ≤ q := by
    rw [hpowy]
    calc q ^ (δ / 4 * ((3 : ℕ) : ℝ)) ≤ q ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hq1.le (by push_cast; linarith)
      _ = q := Real.rpow_one q
  have hy2ge : 1 ≤ y ^ 2 := one_le_pow₀ hy1.le
  have hy24 : y ^ 2 ≤ y ^ 4 := pow_le_pow_right₀ hy1.le (by norm_num)
  have hpR : y ^ 4 ≤ (p : ℝ) := by rw [hy4]; exact hpl
  have hpq : (p : ℝ) ≤ q / y ^ 4 := by rw [← hq1δ]; exact hpu
  have hy4pos : 0 < y ^ 4 := by positivity
  have hpq' : (p : ℝ) ≤ q := hpq.trans (div_le_self hq0.le (one_le_pow₀ hy1.le))
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hqy4 : q / y ^ 4 ≤ q / y :=
    div_le_div_of_nonneg_left hq0.le hy0 (le_self_pow₀ hy1.le (by norm_num))
  have hqy : y ^ 2 ≤ q / y := by
    rw [le_div_iff₀ hy0, show y ^ 2 * y = y ^ 3 by ring]; exact hy3
  -- the cutoff `U = ⌊Q^{δ/2}⌋`
  set U := ⌊y ^ 2⌋₊
  have hU1 : 1 ≤ U := Nat.le_floor (by exact_mod_cast hy2ge)
  have hUle : (U : ℝ) ≤ y ^ 2 := Nat.floor_le (by positivity)
  have hUge : y ^ 2 / 2 ≤ U := half_le_natFloor hy2ge
  have hUp : U < p := by
    have : (U : ℝ) < p := lt_of_le_of_lt hUle
      (lt_of_lt_of_le (pow_lt_pow_right₀ hy1 (by norm_num : 2 < 4)) hpR)
    exact_mod_cast this
  -- logarithms
  set L : ℝ := 1 + Real.log (2 * q) with hLdef
  have hlog2q : 0 ≤ Real.log (2 * q) := Real.log_nonneg (by linarith)
  have hL1 : 1 ≤ L := by rw [hLdef]; linarith
  have hcast : ((2 * Q : ℕ) : ℝ) = 2 * q := by push_cast; ring
  have hW : rootHarmonicSum p ≤ p * L := by
    refine (rootHarmonicSum_le p).trans (mul_le_mul_of_nonneg_left ?_ hp0.le)
    have : Real.log p ≤ Real.log (2 * q) := Real.log_le_log hp0 (by linarith)
    rw [hLdef]; linarith
  have hH : invSum (2 * Q) ≤ L := by
    have h := invSum_le_one_add_log (by omega : 1 ≤ 2 * Q)
    rwa [hcast] at h
  have hH0 : 0 ≤ invSum (2 * Q) := invSum_nonneg _
  have hlogtwo : (Nat.log 2 (2 * Q) : ℝ) + 1 ≤ 3 * L := by
    have h := natLog_two_add_one_le (2 * Q) (by omega)
    rwa [hcast] at h
  have hWnn : 0 ≤ rootHarmonicSum p := rootHarmonicSum_nonneg p
  have hUpos : (0 : ℝ) < U := by exact_mod_cast hU1
  -- the Type-II block bound
  have a1 : (2 * q) ^ 2 / p ≤ 4 * (q ^ 2 / y ^ 2) := by
    calc (2 * q) ^ 2 / p ≤ (2 * q) ^ 2 / y ^ 2 :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) (hy24.trans hpR)
      _ = 4 * (q ^ 2 / y ^ 2) := by ring
  have a2 : (2 * q) ^ 2 / U ≤ 8 * (q ^ 2 / y ^ 2) := by
    calc (2 * q) ^ 2 / U ≤ (2 * q) ^ 2 / (y ^ 2 / 2) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) hUge
      _ = 8 * (q ^ 2 / y ^ 2) := by field_simp; ring
  have a3 : (2 * q) ^ 2 * rootHarmonicSum p / (U * p) ≤ 8 * L * (q ^ 2 / y ^ 2) := by
    calc (2 * q) ^ 2 * rootHarmonicSum p / (U * p) ≤ (2 * q) ^ 2 * (p * L) / (U * p) :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hW (by positivity))
            (by positivity)
      _ = (2 * q) ^ 2 * L / U := by field_simp
      _ ≤ (2 * q) ^ 2 * L / (y ^ 2 / 2) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) hUge
      _ = 8 * L * (q ^ 2 / y ^ 2) := by field_simp; ring
  have a4 : 2 * q * rootHarmonicSum p ≤ 2 * L * (q ^ 2 / y ^ 2) := by
    calc 2 * q * rootHarmonicSum p ≤ 2 * q * (p * L) :=
          mul_le_mul_of_nonneg_left hW (by positivity)
      _ ≤ 2 * q * (q / y ^ 4 * L) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hpq (by linarith))
            (by positivity)
      _ = 2 * L * (q ^ 2 / y ^ 4) := by ring
      _ ≤ 2 * L * (q ^ 2 / y ^ 2) :=
          mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left (by positivity) (by positivity)
            hy24) (by linarith)
  have hTB : typeIIBlockBound p U (2 * Q) ≤ 88 * L ^ 4 * (q ^ 2 / y ^ 2) := by
    unfold typeIIBlockBound
    rw [hcast]
    have hsum : (2 * q) ^ 2 / p + (2 * q) ^ 2 / U + (2 * q) ^ 2 * rootHarmonicSum p / (U * p) +
        2 * q * rootHarmonicSum p ≤ 22 * L * (q ^ 2 / y ^ 2) := by
      linarith [mul_le_mul_of_nonneg_right hL1 (by positivity : (0 : ℝ) ≤ q ^ 2 / y ^ 2)]
    have hH3 : 1 + invSum (2 * Q) ^ 3 ≤ 2 * L ^ 3 := by
      have : invSum (2 * Q) ^ 3 ≤ L ^ 3 := pow_le_pow_left₀ hH0 hH 3
      have : 1 ≤ L ^ 3 := one_le_pow₀ hL1
      linarith
    have hs0 : 0 ≤ (2 * q) ^ 2 / p + (2 * q) ^ 2 / U + (2 * q) ^ 2 * rootHarmonicSum p / (U * p) +
        2 * q * rootHarmonicSum p := by positivity
    calc 2 * (1 + invSum (2 * Q) ^ 3) * ((2 * q) ^ 2 / p + (2 * q) ^ 2 / U +
          (2 * q) ^ 2 * rootHarmonicSum p / (U * p) + 2 * q * rootHarmonicSum p)
        ≤ 2 * (2 * L ^ 3) * (22 * L * (q ^ 2 / y ^ 2)) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hH3 (by norm_num)) hsum hs0 (by positivity)
      _ = 88 * L ^ 4 * (q ^ 2 / y ^ 2) := by ring
  have hsqrt : Real.sqrt (typeIIBlockBound p U (2 * Q)) ≤ 10 * L ^ 2 * (q / y) := by
    have h0 : 0 ≤ 10 * L ^ 2 * (q / y) := by positivity
    calc Real.sqrt (typeIIBlockBound p U (2 * Q)) ≤ Real.sqrt ((10 * L ^ 2 * (q / y)) ^ 2) := by
          refine Real.sqrt_le_sqrt (hTB.trans ?_)
          have : (10 * L ^ 2 * (q / y)) ^ 2 = 100 * L ^ 4 * (q ^ 2 / y ^ 2) := by ring
          rw [this]
          have : 0 ≤ L ^ 4 * (q ^ 2 / y ^ 2) := by positivity
          linarith
      _ = 10 * L ^ 2 * (q / y) := Real.sqrt_sq h0
  refine ⟨U, hU1, hUp, hUle.trans hqy, ?_, ?_, ?_, hpq.trans hqy4, ?_⟩
  · have : Real.log U ≤ Real.log (2 * q) :=
      Real.log_le_log hUpos ((hUle.trans hqy).trans ((div_le_self hq0.le hy1.le).trans (by linarith)))
    rw [hLdef]; linarith
  · calc rootHarmonicSum p ≤ p * L := hW
      _ ≤ q / y * L := mul_le_mul_of_nonneg_right (hpq.trans hqy4) (by linarith)
      _ = L * (q / y) := by ring
  · calc (U : ℝ) * rootHarmonicSum p ≤ y ^ 2 * (p * L) :=
          mul_le_mul hUle hW hWnn (by positivity)
      _ ≤ y ^ 2 * (q / y ^ 4 * L) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hpq (by linarith)) (by positivity)
      _ = L * (q / y ^ 2) := by field_simp
      _ ≤ L * (q / y) := mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left hq0.le hy0
          (le_self_pow₀ hy1.le (by norm_num))) (by linarith)
  · calc ((Nat.log 2 (2 * Q) : ℝ) + 1) * Real.sqrt (typeIIBlockBound p U (2 * Q))
        ≤ 3 * L * (10 * L ^ 2 * (q / y)) :=
          mul_le_mul hlogtwo hsqrt (Real.sqrt_nonneg _) (by positivity)
      _ = 30 * L ^ 3 * (q / y) := by ring

/-- **The power saving of the dual-norm statistic below the diagonal.** For `Q ≥ 2`, `0 < δ < 1`,
every prime `Q^δ ≤ p ≤ Q^{1-δ}` and `N ≥ 2Q`,
`|Λ_p(μ𝟙_{(Q,2Q]})| ≤ 23 (1 + log 2Q)³ (p²/Q) Q^{-δ/4}`. -/
theorem abs_kernelStatistic_moebiusWindowRow_le_rpow {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1)
    {Q : ℕ} (hQ : 2 ≤ Q) {p : ℕ} (hp : p.Prime) (hpl : (Q : ℝ) ^ δ ≤ p)
    (hpu : (p : ℝ) ≤ (Q : ℝ) ^ (1 - δ)) {N : ℕ} (hQN : 2 * Q ≤ N) :
    |kernelStatistic N (moebiusWindowRow Q) p| ≤
      23 * (1 + Real.log (2 * Q)) ^ 3 * ((p : ℝ) ^ 2 / Q) * (Q : ℝ) ^ (-(δ / 4)) := by
  obtain ⟨U, hU1, hUp, hUT, -, -, hUW, hpT, hsq⟩ := exists_minorArc_cutoff hδ hδ1 hQ hp hpl hpu
  have hq0 : (0 : ℝ) < Q := by exact_mod_cast (by omega : 0 < Q)
  set L := 1 + Real.log (2 * (Q : ℝ)) with hLdef
  have hL1 : 1 ≤ L := by
    have := Real.log_nonneg (by have : (2 : ℝ) ≤ Q := (by exact_mod_cast hQ); linarith :
      (1 : ℝ) ≤ 2 * Q)
    rw [hLdef]; linarith
  set T := (Q : ℝ) * (Q : ℝ) ^ (-(δ / 4))
  have hT0 : 0 ≤ T := mul_nonneg hq0.le (Real.rpow_nonneg hq0.le _)
  have hM : minorArcBound p U (2 * Q) ≤ 33 * L ^ 3 * T := by
    unfold minorArcBound
    have hL3 : L ≤ L ^ 3 := le_self_pow₀ hL1 (by norm_num)
    have hL31 : 1 ≤ L ^ 3 := one_le_pow₀ hL1
    nlinarith [mul_le_mul_of_nonneg_right hL3 hT0, mul_le_mul_of_nonneg_right hL31 hT0]
  have hfac := spectralFactor_le (by exact_mod_cast hp.one_lt.le) hq0
    (hpT.trans (by
      calc T ≤ (Q : ℝ) * 1 := mul_le_mul_of_nonneg_left
            (Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast (by omega : 1 ≤ Q))
              (by linarith)) hq0.le
        _ = Q := mul_one _))
  calc |kernelStatistic N (moebiusWindowRow Q) p|
      ≤ (Real.pi ^ 2 * ((p : ℝ) ^ 2 - 1) / 36 / ((Q : ℝ) + 1) ^ 2 +
          Real.pi ^ 2 * (p : ℝ) ^ 3 / 24 / ((Q : ℝ) + 1) ^ 3) * minorArcBound p U (2 * Q) :=
        abs_kernelStatistic_moebiusWindowRow_le_minorArc hp hU1 hUp hQN
    _ ≤ 0.69 * ((p : ℝ) ^ 2 / (Q : ℝ) ^ 2) * (33 * L ^ 3 * T) :=
        mul_le_mul hfac hM (minorArcBound_nonneg _ _ _) (by positivity)
    _ ≤ 23 * L ^ 3 * ((p : ℝ) ^ 2 / Q) * (Q : ℝ) ^ (-(δ / 4)) := by
        have e : 0.69 * ((p : ℝ) ^ 2 / (Q : ℝ) ^ 2) * (33 * L ^ 3 * T) =
            22.77 * L ^ 3 * ((p : ℝ) ^ 2 / Q) * (Q : ℝ) ^ (-(δ / 4)) := by
          simp only [T]; field_simp; ring
        rw [e]
        have : 0 ≤ L ^ 3 * ((p : ℝ) ^ 2 / Q) * (Q : ℝ) ^ (-(δ / 4)) := by positivity
        linarith

/-- **Eventual form.** For `0 < δ < 1` and all large `Q`, every prime `Q^δ ≤ p ≤ Q^{1-δ}` has
`|Λ_p(μ𝟙_{(Q,2Q]})| ≤ (p²/Q) Q^{-δ/8}`. -/
theorem eventually_abs_kernelStatistic_moebiusWindowRow_le {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    ∀ᶠ Q : ℕ in atTop, ∀ p : ℕ, p.Prime → (Q : ℝ) ^ δ ≤ p → (p : ℝ) ≤ (Q : ℝ) ^ (1 - δ) →
      ∀ N, 2 * Q ≤ N →
        |kernelStatistic N (moebiusWindowRow Q) p| ≤ (p : ℝ) ^ 2 / Q * (Q : ℝ) ^ (-(δ / 8)) := by
  set ε : ℝ := δ / 48 with hεdef
  have hε : 0 < ε := by rw [hεdef]; positivity
  set C : ℝ := 184 * (1 + 1 / ε) ^ 3
  have hgrow : Tendsto (fun Q : ℕ => (Q : ℝ) ^ (δ / 16)) atTop atTop :=
    (tendsto_rpow_atTop (by positivity)).comp tendsto_natCast_atTop_atTop
  filter_upwards [hgrow.eventually_ge_atTop C, eventually_ge_atTop 2] with Q hQC hQ p hp hpl hpu N hQN
  have hq2 : (2 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hq0 : (0 : ℝ) < Q := by linarith
  have h := abs_kernelStatistic_moebiusWindowRow_le_rpow hδ hδ1 hQ hp hpl hpu hQN
  -- `23 (1 + log 2Q)³ ≤ Q^{δ/8}`
  have h2q : (1 : ℝ) ≤ 2 * Q := by linarith
  have hx : (1 : ℝ) ≤ (2 * (Q : ℝ)) ^ ε := Real.one_le_rpow h2q hε.le
  have hlog : 1 + Real.log (2 * Q) ≤ (1 + 1 / ε) * (2 * (Q : ℝ)) ^ ε := by
    have := Real.log_le_rpow_div (by linarith : (0 : ℝ) ≤ 2 * Q) hε
    have e : (2 * (Q : ℝ)) ^ ε / ε = 1 / ε * (2 * (Q : ℝ)) ^ ε := by ring
    nlinarith
  have hlog0 : 0 ≤ 1 + Real.log (2 * Q) := by
    have := Real.log_nonneg h2q; linarith
  have h2ε : (2 * (Q : ℝ)) ^ ε ≤ 2 * (Q : ℝ) ^ ε := by
    rw [Real.mul_rpow (by norm_num) hq0.le]
    have : (2 : ℝ) ^ ε ≤ 2 := by
      calc (2 : ℝ) ^ ε ≤ 2 ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by simp only [ε]; linarith)
        _ = 2 := Real.rpow_one 2
    nlinarith [Real.rpow_nonneg hq0.le ε]
  have hcube : (1 + Real.log (2 * Q)) ^ 3 ≤ 8 * (1 + 1 / ε) ^ 3 * (Q : ℝ) ^ (δ / 16) := by
    have hle : 1 + Real.log (2 * Q) ≤ 2 * (1 + 1 / ε) * (Q : ℝ) ^ ε := by
      have : 0 ≤ 1 + 1 / ε := by positivity
      nlinarith
    calc (1 + Real.log (2 * Q)) ^ 3 ≤ (2 * (1 + 1 / ε) * (Q : ℝ) ^ ε) ^ 3 :=
          pow_le_pow_left₀ hlog0 hle 3
      _ = 8 * (1 + 1 / ε) ^ 3 * ((Q : ℝ) ^ ε) ^ (3 : ℕ) := by ring
      _ = 8 * (1 + 1 / ε) ^ 3 * (Q : ℝ) ^ (δ / 16) := by
          have e : ((Q : ℝ) ^ ε) ^ (3 : ℕ) = (Q : ℝ) ^ (δ / 16) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul hq0.le]
            congr 1
            simp only [ε]
            push_cast
            ring
          rw [e]
  have hsplit : (Q : ℝ) ^ (δ / 8) = (Q : ℝ) ^ (δ / 16) * (Q : ℝ) ^ (δ / 16) := by
    rw [← Real.rpow_add hq0]; congr 1; ring
  have hkey : 23 * (1 + Real.log (2 * Q)) ^ 3 ≤ (Q : ℝ) ^ (δ / 8) := by
    have hg0 : 0 ≤ (Q : ℝ) ^ (δ / 16) := Real.rpow_nonneg hq0.le _
    rw [hsplit]
    calc 23 * (1 + Real.log (2 * Q)) ^ 3 ≤ 23 * (8 * (1 + 1 / ε) ^ 3 * (Q : ℝ) ^ (δ / 16)) :=
          mul_le_mul_of_nonneg_left hcube (by norm_num)
      _ = C * (Q : ℝ) ^ (δ / 16) := by simp only [C]; ring
      _ ≤ (Q : ℝ) ^ (δ / 16) * (Q : ℝ) ^ (δ / 16) := mul_le_mul_of_nonneg_right hQC hg0
  have hexp : (Q : ℝ) ^ (δ / 8) * (Q : ℝ) ^ (-(δ / 4)) = (Q : ℝ) ^ (-(δ / 8)) := by
    rw [← Real.rpow_add hq0]; congr 1; ring
  refine h.trans ?_
  have hpos : 0 ≤ (p : ℝ) ^ 2 / Q * (Q : ℝ) ^ (-(δ / 4)) := by positivity
  calc 23 * (1 + Real.log (2 * Q)) ^ 3 * ((p : ℝ) ^ 2 / Q) * (Q : ℝ) ^ (-(δ / 4))
      = 23 * (1 + Real.log (2 * Q)) ^ 3 * ((p : ℝ) ^ 2 / Q * (Q : ℝ) ^ (-(δ / 4))) := by ring
    _ ≤ (Q : ℝ) ^ (δ / 8) * ((p : ℝ) ^ 2 / Q * (Q : ℝ) ^ (-(δ / 4))) :=
        mul_le_mul_of_nonneg_right hkey hpos
    _ = (p : ℝ) ^ 2 / Q * (Q : ℝ) ^ (-(δ / 8)) := by rw [← hexp]; ring

/-! ## §4. The dual norm and the cross-scale form -/

/-- **The dual norm has a power saving below the diagonal.** For every set `S` of primes in
`[Q^δ, Q^{1-δ}]`, `Σ_{p ∈ S} |Λ_p(μ𝟙_{(Q,2Q]})|/p ≤ 23 (1 + log 2Q)³ Q^{-δ/4} Σ_{p ∈ S} p/Q`. -/
theorem dualNorm_moebiusWindowRow_le_rpow {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) {Q : ℕ}
    (hQ : 2 ≤ Q) {S : Finset ℕ}
    (hS : ∀ p ∈ S, p.Prime ∧ (Q : ℝ) ^ δ ≤ p ∧ (p : ℝ) ≤ (Q : ℝ) ^ (1 - δ)) {N : ℕ}
    (hQN : 2 * Q ≤ N) :
    ∑ p ∈ S, |kernelStatistic N (moebiusWindowRow Q) p| / p ≤
      23 * (1 + Real.log (2 * Q)) ^ 3 * (Q : ℝ) ^ (-(δ / 4)) * ∑ p ∈ S, (p : ℝ) / Q := by
  rw [mul_sum]
  refine sum_le_sum fun p hp => ?_
  obtain ⟨hpp, hpl, hpu⟩ := hS p hp
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
  have h := abs_kernelStatistic_moebiusWindowRow_le_rpow hδ hδ1 hQ hpp hpl hpu hQN
  calc |kernelStatistic N (moebiusWindowRow Q) p| / p
      ≤ 23 * (1 + Real.log (2 * Q)) ^ 3 * ((p : ℝ) ^ 2 / Q) * (Q : ℝ) ^ (-(δ / 4)) / p :=
        div_le_div_of_nonneg_right h hp0.le
    _ = _ := by field_simp

/-- `Σ_n |μ𝟙_{(Q,2Q]}(n)|/nʳ ≤ Q/Qʳ`. -/
theorem sum_Icc_abs_moebiusWindowRow_div_pow_le {Q N : ℕ} (hQ : 1 ≤ Q) (r : ℕ) :
    ∑ n ∈ Icc 1 N, |moebiusWindowRow Q n| / (n : ℝ) ^ r ≤ (Q : ℝ) / (Q : ℝ) ^ r := by
  have hq0 : (0 : ℝ) < Q := by exact_mod_cast hQ
  calc ∑ n ∈ Icc 1 N, |moebiusWindowRow Q n| / (n : ℝ) ^ r
      ≤ ∑ n ∈ Ioc Q (2 * Q), 1 / (Q : ℝ) ^ r := by
        rw [← sum_filter_add_sum_filter_not (Icc 1 N) (fun n => Q < n ∧ n ≤ 2 * Q)]
        have h0 : ∑ n ∈ (Icc 1 N).filter (fun n => ¬(Q < n ∧ n ≤ 2 * Q)),
            |moebiusWindowRow Q n| / (n : ℝ) ^ r = 0 :=
          sum_eq_zero fun n hn => by
            rw [moebiusWindowRow, if_neg (mem_filter.mp hn).2, abs_zero, zero_div]
        rw [h0, add_zero]
        refine (sum_le_sum fun n hn => ?_).trans (sum_le_sum_of_subset_of_nonneg
          (fun n hn => by simp only [mem_filter, mem_Icc, mem_Ioc] at hn ⊢; exact hn.2)
          fun _ _ _ => by positivity)
        have hn1 : Q < n := (mem_filter.mp hn).2.1
        have hnQ : (Q : ℝ) ≤ n := by exact_mod_cast hn1.le
        rw [moebiusWindowRow, if_pos (mem_filter.mp hn).2]
        have hmu : |moebiusReal n| ≤ 1 := by
          unfold moebiusReal; exact_mod_cast ArithmeticFunction.abs_moebius_le_one
        calc |moebiusReal n| / (n : ℝ) ^ r ≤ 1 / (n : ℝ) ^ r :=
              div_le_div_of_nonneg_right hmu (by positivity)
          _ ≤ 1 / (Q : ℝ) ^ r := one_div_le_one_div_of_le (by positivity)
              (pow_le_pow_left₀ hq0.le hnQ r)
    _ = (Q : ℝ) / (Q : ℝ) ^ r := by
        rw [sum_const, Nat.card_Ioc, show 2 * Q - Q = Q by omega, nsmul_eq_mul]
        ring

/-- **The cross-scale form of the Möbius row has a power saving below the diagonal.** For every row
`c` with `|c| ≤ 1` supported on primes in `[Q^δ, Q^{1-δ}]`,
`|B(c, c') + m(c) R(c') + β(c) H(c') - main| ≤ (23 (1 + log 2Q)³ Q^{-δ/4} + 6 Q^{-2δ}) Σ_p p/Q`,
`c' = μ𝟙_{(Q,2Q]}`: a power saving over the trivial size `Σ_p p/Q`, for arbitrary bounded
small-scale coefficients, at every cross-scale exponent `θ ≤ 2 - 2δ`. -/
theorem abs_rowBilinear_moebiusWindowRow_sub_main_le_rpow {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1)
    {Q : ℕ} (hQ : 2 ≤ Q) {S : Finset ℕ}
    (hS : ∀ p ∈ S, p.Prime ∧ (Q : ℝ) ^ δ ≤ p ∧ (p : ℝ) ≤ (Q : ℝ) ^ (1 - δ)) {N : ℕ}
    (hQN : 2 * Q ≤ N) {c : ℕ → ℝ} (hc : ∀ d, |c d| ≤ 1) (hcS : ∀ d, c d ≠ 0 → d ∈ S) :
    |rowBilinear N c (moebiusWindowRow Q) + rowMean N c * vonMangoldtReadout N (moebiusWindowRow Q) +
        rowBeta N c * finiteHarmonicSum N (moebiusWindowRow Q) -
        equidistributedMain N c (moebiusWindowRow Q)| ≤
      (23 * (1 + Real.log (2 * Q)) ^ 3 * (Q : ℝ) ^ (-(δ / 4)) + 6 * (Q : ℝ) ^ (-(2 * δ))) *
        ∑ p ∈ S, (p : ℝ) / Q := by
  have hq0 : (0 : ℝ) < Q := by exact_mod_cast (by omega : 0 < Q)
  have hq1 : (1 : ℝ) ≤ Q := by exact_mod_cast (by omega : 1 ≤ Q)
  have hpQ : ∀ p ∈ S, (p : ℝ) ≤ (Q : ℝ) ^ (1 - δ) := fun p hp => (hS p hp).2.2
  have hpQ' : ∀ p ∈ S, (p : ℝ) ≤ Q := fun p hp => (hpQ p hp).trans (by
    calc (Q : ℝ) ^ (1 - δ) ≤ (Q : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hq1 (by linarith)
      _ = Q := Real.rpow_one _)
  have hSI : S ⊆ Icc 1 N := fun p hp => by
    have h1 := (hS p hp).1.one_lt.le
    have h2 : p ≤ Q := by exact_mod_cast hpQ' p hp
    exact mem_Icc.mpr ⟨h1, by omega⟩
  have hlaw := abs_rowBilinear_sub_kernelStatistic_le N (moebiusWindowRow Q) (c := c)
    (fun d hd => (hS d (hcS d hd)).1)
  have hzero : ∀ d ∈ Icc 1 N, d ∉ S → c d = 0 := fun d _ hd => by
    by_contra h; exact hd (hcS d h)
  have hstat : |∑ d ∈ Icc 1 N, c d / d * kernelStatistic N (moebiusWindowRow Q) d| ≤
      ∑ p ∈ S, |kernelStatistic N (moebiusWindowRow Q) p| / p := by
    rw [← sum_subset hSI fun d hd hdS => by rw [hzero d hd hdS, zero_div, zero_mul]]
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun p hp => ?_)
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (hS p hp).1.pos
    rw [abs_mul, abs_div, abs_of_pos hp0]
    calc |c p| / p * |kernelStatistic N (moebiusWindowRow Q) p|
        ≤ 1 / p * |kernelStatistic N (moebiusWindowRow Q) p| :=
          mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (hc p) hp0.le) (abs_nonneg _)
      _ = _ := by ring
  have hcube : (∑ d ∈ Icc 1 N, |c d| * (d : ℝ) ^ 3) ≤ ∑ p ∈ S, (p : ℝ) ^ 3 := by
    rw [← sum_subset hSI fun d hd hdS => by rw [hzero d hd hdS, abs_zero, zero_mul]]
    exact sum_le_sum fun p _ => by
      have := hc p
      have : (0 : ℝ) ≤ (p : ℝ) ^ 3 := by positivity
      nlinarith [abs_nonneg (c p)]
  have hfour : ∑ n ∈ Icc 1 N, |moebiusWindowRow Q n| / (n : ℝ) ^ 4 ≤ 1 / (Q : ℝ) ^ 3 := by
    have h := sum_Icc_abs_moebiusWindowRow_div_pow_le (N := N) (by omega : 1 ≤ Q) 4
    rwa [show (Q : ℝ) / (Q : ℝ) ^ 4 = 1 / (Q : ℝ) ^ 3 by field_simp] at h
  have hcube_le : 6 * (∑ p ∈ S, (p : ℝ) ^ 3) * (1 / (Q : ℝ) ^ 3) ≤
      6 * (Q : ℝ) ^ (-(2 * δ)) * ∑ p ∈ S, (p : ℝ) / Q := by
    suffices hsum : (∑ p ∈ S, (p : ℝ) ^ 3) * (1 / (Q : ℝ) ^ 3) ≤
        (Q : ℝ) ^ (-(2 * δ)) * ∑ p ∈ S, (p : ℝ) / Q by linarith
    rw [sum_mul, mul_sum]
    refine sum_le_sum fun p hp => ?_
    have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
    have hratio : (p : ℝ) / Q ≤ (Q : ℝ) ^ (-δ) := by
      rw [div_le_iff₀ hq0]
      calc (p : ℝ) ≤ (Q : ℝ) ^ (1 - δ) := hpQ p hp
        _ = (Q : ℝ) ^ (-δ) * Q := by
            rw [sub_eq_add_neg, add_comm, Real.rpow_add hq0, Real.rpow_one]
    have hsq : ((p : ℝ) / Q) ^ 2 ≤ (Q : ℝ) ^ (-(2 * δ)) := by
      calc ((p : ℝ) / Q) ^ 2 ≤ ((Q : ℝ) ^ (-δ)) ^ 2 :=
            pow_le_pow_left₀ (by positivity) hratio 2
        _ = (Q : ℝ) ^ (-(2 * δ)) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul hq0.le]; congr 1; push_cast; ring
    calc (p : ℝ) ^ 3 * (1 / (Q : ℝ) ^ 3) = ((p : ℝ) / Q) ^ 2 * ((p : ℝ) / Q) := by
          field_simp
      _ ≤ (Q : ℝ) ^ (-(2 * δ)) * ((p : ℝ) / Q) :=
          mul_le_mul_of_nonneg_right hsq (by positivity)
  have hdual := dualNorm_moebiusWindowRow_le_rpow hδ hδ1 hQ hS hQN
  have h6 : 6 * (∑ d ∈ Icc 1 N, |c d| * (d : ℝ) ^ 3) *
      ∑ n ∈ Icc 1 N, |moebiusWindowRow Q n| / (n : ℝ) ^ 4 ≤
        6 * (∑ p ∈ S, (p : ℝ) ^ 3) * (1 / (Q : ℝ) ^ 3) :=
    mul_le_mul (mul_le_mul_of_nonneg_left hcube (by norm_num)) hfour
      (sum_nonneg fun _ _ => by positivity) (by positivity)
  have key := abs_sub_abs_le_abs_sub (rowBilinear N c (moebiusWindowRow Q) +
    rowMean N c * vonMangoldtReadout N (moebiusWindowRow Q) +
    rowBeta N c * finiteHarmonicSum N (moebiusWindowRow Q) -
    equidistributedMain N c (moebiusWindowRow Q))
    (∑ d ∈ Icc 1 N, c d / d * kernelStatistic N (moebiusWindowRow Q) d)
  rw [add_mul]
  linarith

end

end GaloisForLFunctions.BezoutValuationIncidence
