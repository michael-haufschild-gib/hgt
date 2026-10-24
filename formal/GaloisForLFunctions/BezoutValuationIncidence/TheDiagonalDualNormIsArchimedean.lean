import GaloisForLFunctions.BezoutValuationIncidence.TheDualNormIsMinorArcBelowTheDiagonal
import GaloisForLFunctions.BezoutValuationIncidence.ReceiverBoundedInTheZeroFreeBandBelowHalfDamping

/-!
# On the diagonal the dual norm is archimedean

At a balanced modulus `d ≍ Q` the low harmonics of the spectral law are archimedean: for
`η = e(b/d)` with `b` small, `η^{jn}` turns only `O(jb)` times as `n` runs over `(Q, 2Q]`, so it is
a slowly varying weight rather than an arithmetic character. Abel summation of the twists
`S_r(w) = Σ_n (c'(n)/nʳ) wⁿ` against the long-window partial sums `C(x) = Σ_{Q<n≤x} c'(n)`,
`|C| ≤ A`, gives `‖S_r(w)‖ ≤ A (2 + Q|w - 1|)/(Q+1)ʳ`. With `|η^j - 1| ≤ j|η - 1|`, the root sums
`Σ|η - 1|^{-2} = (d² - 1)/12`, `Σ 2|η - 1|^{-1} = W_d ≤ d(1 + log d)`, `|η - 1| ≥ 4/d`, and the
harmonic series cut at `J`,

`|Λ_d(c')| ≤ A/(Q+1)² (π²(d²-1)/36 + Q W_d (1 + log J)/2) + A/(Q+1)³ π²(d²-1)(d + 2Q)/72
  + (d² - 1)/(12J) Σ|c'(n)|/n²`  (`abs_kernelStatisticAll_le_archimedean`),

at every modulus `d ≥ 1`, prime or composite. The diagonal statistic is a functional of the
long-window partial sums of the large-scale row and of nothing else; no Kloosterman sum enters.
For `c' = μ𝟙_{(Q,2Q]}` the partial sums are differences of Mertens' function, and the
de la Vallée Poussin rate gives, at every balanced modulus `Q/K ≤ d ≤ 2Q`,

`|Λ_d(μ𝟙_{(Q,2Q]})| ≤ C (d²/Q) e^{-√(log Q)/24}`  (`exists_balanced_kernelStatisticAll_moebiusWindowRow_le`).

A bound `M(x) ≪ x^{1-η}` would turn this into a power saving; conversely the law shows that on the
diagonal no estimate beyond the long-window Mertens oscillation is available to the cross-scale
form. Below the diagonal the minor-arc law gives a power saving unconditionally.
-/

open Finset Filter Topology ArithmeticFunction RHTower RHTower.Sieve
open scoped BigOperators

namespace GaloisForLFunctions.BezoutValuationIncidence

noncomputable section
set_option autoImplicit false

/-! ## §1. Abel summation with complex weights -/

/-- **Abel summation with variation.** If the partial sums of the real sequence `a` are at most
`A`, then `‖Σ_{i<n} a(i) b(i)‖ ≤ A (‖b(n-1)‖ + Σ_{i<n-1} ‖b(i+1) - b(i)‖)`. -/
theorem norm_sum_range_ofReal_mul_le_variation {a : ℕ → ℝ} {b : ℕ → ℂ} {A : ℝ} (n : ℕ)
    (hA : ∀ k ≤ n, |∑ j ∈ range k, a j| ≤ A) :
    ‖∑ i ∈ range n, (a i : ℂ) * b i‖ ≤
      A * (‖b (n - 1)‖ + ∑ i ∈ range (n - 1), ‖b (i + 1) - b i‖) := by
  have hparts := sum_range_by_parts b (fun i => (a i : ℂ)) n
  simp only [smul_eq_mul] at hparts
  have hcomm : ∑ i ∈ range n, (a i : ℂ) * b i = ∑ i ∈ range n, b i * (a i : ℂ) :=
    sum_congr rfl fun i _ => mul_comm _ _
  have hpart : ∀ k ≤ n, ‖∑ j ∈ range k, (a j : ℂ)‖ ≤ A := fun k hk => by
    rw [← Complex.ofReal_sum, Complex.norm_real, Real.norm_eq_abs]
    exact hA k hk
  rw [hcomm, hparts]
  calc _ ≤ ‖b (n - 1) * ∑ i ∈ range n, (a i : ℂ)‖ +
        ‖∑ i ∈ range (n - 1), (b (i + 1) - b i) * ∑ j ∈ range (i + 1), (a j : ℂ)‖ :=
        norm_sub_le _ _
    _ ≤ ‖b (n - 1)‖ * A + ∑ i ∈ range (n - 1), ‖b (i + 1) - b i‖ * A := by
        refine add_le_add ?_ ((norm_sum_le _ _).trans (sum_le_sum fun i hi => ?_))
        · rw [norm_mul]
          exact mul_le_mul_of_nonneg_left (hpart n le_rfl) (norm_nonneg _)
        · rw [norm_mul]
          exact mul_le_mul_of_nonneg_left (hpart _ (by have := mem_range.mp hi; omega))
            (norm_nonneg _)
    _ = _ := by rw [← sum_mul]; ring

/-- A nontrivial `d`-th root of unity is at distance at least `4/d` from `1`. -/
theorem four_div_le_norm_sub_one_of_mem_nontrivialRoots {d : ℕ} (hd : 0 < d) {η : ℂ}
    (hη : η ∈ nontrivialRoots d) : 4 / (d : ℝ) ≤ ‖η - 1‖ := by
  obtain ⟨h1, hdη⟩ := (mem_nontrivialRoots hd).mp hη
  have hnorm := norm_eq_one_of_mem_nontrivialRoots hd hη
  have ht := one_div_le_toIntDist_rootAngle_of_pow hd hnorm hdη h1
  have h4 := four_mul_toIntDist_rootAngle_le hnorm
  calc 4 / (d : ℝ) = 4 * (1 / d) := by ring
    _ ≤ 4 * toIntDist (rootAngle η) := by linarith
    _ ≤ _ := h4

/-! ## §2. Window twists against long-window partial sums -/

/-- **The archimedean twist bound.** Let `c'` live on `(Q, 2Q]` with partial sums
`|Σ_{Q<n≤Q+x} c'(n)| ≤ A` for `x ≤ Q`. For `‖w‖ = 1`, `N ≥ 2Q` and every `r`,
`‖Σ_{n ≤ N} (c'(n)/nʳ) wⁿ‖ ≤ A (2 + Q ‖w - 1‖)/(Q+1)ʳ`. -/
theorem norm_sum_window_div_pow_le_archimedean {Q N r : ℕ} (hQN : 2 * Q ≤ N) {c' : ℕ → ℝ}
    (hsupp : ∀ n, c' n ≠ 0 → Q < n ∧ n ≤ 2 * Q) {A : ℝ}
    (hA : ∀ x ≤ Q, |∑ i ∈ range x, c' (Q + 1 + i)| ≤ A) {w : ℂ} (hw : ‖w‖ = 1) :
    ‖∑ n ∈ Icc 1 N, ((c' n / (n : ℝ) ^ r : ℝ) : ℂ) * w ^ n‖ ≤
      A * (2 + Q * ‖w - 1‖) / ((Q : ℝ) + 1) ^ r := by
  have hA0 : 0 ≤ A := (abs_nonneg _).trans (hA 0 (Nat.zero_le _))
  set b : ℕ → ℂ := fun i => (((1 : ℝ) / ((Q + 1 + i : ℕ) : ℝ) ^ r : ℝ) : ℂ) * w ^ (Q + 1 + i)
  have hwin : ∑ n ∈ Icc 1 N, ((c' n / (n : ℝ) ^ r : ℝ) : ℂ) * w ^ n =
      ∑ i ∈ range Q, (c' (Q + 1 + i) : ℂ) * b i := by
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
    simp only [b]
    push_cast
    ring
  rw [hwin]
  rcases Nat.eq_zero_or_pos Q with rfl | hQ
  · simp only [range_zero, sum_empty, norm_zero]
    exact div_nonneg (mul_nonneg hA0 (by positivity)) (by positivity)
  have hq1 : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hvar := norm_sum_range_ofReal_mul_le_variation (b := b) Q hA
  refine hvar.trans ?_
  set f : ℕ → ℝ := fun i => 1 / ((Q + 1 + i : ℕ) : ℝ) ^ r
  have hf0 : ∀ i, 0 ≤ f i := fun i => by positivity
  have hfle : ∀ i, f i ≤ 1 / ((Q : ℝ) + 1) ^ r := fun i =>
    one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ (by positivity) (by push_cast; linarith) r)
  have hfanti : ∀ i, f (i + 1) ≤ f i := fun i =>
    one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ (by positivity) (by push_cast; linarith) r)
  have hnormb : ∀ i, ‖b i‖ = f i := fun i => by
    simp only [b, f, norm_mul, norm_pow, hw, one_pow, mul_one, Complex.norm_real, Real.norm_eq_abs]
    exact abs_of_nonneg (by positivity)
  have hstep : ∀ i, ‖b (i + 1) - b i‖ ≤ ‖w - 1‖ * (1 / ((Q : ℝ) + 1) ^ r) + (f i - f (i + 1)) := by
    intro i
    have e : b (i + 1) - b i = w ^ (Q + 1 + i) * (((f (i + 1) : ℝ) : ℂ) * (w - 1) +
        ((f (i + 1) - f i : ℝ) : ℂ)) := by
      simp only [b, f, show Q + 1 + (i + 1) = Q + 1 + i + 1 by ring, pow_succ]
      push_cast
      ring
    rw [e, norm_mul, norm_pow, hw, one_pow, one_mul]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hf0 _), mul_comm]
      exact mul_le_mul_of_nonneg_left (hfle _) (norm_nonneg _)
    · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith [hfanti i]), neg_sub]
  have hsum : ∑ i ∈ range (Q - 1), ‖b (i + 1) - b i‖ ≤
      Q * ‖w - 1‖ * (1 / ((Q : ℝ) + 1) ^ r) + 1 / ((Q : ℝ) + 1) ^ r := by
    calc ∑ i ∈ range (Q - 1), ‖b (i + 1) - b i‖
        ≤ ∑ i ∈ range (Q - 1), (‖w - 1‖ * (1 / ((Q : ℝ) + 1) ^ r) + (f i - f (i + 1))) :=
          sum_le_sum fun i _ => hstep i
      _ = (Q - 1 : ℕ) * (‖w - 1‖ * (1 / ((Q : ℝ) + 1) ^ r)) + (f 0 - f (Q - 1)) := by
          rw [sum_add_distrib, sum_const, card_range, nsmul_eq_mul, sum_range_sub']
      _ ≤ Q * ‖w - 1‖ * (1 / ((Q : ℝ) + 1) ^ r) + 1 / ((Q : ℝ) + 1) ^ r := by
          have hQ1 : ((Q - 1 : ℕ) : ℝ) ≤ Q := by exact_mod_cast Nat.sub_le Q 1
          have h0 : 0 ≤ ‖w - 1‖ * (1 / ((Q : ℝ) + 1) ^ r) := by positivity
          have hf00 : f 0 ≤ 1 / ((Q : ℝ) + 1) ^ r := hfle 0
          have := hf0 (Q - 1)
          nlinarith
  rw [hnormb]
  have hlast := hfle (Q - 1)
  calc A * (f (Q - 1) + ∑ i ∈ range (Q - 1), ‖b (i + 1) - b i‖)
      ≤ A * (1 / ((Q : ℝ) + 1) ^ r + (Q * ‖w - 1‖ * (1 / ((Q : ℝ) + 1) ^ r) +
          1 / ((Q : ℝ) + 1) ^ r)) := mul_le_mul_of_nonneg_left (add_le_add hlast hsum) hA0
    _ = A * (2 + Q * ‖w - 1‖) / ((Q : ℝ) + 1) ^ r := by ring

/-! ## §3. The harmonics of both kernel layers on the diagonal -/

/-- `Σ_{J ≤ j < K} 1/(j+1)² ≤ 1/J`. -/
theorem sum_Ico_one_div_succ_sq_le {J : ℕ} (hJ : 1 ≤ J) (K : ℕ) :
    ∑ j ∈ Ico J K, 1 / ((j : ℝ) + 1) ^ 2 ≤ 1 / (J : ℝ) := by
  have hJR : (0 : ℝ) < J := by exact_mod_cast hJ
  have key : ∀ M, J ≤ M → ∑ j ∈ Ico J M, 1 / ((j : ℝ) + 1) ^ 2 ≤ 1 / (J : ℝ) - 1 / (M : ℝ) := by
    intro M hM
    induction M, hM using Nat.le_induction with
    | base => simp
    | succ M hJM ih =>
      have hM0 : (0 : ℝ) < M := by exact_mod_cast (lt_of_lt_of_le hJ hJM)
      rw [sum_Ico_succ_top hJM]
      push_cast
      have h : 1 / ((M : ℝ) + 1) ^ 2 ≤ 1 / (M : ℝ) - 1 / ((M : ℝ) + 1) := by
        rw [div_sub_div _ _ hM0.ne' (by positivity), div_le_div_iff₀ (by positivity)
          (mul_pos hM0 (by linarith))]
        nlinarith
      linarith
  rcases le_or_gt K J with hKJ | hKJ
  · rw [Ico_eq_empty_of_le hKJ, sum_empty]; positivity
  have hK0 : (0 : ℝ) < K := by exact_mod_cast (lt_trans (by omega : 0 < J) hKJ)
  have h1 := key K hKJ.le
  have h2 : 0 ≤ 1 / (K : ℝ) := by positivity
  linarith

/-- **Quadratic harmonics on the diagonal.** For a row on `(Q, 2Q]` with partial sums at most `A`,
`|Σ_n (c'(n)/n²)(Φ_d(jn) - (gcd(j,d)² - 1)/12)| ≤ A/(Q+1)² ((d² - 1)/6 + j Q W_d/2)`. -/
theorem abs_quadraticHarmonic_le_archimedean {d : ℕ} (hd : 0 < d) {Q N : ℕ} (hQN : 2 * Q ≤ N)
    {c' : ℕ → ℝ} (hsupp : ∀ n, c' n ≠ 0 → Q < n ∧ n ≤ 2 * Q) {A : ℝ}
    (hA : ∀ x ≤ Q, |∑ i ∈ range x, c' (Q + 1 + i)| ≤ A) (j : ℕ) :
    |∑ n ∈ Icc 1 N, c' n / (n : ℝ) ^ 2 *
        (residuePotential d (j * n) - (((Nat.gcd j d : ℕ) : ℝ) ^ 2 - 1) / 12)| ≤
      A / ((Q : ℝ) + 1) ^ 2 * (((d : ℝ) ^ 2 - 1) / 6 + j * Q * rootHarmonicSum d / 2) := by
  have hA0 : 0 ≤ A := (abs_nonneg _).trans (hA 0 (Nat.zero_le _))
  refine (abs_sum_mul_residuePotential_sub_gcd_le_sum hd N j c').trans ?_
  have hterm : ∀ η ∈ nontrivialRoots d, (‖η - 1‖ ^ 2)⁻¹ * ‖rowTransform N c' (η ^ j)‖ ≤
      A / ((Q : ℝ) + 1) ^ 2 * (2 * (‖η - 1‖ ^ 2)⁻¹ + j * Q * (1 / ‖η - 1‖)) := by
    intro η hη
    have hη1 := norm_eq_one_of_mem_nontrivialRoots hd hη
    have hpos : 0 < ‖η - 1‖ :=
      lt_of_lt_of_le (by positivity) (four_div_le_norm_sub_one_of_mem_nontrivialRoots hd hη)
    have hne : ‖η - 1‖ ≠ 0 := hpos.ne'
    have hw : ‖η ^ j‖ = 1 := by rw [norm_pow, hη1, one_pow]
    have htw := norm_sum_window_div_pow_le_archimedean (r := 2) hQN hsupp hA hw
    have hpow := norm_pow_sub_one_le hη1 j
    calc (‖η - 1‖ ^ 2)⁻¹ * ‖rowTransform N c' (η ^ j)‖
        ≤ (‖η - 1‖ ^ 2)⁻¹ * (A * (2 + Q * (j * ‖η - 1‖)) / ((Q : ℝ) + 1) ^ 2) := by
          refine mul_le_mul_of_nonneg_left (htw.trans ?_) (by positivity)
          gcongr
      _ = A / ((Q : ℝ) + 1) ^ 2 * (2 * (‖η - 1‖ ^ 2)⁻¹ + j * Q * (1 / ‖η - 1‖)) := by
          field_simp
  refine (sum_le_sum hterm).trans (le_of_eq ?_)
  rw [← mul_sum, sum_add_distrib, ← mul_sum, ← mul_sum, sum_nontrivialRoots_inv_norm_sq hd]
  unfold rootHarmonicSum
  rw [show ∑ η ∈ nontrivialRoots d, 2 / ‖η - 1‖ = 2 * ∑ η ∈ nontrivialRoots d, 1 / ‖η - 1‖ by
    rw [mul_sum]; exact sum_congr rfl fun _ _ => by ring]
  ring

/-- **Cubic harmonics on the diagonal.**
`|Σ_n (c'(n)/n³)(2Ψ_d(jn) - Φ_d(jn))| ≤ A/(Q+1)³ (d² - 1)(d + 2jQ)/12`. -/
theorem abs_cubicHarmonic_le_archimedean {d : ℕ} (hd : 0 < d) {Q N : ℕ} (hQN : 2 * Q ≤ N)
    {c' : ℕ → ℝ} (hsupp : ∀ n, c' n ≠ 0 → Q < n ∧ n ≤ 2 * Q) {A : ℝ}
    (hA : ∀ x ≤ Q, |∑ i ∈ range x, c' (Q + 1 + i)| ≤ A) (j : ℕ) :
    |∑ n ∈ Icc 1 N, c' n / (n : ℝ) ^ 3 *
        (2 * cubicPotential d (j * n) - residuePotential d (j * n))| ≤
      A / ((Q : ℝ) + 1) ^ 3 * (((d : ℝ) ^ 2 - 1) * (d + 2 * j * Q) / 12) := by
  have hA0 : 0 ≤ A := (abs_nonneg _).trans (hA 0 (Nat.zero_le _))
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  refine (abs_sum_mul_cubicDiff_le_sum hd N j c').trans ?_
  have hterm : ∀ η ∈ nontrivialRoots d, 2 / ‖η - 1‖ ^ 3 * ‖cubicRowTransform N c' (η ^ j)‖ ≤
      A / ((Q : ℝ) + 1) ^ 3 * ((d : ℝ) * (‖η - 1‖ ^ 2)⁻¹ + 2 * j * Q * (‖η - 1‖ ^ 2)⁻¹) := by
    intro η hη
    have hη1 := norm_eq_one_of_mem_nontrivialRoots hd hη
    have h4 := four_div_le_norm_sub_one_of_mem_nontrivialRoots hd hη
    have hpos : 0 < ‖η - 1‖ := lt_of_lt_of_le (by positivity) h4
    have hinv : 1 / ‖η - 1‖ ≤ (d : ℝ) / 4 := by
      rw [div_le_div_iff₀ hpos (by norm_num)]
      rw [div_le_iff₀ hdR] at h4
      linarith
    have hw : ‖η ^ j‖ = 1 := by rw [norm_pow, hη1, one_pow]
    have htw := norm_sum_window_div_pow_le_archimedean (r := 3) hQN hsupp hA hw
    have hpow := norm_pow_sub_one_le hη1 j
    calc 2 / ‖η - 1‖ ^ 3 * ‖cubicRowTransform N c' (η ^ j)‖
        ≤ 2 / ‖η - 1‖ ^ 3 * (A * (2 + Q * (j * ‖η - 1‖)) / ((Q : ℝ) + 1) ^ 3) := by
          refine mul_le_mul_of_nonneg_left (htw.trans ?_) (by positivity)
          gcongr
      _ = A / ((Q : ℝ) + 1) ^ 3 * (4 * (1 / ‖η - 1‖) * (‖η - 1‖ ^ 2)⁻¹ +
            2 * j * Q * (‖η - 1‖ ^ 2)⁻¹) := by
          field_simp
          ring
      _ ≤ A / ((Q : ℝ) + 1) ^ 3 * ((d : ℝ) * (‖η - 1‖ ^ 2)⁻¹ + 2 * j * Q * (‖η - 1‖ ^ 2)⁻¹) := by
          gcongr
          linarith
  refine (sum_le_sum hterm).trans (le_of_eq ?_)
  rw [← mul_sum, sum_add_distrib, ← mul_sum, ← mul_sum, sum_nontrivialRoots_inv_norm_sq hd]
  ring

/-- `Σ_{j < J} 1/(j+1) ≤ 1 + log J`. -/
theorem sum_range_one_div_succ_le {J : ℕ} (hJ : 1 ≤ J) :
    ∑ j ∈ range J, 1 / ((j : ℝ) + 1) ≤ 1 + Real.log J := by
  have h : ∀ M, ∑ j ∈ range M, 1 / ((j : ℝ) + 1) = invSum M := by
    intro M
    induction M with
    | zero => simp [invSum]
    | succ M ih =>
      rw [Finset.sum_range_succ, ih, invSum, invSum, sum_Icc_succ_top (by omega : 1 ≤ M + 1)]
      push_cast
      ring
  rw [h]
  exact invSum_le_one_add_log hJ

/-! ## §4. The archimedean law for the kernel statistic -/

/-- **The diagonal dual-norm law.** For a row `c'` on `(Q, 2Q]` whose partial sums
`Σ_{Q<n≤Q+x} c'(n)`, `x ≤ Q`, are at most `A`, every modulus `d ≥ 1`, `N ≥ 2Q` and `J ≥ 1`,
`|Λ_d(c')| ≤ A/(Q+1)² (π²(d²-1)/36 + Q W_d (1 + log J)/2) + A/(Q+1)³ π²(d²-1)(d+2Q)/72
  + (d² - 1)/(12J) Σ_n |c'(n)|/n²`. -/
theorem abs_kernelStatisticAll_le_archimedean {d : ℕ} (hd : 0 < d) {Q N : ℕ} (hQN : 2 * Q ≤ N)
    {c' : ℕ → ℝ} (hsupp : ∀ n, c' n ≠ 0 → Q < n ∧ n ≤ 2 * Q) {A : ℝ}
    (hA : ∀ x ≤ Q, |∑ i ∈ range x, c' (Q + 1 + i)| ≤ A) {J : ℕ} (hJ : 1 ≤ J) :
    |kernelStatisticAll N c' d| ≤
      A / ((Q : ℝ) + 1) ^ 2 * (Real.pi ^ 2 * ((d : ℝ) ^ 2 - 1) / 36 +
          Q * rootHarmonicSum d * (1 + Real.log J) / 2) +
        A / ((Q : ℝ) + 1) ^ 3 * (Real.pi ^ 2 * ((d : ℝ) ^ 2 - 1) * (d + 2 * Q) / 72) +
        ((d : ℝ) ^ 2 - 1) / (12 * J) * ∑ n ∈ Icc 1 N, |c' n| / (n : ℝ) ^ 2 := by
  have hA0 : 0 ≤ A := (abs_nonneg _).trans (hA 0 (Nat.zero_le _))
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hd2 : (0 : ℝ) ≤ (d : ℝ) ^ 2 - 1 := by nlinarith
  have hW := rootHarmonicSum_nonneg d
  have hJR : (1 : ℝ) ≤ J := by exact_mod_cast hJ
  set T := ∑ n ∈ Icc 1 N, |c' n| / (n : ℝ) ^ 2
  have hT0 : 0 ≤ T := sum_nonneg fun _ _ => by positivity
  set a := A / ((Q : ℝ) + 1) ^ 2
  have ha0 : 0 ≤ a := by positivity
  have hz : HasSum (fun j : ℕ => 1 / ((j : ℝ) + 1) ^ 2) (Real.pi ^ 2 / 6) := by
    have := (hasSum_nat_add_iff' 1).mpr hasSum_zeta_two
    simpa using this
  -- the quadratic layer
  have hquad : |∑ n ∈ Icc 1 N, c' n / (n : ℝ) ^ 2 * (bernoulliKernel d n - kernelMean d)| ≤
      a * (Real.pi ^ 2 * ((d : ℝ) ^ 2 - 1) / 36 + Q * rootHarmonicSum d * (1 + Real.log J) / 2) +
        ((d : ℝ) ^ 2 - 1) / (12 * J) * T := by
    have ht := hasSum_sum_mul_bernoulliKernel_sub_kernelMean hd N c'
    refine le_of_tendsto' ht.tendsto_sum_nat.abs fun K => ?_
    set H : ℕ → ℝ := fun j => ∑ n ∈ Icc 1 N, c' n / (n : ℝ) ^ 2 *
      (residuePotential d (j * n) - (((Nat.gcd j d : ℕ) : ℝ) ^ 2 - 1) / 12)
    have htriv : ∀ j, |H j| ≤ ((d : ℝ) ^ 2 - 1) / 12 * T := fun j => by
      refine (abs_sum_mul_residuePotential_sub_gcd_le hd N j c').trans
        (mul_le_mul_of_nonneg_left ?_ (by positivity))
      exact rowTransformMax_le_of_forall hT0 fun ζ hζ => by
        unfold rowTransform
        refine (norm_sum_le _ _).trans (le_of_eq (sum_congr rfl fun n _ => ?_))
        rw [norm_mul, norm_pow, norm_eq_one_of_mem_nontrivialRoots hd hζ, one_pow, mul_one,
          Complex.norm_real, Real.norm_eq_abs, abs_div,
          abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) ^ 2)]
    have hbound : ∀ j, |H (j + 1) * (1 / ((j : ℝ) + 1) ^ 2)| ≤
        a * (((d : ℝ) ^ 2 - 1) / 6) * (1 / ((j : ℝ) + 1) ^ 2) +
          (if j < J then a * (Q * rootHarmonicSum d / 2) * (1 / ((j : ℝ) + 1)) else 0) +
          (if J ≤ j then ((d : ℝ) ^ 2 - 1) / 12 * T * (1 / ((j : ℝ) + 1) ^ 2) else 0) := by
      intro j
      have hj0 : (0 : ℝ) < (j : ℝ) + 1 := by positivity
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / ((j : ℝ) + 1) ^ 2)]
      by_cases hjJ : j < J
      · rw [if_pos hjJ, if_neg (by omega), add_zero]
        have h := abs_quadraticHarmonic_le_archimedean hd hQN hsupp hA (j + 1)
        calc |H (j + 1)| * (1 / ((j : ℝ) + 1) ^ 2)
            ≤ a * (((d : ℝ) ^ 2 - 1) / 6 + ((j + 1 : ℕ) : ℝ) * Q * rootHarmonicSum d / 2) *
                (1 / ((j : ℝ) + 1) ^ 2) := mul_le_mul_of_nonneg_right h (by positivity)
          _ = _ := by push_cast; field_simp
      · rw [if_neg hjJ, if_pos (by omega), add_zero]
        have h0 : 0 ≤ a * (((d : ℝ) ^ 2 - 1) / 6) * (1 / ((j : ℝ) + 1) ^ 2) := by positivity
        have := mul_le_mul_of_nonneg_right (htriv (j + 1))
          (by positivity : (0 : ℝ) ≤ 1 / ((j : ℝ) + 1) ^ 2)
        linarith
    calc |∑ j ∈ range K, H (j + 1) * (1 / ((j : ℝ) + 1) ^ 2)|
        ≤ ∑ j ∈ range K, (a * (((d : ℝ) ^ 2 - 1) / 6) * (1 / ((j : ℝ) + 1) ^ 2) +
          (if j < J then a * (Q * rootHarmonicSum d / 2) * (1 / ((j : ℝ) + 1)) else 0) +
          (if J ≤ j then ((d : ℝ) ^ 2 - 1) / 12 * T * (1 / ((j : ℝ) + 1) ^ 2) else 0)) :=
          (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun j _ => hbound j)
      _ ≤ a * (((d : ℝ) ^ 2 - 1) / 6) * (Real.pi ^ 2 / 6) +
          a * (Q * rootHarmonicSum d / 2) * (1 + Real.log J) +
          ((d : ℝ) ^ 2 - 1) / 12 * T * (1 / J) := by
          rw [sum_add_distrib, sum_add_distrib]
          gcongr
          · rw [← mul_sum]
            exact mul_le_mul_of_nonneg_left (sum_le_hasSum _ (fun j _ => by positivity) hz)
              (by positivity)
          · rw [← sum_filter]
            calc ∑ j ∈ (range K).filter (· < J), a * (Q * rootHarmonicSum d / 2) * (1 / ((j : ℝ) + 1))
                ≤ ∑ j ∈ range J, a * (Q * rootHarmonicSum d / 2) * (1 / ((j : ℝ) + 1)) :=
                  sum_le_sum_of_subset_of_nonneg (fun j hj => by
                    simp only [mem_filter, mem_range] at hj ⊢; exact hj.2) fun _ _ _ => by positivity
              _ = a * (Q * rootHarmonicSum d / 2) * ∑ j ∈ range J, 1 / ((j : ℝ) + 1) := by
                  rw [mul_sum]
              _ ≤ a * (Q * rootHarmonicSum d / 2) * (1 + Real.log J) :=
                  mul_le_mul_of_nonneg_left (sum_range_one_div_succ_le hJ) (by positivity)
          · rw [← sum_filter]
            have hfilt : (range K).filter (fun j => J ≤ j) = Ico J K := by
              ext j; simp only [mem_filter, mem_range, mem_Ico]; omega
            rw [hfilt, ← mul_sum]
            exact mul_le_mul_of_nonneg_left (sum_Ico_one_div_succ_sq_le hJ K) (by positivity)
      _ = a * (Real.pi ^ 2 * ((d : ℝ) ^ 2 - 1) / 36 + Q * rootHarmonicSum d * (1 + Real.log J) / 2) +
          ((d : ℝ) ^ 2 - 1) / (12 * J) * T := by
          have hJ0 : (J : ℝ) ≠ 0 := by positivity
          field_simp
          ring
  -- the cubic layer
  have hcub : |∑ n ∈ Icc 1 N, c' n / (n : ℝ) ^ 3 * cubicKernel d n| ≤
      A / ((Q : ℝ) + 1) ^ 3 * (Real.pi ^ 2 * ((d : ℝ) ^ 2 - 1) * (d + 2 * Q) / 72) := by
    have ht := hasSum_sum_mul_cubicKernel hd N c'
    refine le_of_tendsto' ht.tendsto_sum_nat.abs fun K => ?_
    set b := A / ((Q : ℝ) + 1) ^ 3 * (((d : ℝ) ^ 2 - 1) * (d + 2 * Q) / 12)
    have hb0 : 0 ≤ b := by positivity
    calc _ ≤ ∑ j ∈ range K, b * (1 / ((j : ℝ) + 1) ^ 2) := by
          refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun j _ => ?_)
          have hj1 : (1 : ℝ) ≤ (j : ℝ) + 1 := by have := (Nat.cast_nonneg j : (0 : ℝ) ≤ j); linarith
          rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / ((j : ℝ) + 1) ^ 3)]
          have h := abs_cubicHarmonic_le_archimedean hd hQN hsupp hA (j + 1)
          calc _ ≤ A / ((Q : ℝ) + 1) ^ 3 * (((d : ℝ) ^ 2 - 1) * (d + 2 * ((j + 1 : ℕ) : ℝ) * Q) / 12) *
                (1 / ((j : ℝ) + 1) ^ 3) := mul_le_mul_of_nonneg_right h (by positivity)
            _ = A / ((Q : ℝ) + 1) ^ 3 * (((d : ℝ) ^ 2 - 1) / 12) *
                (((d : ℝ) + 2 * ((j : ℝ) + 1) * Q) * (1 / ((j : ℝ) + 1) ^ 3)) := by push_cast; ring
            _ ≤ A / ((Q : ℝ) + 1) ^ 3 * (((d : ℝ) ^ 2 - 1) / 12) *
                (((d : ℝ) + 2 * Q) * (1 / ((j : ℝ) + 1) ^ 2)) := by
                refine mul_le_mul_of_nonneg_left ?_ (by positivity)
                rw [mul_one_div, mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
                have hd0 : (0 : ℝ) ≤ d := by linarith
                have hQ0 : (0 : ℝ) ≤ Q := Nat.cast_nonneg Q
                have h23 : ((j : ℝ) + 1) ^ 2 ≤ ((j : ℝ) + 1) ^ 3 :=
                  pow_le_pow_right₀ hj1 (by norm_num)
                nlinarith [mul_le_mul_of_nonneg_left h23 hd0]
            _ = b * (1 / ((j : ℝ) + 1) ^ 2) := by simp only [b]; ring
      _ ≤ b * (Real.pi ^ 2 / 6) := by
          rw [← mul_sum]
          exact mul_le_mul_of_nonneg_left (sum_le_hasSum _ (fun j _ => by positivity) hz) hb0
      _ = _ := by simp only [b]; ring
  rw [kernelStatisticAll, sum_add_distrib]
  calc _ ≤ |∑ n ∈ Icc 1 N, c' n / (n : ℝ) ^ 2 * (bernoulliKernel d n - kernelMean d)| +
        |∑ n ∈ Icc 1 N, c' n / (n : ℝ) ^ 3 * cubicKernel d n| := abs_add_le _ _
    _ ≤ _ := by linarith

/-! ## §5. Balanced moduli: rows whose long-window partial sums carry a zero-free-region saving -/

/-- `(2 + s)³ e^{-cs} ≤ (32 + 192/c³) e^{-cs/2}` for `s ≥ 0`, `c > 0`. -/
theorem cube_mul_exp_le {c s : ℝ} (hc : 0 < c) (hs : 0 ≤ s) :
    (2 + s) ^ 3 * Real.exp (-(c * s)) ≤ (32 + 192 / c ^ 3) * Real.exp (-(c * s / 2)) := by
  have hfac : c ^ 3 * s ^ 3 / 48 ≤ Real.exp (c * s / 2) := by
    calc c ^ 3 * s ^ 3 / 48 = (c * s / 2) ^ 3 / ((Nat.factorial 3 : ℕ) : ℝ) := by
          norm_num [Nat.factorial]; ring
      _ ≤ Real.exp (c * s / 2) := Real.pow_div_factorial_le_exp _ (by positivity) 3
  have hexp1 : 1 ≤ Real.exp (c * s / 2) := Real.one_le_exp (by positivity)
  have hc3 : 0 < c ^ 3 := by positivity
  have hcube : s ^ 3 ≤ 48 / c ^ 3 * Real.exp (c * s / 2) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hc3]
    nlinarith
  have hconv : (2 + s) ^ 3 ≤ 4 * (8 + s ^ 3) := by
    nlinarith [mul_nonneg (sq_nonneg (s - 2)) (by linarith : 0 ≤ s + 2)]
  have hP : (2 + s) ^ 3 ≤ (32 + 192 / c ^ 3) * Real.exp (c * s / 2) := by
    calc (2 + s) ^ 3 ≤ 4 * (8 + s ^ 3) := hconv
      _ ≤ 32 * Real.exp (c * s / 2) + 4 * (48 / c ^ 3 * Real.exp (c * s / 2)) := by
          linarith [hcube, hexp1]
      _ = (32 + 192 / c ^ 3) * Real.exp (c * s / 2) := by ring
  have hsplit : Real.exp (c * s / 2) * Real.exp (-(c * s)) = Real.exp (-(c * s / 2)) := by
    rw [← Real.exp_add]; congr 1; ring
  calc (2 + s) ^ 3 * Real.exp (-(c * s)) ≤
        (32 + 192 / c ^ 3) * Real.exp (c * s / 2) * Real.exp (-(c * s)) :=
        mul_le_mul_of_nonneg_right hP (Real.exp_pos _).le
    _ = (32 + 192 / c ^ 3) * Real.exp (-(c * s / 2)) := by rw [mul_assoc, hsplit]

/-- The harmonic cut `J = ⌈e^{cs/2}⌉`: `1/J ≤ e^{-cs/2}` and `1 + log J ≤ (1 + c)(2 + s)`. -/
theorem exists_harmonic_cut {c s : ℝ} (hc : 0 < c) (hs : 0 ≤ s) :
    ∃ J : ℕ, 1 ≤ J ∧ 1 / (J : ℝ) ≤ Real.exp (-(c / 2 * s)) ∧
      1 + Real.log J ≤ (1 + c) * (2 + s) := by
  have hexp1 : 1 ≤ Real.exp (c / 2 * s) := Real.one_le_exp (by positivity)
  have hge : Real.exp (c / 2 * s) ≤ (⌈Real.exp (c / 2 * s)⌉₊ : ℝ) := Nat.le_ceil _
  have hle : (⌈Real.exp (c / 2 * s)⌉₊ : ℝ) ≤ 2 * Real.exp (c / 2 * s) := by
    have := Nat.ceil_lt_add_one (by positivity : (0 : ℝ) ≤ Real.exp (c / 2 * s))
    linarith
  have hJ0 : (0 : ℝ) < ⌈Real.exp (c / 2 * s)⌉₊ := by linarith
  refine ⟨⌈Real.exp (c / 2 * s)⌉₊, by exact_mod_cast hJ0, ?_, ?_⟩
  · rw [Real.exp_neg, ← one_div]
    exact one_div_le_one_div_of_le (Real.exp_pos _) hge
  · have := Real.log_le_log hJ0 hle
    rw [Real.log_mul (by norm_num) (Real.exp_pos _).ne', Real.log_exp] at this
    have := Real.log_two_lt_d9
    nlinarith

/-- `B q/(q+1)² ≤ B/q` and `B q/(q+1)³ ≤ B/q²` for `B ≥ 0`, `q > 0`. -/
theorem div_succ_sq_le {B q : ℝ} (hB : 0 ≤ B) (hq : 0 < q) : B * q / (q + 1) ^ 2 ≤ B / q := by
  rw [div_le_div_iff₀ (by positivity) hq]
  nlinarith [mul_nonneg hB (by linarith : (0 : ℝ) ≤ 2 * q + 1)]

theorem div_succ_cube_le {B q : ℝ} (hB : 0 ≤ B) (hq : 0 < q) : B * q / (q + 1) ^ 3 ≤ B / q ^ 2 := by
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_nonneg hB (by positivity : (0 : ℝ) ≤ 3 * q ^ 2 + 3 * q + 1)]

/-- The quadratic layer of the archimedean law at a balanced modulus. -/
theorem balanced_square_layer_le {B₀ q E d W L K c s : ℝ} (hB₀ : 0 ≤ B₀) (hq : 0 < q)
    (hE : 0 ≤ E) (hd1 : 1 ≤ d) (hW0 : 0 ≤ W) (hL0 : 0 ≤ L) (hc : 0 ≤ c) (hs : 0 ≤ s)
    (hWL : W * L ≤ d * ((1 + c) * (2 + s) ^ 3)) (hdK : d ≤ K * (d ^ 2 / q)) :
    B₀ * q * E / (q + 1) ^ 2 * (Real.pi ^ 2 * (d ^ 2 - 1) / 36 + q * W * L / 2) ≤
      Real.pi ^ 2 * B₀ / 36 * (d ^ 2 / q * E) +
        B₀ * K * (1 + c) / 2 * ((2 + s) ^ 3 * E * (d ^ 2 / q)) := by
  have h1 : B₀ * q * E / (q + 1) ^ 2 ≤ B₀ * E / q := by
    have := div_succ_sq_le (mul_nonneg hB₀ hE) hq
    rwa [show B₀ * E * q = B₀ * q * E by ring] at this
  have hd21 : 0 ≤ d ^ 2 - 1 := by nlinarith
  have h2 : 0 ≤ Real.pi ^ 2 * (d ^ 2 - 1) / 36 + q * W * L / 2 := by positivity
  have hM : 0 ≤ (1 + c) * (2 + s) ^ 3 := by positivity
  calc B₀ * q * E / (q + 1) ^ 2 * (Real.pi ^ 2 * (d ^ 2 - 1) / 36 + q * W * L / 2)
      ≤ B₀ * E / q * (Real.pi ^ 2 * (d ^ 2 - 1) / 36 + q * W * L / 2) :=
        mul_le_mul_of_nonneg_right h1 h2
    _ = Real.pi ^ 2 * B₀ / 36 * ((d ^ 2 - 1) / q * E) + B₀ * E * (W * L) / 2 := by
        field_simp
    _ ≤ Real.pi ^ 2 * B₀ / 36 * (d ^ 2 / q * E) +
          B₀ * E * (K * (d ^ 2 / q) * ((1 + c) * (2 + s) ^ 3)) / 2 :=
        add_le_add (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
          (div_le_div_of_nonneg_right (by linarith) hq.le) hE) (by positivity))
          (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
            (hWL.trans (mul_le_mul_of_nonneg_right hdK hM)) (mul_nonneg hB₀ hE)) (by norm_num))
    _ = _ := by ring

/-- The cubic layer of the archimedean law at a balanced modulus. -/
theorem balanced_cubic_layer_le {B₀ q E d : ℝ} (hB₀ : 0 ≤ B₀) (hq : 0 < q) (hE : 0 ≤ E)
    (hd1 : 1 ≤ d) (hd2 : d ≤ 2 * q) :
    B₀ * q * E / (q + 1) ^ 3 * (Real.pi ^ 2 * (d ^ 2 - 1) * (d + 2 * q) / 72) ≤
      Real.pi ^ 2 * B₀ / 18 * (d ^ 2 / q * E) := by
  have h1 : B₀ * q * E / (q + 1) ^ 3 ≤ B₀ * E / q ^ 2 := by
    have := div_succ_cube_le (mul_nonneg hB₀ hE) hq
    rwa [show B₀ * E * q = B₀ * q * E by ring] at this
  have hd21 : 0 ≤ d ^ 2 - 1 := by nlinarith
  have hpoly : (d ^ 2 - 1) * (d + 2 * q) ≤ d ^ 2 * (4 * q) :=
    calc (d ^ 2 - 1) * (d + 2 * q) ≤ d ^ 2 * (d + 2 * q) :=
          mul_le_mul_of_nonneg_right (by linarith) (by linarith)
      _ ≤ d ^ 2 * (4 * q) := mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg d)
  have h2 : Real.pi ^ 2 * (d ^ 2 - 1) * (d + 2 * q) / 72 ≤ Real.pi ^ 2 * d ^ 2 * (4 * q) / 72 := by
    have := mul_le_mul_of_nonneg_left hpoly (sq_nonneg Real.pi)
    linarith
  have h20 : 0 ≤ Real.pi ^ 2 * (d ^ 2 - 1) * (d + 2 * q) / 72 := by
    have : 0 ≤ d + 2 * q := by linarith
    positivity
  calc B₀ * q * E / (q + 1) ^ 3 * (Real.pi ^ 2 * (d ^ 2 - 1) * (d + 2 * q) / 72)
      ≤ B₀ * E / q ^ 2 * (Real.pi ^ 2 * d ^ 2 * (4 * q) / 72) :=
        mul_le_mul h1 h2 h20 (by positivity)
    _ = Real.pi ^ 2 * B₀ / 18 * (d ^ 2 / q * E) := by
        field_simp; ring

/-- The harmonic tail of the archimedean law at a balanced modulus. -/
theorem balanced_tail_le {d J T T₀ q F : ℝ} (hd1 : 1 ≤ d) (hJ : 0 < J) (hT0 : 0 ≤ T)
    (hT₀ : 0 ≤ T₀) (hT : T ≤ T₀ / q) (hq : 0 < q) (hJF : 1 / J ≤ F) :
    (d ^ 2 - 1) / (12 * J) * T ≤ T₀ / 12 * (d ^ 2 / q * F) := by
  calc (d ^ 2 - 1) / (12 * J) * T ≤ d ^ 2 / (12 * J) * (T₀ / q) :=
        mul_le_mul (div_le_div_of_nonneg_right (by linarith) (by positivity)) hT hT0
          (by positivity)
    _ = T₀ / 12 * (d ^ 2 / q * (1 / J)) := by
        field_simp
    _ ≤ T₀ / 12 * (d ^ 2 / q * F) := by gcongr

/-- **The balanced dual-norm law.** Let `c > 0`, `K ≥ 1`, `B₀, T₀ ≥ 0`. There is `C ≥ 0` such that
for every `Q ≥ 1` and every row `c'` on `(Q, 2Q]` with long-window partial sums at most
`B₀ Q e^{-c√(log Q)}` and `Σ |c'(n)|/n² ≤ T₀/Q`, every modulus `d` with `Q ≤ K d`, `d ≤ 2Q` and
every `N ≥ 2Q`, `|Λ_d(c')| ≤ C (d²/Q) e^{-(c/2)√(log Q)}`. -/
theorem exists_balanced_kernelStatisticAll_le {c K B₀ T₀ : ℝ} (hc : 0 < c) (hK : 1 ≤ K)
    (hB₀ : 0 ≤ B₀) (hT₀ : 0 ≤ T₀) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ Q : ℕ, 1 ≤ Q → ∀ c' : ℕ → ℝ, (∀ n, c' n ≠ 0 → Q < n ∧ n ≤ 2 * Q) →
      (∀ x ≤ Q, |∑ i ∈ range x, c' (Q + 1 + i)| ≤
        B₀ * Q * Real.exp (-(c * Real.sqrt (Real.log Q)))) →
      ∀ N, 2 * Q ≤ N → ∑ n ∈ Icc 1 N, |c' n| / (n : ℝ) ^ 2 ≤ T₀ / Q →
      ∀ d : ℕ, 1 ≤ d → (Q : ℝ) ≤ K * d → d ≤ 2 * Q →
        |kernelStatisticAll N c' d| ≤
          C * ((d : ℝ) ^ 2 / Q) * Real.exp (-(c / 2 * Real.sqrt (Real.log Q))) := by
  have hP0 : (0 : ℝ) ≤ 32 + 192 / c ^ 3 := by positivity
  have hK0 : (0 : ℝ) ≤ K := by linarith
  refine ⟨Real.pi ^ 2 * B₀ / 12 + B₀ * K * (1 + c) * (32 + 192 / c ^ 3) / 2 + T₀ / 12,
    by positivity, fun Q hQ1 c' hsupp hA N hQN hT d hd hQd hd2 => ?_⟩
  have hq1 : (1 : ℝ) ≤ Q := by exact_mod_cast hQ1
  have hq0 : (0 : ℝ) < Q := by linarith
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hd2R : (d : ℝ) ≤ 2 * Q := by exact_mod_cast hd2
  set s := Real.sqrt (Real.log Q)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hlogQ : Real.log Q = s ^ 2 := (Real.sq_sqrt (Real.log_nonneg hq1)).symm
  obtain ⟨J, hJ1, hJF, hlogJ⟩ := exists_harmonic_cut hc hs0
  have hJ0 : (0 : ℝ) < J := by exact_mod_cast hJ1
  have hlogJ0 : 0 ≤ 1 + Real.log J := by
    have := Real.log_nonneg (by exact_mod_cast hJ1 : (1 : ℝ) ≤ J); linarith
  have hlaw := abs_kernelStatisticAll_le_archimedean (by omega : 0 < d) hQN hsupp hA hJ1
  have hW : rootHarmonicSum d ≤ d * (2 + s) ^ 2 := by
    refine (rootHarmonicSum_le d).trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    have : Real.log d ≤ Real.log (2 * Q) := Real.log_le_log (by positivity) hd2R
    rw [Real.log_mul (by norm_num) hq0.ne', hlogQ] at this
    have := Real.log_two_lt_d9
    nlinarith
  have hWnn := rootHarmonicSum_nonneg d
  have hWL : rootHarmonicSum d * (1 + Real.log J) ≤ d * ((1 + c) * (2 + s) ^ 3) :=
    calc rootHarmonicSum d * (1 + Real.log J) ≤ (d * (2 + s) ^ 2) * ((1 + c) * (2 + s)) :=
          mul_le_mul hW hlogJ hlogJ0 (by positivity)
      _ = d * ((1 + c) * (2 + s) ^ 3) := by ring
  have hdK : (d : ℝ) ≤ K * ((d : ℝ) ^ 2 / Q) := by
    rw [mul_div_assoc', le_div_iff₀ hq0]
    nlinarith [mul_le_mul_of_nonneg_left hQd (by linarith : (0 : ℝ) ≤ d)]
  have hE0 : 0 ≤ Real.exp (-(c * s)) := (Real.exp_pos _).le
  have hTnn : 0 ≤ ∑ n ∈ Icc 1 N, |c' n| / (n : ℝ) ^ 2 := sum_nonneg fun _ _ => by positivity
  have h12 := balanced_square_layer_le (W := rootHarmonicSum d) (L := 1 + Real.log J) hB₀ hq0
    hE0 hdR hWnn hlogJ0 hc.le hs0 hWL hdK
  have h3 := balanced_cubic_layer_le hB₀ hq0 hE0 hdR hd2R
  have h4 := balanced_tail_le hdR hJ0 hTnn hT₀ hT hq0 hJF
  -- the zero-free-region factor: `E ≤ F` and `(2 + s)³ E ≤ (32 + 192/c³) F`
  set D := (d : ℝ) ^ 2 / Q
  have hD0 : 0 ≤ D := div_nonneg (sq_nonneg _) hq0.le
  have hEF : Real.exp (-(c * s)) ≤ Real.exp (-(c / 2 * s)) :=
    Real.exp_le_exp.mpr (by nlinarith [mul_nonneg hc.le hs0])
  have hDE := mul_le_mul_of_nonneg_left hEF hD0
  have hcubeD : (2 + s) ^ 3 * Real.exp (-(c * s)) * D ≤
      (32 + 192 / c ^ 3) * (D * Real.exp (-(c / 2 * s))) := by
    have hcube := cube_mul_exp_le hc hs0
    rw [show c * s / 2 = c / 2 * s by ring] at hcube
    have := mul_le_mul_of_nonneg_right hcube hD0
    linarith
  have hB1 : 0 ≤ Real.pi ^ 2 * B₀ := by positivity
  have hB2 : 0 ≤ B₀ * K * (1 + c) / 2 := by positivity
  calc |kernelStatisticAll N c' d| ≤ _ := hlaw
    _ ≤ Real.pi ^ 2 * B₀ / 36 * (D * Real.exp (-(c * s))) +
          B₀ * K * (1 + c) / 2 * ((2 + s) ^ 3 * Real.exp (-(c * s)) * D) +
          Real.pi ^ 2 * B₀ / 18 * (D * Real.exp (-(c * s))) +
          T₀ / 12 * (D * Real.exp (-(c / 2 * s))) := by linarith
    _ ≤ (Real.pi ^ 2 * B₀ / 12 + B₀ * K * (1 + c) * (32 + 192 / c ^ 3) / 2 + T₀ / 12) *
          (D * Real.exp (-(c / 2 * s))) := by
        linarith [mul_le_mul_of_nonneg_left hcubeD hB2, mul_le_mul_of_nonneg_left hDE hB1]
    _ = _ := by ring

/-! ## §6. The Möbius row on the diagonal -/

theorem moebiusWindowRow_ne_zero_imp {Q n : ℕ} (h : moebiusWindowRow Q n ≠ 0) :
    Q < n ∧ n ≤ 2 * Q := by
  unfold moebiusWindowRow at h
  split_ifs at h with hn
  · exact hn
  · exact absurd rfl h

/-- The partial sums of the Möbius window are differences of Mertens' function. -/
theorem sum_range_moebiusWindowRow (Q x : ℕ) (hx : x ≤ Q) :
    ∑ i ∈ range x, moebiusWindowRow Q (Q + 1 + i) =
      ∑ e ∈ Icc 1 (Q + x), moebiusReal e - ∑ e ∈ Icc 1 Q, moebiusReal e := by
  induction x with
  | zero => simp
  | succ x ih =>
    rw [Finset.sum_range_succ, ih (by omega), show Q + (x + 1) = Q + x + 1 by ring,
      sum_Icc_succ_top (by omega : 1 ≤ Q + x + 1), moebiusWindowRow, if_pos (by omega),
      show Q + 1 + x = Q + x + 1 by ring]
    ring

/-- **The balanced dual-norm law for the Möbius row.** For every `K ≥ 1` there are `C ≥ 0` and
`Q₀` such that for `Q ≥ Q₀`, every modulus `d` (prime or composite) with `Q ≤ K d`, `d ≤ 2Q` and
every `N ≥ 2Q`, `|Λ_d(μ𝟙_{(Q,2Q]})| ≤ C (d²/Q) e^{-√(log Q)/24}`: the de la Vallée Poussin saving of
the long-window Mertens oscillation. -/
theorem exists_balanced_kernelStatisticAll_moebiusWindowRow_le {K : ℝ} (hK : 1 ≤ K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ Q₀ : ℕ, ∀ Q, Q₀ ≤ Q → ∀ d : ℕ, 1 ≤ d → (Q : ℝ) ≤ K * d →
      d ≤ 2 * Q → ∀ N, 2 * Q ≤ N →
        |kernelStatisticAll N (moebiusWindowRow Q) d| ≤
          C * ((d : ℝ) ^ 2 / Q) * Real.exp (-(Real.sqrt (Real.log Q) / 24)) := by
  obtain ⟨B, hB0, N₀, hM⟩ := exists_abs_sum_moebiusReal_le_sqrtLog
  obtain ⟨C, hC0, hlaw⟩ := exists_balanced_kernelStatisticAll_le (c := 1 / 12) (by norm_num) hK
    (by positivity : (0 : ℝ) ≤ 3 * B) zero_le_one
  refine ⟨C, hC0, max N₀ 1, fun Q hQ d hd hQd hd2 N hQN => ?_⟩
  have hQ1 : 1 ≤ Q := le_of_max_le_right hQ
  have hQN₀ : N₀ ≤ Q := le_of_max_le_left hQ
  have hq1 : (1 : ℝ) ≤ Q := by exact_mod_cast hQ1
  have hq0 : (0 : ℝ) < Q := by linarith
  have hA : ∀ x ≤ Q, |∑ i ∈ range x, moebiusWindowRow Q (Q + 1 + i)| ≤
      3 * B * Q * Real.exp (-(1 / 12 * Real.sqrt (Real.log Q))) := by
    intro x hx
    rw [sum_range_moebiusWindowRow Q x hx]
    have h1 := hM (Q + x) (by omega)
    have h2 := hM Q hQN₀
    have hE : Real.exp (-(Real.sqrt (Real.log Q) / 12)) =
        Real.exp (-(1 / 12 * Real.sqrt (Real.log Q))) := by congr 1; ring
    have hmono : Real.exp (-(Real.sqrt (Real.log ((Q + x : ℕ) : ℝ)) / 12)) ≤
        Real.exp (-(1 / 12 * Real.sqrt (Real.log Q))) := by
      apply Real.exp_le_exp.mpr
      have : Real.sqrt (Real.log Q) ≤ Real.sqrt (Real.log ((Q + x : ℕ) : ℝ)) :=
        Real.sqrt_le_sqrt (Real.log_le_log hq0 (by push_cast; linarith [(Nat.cast_nonneg x : (0 : ℝ) ≤ x)]))
      linarith
    have hQx : ((Q + x : ℕ) : ℝ) ≤ 2 * Q := by
      push_cast; have : (x : ℝ) ≤ Q := (by exact_mod_cast hx); linarith
    rw [hE] at h2
    calc |∑ e ∈ Icc 1 (Q + x), moebiusReal e - ∑ e ∈ Icc 1 Q, moebiusReal e|
        ≤ |∑ e ∈ Icc 1 (Q + x), moebiusReal e| + |∑ e ∈ Icc 1 Q, moebiusReal e| := abs_sub _ _
      _ ≤ B * ((Q + x : ℕ) : ℝ) * Real.exp (-(Real.sqrt (Real.log ((Q + x : ℕ) : ℝ)) / 12)) +
          B * Q * Real.exp (-(1 / 12 * Real.sqrt (Real.log Q))) := add_le_add h1 h2
      _ ≤ B * (2 * Q) * Real.exp (-(1 / 12 * Real.sqrt (Real.log Q))) +
          B * Q * Real.exp (-(1 / 12 * Real.sqrt (Real.log Q))) := by gcongr
      _ = 3 * B * Q * Real.exp (-(1 / 12 * Real.sqrt (Real.log Q))) := by ring
  have hT : ∑ n ∈ Icc 1 N, |moebiusWindowRow Q n| / (n : ℝ) ^ 2 ≤ 1 / Q := by
    have h := sum_Icc_abs_moebiusWindowRow_div_pow_le (N := N) hQ1 2
    rwa [show (Q : ℝ) / (Q : ℝ) ^ 2 = 1 / Q by field_simp] at h
  have h := hlaw Q hQ1 _ (fun n h => moebiusWindowRow_ne_zero_imp h) hA N hQN hT d hd hQd hd2
  rwa [show -(1 / 12 / 2 * Real.sqrt (Real.log Q)) = -(Real.sqrt (Real.log Q) / 24) by ring] at h

end

end GaloisForLFunctions.BezoutValuationIncidence
