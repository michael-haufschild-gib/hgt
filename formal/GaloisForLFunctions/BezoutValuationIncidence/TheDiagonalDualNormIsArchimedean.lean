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

open Finset Filter Topology ArithmeticFunction RHTower.Sieve
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

/-- `‖η^j - 1‖ ≤ j ‖η - 1‖` on the unit circle. -/
theorem norm_pow_sub_one_le {η : ℂ} (hη : ‖η‖ = 1) (j : ℕ) : ‖η ^ j - 1‖ ≤ j * ‖η - 1‖ := by
  induction j with
  | zero => simp
  | succ j ih =>
    have e : η ^ (j + 1) - 1 = η * (η ^ j - 1) + (η - 1) := by ring
    rw [e]
    push_cast
    calc ‖η * (η ^ j - 1) + (η - 1)‖ ≤ ‖η * (η ^ j - 1)‖ + ‖η - 1‖ := norm_add_le _ _
      _ = ‖η ^ j - 1‖ + ‖η - 1‖ := by rw [norm_mul, hη, one_mul]
      _ ≤ j * ‖η - 1‖ + ‖η - 1‖ := by linarith
      _ = ((j : ℝ) + 1) * ‖η - 1‖ := by ring

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
    positivity
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
          1 / ((Q : ℝ) + 1) ^ r)) := by gcongr
    _ = A * (2 + Q * ‖w - 1‖) / ((Q : ℝ) + 1) ^ r := by ring

/-! ## §3. The harmonics of both kernel layers on the diagonal -/

/-- `Σ_{J ≤ j < K} 1/(j+1)² ≤ 1/J`. -/
theorem sum_Ico_one_div_succ_sq_le {J : ℕ} (hJ : 1 ≤ J) (K : ℕ) :
    ∑ j ∈ Ico J K, 1 / ((j : ℝ) + 1) ^ 2 ≤ 1 / J := by
  have hJR : (0 : ℝ) < J := by exact_mod_cast hJ
  rcases le_or_gt K J with hKJ | hKJ
  · rw [Ico_eq_empty_of_le hKJ, sum_empty]; positivity
  have key : ∀ K, J ≤ K → ∑ j ∈ Ico J K, 1 / ((j : ℝ) + 1) ^ 2 ≤ 1 / J - 1 / K := by
    intro K hK
    induction K, hK using Nat.le_induction with
    | base => simp
    | succ K hJK ih =>
      have hK0 : (0 : ℝ) < K := by exact_mod_cast (lt_of_lt_of_le hJ hJK)
      rw [sum_Ico_succ_top hJK, Nat.cast_succ]
      have h : 1 / ((K : ℝ) + 1) ^ 2 ≤ 1 / K - 1 / ((K : ℝ) + 1) := by
        rw [div_sub_div _ _ hK0.ne' (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
      linarith
  have hK0 : (0 : ℝ) < K := by exact_mod_cast (lt_trans (by omega : 0 < J) hKJ)
  have := key K hKJ.le
  have : 0 ≤ 1 / (K : ℝ) := by positivity
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
      exact rowTransformMax_le_of_forall hT0 fun ζ _ => by
        refine (norm_sum_le _ _).trans (le_of_eq (sum_congr rfl fun n _ => ?_))
        rw [norm_mul, norm_pow, norm_eq_one_of_mem_nontrivialRoots hd ‹_›, one_pow, mul_one,
          Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) ^ 2)]
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
          _ = _ := by push_cast; field_simp; ring
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
              _ = a * (Q * rootHarmonicSum d / 2) * (harmonic J : ℝ) := by
                  rw [← mul_sum, harmonic_eq_sum_Icc]
                  push_cast
                  congr 1
                  rw [← Nat.Ico_succ_right, sum_Ico_eq_sum_range, Nat.add_sub_cancel]
                  refine sum_congr rfl fun j _ => ?_
                  rw [add_comm 1 j]; push_cast; ring
              _ ≤ a * (Q * rootHarmonicSum d / 2) * (1 + Real.log J) :=
                  mul_le_mul_of_nonneg_left (harmonic_le_one_add_log J) (by positivity)
          · rw [← sum_filter]
            have hfilt : (range K).filter (fun j => J ≤ j) = Ico J K := by
              ext j; simp only [mem_filter, mem_range, mem_Ico]; omega
            rw [hfilt, ← mul_sum]
            exact mul_le_mul_of_nonneg_left (sum_Ico_one_div_succ_sq_le hJ K) (by positivity)
      _ = a * (Real.pi ^ 2 * ((d : ℝ) ^ 2 - 1) / 36 + Q * rootHarmonicSum d * (1 + Real.log J) / 2) +
          ((d : ℝ) ^ 2 - 1) / (12 * J) * T := by
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
            _ ≤ b * (1 / ((j : ℝ) + 1) ^ 2) := by
                simp only [b]
                push_cast
                rw [div_mul_div_comm, div_mul_div_comm, mul_one, mul_one]
                rw [div_le_div_iff₀ (by positivity) (by positivity)]
                have hQ0 : (0 : ℝ) ≤ Q := Nat.cast_nonneg Q
                have hX : 0 ≤ A * ((d : ℝ) ^ 2 - 1) := by positivity
                have hdd : (d : ℝ) + 2 * ((j : ℝ) + 1) * Q ≤ ((d : ℝ) + 2 * Q) * ((j : ℝ) + 1) := by
                  nlinarith
                have hY : (0 : ℝ) ≤ ((Q : ℝ) + 1) ^ 3 * ((j : ℝ) + 1) ^ 2 * 12 := by positivity
                calc A * (((d : ℝ) ^ 2 - 1) * ((d : ℝ) + 2 * ((j : ℝ) + 1) * Q)) *
                      (((Q : ℝ) + 1) ^ 3 * 12 * ((j : ℝ) + 1) ^ 2)
                    ≤ A * (((d : ℝ) ^ 2 - 1) * (((d : ℝ) + 2 * Q) * ((j : ℝ) + 1))) *
                      (((Q : ℝ) + 1) ^ 3 * 12 * ((j : ℝ) + 1) ^ 2) := by gcongr
                  _ = A * (((d : ℝ) ^ 2 - 1) * ((d : ℝ) + 2 * Q)) *
                      (((Q : ℝ) + 1) ^ 3 * 12 * ((j : ℝ) + 1) ^ 3) := by ring
      _ ≤ b * (Real.pi ^ 2 / 6) := by
          rw [← mul_sum]
          exact mul_le_mul_of_nonneg_left (sum_le_hasSum _ (fun j _ => by positivity) hz) hb0
      _ = _ := by simp only [b]; ring
  rw [kernelStatisticAll, sum_add_distrib]
  calc _ ≤ |∑ n ∈ Icc 1 N, c' n / (n : ℝ) ^ 2 * (bernoulliKernel d n - kernelMean d)| +
        |∑ n ∈ Icc 1 N, c' n / (n : ℝ) ^ 3 * cubicKernel d n| := abs_add_le _ _
    _ ≤ _ := by linarith

end

end GaloisForLFunctions.BezoutValuationIncidence
