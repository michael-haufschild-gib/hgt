import GaloisForLFunctions.BezoutValuationIncidence.FourierFormOfTheBernoulliKernelAndTheExactCrossScaleLoss

/-!
# Block equidistribution suffices for cross-scale dispersion

Split the window `[A, A + KH)` of a large-scale row `c'` into `K` blocks of length `H` and put

`Δ_H(c') = Σ_m |Σ_{n ∈ [A + mH, A + (m+1)H)} c'(n)/n²|`,  `S₀ = Σ_n |c'(n)|/n²`.

Comparing `ζⁿ` with its value at the left end of each block (`|ζ^t - 1| ≤ t |ζ - 1|`) gives, on the
unit circle,

`|Σ_n (c'(n)/n²) ζⁿ| ≤ Δ_H + H |ζ - 1| S₀`.

In the Fourier form `Σ_n (c'(n)/n²) Φ_d(jn) = Σ_{η ∈ T_d} |η - 1|^{-2} S(η^j)` the Lipschitz term
costs `j |η - 1|^{-1}`. The separated-family row sum of the circle (`circle_row_sum_le`) gives
`Σ_{η ∈ T_d} |η - 1|^{-1} ≤ (d/2) h_d`, `h_m = Σ_{k ≤ m} 1/k`. Truncating the `j`-sum at `j < d`, with
the trivial bound `|Φ_d| ≤ d²/8` beyond, gives for every modulus `d`

`|Σ_n c'(n) 𝔅(d, n)/n²| ≤ (π²/72)(d² - 1) Δ_H + (d/2) H h_d² S₀ + d S₀/8`,

and for every row `c` (all moduli, no support hypothesis)

`|B + m R' + β H'| ≤ (π²/72) Δ_H Σ_d |c(d)| d + (H h_N²/2 + 1/8) S₀ Σ_d |c(d)|
  + ¾ Σ_d |c(d)| d² Σ_n |c'(n)|/n³`.

Against the rank-two remainder bound `S₀ Σ_d |c(d)| d` the gain is
`Δ_H/S₀ + H log² N / P + P/Q` for `c` on `[P, 2P]` and `c'` above `Q`. Equidistribution of `c'/n²` in
blocks of length `H = o(P/log² P)` makes the cross-scale remainder negligible. A nonnegative `c'` on
one window of length `P/64` keeps it at the rank-two size. The replacement hypothesis of the
Type-II no-go is therefore exactly block equidistribution at the scale of the small moduli.
-/

open Finset Filter Topology Complex RHTower RHTower.Sieve GaloisForLFunctions.BiScaleUncertainty
open scoped BigOperators ComplexConjugate

namespace GaloisForLFunctions.BezoutValuationIncidence

noncomputable section
set_option autoImplicit false

/-! ## §1. Block Abel summation -/

theorem norm_pow_sub_one_le {ζ : ℂ} (hζ : ‖ζ‖ = 1) (t : ℕ) : ‖ζ ^ t - 1‖ ≤ t * ‖ζ - 1‖ := by
  induction t with
  | zero => simp
  | succ t ih =>
    have h : ζ ^ (t + 1) - 1 = ζ * (ζ ^ t - 1) + (ζ - 1) := by ring
    rw [h]
    calc ‖ζ * (ζ ^ t - 1) + (ζ - 1)‖ ≤ ‖ζ * (ζ ^ t - 1)‖ + ‖ζ - 1‖ := norm_add_le _ _
      _ = ‖ζ ^ t - 1‖ + ‖ζ - 1‖ := by rw [norm_mul, hζ, one_mul]
      _ ≤ t * ‖ζ - 1‖ + ‖ζ - 1‖ := by linarith
      _ = ((t + 1 : ℕ) : ℝ) * ‖ζ - 1‖ := by push_cast; ring

/-- The block discrepancy `Δ_H` of a large-scale row on `[A, A + KH)`. -/
def blockDiscrepancy (c' : ℕ → ℝ) (A H K : ℕ) : ℝ :=
  ∑ m ∈ range K, |∑ n ∈ Ico (A + m * H) (A + m * H + H), c' n / (n : ℝ) ^ 2|

/-- One block: `|Σ_{a ≤ n < a+H} xₙ ζⁿ| ≤ |Σ xₙ| + H |ζ - 1| Σ |xₙ|`. -/
theorem norm_sum_Ico_block_le (x : ℕ → ℝ) (a H : ℕ) {ζ : ℂ} (hζ : ‖ζ‖ = 1) :
    ‖∑ n ∈ Ico a (a + H), (x n : ℂ) * ζ ^ n‖ ≤
      |∑ n ∈ Ico a (a + H), x n| + H * ‖ζ - 1‖ * ∑ n ∈ Ico a (a + H), |x n| := by
  have hsplit : ∑ n ∈ Ico a (a + H), (x n : ℂ) * ζ ^ n =
      ζ ^ a * ((∑ n ∈ Ico a (a + H), x n : ℝ) : ℂ) +
        ∑ n ∈ Ico a (a + H), (x n : ℂ) * (ζ ^ n - ζ ^ a) := by
    push_cast
    rw [mul_sum, ← sum_add_distrib]
    exact sum_congr rfl fun n _ => by ring
  rw [hsplit]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [norm_mul, norm_pow, hζ, one_pow, one_mul, Complex.norm_real, Real.norm_eq_abs]
  · refine (norm_sum_le _ _).trans ?_
    rw [mul_sum]
    refine sum_le_sum fun n hn => ?_
    have hn' := mem_Ico.mp hn
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hpow : ζ ^ n - ζ ^ a = ζ ^ a * (ζ ^ (n - a) - 1) := by
      rw [mul_sub, ← pow_add, Nat.add_sub_cancel' hn'.1, mul_one]
    rw [hpow, norm_mul, norm_pow, hζ, one_pow, one_mul]
    have h1 := norm_pow_sub_one_le hζ (n - a)
    have h2 : ((n - a : ℕ) : ℝ) ≤ H := by exact_mod_cast (by omega : n - a ≤ H)
    calc |x n| * ‖ζ ^ (n - a) - 1‖ ≤ |x n| * (H * ‖ζ - 1‖) :=
          mul_le_mul_of_nonneg_left (h1.trans (mul_le_mul_of_nonneg_right h2 (norm_nonneg _)))
            (abs_nonneg _)
      _ = H * ‖ζ - 1‖ * |x n| := by ring

/-- All blocks: `|Σ_{A ≤ n < A+KH} xₙ ζⁿ| ≤ Σ_m |Σ_{block m} xₙ| + H |ζ - 1| Σ |xₙ|`. -/
theorem norm_sum_Ico_blocks_le (x : ℕ → ℝ) (A H K : ℕ) {ζ : ℂ} (hζ : ‖ζ‖ = 1) :
    ‖∑ n ∈ Ico A (A + K * H), (x n : ℂ) * ζ ^ n‖ ≤
      ∑ m ∈ range K, |∑ n ∈ Ico (A + m * H) (A + m * H + H), x n| +
        H * ‖ζ - 1‖ * ∑ n ∈ Ico A (A + K * H), |x n| := by
  induction K with
  | zero => simp
  | succ K ih =>
    have hK : A + (K + 1) * H = A + K * H + H := by ring
    rw [hK, ← sum_Ico_consecutive _ (by omega : A ≤ A + K * H) (by omega : A + K * H ≤ A + K * H + H),
      ← sum_Ico_consecutive (fun n => |x n|) (by omega : A ≤ A + K * H)
        (by omega : A + K * H ≤ A + K * H + H), Finset.sum_range_succ]
    have hb := norm_sum_Ico_block_le x (A + K * H) H hζ
    calc ‖∑ n ∈ Ico A (A + K * H), (x n : ℂ) * ζ ^ n +
          ∑ n ∈ Ico (A + K * H) (A + K * H + H), (x n : ℂ) * ζ ^ n‖
        ≤ ‖∑ n ∈ Ico A (A + K * H), (x n : ℂ) * ζ ^ n‖ +
            ‖∑ n ∈ Ico (A + K * H) (A + K * H + H), (x n : ℂ) * ζ ^ n‖ := norm_add_le _ _
      _ ≤ _ := add_le_add ih hb
      _ = _ := by ring

/-! ## §2. The first-power Farey sum -/

/-- `Σ_{η ∈ T_d} |η - 1|^{-1} ≤ (d/2) h_d`. -/
theorem sum_nontrivialRoots_inv_norm_le {d : ℕ} (hd : 0 < d) :
    ∑ η ∈ nontrivialRoots d, 1 / ‖η - 1‖ ≤ (d : ℝ) / 2 * ∑ k ∈ Icc 1 d, 1 / (k : ℝ) := by
  have hH0 : 0 ≤ ∑ k ∈ Icc 1 d, 1 / (k : ℝ) := sum_nonneg fun k _ => by positivity
  rcases Nat.lt_or_ge d 2 with hd1 | hd2
  · have : d = 1 := by omega
    subst this
    have hempty : nontrivialRoots 1 = ∅ := by
      ext η
      simp only [mem_nontrivialRoots one_pos, pow_one, Finset.notMem_empty, iff_false, not_and]
      exact fun h1 h => h1 h
    rw [hempty, sum_empty]
    positivity
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd2
  set s := Polynomial.nthRootsFinset d (1 : ℂ)
  have hmem : ∀ ζ ∈ s, ζ ^ d = 1 := fun ζ hζ => (Polynomial.mem_nthRootsFinset hd 1).mp hζ
  have hnorm : ∀ ζ ∈ s, ‖ζ‖ = 1 := fun ζ hζ => norm_eq_one_of_pow_eq_one (hmem ζ hζ) (by omega)
  have hsep : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → 1 / (d : ℝ) ≤ toIntDist (rootAngle b - rootAngle a) := by
    intro a ha b hb hab
    have hcf : circleFreq (rootAngle b - rootAngle a) = conj a * b := by
      rw [← conj_circleFreq_mul, circleFreq_rootAngle (hnorm a ha), circleFreq_rootAngle (hnorm b hb)]
    refine one_div_le_toIntDist_of_circleFreq_pow hd ?_ ?_
    · rw [hcf, mul_pow, ← map_pow, hmem a ha, hmem b hb, map_one, one_mul]
    · rw [hcf]
      intro h
      apply hab
      calc a = a * (conj a * b) := by rw [h, mul_one]
        _ = (conj a * a) * b := by ring
        _ = b := by rw [conj_mul_self_of_norm_eq_one (hnorm a ha), one_mul]
  have h1s : (1 : ℂ) ∈ s := (Polynomial.mem_nthRootsFinset hd 1).mpr (one_pow d)
  have hrow := circle_row_sum_le s rootAngle (δ := 1 / (d : ℝ)) (by positivity)
    (by rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith) hsep h1s (M := d)
    (by rw [show (1 : ℝ) / (2 * (1 / (d : ℝ))) = d / 2 by field_simp]; linarith)
  rw [rootAngle_one] at hrow
  simp only [sub_zero] at hrow
  calc ∑ η ∈ nontrivialRoots d, 1 / ‖η - 1‖
      ≤ ∑ η ∈ s.erase 1, 1 / 4 * (1 / toIntDist (rootAngle η)) := by
        refine sum_le_sum fun η hη => ?_
        have hηs := mem_of_mem_erase hη
        have hdist : 1 / (d : ℝ) ≤ toIntDist (rootAngle η) :=
          one_div_le_toIntDist_rootAngle_of_pow hd (hnorm η hηs) (hmem η hηs) (ne_of_mem_erase hη)
        have hdpos : 0 < toIntDist (rootAngle η) := lt_of_lt_of_le (by positivity) hdist
        have h4 := four_mul_toIntDist_rootAngle_le (hnorm η hηs)
        calc 1 / ‖η - 1‖ ≤ 1 / (4 * toIntDist (rootAngle η)) :=
              one_div_le_one_div_of_le (by positivity) h4
          _ = 1 / 4 * (1 / toIntDist (rootAngle η)) := by rw [one_div_mul_one_div]
    _ = 1 / 4 * ∑ η ∈ s.erase 1, 1 / toIntDist (rootAngle η) := by rw [mul_sum]
    _ ≤ 1 / 4 * (2 / (1 / (d : ℝ)) * ∑ k ∈ Icc 1 d, 1 / (k : ℝ)) :=
        mul_le_mul_of_nonneg_left hrow (by norm_num)
    _ = (d : ℝ) / 2 * ∑ k ∈ Icc 1 d, 1 / (k : ℝ) := by field_simp; ring

/-! ## §3. One small modulus -/

theorem sum_range_ite_ge_div_sq_le {J : ℕ} (hJ : 1 ≤ J) (K : ℕ) :
    ∑ j ∈ range K, (if J ≤ j then 1 / ((j : ℝ) + 1) ^ 2 else 0) ≤ 1 / (J : ℝ) := by
  have hJR : (1 : ℝ) ≤ J := by exact_mod_cast hJ
  have key : ∀ K, ∑ j ∈ range K, (if J ≤ j then 1 / ((j : ℝ) + 1) ^ 2 else 0) ≤
      1 / (J : ℝ) - (if J ≤ K then 1 / (K : ℝ) else 1 / (J : ℝ)) := by
    intro K
    induction K with
    | zero =>
      simp only [range_zero, sum_empty, CharP.cast_eq_zero]
      rw [if_neg (by omega)]; simp
    | succ K ih =>
      rw [Finset.sum_range_succ]
      by_cases hJK : J ≤ K
      · rw [if_pos hJK] at ih
        rw [if_pos hJK, if_pos (by omega)]
        have hKR : (1 : ℝ) ≤ K := by exact_mod_cast (le_trans hJ hJK)
        have hstep : 1 / ((K : ℝ) + 1) ^ 2 ≤ 1 / (K : ℝ) - 1 / ((K + 1 : ℕ) : ℝ) := by
          push_cast
          rw [div_sub_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity)
            (by positivity)]
          nlinarith
        linarith
      · rw [if_neg hJK] at ih
        rw [if_neg hJK]
        by_cases hJK1 : J ≤ K + 1
        · have hJeq : J = K + 1 := by omega
          rw [if_pos hJK1, hJeq]
          subst hJeq
          push_cast
          simp only [sub_self] at ih ⊢
          linarith
        · rw [if_neg hJK1]; linarith
  have h := key K
  have hnn : 0 ≤ (if J ≤ K then 1 / (K : ℝ) else 1 / (J : ℝ)) := by split_ifs <;> positivity
  linarith

/-- **One small modulus against an equidistributed large scale.** For `d ≥ 1`, a row `c'`
supported on `[A, A + KH) ⊆ [1, N]`, and `J ≥ 1`,
`|Σ_n c'(n) 𝔅(d, n)/n²| ≤ (π²/72)(d² - 1) Δ_H + H S₀ (d/2) h_d h_J + S₀ d²/(8J)`. -/
theorem abs_sum_mul_bernoulliKernel_le_block {d N A H K : ℕ} (hd : 0 < d) {c' : ℕ → ℝ}
    (hA : 1 ≤ A) (hAN : A + K * H ≤ N + 1) (hsupp : ∀ n, c' n ≠ 0 → n ∈ Ico A (A + K * H))
    {J : ℕ} (hJ : 1 ≤ J) :
    |∑ n ∈ Icc 1 N, c' n * (bernoulliKernel d n / (n : ℝ) ^ 2)| ≤
      Real.pi ^ 2 / 72 * ((d : ℝ) ^ 2 - 1) * blockDiscrepancy c' A H K +
        H * (∑ n ∈ Icc 1 N, |c' n| / (n : ℝ) ^ 2) *
          ((d : ℝ) / 2 * ∑ k ∈ Icc 1 d, 1 / (k : ℝ)) * ∑ k ∈ Icc 1 J, 1 / (k : ℝ) +
        (∑ n ∈ Icc 1 N, |c' n| / (n : ℝ) ^ 2) * (d : ℝ) ^ 2 / (8 * J) := by
  set S₀ := ∑ n ∈ Icc 1 N, |c' n| / (n : ℝ) ^ 2
  set Δ := blockDiscrepancy c' A H K
  set R := (d : ℝ) / 2 * ∑ k ∈ Icc 1 d, 1 / (k : ℝ)
  have hS₀ : 0 ≤ S₀ := sum_nonneg fun n _ => by positivity
  have hΔ : 0 ≤ Δ := sum_nonneg fun m _ => abs_nonneg _
  have hR : 0 ≤ R := by positivity
  have hd2 : (0 : ℝ) ≤ ((d : ℝ) ^ 2 - 1) / 12 := by
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    nlinarith
  have hWN : Ico A (A + K * H) ⊆ Icc 1 N := fun n hn => by
    have := mem_Ico.mp hn; exact mem_Icc.mpr ⟨by omega, by omega⟩
  -- the transform on the window
  have hT : ∀ ζ : ℂ, ‖ζ‖ = 1 → ‖rowTransform N c' ζ‖ ≤ Δ + H * ‖ζ - 1‖ * S₀ := by
    intro ζ hζ
    have hrw : rowTransform N c' ζ =
        ∑ n ∈ Ico A (A + K * H), ((c' n / (n : ℝ) ^ 2 : ℝ) : ℂ) * ζ ^ n := by
      rw [rowTransform, ← sum_subset hWN fun n _ hn => by
        have : c' n = 0 := by by_contra h; exact hn (hsupp n h)
        simp [this]]
    have hS : ∑ n ∈ Ico A (A + K * H), |c' n / (n : ℝ) ^ 2| = S₀ := by
      simp only [S₀]
      rw [← sum_subset hWN fun n _ hn => by
        have : c' n = 0 := by by_contra h; exact hn (hsupp n h)
        simp [this]]
      exact sum_congr rfl fun n _ => by rw [abs_div, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) ^ 2)]
    rw [hrw]
    have h := norm_sum_Ico_blocks_le (fun n => c' n / (n : ℝ) ^ 2) A H K hζ
    rw [hS] at h
    exact h
  -- the `m`-th layer, two bounds
  have hlayer : ∀ m : ℕ, 1 ≤ m →
      |∑ n ∈ Icc 1 N, c' n / (n : ℝ) ^ 2 * residuePotential d (m * n)| ≤
        ((d : ℝ) ^ 2 - 1) / 12 * Δ + H * S₀ * m * R := by
    intro m hm
    rw [← Real.norm_eq_abs, ← Complex.norm_real, sum_mul_residuePotential_eq_spectral hd]
    refine (norm_sum_le _ _).trans ?_
    calc ∑ η ∈ nontrivialRoots d, ‖(((‖η - 1‖ ^ 2)⁻¹ : ℝ) : ℂ) * rowTransform N c' (η ^ m)‖
        ≤ ∑ η ∈ nontrivialRoots d, ((‖η - 1‖ ^ 2)⁻¹ * Δ + H * S₀ * m * (1 / ‖η - 1‖)) := by
          refine sum_le_sum fun η hη => ?_
          have hηn := norm_eq_one_of_mem_nontrivialRoots hd hη
          have hη1 : 0 < ‖η - 1‖ :=
            norm_pos_iff.mpr (sub_ne_zero.mpr ((mem_nontrivialRoots hd).mp hη).1)
          rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
          have hTη := hT (η ^ m) (by rw [norm_pow, hηn, one_pow])
          have hpow := norm_pow_sub_one_le hηn m
          calc (‖η - 1‖ ^ 2)⁻¹ * ‖rowTransform N c' (η ^ m)‖
              ≤ (‖η - 1‖ ^ 2)⁻¹ * (Δ + H * (m * ‖η - 1‖) * S₀) := by
                refine mul_le_mul_of_nonneg_left (hTη.trans ?_) (by positivity)
                gcongr
            _ = (‖η - 1‖ ^ 2)⁻¹ * Δ + H * S₀ * m * (1 / ‖η - 1‖) := by
                field_simp
      _ = (∑ η ∈ nontrivialRoots d, (‖η - 1‖ ^ 2)⁻¹) * Δ +
            H * S₀ * m * ∑ η ∈ nontrivialRoots d, 1 / ‖η - 1‖ := by
          rw [sum_add_distrib, ← sum_mul, ← mul_sum]
      _ ≤ ((d : ℝ) ^ 2 - 1) / 12 * Δ + H * S₀ * m * R := by
          rw [sum_nontrivialRoots_inv_norm_sq hd]
          gcongr
          exact sum_nontrivialRoots_inv_norm_le hd
  have htriv : ∀ m : ℕ, |∑ n ∈ Icc 1 N, c' n / (n : ℝ) ^ 2 * residuePotential d (m * n)| ≤
      S₀ * ((d : ℝ) ^ 2 / 8) := by
    intro m
    refine (abs_sum_le_sum_abs _ _).trans ?_
    rw [sum_mul]
    refine sum_le_sum fun n _ => ?_
    rw [abs_mul, abs_div, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) ^ 2)]
    exact mul_le_mul_of_nonneg_left (abs_residuePotential_le hd _) (by positivity)
  -- the series over `j`
  set t : ℕ → ℝ := fun j => ∑ n ∈ Icc 1 N, c' n / (n : ℝ) ^ 2 *
    (residuePotential d ((j + 1) * n) / ((j : ℝ) + 1) ^ 2)
  have ht : HasSum t (∑ n ∈ Icc 1 N, c' n * (bernoulliKernel d n / (n : ℝ) ^ 2)) := by
    have h := hasSum_sum fun n (_ : n ∈ Icc 1 N) =>
      (hasSum_bernoulliKernel hd n).mul_left (c' n / (n : ℝ) ^ 2)
    have he : ∑ n ∈ Icc 1 N, c' n * (bernoulliKernel d n / (n : ℝ) ^ 2) =
        ∑ n ∈ Icc 1 N, c' n / (n : ℝ) ^ 2 * bernoulliKernel d n :=
      sum_congr rfl fun n _ => by ring
    rw [he]
    exact h
  have hz : HasSum (fun j : ℕ => 1 / ((j : ℝ) + 1) ^ 2) (Real.pi ^ 2 / 6) := by
    have := (hasSum_nat_add_iff' 1).mpr hasSum_zeta_two
    simpa using this
  have htj : ∀ j, |t j| = |∑ n ∈ Icc 1 N, c' n / (n : ℝ) ^ 2 * residuePotential d ((j + 1) * n)| *
      (1 / ((j : ℝ) + 1) ^ 2) := by
    intro j
    have hrw : t j = (∑ n ∈ Icc 1 N, c' n / (n : ℝ) ^ 2 * residuePotential d ((j + 1) * n)) *
        (1 / ((j : ℝ) + 1) ^ 2) := by
      simp only [t, sum_mul]
      exact sum_congr rfl fun n _ => by ring
    rw [hrw, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / ((j : ℝ) + 1) ^ 2)]
  have hbound : ∀ K', |∑ j ∈ range K', t j| ≤
      Real.pi ^ 2 / 72 * ((d : ℝ) ^ 2 - 1) * Δ + H * S₀ * R * ∑ k ∈ Icc 1 J, 1 / (k : ℝ) +
        S₀ * (d : ℝ) ^ 2 / (8 * J) := by
    intro K'
    have hpt : ∀ j ∈ range K', |t j| ≤
        ((d : ℝ) ^ 2 - 1) / 12 * Δ * (1 / ((j : ℝ) + 1) ^ 2) +
          H * S₀ * R * (if j < J then 1 / ((j : ℝ) + 1) else 0) +
          S₀ * ((d : ℝ) ^ 2 / 8) * (if J ≤ j then 1 / ((j : ℝ) + 1) ^ 2 else 0) := by
      intro j _
      rw [htj]
      have hj1 : (0 : ℝ) < (j : ℝ) + 1 := by positivity
      split_ifs with hjJ hJj hJj
      · omega
      · have h := hlayer (j + 1) (by omega)
        calc |∑ n ∈ Icc 1 N, c' n / (n : ℝ) ^ 2 * residuePotential d ((j + 1) * n)| *
              (1 / ((j : ℝ) + 1) ^ 2)
            ≤ (((d : ℝ) ^ 2 - 1) / 12 * Δ + H * S₀ * ((j + 1 : ℕ) : ℝ) * R) *
                (1 / ((j : ℝ) + 1) ^ 2) := mul_le_mul_of_nonneg_right h (by positivity)
          _ = ((d : ℝ) ^ 2 - 1) / 12 * Δ * (1 / ((j : ℝ) + 1) ^ 2) +
                H * S₀ * R * (1 / ((j : ℝ) + 1)) + S₀ * ((d : ℝ) ^ 2 / 8) * 0 := by
              push_cast; field_simp; ring
      · have h := htriv (j + 1)
        have hfirst : 0 ≤ ((d : ℝ) ^ 2 - 1) / 12 * Δ * (1 / ((j : ℝ) + 1) ^ 2) := by positivity
        calc |∑ n ∈ Icc 1 N, c' n / (n : ℝ) ^ 2 * residuePotential d ((j + 1) * n)| *
              (1 / ((j : ℝ) + 1) ^ 2)
            ≤ S₀ * ((d : ℝ) ^ 2 / 8) * (1 / ((j : ℝ) + 1) ^ 2) :=
              mul_le_mul_of_nonneg_right h (by positivity)
          _ ≤ _ := by linarith
      · omega
    have hsum1 : ∑ j ∈ range K', 1 / ((j : ℝ) + 1) ^ 2 ≤ Real.pi ^ 2 / 6 :=
      sum_le_hasSum _ (fun j _ => by positivity) hz
    have hsum2 : ∑ j ∈ range K', (if j < J then 1 / ((j : ℝ) + 1) else 0) ≤
        ∑ k ∈ Icc 1 J, 1 / (k : ℝ) := by
      have hre : ∀ J : ℕ, ∑ k ∈ Icc 1 J, 1 / (k : ℝ) = ∑ j ∈ range J, 1 / ((j : ℝ) + 1) := by
        intro J
        induction J with
        | zero => simp
        | succ J ih => rw [sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]; push_cast; ring
      rw [hre J, ← sum_filter]
      exact sum_le_sum_of_subset_of_nonneg (fun j hj => mem_range.mpr (mem_filter.mp hj).2)
        (fun _ _ _ => by positivity)
    have hsum3 := sum_range_ite_ge_div_sq_le hJ K'
    calc |∑ j ∈ range K', t j| ≤ ∑ j ∈ range K', |t j| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ j ∈ range K', (((d : ℝ) ^ 2 - 1) / 12 * Δ * (1 / ((j : ℝ) + 1) ^ 2) +
            H * S₀ * R * (if j < J then 1 / ((j : ℝ) + 1) else 0) +
            S₀ * ((d : ℝ) ^ 2 / 8) * (if J ≤ j then 1 / ((j : ℝ) + 1) ^ 2 else 0)) := sum_le_sum hpt
      _ = ((d : ℝ) ^ 2 - 1) / 12 * Δ * ∑ j ∈ range K', 1 / ((j : ℝ) + 1) ^ 2 +
            H * S₀ * R * ∑ j ∈ range K', (if j < J then 1 / ((j : ℝ) + 1) else 0) +
            S₀ * ((d : ℝ) ^ 2 / 8) * ∑ j ∈ range K', (if J ≤ j then 1 / ((j : ℝ) + 1) ^ 2 else 0) := by
          rw [sum_add_distrib, sum_add_distrib, ← mul_sum, ← mul_sum, ← mul_sum]
      _ ≤ ((d : ℝ) ^ 2 - 1) / 12 * Δ * (Real.pi ^ 2 / 6) +
            H * S₀ * R * ∑ k ∈ Icc 1 J, 1 / (k : ℝ) + S₀ * ((d : ℝ) ^ 2 / 8) * (1 / J) := by
          gcongr
      _ = _ := by field_simp; ring
  have := le_of_tendsto' (ht.tendsto_sum_nat.abs) hbound
  refine this.trans (le_of_eq ?_)
  ring

/-! ## §4. Every row -/

theorem sum_Icc_inv_mono {a b : ℕ} (hab : a ≤ b) :
    ∑ k ∈ Icc 1 a, 1 / (k : ℝ) ≤ ∑ k ∈ Icc 1 b, 1 / (k : ℝ) :=
  sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc le_rfl hab) fun _ _ _ => by positivity

/-- **Block equidistribution suffices.** For every row `c` and a large-scale row `c'` supported on
`[A, A + KH) ⊆ [1, N]`, with `h_N = Σ_{k ≤ N} 1/k`,
`|B + m R' + β H'| ≤ (π²/72) Δ_H Σ_d |c(d)| d + (H h_N²/2 + 1/8) S₀ Σ_d |c(d)|
  + ¾ Σ_d |c(d)| d² Σ_n |c'(n)|/n³`. -/
theorem abs_rowBilinear_add_mean_add_beta_le_block {N A H K : ℕ} {c c' : ℕ → ℝ} (hA : 1 ≤ A)
    (hAN : A + K * H ≤ N + 1) (hsupp : ∀ n, c' n ≠ 0 → n ∈ Ico A (A + K * H)) :
    |rowBilinear N c c' + rowMean N c * vonMangoldtReadout N c' +
        rowBeta N c * finiteHarmonicSum N c'| ≤
      Real.pi ^ 2 / 72 * blockDiscrepancy c' A H K * ∑ d ∈ Icc 1 N, |c d| * d +
        (H * (∑ k ∈ Icc 1 N, 1 / (k : ℝ)) ^ 2 / 2 + 1 / 8) *
          (∑ n ∈ Icc 1 N, |c' n| / (n : ℝ) ^ 2) * ∑ d ∈ Icc 1 N, |c d| +
        3 / 4 * (∑ d ∈ Icc 1 N, |c d| * (d : ℝ) ^ 2) * ∑ n ∈ Icc 1 N, |c' n| / (n : ℝ) ^ 3 := by
  set S₀ := ∑ n ∈ Icc 1 N, |c' n| / (n : ℝ) ^ 2
  set Δ := blockDiscrepancy c' A H K
  set hN := ∑ k ∈ Icc 1 N, 1 / (k : ℝ)
  have hS₀ : 0 ≤ S₀ := sum_nonneg fun n _ => by positivity
  have hΔ : 0 ≤ Δ := sum_nonneg fun m _ => abs_nonneg _
  have hlaw := abs_rowBilinear_add_mean_add_beta_sub_bernoulli_le N c c'
  set M := ∑ n ∈ Icc 1 N, ∑ d ∈ Icc 1 N, c' n * (c d / d) * (bernoulliKernel d n / (n : ℝ) ^ 2)
  have hM : M = ∑ d ∈ Icc 1 N, c d / d * ∑ n ∈ Icc 1 N, c' n * (bernoulliKernel d n / (n : ℝ) ^ 2) := by
    simp only [M]
    rw [sum_comm]
    refine sum_congr rfl fun d _ => ?_
    rw [mul_sum]
    exact sum_congr rfl fun n _ => by ring
  have hMb : |M| ≤ Real.pi ^ 2 / 72 * Δ * ∑ d ∈ Icc 1 N, |c d| * d +
      (H * hN ^ 2 / 2 + 1 / 8) * S₀ * ∑ d ∈ Icc 1 N, |c d| := by
    rw [hM, mul_sum, mul_sum, ← sum_add_distrib]
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun d hd => ?_)
    have hd0 : 0 < d := (mem_Icc.mp hd).1
    have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd0
    have hk := abs_sum_mul_bernoulliKernel_le_block (d := d) hd0 hA hAN hsupp (J := d) hd0
    have hhd : ∑ k ∈ Icc 1 d, 1 / (k : ℝ) ≤ hN := sum_Icc_inv_mono (mem_Icc.mp hd).2
    have hh0 : 0 ≤ ∑ k ∈ Icc 1 d, 1 / (k : ℝ) := sum_nonneg fun k _ => by positivity
    have hc := abs_nonneg (c d)
    rw [abs_mul, abs_div, abs_of_pos (by linarith : (0 : ℝ) < d)]
    calc |c d| / d * |∑ n ∈ Icc 1 N, c' n * (bernoulliKernel d n / (n : ℝ) ^ 2)|
        ≤ |c d| / d * (Real.pi ^ 2 / 72 * ((d : ℝ) ^ 2 - 1) * Δ +
            H * S₀ * ((d : ℝ) / 2 * ∑ k ∈ Icc 1 d, 1 / (k : ℝ)) * ∑ k ∈ Icc 1 d, 1 / (k : ℝ) +
            S₀ * (d : ℝ) ^ 2 / (8 * d)) := mul_le_mul_of_nonneg_left hk (by positivity)
      _ = Real.pi ^ 2 / 72 * Δ * (|c d| * d) - Real.pi ^ 2 / 72 * Δ * (|c d| / d) +
            (H * (∑ k ∈ Icc 1 d, 1 / (k : ℝ)) ^ 2 / 2 + 1 / 8) * S₀ * |c d| := by
          field_simp; ring
      _ ≤ Real.pi ^ 2 / 72 * Δ * (|c d| * d) + (H * hN ^ 2 / 2 + 1 / 8) * S₀ * |c d| := by
          have h1 : 0 ≤ Real.pi ^ 2 / 72 * Δ * (|c d| / d) := by positivity
          have h2 : (∑ k ∈ Icc 1 d, 1 / (k : ℝ)) ^ 2 ≤ hN ^ 2 := pow_le_pow_left₀ hh0 hhd 2
          have h3 : (H * (∑ k ∈ Icc 1 d, 1 / (k : ℝ)) ^ 2 / 2 + 1 / 8) * S₀ * |c d| ≤
              (H * hN ^ 2 / 2 + 1 / 8) * S₀ * |c d| := by gcongr
          linarith
  have hsplit := abs_sub_abs_le_abs_sub (rowBilinear N c c' + rowMean N c * vonMangoldtReadout N c' +
    rowBeta N c * finiteHarmonicSum N c') M
  linarith

end

end GaloisForLFunctions.BezoutValuationIncidence
