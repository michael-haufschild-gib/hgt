import GaloisForLFunctions.RHTower.WeilWorkQuantizationCenteredSource
import GaloisForLFunctions.RHTower.Sieve.BivariateConvolutionSummatorySwap

/-!
# Sublinear summatory cancellation of the pole-centered square

The actual forward source has its own pole residue removed. Its signed
summatory bound and absolute convergence give a sublinear summatory bound
for its Dirichlet square by the exact square-root hyperbola decomposition.
No coefficient sign or source functional equation is assumed.
-/

open Complex Finset Filter Topology
noncomputable section
namespace RHTower.WeilWorkSettledPhase
open WeilSpectral

private theorem sum_cutoff (m n : ℕ) (hn : n ≤ m) (f : ℕ → ℂ) :
    (∑ i ∈ Icc 1 m, if i ≤ n then f i else 0) = ∑ i ∈ Icc 1 n, f i := by
  rw [← sum_filter]
  congr 1
  ext i
  simp only [mem_filter, mem_Icc]
  omega

private theorem hyperbola_row (M d : ℕ) (hd : 0 < d) (f : ℕ → ℂ) :
    (∑ e ∈ Icc 1 M, if d * e ≤ M then f d * f e else 0) =
      f d * (∑ e ∈ Icc 1 (M / d), f e) := by
  rw [← sum_filter]
  have hf : {e ∈ Icc 1 M | d * e ≤ M} = Icc 1 (M / d) := by
    ext e
    simp only [mem_filter, mem_Icc]
    have hdiv : e ≤ M / d ↔ d * e ≤ M := by
      rw [Nat.le_div_iff_mul_le hd, Nat.mul_comm]
    have hMd := Nat.div_le_self M d
    omega
  rw [hf, mul_sum]

/-- Finite complex hyperbola decomposition, retaining the full square overlap. -/
theorem sum_self_convolution_hyperbola (f : ℕ → ℂ) (M : ℕ) :
    (∑ n ∈ Icc 1 M, LSeries.convolution f f n) =
      2 * (∑ d ∈ Icc 1 (Nat.sqrt M), f d * (∑ e ∈ Icc 1 (M / d), f e)) -
        (∑ d ∈ Icc 1 (Nat.sqrt M), f d) ^ 2 := by
  let r := Nat.sqrt M
  let L := fun d e => if d ≤ r then (if d * e ≤ M then f d * f e else 0) else 0
  let Q := fun d e => if d ≤ r then (if e ≤ r then f d * f e else 0) else 0
  have hrr : r * r ≤ M := Nat.sqrt_le M
  have hnext : M < (r + 1) * (r + 1) := Nat.lt_succ_sqrt M
  have hpoint (d e : ℕ) :
      (if d * e ≤ M then f d * f e else 0) = L d e + L e d - Q d e := by
    by_cases hd : d ≤ r <;> by_cases he : e ≤ r
    · have hp : d * e ≤ M := (Nat.mul_le_mul hd he).trans hrr
      simp [L, Q, hd, he, hp, mul_comm]
    · simp [L, Q, hd, he]
    · simp [L, Q, hd, he, mul_comm]
    · have hp : ¬d * e ≤ M := by
        have h := Nat.mul_le_mul (show r + 1 ≤ d by omega) (show r + 1 ≤ e by omega)
        omega
      simp [L, Q, hd, he, hp]
  have hL : (∑ d ∈ Icc 1 M, ∑ e ∈ Icc 1 M, L d e) =
      ∑ d ∈ Icc 1 r, f d * (∑ e ∈ Icc 1 (M / d), f e) := by
    have hp (d : ℕ) : (∑ e ∈ Icc 1 M, L d e) =
        if d ≤ r then (∑ e ∈ Icc 1 M, if d * e ≤ M then f d * f e else 0) else 0 := by
      by_cases hd : d ≤ r <;> simp [L, hd]
    simp_rw [hp]
    rw [sum_cutoff M r (Nat.sqrt_le_self M)]
    exact sum_congr rfl fun d hd => hyperbola_row M d (mem_Icc.mp hd).1 f
  have hQ : (∑ d ∈ Icc 1 M, ∑ e ∈ Icc 1 M, Q d e) =
      (∑ d ∈ Icc 1 r, f d) ^ 2 := by
    have hp (d : ℕ) : (∑ e ∈ Icc 1 M, Q d e) =
        if d ≤ r then f d * (∑ e ∈ Icc 1 r, f e) else 0 := by
      by_cases hd : d ≤ r
      · simp only [Q, if_pos hd]
        rw [sum_cutoff M r (Nat.sqrt_le_self M), mul_sum]
      · simp [Q, hd]
    simp_rw [hp]
    rw [sum_cutoff M r (Nat.sqrt_le_self M), ← sum_mul, pow_two]
  have hswap : (∑ d ∈ Icc 1 M, ∑ e ∈ Icc 1 M, L e d) =
      ∑ d ∈ Icc 1 M, ∑ e ∈ Icc 1 M, L d e := sum_comm
  have hfull : (∑ n ∈ Icc 1 M, LSeries.convolution f f n) =
      ∑ d ∈ Icc 1 M, ∑ e ∈ Icc 1 M, if d * e ≤ M then f d * f e else 0 := by
    simp only [LSeries.convolution_def]
    rw [Sieve.sum_Icc_divisorsAntidiagonal_swap (fun d e => f d * f e) M]
    apply sum_congr rfl
    intro d hd
    rw [hyperbola_row M d (mem_Icc.mp hd).1, mul_sum]
  rw [hfull]
  simp_rw [hpoint, sum_sub_distrib, sum_add_distrib]
  rw [hswap, hL, hQ]
  ring

/-- The source pays a fixed summatory exponent strictly below one. -/
theorem exists_centered_coeff_sum_le (hW : WeilPositiveFull lam) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ N : ℕ,
      ‖∑ n ∈ Icc 1 N, quantizationCenteredCoeff hW n‖ ≤ A * (N : ℝ) ^ (9 / 16 : ℝ) := by
  obtain ⟨C, hC, hb⟩ := exists_sharp_forward_sum_le hW (ε := 1 / 16) (by norm_num)
  refine ⟨C * 2 ^ (9 / 16 : ℝ), by positivity, fun N => ?_⟩
  rcases N.eq_zero_or_pos with rfl | hN
  · simp
  have he : (∑ n ∈ Icc 1 N, quantizationCenteredCoeff hW n) =
      (∑ n ∈ range (N + 1), sourceCoeff lam n) - sourceCompletion hW 1 * N := by
    unfold quantizationCenteredCoeff
    have hz (n : ℕ) (hn : n ∈ Icc 1 N) : n ≠ 0 := by have := (mem_Icc.mp hn).1; omega
    rw [sum_congr rfl (fun n hn => if_neg (hz n hn))]
    rw [sum_sub_distrib, sum_const, Nat.card_Icc]
    simp only [Nat.add_sub_cancel, nsmul_eq_mul]
    rw [show (∑ n ∈ range (N + 1), sourceCoeff lam n) =
        sourceCoeff lam 0 + ∑ n ∈ Icc 1 N, sourceCoeff lam n by
      rw [← Nat.Ico_zero_eq_range, ← Finset.Ico_add_one_right_eq_Icc,
        Finset.sum_eq_sum_Ico_succ_bot (by omega)]]
    simp [sourceCoeff, GaloisForLFunctions.HTGeometry.dirichletExp_zero, mul_comm]
  rw [he]
  have hn1 : 1 ≤ (N : ℝ) := by exact_mod_cast hN
  have hh := hb N
  norm_num only [show (1 / 2 : ℝ) + 1 / 16 = 9 / 16 by norm_num] at hh
  calc
    _ ≤ C * ((N : ℝ) + 1) ^ (9 / 16 : ℝ) := hh
    _ ≤ C * (2 * (N : ℝ)) ^ (9 / 16 : ℝ) := by gcongr <;> linarith
    _ = _ := by rw [Real.mul_rpow (by norm_num) (by positivity)]; ring

/-- Signed hyperbola cancellation needs no positivity of the coefficients. -/
theorem self_convolution_prefix_le {b : ℕ → ℂ} {A M : ℝ}
    (hA : 0 ≤ A) (hM : 0 ≤ M)
    (hs : ∀ N : ℕ, ‖∑ n ∈ Icc 1 N, b n‖ ≤ A * (N : ℝ) ^ (9 / 16 : ℝ))
    (hm : ∀ N : ℕ, ∑ n ∈ Icc 1 N, ‖b n‖ / (n : ℝ) ^ (17 / 16 : ℝ) ≤ M)
    (N : ℕ) :
    ‖∑ n ∈ Icc 1 N, LSeries.convolution b b n‖ ≤
      (2 * A * M + A ^ 2) * (N : ℝ) ^ (13 / 16 : ℝ) := by
  rcases N.eq_zero_or_pos with rfl | hN
  · simp
  have hN0 : 0 < (N : ℝ) := by exact_mod_cast hN
  have hN1 : 1 ≤ (N : ℝ) := by exact_mod_cast hN
  let r := Nat.sqrt N
  have hr0 : 0 ≤ (r : ℝ) := Nat.cast_nonneg r
  have hrsq : (r : ℝ) ^ 2 ≤ N := by
    have hh := Nat.sqrt_le N
    simpa only [r, pow_two, Nat.cast_mul] using (Nat.cast_le (α := ℝ)).mpr hh
  have hrhalf : (r : ℝ) ^ (1 / 2 : ℝ) ≤ (N : ℝ) ^ (1 / 4 : ℝ) := by
    calc
      _ = ((r : ℝ) ^ (2 : ℕ)) ^ (1 / 4 : ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hr0]
        norm_num
      _ ≤ _ := Real.rpow_le_rpow (sq_nonneg _) hrsq (by norm_num)
  have hweighted : (∑ n ∈ Icc 1 r, ‖b n‖ / (n : ℝ) ^ (9 / 16 : ℝ)) ≤
      M * (r : ℝ) ^ (1 / 2 : ℝ) := by
    calc
      _ ≤ ∑ n ∈ Icc 1 r,
          (‖b n‖ / (n : ℝ) ^ (17 / 16 : ℝ)) * (r : ℝ) ^ (1 / 2 : ℝ) := by
        apply sum_le_sum
        intro n hn
        have hn0 : 0 < (n : ℝ) := by exact_mod_cast (mem_Icc.mp hn).1
        have hnle : (n : ℝ) ≤ r := by exact_mod_cast (mem_Icc.mp hn).2
        have hp : (n : ℝ) ^ (17 / 16 : ℝ) =
            (n : ℝ) ^ (9 / 16 : ℝ) * (n : ℝ) ^ (1 / 2 : ℝ) := by
          rw [← Real.rpow_add hn0]
          norm_num
        have he : ‖b n‖ / (n : ℝ) ^ (9 / 16 : ℝ) =
            (‖b n‖ / (n : ℝ) ^ (17 / 16 : ℝ)) * (n : ℝ) ^ (1 / 2 : ℝ) := by
          rw [hp]
          field_simp [(Real.rpow_pos_of_pos hn0 (9 / 16)).ne',
            (Real.rpow_pos_of_pos hn0 (1 / 2)).ne']
        rw [he]
        gcongr
      _ = (∑ n ∈ Icc 1 r, ‖b n‖ / (n : ℝ) ^ (17 / 16 : ℝ)) *
          (r : ℝ) ^ (1 / 2 : ℝ) := (sum_mul _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right (hm r) (Real.rpow_nonneg hr0 _)
  have hrow : ‖∑ d ∈ Icc 1 r, b d * (∑ e ∈ Icc 1 (N / d), b e)‖ ≤
      A * M * (N : ℝ) ^ (13 / 16 : ℝ) := by
    calc
      _ ≤ ∑ d ∈ Icc 1 r, ‖b d‖ * (A * ((N / d : ℕ) : ℝ) ^ (9 / 16 : ℝ)) := by
        apply (norm_sum_le _ _).trans
        apply sum_le_sum
        intro d _
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hs (N / d)) (norm_nonneg _)
      _ ≤ ∑ d ∈ Icc 1 r, A * (N : ℝ) ^ (9 / 16 : ℝ) *
          (‖b d‖ / (d : ℝ) ^ (9 / 16 : ℝ)) := by
        apply sum_le_sum
        intro d hd
        have hdiv : ((N / d : ℕ) : ℝ) ≤ (N : ℝ) / d := Nat.cast_div_le
        calc
          _ ≤ ‖b d‖ * (A * ((N : ℝ) / d) ^ (9 / 16 : ℝ)) := by gcongr
          _ = _ := by rw [Real.div_rpow hN0.le (Nat.cast_nonneg d)]; ring
      _ = A * (N : ℝ) ^ (9 / 16 : ℝ) *
          (∑ d ∈ Icc 1 r, ‖b d‖ / (d : ℝ) ^ (9 / 16 : ℝ)) := (mul_sum _ _ _).symm
      _ ≤ A * (N : ℝ) ^ (9 / 16 : ℝ) * (M * (r : ℝ) ^ (1 / 2 : ℝ)) := by gcongr
      _ ≤ A * (N : ℝ) ^ (9 / 16 : ℝ) * (M * (N : ℝ) ^ (1 / 4 : ℝ)) := by gcongr
      _ = _ := by rw [mul_mul_mul_comm, ← Real.rpow_add hN0]; norm_num
  have hdiag : ‖(∑ d ∈ Icc 1 r, b d) ^ 2‖ ≤ A ^ 2 * (N : ℝ) ^ (13 / 16 : ℝ) := by
    rw [norm_pow]
    calc
      _ ≤ (A * (r : ℝ) ^ (9 / 16 : ℝ)) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (hs r) 2
      _ = A ^ 2 * ((r : ℝ) ^ (2 : ℕ)) ^ (9 / 16 : ℝ) := by
        rw [mul_pow]
        congr 1
        rw [← Real.rpow_natCast, ← Real.rpow_natCast,
          ← Real.rpow_mul hr0, ← Real.rpow_mul hr0]
        congr 1
        ring
      _ ≤ A ^ 2 * (N : ℝ) ^ (9 / 16 : ℝ) := by gcongr
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)) (sq_nonneg A)
  rw [sum_self_convolution_hyperbola]
  calc
    _ ≤ ‖2 * (∑ d ∈ Icc 1 r, b d * (∑ e ∈ Icc 1 (N / d), b e))‖ +
        ‖(∑ d ∈ Icc 1 r, b d) ^ 2‖ := norm_sub_le _ _
    _ ≤ 2 * (A * M * (N : ℝ) ^ (13 / 16 : ℝ)) +
        A ^ 2 * (N : ℝ) ^ (13 / 16 : ℝ) := by
      rw [norm_mul, Complex.norm_ofNat]
      gcongr
    _ = _ := by ring

/-- Original positivity gives a power saving for the literal centered square. -/
theorem exists_centered_square_sum_le (hW : WeilPositiveFull lam) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ,
      ‖∑ n ∈ Icc 1 N,
        LSeries.convolution (quantizationCenteredCoeff hW) (quantizationCenteredCoeff hW) n‖ ≤
          C * (N : ℝ) ^ (13 / 16 : ℝ) := by
  obtain ⟨A, hA, hs⟩ := exists_centered_coeff_sum_le hW
  let w : ℕ → ℝ := fun n => ‖quantizationCenteredCoeff hW n‖ / (n : ℝ) ^ (17 / 16 : ℝ)
  have hw : Summable w := by
    have hh := (quantizationCenteredCoeff_summable hW
      (s := (17 / 16 : ℝ)) (by norm_num)).norm
    refine hh.congr fun n => ?_
    by_cases hn : n = 0
    · subst n; simp [w, LSeries.term]
    · rw [LSeries.norm_term_eq, if_neg hn]
      simp only [Complex.ofReal_re]
      rfl
  have hw0 (n : ℕ) : 0 ≤ w n := by dsimp [w]; positivity
  refine ⟨2 * A * (∑' n, w n) + A ^ 2, by positivity, fun N => ?_⟩
  exact self_convolution_prefix_le hA (tsum_nonneg hw0) hs
    (fun M => hw.sum_le_tsum _ (fun n _ => hw0 n)) N

end RHTower.WeilWorkSettledPhase
