import GaloisForLFunctions.RHTower.Sieve.HuxleyFinsetLargeValues
import GaloisForLFunctions.RHTower.Sieve.HarmonicLogBound

/-!
# Huxley's large-values theorem for a dyadic Dirichlet block
-/

namespace RHTower.Sieve

open Finset
open scoped InnerProductSpace

/-- Coefficient vector of a dyadic Dirichlet block, weighted by `n^{-sigma}`. -/
noncomputable def blockCoeff (N : ℕ) (c : ℕ → ℂ) (sigma : ℝ) : EuclideanSpace ℂ (Fin N) :=
  WithLp.toLp 2 (fun j : Fin N =>
    c (N + (j : ℕ)) * ((((N + (j : ℕ) : ℕ) : ℝ) ^ (-sigma) : ℝ) : ℂ))

/-- The dyadic Dirichlet block `∑_{N ≤ n < 2N} c_n n^{-sigma-it}`. -/
noncomputable def blockPoly (N : ℕ) (c : ℕ → ℂ) (sigma t : ℝ) : ℂ :=
  ∑ n ∈ Finset.Ico N (2 * N), c n * (((n : ℝ) ^ (-sigma) : ℝ) : ℂ) *
    Complex.exp (((-(t * Real.log (n : ℝ)) : ℝ) : ℂ) * Complex.I)

/-- The Gram row against the block coefficient vector is the block itself. -/
theorem inner_dyadicDirRow_blockCoeff (N : ℕ) (c : ℕ → ℂ) (sigma t : ℝ) :
    ⟪dyadicDirRow N t, blockCoeff N c sigma⟫_ℂ = blockPoly N c sigma t := by
  have hlen : 2 * N - N = N := by omega
  rw [blockPoly, Finset.sum_Ico_eq_sum_range, hlen, PiLp.inner_apply,
    ← Fin.sum_univ_eq_sum_range (fun j : ℕ =>
      c (N + j) * (((((N + j : ℕ) : ℝ) ^ (-sigma) : ℝ)) : ℂ) *
        Complex.exp (((-(t * Real.log ((N + j : ℕ) : ℝ)) : ℝ) : ℂ) * Complex.I)) N]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [dyadicDirRow, blockCoeff, RCLike.inner_apply]
  have hconj : (starRingEnd ℂ)
      (Complex.exp ((((t * Real.log ((N + (j : ℕ) : ℕ) : ℝ) : ℝ) : ℂ) * Complex.I)))
      = Complex.exp (((-(t * Real.log ((N + (j : ℕ) : ℕ) : ℝ)) : ℝ) : ℂ) * Complex.I) := by
    rw [← Complex.exp_conj]
    congr 1
    rw [map_mul, Complex.conj_I, Complex.conj_ofReal]
    push_cast
    ring
  rw [hconj]

/-- Hilbert energy of the block coefficient vector. -/
theorem norm_blockCoeff_sq (N : ℕ) (c : ℕ → ℂ) (sigma : ℝ) :
    ‖blockCoeff N c sigma‖ ^ 2
      = ∑ n ∈ Finset.Ico N (2 * N), ‖c n‖ ^ 2 * (((n : ℝ) ^ (-sigma)) ^ 2) := by
  have hlen : 2 * N - N = N := by omega
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity),
    Finset.sum_Ico_eq_sum_range, hlen,
    ← Fin.sum_univ_eq_sum_range (fun j : ℕ =>
      ‖c (N + j)‖ ^ 2 * (((((N + j : ℕ) : ℝ) ^ (-sigma)) ^ 2))) N]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [blockCoeff, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  rw [mul_pow]
  congr 1
  rw [sq_abs]

/-- Energy bound for divisor-bounded coefficients on the line `sigma = 1`. -/
theorem norm_blockCoeff_one_sq_le {N : ℕ} (hN : 1 ≤ N) (c : ℕ → ℂ) {D : ℝ} (hD : 0 ≤ D)
    (hc : ∀ n ∈ Finset.Ico N (2 * N), ‖c n‖ ≤ D) :
    ‖blockCoeff N c 1‖ ^ 2 ≤ D ^ 2 / (N : ℝ) := by
  have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < (N : ℝ) := by linarith
  rw [norm_blockCoeff_sq]
  have hterm : ∀ n ∈ Finset.Ico N (2 * N),
      ‖c n‖ ^ 2 * (((n : ℝ) ^ (-(1 : ℝ))) ^ 2) ≤ D ^ 2 * (1 / (N : ℝ) ^ 2) := by
    intro n hn
    have hnN : N ≤ n := (Finset.mem_Ico.1 hn).1
    have hnR : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnN
    have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
    have hinv : ((n : ℝ) ^ (-(1 : ℝ))) = ((n : ℝ))⁻¹ := by
      rw [Real.rpow_neg_one]
    have hsq : (((n : ℝ) ^ (-(1 : ℝ))) ^ 2) ≤ 1 / (N : ℝ) ^ 2 := by
      rw [hinv, inv_pow, ← one_div]
      apply one_div_le_one_div_of_le (by positivity)
      nlinarith [hnR, hN0]
    have hcn : ‖c n‖ ^ 2 ≤ D ^ 2 := by
      have := hc n hn
      nlinarith [norm_nonneg (c n), hD]
    have hpos : (0 : ℝ) ≤ (((n : ℝ) ^ (-(1 : ℝ))) ^ 2) := by positivity
    nlinarith [hcn, hsq, hpos, sq_nonneg D]
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [Finset.sum_const, Nat.card_Ico]
  have hcnt : 2 * N - N = N := by omega
  rw [hcnt, nsmul_eq_mul]
  have hval : (N : ℝ) * (D ^ 2 * (1 / (N : ℝ) ^ 2)) = D ^ 2 / (N : ℝ) := by
    field_simp
  exact le_of_eq hval

/-- **Huxley's large-values theorem for a dyadic Dirichlet block, in its published shape.**
For divisor-bounded coefficients `‖c n‖ ≤ D` on `[N,2N)`, a `delta`-separated set `S` of ordinates
confined to a range of length `Ttot` on which the block exceeds `V` satisfies

`|S| ≪ D²/V² + Ttot·D⁶/(N²V⁶)`  (up to the logarithmic factor and the absolute constants below),

which is Huxley's `G N V^{-2} + T G³ N V^{-6}` at `G = D²/N`.  The side condition
`(D²/N)(1 + 1536√(3N/4π)) ≤ V²/3` is Huxley's `V ≥ N^{3/4+o(1)}`. -/
theorem huxley_block_large_values {N : ℕ} (hN : 1 ≤ N) (c : ℕ → ℂ)
    {delta Ttot V D : ℝ} (hdelta : 0 < delta) (hV : 0 < V) (hTtot : 0 ≤ Ttot) (hD : 0 ≤ D)
    (hc : ∀ n ∈ Finset.Ico N (2 * N), ‖c n‖ ≤ D)
    (S : Finset ℝ)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → delta ≤ |x - y|)
    (hspread : ∀ x ∈ S, ∀ y ∈ S, |x - y| ≤ Ttot)
    (hbig : ∀ x ∈ S, V ≤ ‖blockPoly N c 1 x‖)
    (hthresh : (D ^ 2 / (N : ℝ)) * (1 + 1536 * Real.sqrt (3 * (N : ℝ) / (4 * Real.pi)))
      ≤ V ^ 2 / 3) :
    ((S.card : ℝ)) * V ^ 2
      ≤ (1648656 * Ttot * D ^ 4 / ((N : ℝ) ^ 2 * V ^ 4) + 1)
        * (2 * D ^ 2 * (1 + 12 * Real.pi * (1 + Real.log (S.card : ℝ)) / delta)) := by
  have hN0 : (0 : ℝ) < (N : ℝ) := by
    exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one hN
  have hG : ‖blockCoeff N c 1‖ ^ 2 ≤ D ^ 2 / (N : ℝ) := norm_blockCoeff_one_sq_le hN c hD hc
  have hbig' : ∀ x ∈ S, V ≤ ‖⟪dyadicDirRow N x, blockCoeff N c 1⟫_ℂ‖ := by
    intro x hx
    rw [inner_dyadicDirRow_blockCoeff]
    exact hbig x hx
  have hmain := huxley_large_values_finset hN (blockCoeff N c 1) hdelta hV hTtot hG S
    hsep hspread hbig' hthresh
  refine le_trans hmain ?_
  set H : ℝ := ∑ i ∈ Finset.range S.card, 1 / ((i : ℝ) + 1) with hH
  have hHle : H ≤ 1 + Real.log (S.card : ℝ) := by
    rw [hH, ← sum_Icc_one_div_eq_sum_range]
    exact sum_Icc_one_div_le_one_add_log S.card
  have hfac1 : Ttot * (1284 * (D ^ 2 / (N : ℝ))) ^ 2 / V ^ 4
      = 1648656 * Ttot * D ^ 4 / ((N : ℝ) ^ 2 * V ^ 4) := by
    field_simp
    ring
  have hfac2 : 2 * (D ^ 2 / (N : ℝ)) * ((N : ℝ) + (12 * Real.pi * (N : ℝ) / delta) * H)
      = 2 * D ^ 2 * (1 + 12 * Real.pi * H / delta) := by
    field_simp
  rw [hfac1, hfac2]
  have hnum : (0 : ℝ) ≤ 1648656 * Ttot * D ^ 4 :=
    mul_nonneg (mul_nonneg (by norm_num) hTtot) (by positivity)
  have hpos1 : (0 : ℝ) ≤ 1648656 * Ttot * D ^ 4 / ((N : ℝ) ^ 2 * V ^ 4) + 1 := by
    have hq : (0 : ℝ) ≤ 1648656 * Ttot * D ^ 4 / ((N : ℝ) ^ 2 * V ^ 4) :=
      div_nonneg hnum (by positivity)
    linarith
  refine mul_le_mul_of_nonneg_left ?_ hpos1
  have hstep : 12 * Real.pi * H / delta
      ≤ 12 * Real.pi * (1 + Real.log (S.card : ℝ)) / delta :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hHle (by positivity)) hdelta.le
  have hD2 : (0 : ℝ) ≤ 2 * D ^ 2 := by positivity
  nlinarith [hstep, hD2]

end RHTower.Sieve
