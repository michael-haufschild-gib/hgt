import GaloisForLFunctions.RHTower.DigammaVerticalMinimum

/-!
# Logarithmic growth of the digamma real part on a vertical line

Every Gauss summand of `psi(a + iy)` has real part

`1/(n+1) - (a+n)/((a+n)^2 + y^2)`,

which is at least `1/(n+1) - 1/(a+n)` for every height and at least `1/(n+1) - 1/(M+a)` once the
height exceeds `M + a` and the index is below `M`.  Summing the first `M` terms against the harmonic
lower bound `log(M+1)` and the tail against the absolutely convergent defect series gives the
archimedean coercivity

`Re psi(a + iy) >= log(2 + |y|) - C`

with an explicit constant, uniformly in the height.  This is the confining potential of the
completed source: the archimedean rate grows logarithmically.
-/

open Complex Filter

noncomputable section

namespace RHTower

/-- The Gauss-series defect weight: the loss of a summand at zero height. -/
def digammaGaussDefect (a : ℝ) (n : ℕ) : ℝ := 1 / (a + n) - 1 / ((n : ℝ) + 1)

theorem digammaGaussDefect_nonneg {a : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1) (n : ℕ) :
    0 ≤ digammaGaussDefect a n := by
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have h1 : (0 : ℝ) < a + n := by linarith
  have h2 : (0 : ℝ) < (n : ℝ) + 1 := by linarith
  rw [digammaGaussDefect, sub_nonneg]
  refine one_div_le_one_div_of_le h1 ?_
  linarith

theorem digammaGaussDefect_eq {a : ℝ} (ha0 : 0 < a) (n : ℕ) :
    digammaGaussDefect a n = (1 - a) / ((a + n) * ((n : ℝ) + 1)) := by
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have h1 : (a + (n : ℝ)) ≠ 0 := by positivity
  have h2 : ((n : ℝ) + 1) ≠ 0 := by positivity
  rw [digammaGaussDefect, div_sub_div 1 1 h1 h2]
  congr 1
  ring

theorem summable_digammaGaussDefect {a : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1) :
    Summable (digammaGaussDefect a) := by
  have h0 : Summable fun n : ℕ => 1 / ((n : ℝ)) ^ 2 :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  have hshift : Summable fun n : ℕ => 1 / (((n : ℝ) + 1)) ^ 2 := by
    have h := (summable_nat_add_iff 1).2 h0
    refine h.congr fun n => ?_
    push_cast
    ring
  refine Summable.of_nonneg_of_le (fun n => digammaGaussDefect_nonneg ha0 ha1 n) (fun n => ?_)
    (hshift.mul_left (1 / a))
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have h1 : (0 : ℝ) < a + n := by linarith
  have h2 : (0 : ℝ) < (n : ℝ) + 1 := by linarith
  rw [digammaGaussDefect_eq ha0]
  have hden : a * ((n : ℝ) + 1) ^ 2 ≤ (a + n) * ((n : ℝ) + 1) := by
    nlinarith [mul_nonneg (mul_nonneg h2.le hn) (sub_nonneg.2 ha1), hn, ha0, ha1]
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < (a + n) * ((n : ℝ) + 1))]
  have hval : 1 / a * (1 / (((n : ℝ) + 1)) ^ 2) * ((a + n) * ((n : ℝ) + 1))
      = (a + n) * ((n : ℝ) + 1) / (a * ((n : ℝ) + 1) ^ 2) := by
    field_simp
  rw [hval]
  have hone : (1 : ℝ) ≤ (a + n) * ((n : ℝ) + 1) / (a * ((n : ℝ) + 1) ^ 2) := by
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < a * ((n : ℝ) + 1) ^ 2)]
    linarith [hden]
  linarith [hone, ha1]

/-- The total Gauss defect. -/
def digammaGaussDefectTotal (a : ℝ) : ℝ := ∑' n : ℕ, digammaGaussDefect a n

theorem digammaGaussDefectTotal_nonneg {a : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1) :
    0 ≤ digammaGaussDefectTotal a :=
  tsum_nonneg fun n => digammaGaussDefect_nonneg ha0 ha1 n

/-- **The harmonic sum dominates the logarithm.** -/
theorem log_le_harmonic (M : ℕ) :
    Real.log ((M : ℝ) + 1) ≤ ∑ n ∈ Finset.range M, 1 / ((n : ℝ) + 1) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Finset.sum_range_succ]
    have hM : (0 : ℝ) < (M : ℝ) + 1 := by positivity
    have hstep : Real.log ((M : ℝ) + 2) - Real.log ((M : ℝ) + 1) ≤ 1 / ((M : ℝ) + 1) := by
      have hdiv : Real.log ((M : ℝ) + 2) - Real.log ((M : ℝ) + 1)
          = Real.log (((M : ℝ) + 2) / ((M : ℝ) + 1)) := by
        rw [Real.log_div (by positivity) (by positivity)]
      rw [hdiv]
      have hle := Real.log_le_sub_one_of_pos
        (show (0 : ℝ) < ((M : ℝ) + 2) / ((M : ℝ) + 1) by positivity)
      have hval : ((M : ℝ) + 2) / ((M : ℝ) + 1) - 1 = 1 / ((M : ℝ) + 1) := by
        field_simp
        ring
      linarith [hle, hval.le, hval.ge]
    have hcast : ((M + 1 : ℕ) : ℝ) + 1 = (M : ℝ) + 2 := by push_cast; ring
    rw [hcast]
    linarith [ih, hstep]

/-- The real part of a Gauss summand on a vertical line. -/
theorem re_gaussDigammaSeriesTerm_vertical (a y : ℝ) (n : ℕ) :
    (gaussDigammaSeriesTerm
        ((a : ℂ) + (y : ℂ) * Complex.I) n).re
      = 1 / ((n : ℝ) + 1) - (a + n) / ((a + n) ^ 2 + y ^ 2) := by
  rw [gaussDigammaSeriesTerm, Complex.sub_re]
  have h1 : ((1 : ℂ) / ((n : ℂ) + 1)).re = 1 / ((n : ℝ) + 1) := by
    rw [show ((n : ℂ) + 1) = (((n : ℝ) + 1 : ℝ) : ℂ) by push_cast; ring,
      show (1 : ℂ) = ((1 : ℝ) : ℂ) by norm_num, ← Complex.ofReal_div, Complex.ofReal_re]
  have hshift : ((a : ℂ) + (y : ℂ) * Complex.I + (n : ℂ))
      = (((a + n : ℝ)) : ℂ) + ((y : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  have h2 : ((1 : ℂ) / ((a : ℂ) + (y : ℂ) * Complex.I + (n : ℂ))).re
      = (a + n) / ((a + n) ^ 2 + y ^ 2) := by
    rw [hshift, one_div, Complex.inv_re, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero, mul_one,
      sub_zero, zero_add, add_zero]
    ring
  rw [h1, h2]


/-! ## The coercivity constant and the logarithmic lower bound -/

/-- The archimedean coercivity constant of the vertical digamma line. -/
def digammaVerticalCoercivityConst (a : ℝ) : ℝ :=
  max (Real.log 4 - (Complex.digamma ((a : ℂ))).re)
    (2 * Real.log 2 + 1 + Real.eulerMascheroniConstant + digammaGaussDefectTotal a)

theorem summable_re_gaussDigammaSeriesTerm (s : ℂ) :
    Summable fun n : ℕ => (gaussDigammaSeriesTerm s n).re := by
  have hsum : Summable fun n : ℕ => gaussDigammaSeriesTerm s n :=
    summable_norm_iff.mp
      (GaloisForLFunctions.HTGeometry.summable_norm_gaussDigammaSeriesTerm_all s)
  exact (Complex.hasSum_re hsum.hasSum).summable

theorem re_digamma_vertical_eq {a : ℝ} (ha0 : 0 < a) (y : ℝ) :
    (Complex.digamma ((a : ℂ) + (y : ℂ) * Complex.I)).re
      = -Real.eulerMascheroniConstant
        + ∑' n : ℕ, (gaussDigammaSeriesTerm ((a : ℂ) + (y : ℂ) * Complex.I) n).re := by
  have hre : ((a : ℂ) + (y : ℂ) * Complex.I).re = a := by
    simp [Complex.add_re, Complex.mul_re]
  have hsum : Summable fun n : ℕ =>
      gaussDigammaSeriesTerm ((a : ℂ) + (y : ℂ) * Complex.I) n :=
    summable_norm_iff.mp
      (GaloisForLFunctions.HTGeometry.summable_norm_gaussDigammaSeriesTerm_all _)
  rw [digamma_eq_neg_euler_add_tsum_gauss
    (s := (a : ℂ) + (y : ℂ) * Complex.I) (by rw [hre]; exact ha0), Complex.add_re,
    Complex.re_tsum hsum]
  congr 1

/-- Each Gauss summand is at least minus the defect weight, at every height. -/
theorem neg_digammaGaussDefect_le_re_gaussDigammaSeriesTerm {a : ℝ} (ha0 : 0 < a) (y : ℝ)
    (n : ℕ) :
    -digammaGaussDefect a n
      ≤ (gaussDigammaSeriesTerm ((a : ℂ) + (y : ℂ) * Complex.I) n).re := by
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have h1 : (0 : ℝ) < a + n := by linarith
  rw [re_gaussDigammaSeriesTerm_vertical, digammaGaussDefect]
  have hle : (a + n) / ((a + n) ^ 2 + y ^ 2) ≤ 1 / (a + n) := by
    rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < (a + n) ^ 2 + y ^ 2) h1]
    nlinarith [sq_nonneg y]
  linarith

/-- The Gauss tail beyond an index is bounded below by minus the total defect. -/
theorem neg_digammaGaussDefectTotal_le_tsum_tail {a : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1) (y : ℝ)
    (M : ℕ) :
    -digammaGaussDefectTotal a
      ≤ ∑' i : ℕ, (gaussDigammaSeriesTerm ((a : ℂ) + (y : ℂ) * Complex.I) (i + M)).re := by
  have hD := summable_digammaGaussDefect ha0 ha1
  have hDtail : Summable fun i : ℕ => digammaGaussDefect a (i + M) :=
    (summable_nat_add_iff M).2 hD
  have hTtail : Summable fun i : ℕ =>
      (gaussDigammaSeriesTerm ((a : ℂ) + (y : ℂ) * Complex.I) (i + M)).re :=
    (summable_nat_add_iff M).2 (summable_re_gaussDigammaSeriesTerm _)
  have hcmp : ∑' i : ℕ, (-digammaGaussDefect a (i + M))
      ≤ ∑' i : ℕ, (gaussDigammaSeriesTerm ((a : ℂ) + (y : ℂ) * Complex.I) (i + M)).re :=
    hDtail.neg.tsum_le_tsum
      (fun i => neg_digammaGaussDefect_le_re_gaussDigammaSeriesTerm ha0 y (i + M)) hTtail
  have hneg : ∑' i : ℕ, (-digammaGaussDefect a (i + M))
      = -∑' i : ℕ, digammaGaussDefect a (i + M) := tsum_neg
  have hsplit : ∑ i ∈ Finset.range M, digammaGaussDefect a i
      + ∑' i : ℕ, digammaGaussDefect a (i + M) = digammaGaussDefectTotal a :=
    hD.sum_add_tsum_nat_add M
  have hpre : 0 ≤ ∑ i ∈ Finset.range M, digammaGaussDefect a i :=
    Finset.sum_nonneg fun i _ => digammaGaussDefect_nonneg ha0 ha1 i
  rw [hneg] at hcmp
  linarith [hcmp, hsplit, hpre]

/-- **(CSHC.7) Archimedean coercivity.**  The real part of digamma on a vertical line grows at least
logarithmically in the height, with an explicit constant. -/
theorem re_digamma_vertical_ge {a : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1) (y : ℝ) :
    Real.log (2 + |y|) - digammaVerticalCoercivityConst a
      ≤ (Complex.digamma ((a : ℂ) + (y : ℂ) * Complex.I)).re := by
  rcases le_or_gt |y| 2 with hy | hy
  · have hlow : (Complex.digamma ((a : ℂ))).re
        ≤ (Complex.digamma ((a : ℂ) + (y : ℂ) * Complex.I)).re :=
      digamma_real_le_re_digamma_add_mul_I ha0 y
    have hlog : Real.log (2 + |y|) ≤ Real.log 4 := by
      refine Real.log_le_log (by positivity) ?_
      linarith
    have hC : Real.log 4 - (Complex.digamma ((a : ℂ))).re ≤ digammaVerticalCoercivityConst a :=
      le_max_left _ _
    linarith
  · -- large height: the first `M` Gauss terms give the logarithm
    have hy0 : (0 : ℝ) < |y| := by linarith
    have hfloor2 : 2 ≤ Nat.floor |y| := by
      have := Nat.le_floor (show ((2 : ℕ) : ℝ) ≤ |y| by push_cast; linarith)
      exact this
    obtain ⟨M, hM⟩ : ∃ M : ℕ, Nat.floor |y| = M + 1 := ⟨Nat.floor |y| - 1, by omega⟩
    have hM1 : 1 ≤ M := by omega
    have hMle : ((M : ℝ) + 1) ≤ |y| := by
      have := Nat.floor_le (le_of_lt hy0)
      rw [hM] at this
      push_cast at this
      linarith
    have hMa : (M : ℝ) + a ≤ |y| := by linarith
    have hMy : (M : ℝ) ≤ |y| := by
      have : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
      linarith
    have hfloorlt : |y| - 1 < ((M : ℝ) + 1) := by
      have := Nat.lt_floor_add_one |y|
      rw [hM] at this
      push_cast at this
      linarith
    -- the head sum
    have hhead : Real.log ((M : ℝ) + 1) - 1
        ≤ ∑ n ∈ Finset.range M,
            (gaussDigammaSeriesTerm ((a : ℂ) + (y : ℂ) * Complex.I) n).re := by
      have hterm : ∀ n ∈ Finset.range M,
          1 / ((n : ℝ) + 1) - ((M : ℝ) + a) / y ^ 2
            ≤ (gaussDigammaSeriesTerm ((a : ℂ) + (y : ℂ) * Complex.I) n).re := by
        intro n hn
        simp only [Finset.mem_range] at hn
        have hnc : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        have hnM : (n : ℝ) ≤ (M : ℝ) := by exact_mod_cast Nat.le_of_lt hn
        have hy2 : (0 : ℝ) < y ^ 2 := by
          have : y ^ 2 = |y| ^ 2 := (sq_abs y).symm
          rw [this]
          positivity
        rw [re_gaussDigammaSeriesTerm_vertical]
        have hb1 : (a + n) / ((a + n) ^ 2 + y ^ 2) ≤ (a + n) / y ^ 2 :=
          div_le_div_of_nonneg_left (by linarith) hy2 (by nlinarith [sq_nonneg (a + n)])
        have hb2 : (a + n) / y ^ 2 ≤ ((M : ℝ) + a) / y ^ 2 := by
          rw [div_le_div_iff₀ hy2 hy2]
          nlinarith [hnM, hy2]
        linarith [hb1, hb2]
      refine le_trans ?_ (Finset.sum_le_sum hterm)
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      have hharm := log_le_harmonic M
      have hy2 : (0 : ℝ) < y ^ 2 := by
        have : y ^ 2 = |y| ^ 2 := (sq_abs y).symm
        rw [this]
        positivity
      have hsmall : (M : ℝ) * (((M : ℝ) + a) / y ^ 2) ≤ 1 := by
        rw [mul_div_assoc'] at *
        rw [div_le_one hy2]
        have hy2eq : y ^ 2 = |y| * |y| := by
          rw [← sq_abs y]
          ring
        rw [hy2eq]
        have hM0 : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
        nlinarith [hMy, hMa, hM0, hy0]
      linarith
    -- assemble
    have hsplit : ∑ n ∈ Finset.range M,
          (gaussDigammaSeriesTerm ((a : ℂ) + (y : ℂ) * Complex.I) n).re
        + ∑' i : ℕ, (gaussDigammaSeriesTerm ((a : ℂ) + (y : ℂ) * Complex.I) (i + M)).re
        = ∑' n : ℕ, (gaussDigammaSeriesTerm ((a : ℂ) + (y : ℂ) * Complex.I) n).re :=
      (summable_re_gaussDigammaSeriesTerm _).sum_add_tsum_nat_add M
    have htail := neg_digammaGaussDefectTotal_le_tsum_tail ha0 ha1 y M
    have hpsi := re_digamma_vertical_eq ha0 y
    -- the logarithm comparison
    have hlogcmp : Real.log (2 + |y|) - 2 * Real.log 2 ≤ Real.log ((M : ℝ) + 1) := by
      have h1 : (2 : ℝ) + |y| ≤ 4 * ((M : ℝ) + 1) := by linarith
      have h2 : Real.log (2 + |y|) ≤ Real.log (4 * ((M : ℝ) + 1)) :=
        Real.log_le_log (by positivity) h1
      have h3 : Real.log (4 * ((M : ℝ) + 1))
          = Real.log 4 + Real.log ((M : ℝ) + 1) := by
        rw [Real.log_mul (by norm_num) (by positivity)]
      have h4 : Real.log 4 = 2 * Real.log 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
        push_cast
        ring
      rw [h3, h4] at h2
      linarith
    have hC : 2 * Real.log 2 + 1 + Real.eulerMascheroniConstant + digammaGaussDefectTotal a
        ≤ digammaVerticalCoercivityConst a := le_max_right _ _
    rw [hpsi]
    linarith [hhead, htail, hsplit, hlogcmp, hC]

end RHTower

end
