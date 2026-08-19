import Mathlib

/-!
# Connes--van Suijlekom, Appendix A: literal truncation matrix

This module records the exact bi-infinite matrix `μ` displayed in Lemma A.1
of arXiv:2511.23257v1, on the source Fourier index set `ℤ`.  The remaining
analytic task is to identify this concrete matrix with the quadratic form of
the paper's distribution `δ₀ + 2π b sin(2πx)`.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open MeasureTheory intervalIntegral
open scoped Convolution

/-- The `b`-independent matrix `μ` of Appendix A, Lemma A.1. -/
def connesVanSuijlekomA1Mu (n m : ℤ) : ℝ :=
  if n = -1 then
    if m = -1 then 1 / 2 else if m = 0 then -1 else if m = 1 then -1 else 1 / (-1 - m)
  else if n = 0 then
    if m = -1 then -1 else if m = 0 then 2 else if m = 1 then -1 else 0
  else if n = 1 then
    if m = -1 then -1 else if m = 0 then -1 else if m = 1 then 1 / 2 else 1 / (-1 + m)
  else if m = -1 then 1 / (-1 - n)
  else if m = 1 then 1 / (-1 + n)
  else if n = m then 2 / (1 - (n : ℝ) ^ 2)
  else 0

/-- The matrix-element formula claimed for the quadratic form in Lemma A.1. -/
def connesVanSuijlekomA1QEntry (b : ℝ) (n m : ℤ) : ℝ :=
  2 * (if n = m then 1 else 0) + b * connesVanSuijlekomA1Mu n m

/-- Literal formula of Appendix A, Lemma A.1, once the paper's analytic
quadratic form has been identified with `connesVanSuijlekomA1QEntry`. -/
theorem connesVanSuijlekomA1_qEntry_eq (b : ℝ) (n m : ℤ) :
    connesVanSuijlekomA1QEntry b n m =
      2 * (if n = m then 1 else 0) + b * connesVanSuijlekomA1Mu n m := rfl

theorem connesVanSuijlekomA1_mu_center_block :
    (fun i j : Fin 3 => connesVanSuijlekomA1Mu ((i : ℤ) - 1) ((j : ℤ) - 1)) =
      !![(1 / 2 : ℝ), -1, -1;
         -1, 2, -1;
         -1, -1, (1 / 2 : ℝ)] := by
  funext i j
  fin_cases i <;> fin_cases j <;> norm_num [connesVanSuijlekomA1Mu]

theorem connesVanSuijlekomA1_mu_off_special_zero
    {n m : ℤ} (hn : n ≠ -1) (hn0 : n ≠ 0) (hn1 : n ≠ 1)
    (hm : m ≠ -1) (_hm0 : m ≠ 0) (hm1 : m ≠ 1) (hnm : n ≠ m) :
    connesVanSuijlekomA1Mu n m = 0 := by
  simp [connesVanSuijlekomA1Mu, hn, hn0, hn1, hm, hm1, hnm]

theorem connesVanSuijlekomA1_mu_diag
    {n : ℤ} (hn : n ≠ -1) (hn0 : n ≠ 0) (hn1 : n ≠ 1) :
    connesVanSuijlekomA1Mu n n = 2 / (1 - (n : ℝ) ^ 2) := by
  simp [connesVanSuijlekomA1Mu, hn, hn0, hn1]

theorem connesVanSuijlekomA1_mu_right_neg_one
    {n : ℤ} (hn : n ≠ -1) (hn0 : n ≠ 0) (hn1 : n ≠ 1) :
    connesVanSuijlekomA1Mu n (-1) = 1 / (-1 - n) := by
  simp [connesVanSuijlekomA1Mu, hn, hn0, hn1]

theorem connesVanSuijlekomA1_mu_right_one
    {n : ℤ} (hn : n ≠ -1) (hn0 : n ≠ 0) (hn1 : n ≠ 1) :
    connesVanSuijlekomA1Mu n 1 = 1 / (-1 + n) := by
  simp [connesVanSuijlekomA1Mu, hn, hn0, hn1]

/-- The diagonal operator in Lemma A.2(i), at the matrix-entry level. -/
def connesVanSuijlekomA2Diagonal (n : ℤ) : ℝ :=
  if n = -1 then 1 / 2 else if n = 1 then 1 / 2 else 2 / (1 - (n : ℝ) ^ 2)

/-- The vector `ξ` of Lemma A.2(i), at the level of Fourier coefficients. -/
def connesVanSuijlekomA2Xi (n : ℤ) : ℝ :=
  if n = -1 then 0 else 1 / (1 + n)

/-- The vector `η` of Lemma A.2(i), at the level of Fourier coefficients. -/
def connesVanSuijlekomA2Eta (n : ℤ) : ℝ :=
  if n = 1 then 0 else 1 / (-1 + n)

/-- Matrix entries of the rank-four correction in Lemma A.2(i). -/
def connesVanSuijlekomA2RankFour (n m : ℤ) : ℝ :=
    connesVanSuijlekomA2Eta n * (if m = 1 then 1 else 0)
  + (if n = 1 then 1 else 0) * connesVanSuijlekomA2Eta m
  - connesVanSuijlekomA2Xi n * (if m = -1 then 1 else 0)
  - (if n = -1 then 1 else 0) * connesVanSuijlekomA2Xi m

/-- Kronecker-delta notation for matrix entries. -/
def connesVanSuijlekomA2Delta (n m : ℤ) : ℝ := if n = m then 1 else 0

theorem connesVanSuijlekomA2_diagonal_eq_source (n : ℤ) :
    connesVanSuijlekomA2Diagonal n =
      if n ^ 2 = 1 then 1 / 2 else 2 / (1 - (n : ℝ) ^ 2) := by
  by_cases hn : n = -1
  · subst n
    norm_num [connesVanSuijlekomA2Diagonal]
  by_cases hn1 : n = 1
  · subst n
    norm_num [connesVanSuijlekomA2Diagonal]
  rw [connesVanSuijlekomA2Diagonal, if_neg hn, if_neg hn1]
  have hs : n ^ 2 ≠ 1 := by
    intro h
    have : n = 1 ∨ n = -1 := by
      exact (sq_eq_one_iff).mp h
    rcases this with h | h <;> contradiction
  rw [if_neg hs]

theorem connesVanSuijlekomA2_neg_xi (m : ℤ) :
    1 / (-1 - (m : ℝ)) = - (1 / (1 + (m : ℝ))) := by
  simp only [one_div]
  rw [show (-1 - (m : ℝ)) = -(1 + (m : ℝ)) by ring]
  exact inv_neg

theorem connesVanSuijlekomA2_rankFour_off_special
    {n m : ℤ} (hn : n ≠ -1) (hn1 : n ≠ 1) (hm : m ≠ -1) (hm1 : m ≠ 1) :
    connesVanSuijlekomA2RankFour n m = 0 := by
  simp [connesVanSuijlekomA2RankFour, hn, hn1, hm, hm1]

/-- Lemma A.2(i), exactly as an identity of the source's bi-infinite matrix
entries.  The Hilbert-space operator realization is deliberately kept
separate from this closed algebraic statement. -/
theorem connesVanSuijlekomA2_mu_eq_diagonal_add_rankFour (n m : ℤ) :
    connesVanSuijlekomA1Mu n m =
      connesVanSuijlekomA2Diagonal n * connesVanSuijlekomA2Delta n m
        + connesVanSuijlekomA2RankFour n m := by
  by_cases hn : n = -1
  · subst n
    by_cases hm : m = -1
    · subst m
      norm_num [connesVanSuijlekomA1Mu, connesVanSuijlekomA2Diagonal,
        connesVanSuijlekomA2Delta, connesVanSuijlekomA2RankFour,
        connesVanSuijlekomA2Xi, connesVanSuijlekomA2Eta]
    by_cases hm0 : m = 0
    · subst m
      clear hm
      norm_num [connesVanSuijlekomA1Mu, connesVanSuijlekomA2Diagonal,
        connesVanSuijlekomA2Delta, connesVanSuijlekomA2RankFour,
        connesVanSuijlekomA2Xi, connesVanSuijlekomA2Eta]
    by_cases hm1 : m = 1
    · subst m
      clear hm hm0
      norm_num [connesVanSuijlekomA1Mu, connesVanSuijlekomA2Diagonal,
        connesVanSuijlekomA2Delta, connesVanSuijlekomA2RankFour,
        connesVanSuijlekomA2Xi, connesVanSuijlekomA2Eta]
    have hm' : (-1 : ℤ) ≠ m := Ne.symm hm
    simp [connesVanSuijlekomA1Mu, connesVanSuijlekomA2Diagonal,
      connesVanSuijlekomA2Delta, connesVanSuijlekomA2RankFour,
      connesVanSuijlekomA2Xi, connesVanSuijlekomA2Eta, hm, hm', hm0, hm1]
    simpa only [one_div] using connesVanSuijlekomA2_neg_xi m
  by_cases hn0 : n = 0
  · subst n
    by_cases hm : m = -1
    · subst m
      clear hn
      norm_num [connesVanSuijlekomA1Mu, connesVanSuijlekomA2Diagonal,
        connesVanSuijlekomA2Delta, connesVanSuijlekomA2RankFour,
        connesVanSuijlekomA2Xi, connesVanSuijlekomA2Eta]
    by_cases hm0 : m = 0
    · subst m
      norm_num [connesVanSuijlekomA1Mu, connesVanSuijlekomA2Diagonal,
        connesVanSuijlekomA2Delta, connesVanSuijlekomA2RankFour,
        connesVanSuijlekomA2Xi, connesVanSuijlekomA2Eta]
    by_cases hm1 : m = 1
    · subst m
      clear hn hm hm0
      norm_num [connesVanSuijlekomA1Mu, connesVanSuijlekomA2Diagonal,
        connesVanSuijlekomA2Delta, connesVanSuijlekomA2RankFour,
        connesVanSuijlekomA2Xi, connesVanSuijlekomA2Eta]
    have hm0' : (0 : ℤ) ≠ m := Ne.symm hm0
    simp [connesVanSuijlekomA1Mu, connesVanSuijlekomA2Diagonal,
      connesVanSuijlekomA2Delta, connesVanSuijlekomA2RankFour,
      connesVanSuijlekomA2Xi, connesVanSuijlekomA2Eta, hm, hm0, hm0', hm1]
  by_cases hn1 : n = 1
  · subst n
    by_cases hm : m = -1
    · subst m
      clear hn hn0
      norm_num [connesVanSuijlekomA1Mu, connesVanSuijlekomA2Diagonal,
        connesVanSuijlekomA2Delta, connesVanSuijlekomA2RankFour,
        connesVanSuijlekomA2Xi, connesVanSuijlekomA2Eta]
    by_cases hm0 : m = 0
    · subst m
      clear hn hn0 hm
      norm_num [connesVanSuijlekomA1Mu, connesVanSuijlekomA2Diagonal,
        connesVanSuijlekomA2Delta, connesVanSuijlekomA2RankFour,
        connesVanSuijlekomA2Xi, connesVanSuijlekomA2Eta]
    by_cases hm1 : m = 1
    · subst m
      norm_num [connesVanSuijlekomA1Mu, connesVanSuijlekomA2Diagonal,
        connesVanSuijlekomA2Delta, connesVanSuijlekomA2RankFour,
        connesVanSuijlekomA2Xi, connesVanSuijlekomA2Eta]
    have hm1' : (1 : ℤ) ≠ m := Ne.symm hm1
    simp [connesVanSuijlekomA1Mu, connesVanSuijlekomA2Diagonal,
      connesVanSuijlekomA2Delta, connesVanSuijlekomA2RankFour,
      connesVanSuijlekomA2Xi, connesVanSuijlekomA2Eta, hm, hm0, hm1, hm1']
  by_cases hm : m = -1
  · subst m
    simp [connesVanSuijlekomA1Mu, connesVanSuijlekomA2Diagonal,
      connesVanSuijlekomA2Delta, connesVanSuijlekomA2RankFour,
      connesVanSuijlekomA2Xi, connesVanSuijlekomA2Eta, hn, hn0, hn1]
    simpa only [one_div] using connesVanSuijlekomA2_neg_xi n
  by_cases hm1 : m = 1
  · subst m
    simp [connesVanSuijlekomA1Mu, connesVanSuijlekomA2Diagonal,
      connesVanSuijlekomA2Delta, connesVanSuijlekomA2RankFour,
      connesVanSuijlekomA2Xi, connesVanSuijlekomA2Eta, hn, hn0, hn1]
  by_cases hnm : n = m
  · subst m
    simp [connesVanSuijlekomA1Mu, connesVanSuijlekomA2Diagonal,
      connesVanSuijlekomA2Delta, connesVanSuijlekomA2RankFour,
      connesVanSuijlekomA2Xi, connesVanSuijlekomA2Eta, hn, hn0, hn1]
  simp [connesVanSuijlekomA1Mu, connesVanSuijlekomA2Diagonal,
    connesVanSuijlekomA2Delta, connesVanSuijlekomA2RankFour,
    connesVanSuijlekomA2Xi, connesVanSuijlekomA2Eta, hn, hn0, hn1, hm, hm1, hnm]

/-- The `n = 0` instance of the Fourier-coefficient calculation in the proof
of Lemma A.2(ii). -/
theorem connesVanSuijlekomA2_fourier_coefficient_zero :
    2 * Real.pi *
      (∫ x in (0 : ℝ)..1, (x - 1 / 2) * Real.sin (2 * Real.pi * x)) = -1 := by
  let F : ℝ → ℝ := fun x =>
    -(x - 1 / 2) * Real.cos (2 * Real.pi * x) / (2 * Real.pi)
      + Real.sin (2 * Real.pi * x) / (4 * Real.pi ^ 2)
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  have hF : ∀ x : ℝ,
      HasDerivAt (𝕜 := ℝ) F ((x - 1 / 2) * Real.sin (2 * Real.pi * x)) x := by
    intro x
    dsimp [F]
    have harg : HasDerivAt (𝕜 := ℝ) (fun y : ℝ => 2 * Real.pi * y) (2 * Real.pi) x := by
      exact hasDerivAt_const_mul (2 * Real.pi)
    have hc : HasDerivAt (𝕜 := ℝ) (fun y : ℝ => Real.cos (2 * Real.pi * y))
        (-Real.sin (2 * Real.pi * x) * (2 * Real.pi)) x := by
      convert! (Real.hasDerivAt_cos (2 * Real.pi * x)).comp x harg using 1
    have hs : HasDerivAt (𝕜 := ℝ) (fun y : ℝ => Real.sin (2 * Real.pi * y))
        (Real.cos (2 * Real.pi * x) * (2 * Real.pi)) x := by
      convert! (Real.hasDerivAt_sin (2 * Real.pi * x)).comp x harg using 1
    have h1 : HasDerivAt (𝕜 := ℝ) (fun y : ℝ =>
        -(y - 1 / 2) * Real.cos (2 * Real.pi * y))
        (-Real.cos (2 * Real.pi * x) +
          (x - 1 / 2) * Real.sin (2 * Real.pi * x) * (2 * Real.pi)) x := by
      convert! (((hasDerivAt_id (𝕜 := ℝ) x).sub_const (1 / 2)).neg.mul hc) using 1
      simp only [Pi.neg_apply, id_eq]
      ring
    have hsum := (h1.div_const (2 * Real.pi)).add (hs.div_const (4 * Real.pi ^ 2))
    convert! hsum using 1
    field_simp [hpi]
    ring
  have hInt :
      (∫ x in (0 : ℝ)..1, (x - 1 / 2) * Real.sin (2 * Real.pi * x)) = F 1 - F 0 := by
    apply integral_eq_sub_of_hasDerivAt
    · intro x _
      exact hF x
    · have hCont : Continuous (fun y : ℝ =>
          (y - 1 / 2) * Real.sin (2 * Real.pi * y)) := by
        fun_prop
      exact hCont.intervalIntegrable 0 1
  rw [hInt]
  dsimp [F]
  simp only [mul_one, mul_zero, Real.sin_two_pi, Real.cos_two_pi, Real.sin_zero,
    Real.cos_zero]
  field_simp [hpi]
  ring

/-- A closed antiderivative calculation used for the integral evaluations in
Lemma A.2(ii). -/
theorem connesVanSuijlekomA2_weighted_sin_integral
    (κ : ℝ) (hκ : κ ≠ 0) (hsin : Real.sin κ = 0) (hcos : Real.cos κ = 1) :
    κ * (∫ x in (0 : ℝ)..1, (x - 1 / 2) * Real.sin (κ * x)) = -1 := by
  let F : ℝ → ℝ := fun x =>
    -(x - 1 / 2) * Real.cos (κ * x) / κ + Real.sin (κ * x) / κ ^ 2
  have hF : ∀ x : ℝ,
      HasDerivAt (𝕜 := ℝ) F ((x - 1 / 2) * Real.sin (κ * x)) x := by
    intro x
    dsimp [F]
    have harg : HasDerivAt (𝕜 := ℝ) (fun y : ℝ => κ * y) κ x := by
      exact hasDerivAt_const_mul κ
    have hc : HasDerivAt (𝕜 := ℝ) (fun y : ℝ => Real.cos (κ * y))
        (-Real.sin (κ * x) * κ) x := by
      convert! (Real.hasDerivAt_cos (κ * x)).comp x harg using 1
    have hs : HasDerivAt (𝕜 := ℝ) (fun y : ℝ => Real.sin (κ * y))
        (Real.cos (κ * x) * κ) x := by
      convert! (Real.hasDerivAt_sin (κ * x)).comp x harg using 1
    have h1 : HasDerivAt (𝕜 := ℝ) (fun y : ℝ =>
        -(y - 1 / 2) * Real.cos (κ * y))
        (-Real.cos (κ * x) + (x - 1 / 2) * Real.sin (κ * x) * κ) x := by
      convert! (((hasDerivAt_id (𝕜 := ℝ) x).sub_const (1 / 2)).neg.mul hc) using 1
      simp only [Pi.neg_apply, id_eq]
      ring
    have hsum := (h1.div_const κ).add (hs.div_const (κ ^ 2))
    convert! hsum using 1
    field_simp [hκ]
    ring
  have hInt :
      (∫ x in (0 : ℝ)..1, (x - 1 / 2) * Real.sin (κ * x)) = F 1 - F 0 := by
    apply integral_eq_sub_of_hasDerivAt
    · intro x _
      exact hF x
    · have hCont : Continuous (fun y : ℝ =>
          (y - 1 / 2) * Real.sin (κ * y)) := by
        fun_prop
      exact hCont.intervalIntegrable 0 1
  rw [hInt]
  dsimp [F]
  simp only [mul_one, mul_zero, Real.sin_zero, Real.cos_zero, hsin, hcos]
  field_simp [hκ]
  ring

/-- The `n = 1` exceptional Fourier coefficient in the proof of Lemma A.2(ii). -/
theorem connesVanSuijlekomA2_fourier_coefficient_one :
    2 * Real.pi *
      (∫ x in (0 : ℝ)..1,
        (x - 1 / 2) * Real.sin (2 * Real.pi * x) * Real.cos (2 * Real.pi * x)) = -1 / 4 := by
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  have hfourpi : (4 : ℝ) * Real.pi ≠ 0 := mul_ne_zero (by norm_num) hpi
  have hsin : Real.sin ((4 : ℝ) * Real.pi) = 0 := by
    convert Real.sin_nat_mul_pi 4 using 1
    norm_num
  have hcos : Real.cos ((4 : ℝ) * Real.pi) = 1 := by
    convert Real.cos_nat_mul_pi 4 using 1 <;> norm_num
  have hwave := connesVanSuijlekomA2_weighted_sin_integral ((4 : ℝ) * Real.pi)
    hfourpi hsin hcos
  have hprod : ∀ x : ℝ,
      Real.sin (2 * Real.pi * x) * Real.cos (2 * Real.pi * x) =
        Real.sin ((4 * Real.pi) * x) / 2 := by
    intro x
    rw [show (4 : ℝ) * Real.pi * x = 2 * (2 * Real.pi * x) by ring, Real.sin_two_mul]
    ring
  have hrewrite :
      (fun x : ℝ => (x - 1 / 2) * Real.sin (2 * Real.pi * x) * Real.cos (2 * Real.pi * x)) =
        fun x => (x - 1 / 2) * (Real.sin (2 * Real.pi * x) * Real.cos (2 * Real.pi * x)) := by
    funext x
    ring
  rw [hrewrite]
  simp_rw [hprod]
  rw [show (2 : ℝ) * Real.pi = ((4 : ℝ) * Real.pi) / 2 by ring]
  have hdiv : (∫ x in (0 : ℝ)..1, (x - 1 / 2) * (Real.sin ((4 * Real.pi) * x) / 2)) =
      (∫ x in (0 : ℝ)..1, (x - 1 / 2) * Real.sin ((4 * Real.pi) * x)) / 2 := by
    rw [show (fun x : ℝ => (x - 1 / 2) * (Real.sin ((4 * Real.pi) * x) / 2)) =
        fun x => ((x - 1 / 2) * Real.sin ((4 * Real.pi) * x)) / 2 by
      funext x
      ring]
    exact intervalIntegral.integral_div 2 _
  rw [hdiv]
  nlinarith

/-- The `n = -1` exceptional Fourier coefficient in the proof of Lemma A.2(ii). -/
theorem connesVanSuijlekomA2_fourier_coefficient_neg_one :
    2 * Real.pi *
      (∫ x in (0 : ℝ)..1,
        (x - 1 / 2) * Real.sin (2 * Real.pi * x) * Real.cos (2 * Real.pi * (-1) * x)) =
      -1 / 4 := by
  rw [show (fun x : ℝ =>
      (x - 1 / 2) * Real.sin (2 * Real.pi * x) * Real.cos (2 * Real.pi * (-1) * x)) =
      fun x => (x - 1 / 2) * Real.sin (2 * Real.pi * x) * Real.cos (2 * Real.pi * x) by
    funext x
    rw [show 2 * Real.pi * (-1 : ℝ) * x = -(2 * Real.pi * x) by ring, Real.cos_neg]]
  exact connesVanSuijlekomA2_fourier_coefficient_one

/-- The non-exceptional integer Fourier coefficient computed in the proof of
Lemma A.2(ii). -/
theorem connesVanSuijlekomA2_fourier_coefficient_of_ne
    (n : ℤ) (hnNeg : n ≠ -1) (hnOne : n ≠ 1) :
    2 * Real.pi *
      (∫ x in (0 : ℝ)..1,
        (x - 1 / 2) * Real.sin (2 * Real.pi * x) * Real.cos (2 * Real.pi * (n : ℝ) * x)) =
      1 / ((n : ℝ) ^ 2 - 1) := by
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  have hplus : (1 : ℤ) + n ≠ 0 := by
    intro h
    apply hnNeg
    omega
  have hminus : (1 : ℤ) - n ≠ 0 := by
    intro h
    apply hnOne
    omega
  have hplusR : 1 + (n : ℝ) ≠ 0 := by exact_mod_cast hplus
  have hminusR : 1 - (n : ℝ) ≠ 0 := by exact_mod_cast hminus
  have hκplus : 2 * Real.pi * (1 + (n : ℝ)) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) hpi) hplusR
  have hκminus : 2 * Real.pi * (1 - (n : ℝ)) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) hpi) hminusR
  have hsplus : Real.sin (2 * Real.pi * (1 + (n : ℝ))) = 0 := by
    rw [show 2 * Real.pi * (1 + (n : ℝ)) = ((1 + n : ℤ) : ℝ) * (2 * Real.pi) by
      push_cast
      ring]
    simpa using Real.sin_add_int_mul_two_pi 0 (1 + n)
  have hcplus : Real.cos (2 * Real.pi * (1 + (n : ℝ))) = 1 := by
    rw [show 2 * Real.pi * (1 + (n : ℝ)) = ((1 + n : ℤ) : ℝ) * (2 * Real.pi) by
      push_cast
      ring]
    exact Real.cos_int_mul_two_pi (1 + n)
  have hsminus : Real.sin (2 * Real.pi * (1 - (n : ℝ))) = 0 := by
    rw [show 2 * Real.pi * (1 - (n : ℝ)) = ((1 - n : ℤ) : ℝ) * (2 * Real.pi) by
      push_cast
      ring]
    simpa using Real.sin_add_int_mul_two_pi 0 (1 - n)
  have hcminus : Real.cos (2 * Real.pi * (1 - (n : ℝ))) = 1 := by
    rw [show 2 * Real.pi * (1 - (n : ℝ)) = ((1 - n : ℤ) : ℝ) * (2 * Real.pi) by
      push_cast
      ring]
    exact Real.cos_int_mul_two_pi (1 - n)
  have hwavePlus := connesVanSuijlekomA2_weighted_sin_integral
    (2 * Real.pi * (1 + (n : ℝ))) hκplus hsplus hcplus
  have hwaveMinus := connesVanSuijlekomA2_weighted_sin_integral
    (2 * Real.pi * (1 - (n : ℝ))) hκminus hsminus hcminus
  have hIplus :
      (∫ x in (0 : ℝ)..1, (x - 1 / 2) * Real.sin ((2 * Real.pi * (1 + (n : ℝ))) * x)) =
      -1 / (2 * Real.pi * (1 + (n : ℝ))) := by
    apply (eq_div_iff hκplus).2
    nlinarith [hwavePlus]
  have hIminus :
      (∫ x in (0 : ℝ)..1, (x - 1 / 2) * Real.sin ((2 * Real.pi * (1 - (n : ℝ))) * x)) =
      -1 / (2 * Real.pi * (1 - (n : ℝ))) := by
    apply (eq_div_iff hκminus).2
    nlinarith [hwaveMinus]
  have hprod : ∀ x : ℝ,
      Real.sin (2 * Real.pi * x) * Real.cos (2 * Real.pi * (n : ℝ) * x) =
        (Real.sin ((2 * Real.pi * (1 + (n : ℝ))) * x) +
          Real.sin ((2 * Real.pi * (1 - (n : ℝ))) * x)) / 2 := by
    intro x
    rw [show (2 * Real.pi * (1 + (n : ℝ))) * x =
        2 * Real.pi * x + 2 * Real.pi * (n : ℝ) * x by ring,
      show (2 * Real.pi * (1 - (n : ℝ))) * x =
        2 * Real.pi * x - 2 * Real.pi * (n : ℝ) * x by ring,
      Real.sin_add, Real.sin_sub]
    ring
  have hrewrite :
      (fun x : ℝ =>
        (x - 1 / 2) * Real.sin (2 * Real.pi * x) * Real.cos (2 * Real.pi * (n : ℝ) * x)) =
      fun x => (x - 1 / 2) *
        (Real.sin (2 * Real.pi * x) * Real.cos (2 * Real.pi * (n : ℝ) * x)) := by
    funext x
    ring
  rw [hrewrite]
  simp_rw [hprod]
  have hsplit :
      (∫ x in (0 : ℝ)..1, (x - 1 / 2) *
        (Real.sin ((2 * Real.pi * (1 + (n : ℝ))) * x) +
          Real.sin ((2 * Real.pi * (1 - (n : ℝ))) * x)) / 2) =
      ((∫ x in (0 : ℝ)..1, (x - 1 / 2) * Real.sin ((2 * Real.pi * (1 + (n : ℝ))) * x)) +
        (∫ x in (0 : ℝ)..1, (x - 1 / 2) * Real.sin ((2 * Real.pi * (1 - (n : ℝ))) * x))) / 2 := by
    rw [show (fun x : ℝ => (x - 1 / 2) *
        (Real.sin ((2 * Real.pi * (1 + (n : ℝ))) * x) +
          Real.sin ((2 * Real.pi * (1 - (n : ℝ))) * x)) / 2) =
        fun x => ((x - 1 / 2) * Real.sin ((2 * Real.pi * (1 + (n : ℝ))) * x) +
          (x - 1 / 2) * Real.sin ((2 * Real.pi * (1 - (n : ℝ))) * x)) / 2 by
      funext x
      ring]
    rw [intervalIntegral.integral_div]
    have hContPlus : Continuous (fun x : ℝ =>
        (x - 1 / 2) * Real.sin ((2 * Real.pi * (1 + (n : ℝ))) * x)) := by
      fun_prop
    have hContMinus : Continuous (fun x : ℝ =>
        (x - 1 / 2) * Real.sin ((2 * Real.pi * (1 - (n : ℝ))) * x)) := by
      fun_prop
    rw [intervalIntegral.integral_add (hContPlus.intervalIntegrable (μ := volume) 0 1)
      (hContMinus.intervalIntegrable (μ := volume) 0 1)]
  have hscale :
      (fun x : ℝ => (x - 1 / 2) *
        ((Real.sin ((2 * Real.pi * (1 + (n : ℝ))) * x) +
          Real.sin ((2 * Real.pi * (1 - (n : ℝ))) * x)) / 2)) =
      fun x => (x - 1 / 2) *
        (Real.sin ((2 * Real.pi * (1 + (n : ℝ))) * x) +
          Real.sin ((2 * Real.pi * (1 - (n : ℝ))) * x)) / 2 := by
    funext x
    ring
  rw [hscale, hsplit, hIplus, hIminus]
  have hnNegR : (n : ℝ) ≠ -1 := by exact_mod_cast hnNeg
  have hnOneR : (n : ℝ) ≠ 1 := by exact_mod_cast hnOne
  have hden : (n : ℝ) ^ 2 - 1 ≠ 0 := by
    intro h
    have hsquare : (n : ℝ) ^ 2 = 1 := by linarith
    rcases (sq_eq_one_iff).mp hsquare with h' | h'
    · exact hnOneR h'
    · exact hnNegR h'
  field_simp [hpi, hplusR, hminusR, hden]
  ring

/-- The periodic kernel `α` displayed in Lemma A.2(ii), represented on its
fundamental interval. -/
def connesVanSuijlekomA2Alpha (x : ℝ) : ℝ :=
  -4 * Real.pi * (x - 1 / 2) * Real.sin (2 * Real.pi * x)

/-- The cosine Fourier coefficient of the source kernel is exactly the
diagonal coefficient of `D`. -/
theorem connesVanSuijlekomA2_alpha_cos_coefficient (n : ℤ) :
    (∫ x in (0 : ℝ)..1,
      connesVanSuijlekomA2Alpha x * Real.cos (2 * Real.pi * (n : ℝ) * x)) =
      connesVanSuijlekomA2Diagonal n := by
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  by_cases hnNeg : n = -1
  · subst n
    rw [connesVanSuijlekomA2Diagonal]
    norm_num
    rw [show (fun x : ℝ => connesVanSuijlekomA2Alpha x * Real.cos (2 * Real.pi * x)) =
        fun x => (-4 * Real.pi) *
          ((x - 1 / 2) * Real.sin (2 * Real.pi * x) * Real.cos (2 * Real.pi * x)) by
      funext x
      rw [connesVanSuijlekomA2Alpha]
      ring, intervalIntegral.integral_const_mul]
    have h := connesVanSuijlekomA2_fourier_coefficient_one
    field_simp [hpi] at h ⊢
    nlinarith
  by_cases hnZero : n = 0
  · subst n
    rw [connesVanSuijlekomA2Diagonal]
    norm_num
    rw [show (fun x : ℝ => connesVanSuijlekomA2Alpha x) =
        fun x => (-4 * Real.pi) * ((x - 1 / 2) * Real.sin (2 * Real.pi * x)) by
      funext x
      rw [connesVanSuijlekomA2Alpha]
      norm_num
      ring, intervalIntegral.integral_const_mul]
    have h := connesVanSuijlekomA2_fourier_coefficient_zero
    nlinarith
  by_cases hnOne : n = 1
  · subst n
    rw [connesVanSuijlekomA2Diagonal]
    norm_num
    rw [show (fun x : ℝ => connesVanSuijlekomA2Alpha x * Real.cos (2 * Real.pi * x)) =
        fun x => (-4 * Real.pi) *
          ((x - 1 / 2) * Real.sin (2 * Real.pi * x) * Real.cos (2 * Real.pi * x)) by
      funext x
      rw [connesVanSuijlekomA2Alpha]
      ring, intervalIntegral.integral_const_mul]
    have h := connesVanSuijlekomA2_fourier_coefficient_one
    field_simp [hpi] at h ⊢
    nlinarith
  rw [connesVanSuijlekomA2Diagonal, if_neg hnNeg, if_neg hnOne]
  rw [show (fun x : ℝ => connesVanSuijlekomA2Alpha x * Real.cos (2 * Real.pi * (n : ℝ) * x)) =
      fun x => (-4 * Real.pi) *
        ((x - 1 / 2) * Real.sin (2 * Real.pi * x) * Real.cos (2 * Real.pi * (n : ℝ) * x)) by
    funext x
    rw [connesVanSuijlekomA2Alpha]
    ring, intervalIntegral.integral_const_mul]
  have h := connesVanSuijlekomA2_fourier_coefficient_of_ne n hnNeg hnOne
  have hden : 1 - (n : ℝ) ^ 2 ≠ 0 := by
    intro hz
    have hsquare : (n : ℝ) ^ 2 = 1 := by linarith
    have hnNegR : (n : ℝ) ≠ -1 := by exact_mod_cast hnNeg
    have hnOneR : (n : ℝ) ≠ 1 := by exact_mod_cast hnOne
    rcases (sq_eq_one_iff).mp hsquare with h' | h'
    · exact hnOneR h'
    · exact hnNegR h'
  have hdenSrc : (n : ℝ) ^ 2 - 1 ≠ 0 := by
    intro hzero
    apply hden
    linarith
  rw [show 2 / (1 - (n : ℝ) ^ 2) = -2 * (1 / ((n : ℝ) ^ 2 - 1)) by
    field_simp [hden, hdenSrc]
    ring]
  nlinarith [h]

/-- Reflection symmetry gives the weighted cosine integral needed for the
sine Fourier coefficients of the source kernel. -/
theorem connesVanSuijlekomA2_weighted_cos_integral (k : ℤ) :
    (∫ x in (0 : ℝ)..1, (x - 1 / 2) * Real.cos (2 * Real.pi * (k : ℝ) * x)) = 0 := by
  have hsin : Real.sin (2 * Real.pi * (k : ℝ)) = 0 := by
    rw [show 2 * Real.pi * (k : ℝ) = (k : ℝ) * (2 * Real.pi) by ring]
    simpa using Real.sin_add_int_mul_two_pi 0 k
  have hcos : Real.cos (2 * Real.pi * (k : ℝ)) = 1 := by
    rw [show 2 * Real.pi * (k : ℝ) = (k : ℝ) * (2 * Real.pi) by ring]
    exact Real.cos_int_mul_two_pi k
  let g : ℝ → ℝ := fun x => (x - 1 / 2) * Real.cos (2 * Real.pi * (k : ℝ) * x)
  have hreflect : ∀ x : ℝ, g (1 - x) = -g x := by
    intro x
    dsimp [g]
    rw [show 2 * Real.pi * (k : ℝ) * (1 - x) =
      2 * Real.pi * (k : ℝ) - 2 * Real.pi * (k : ℝ) * x by ring,
      Real.cos_sub, hcos, hsin]
    ring
  have hcomp : (∫ x in (0 : ℝ)..1, g (1 - x)) = (∫ x in (0 : ℝ)..1, g x) := by
    convert intervalIntegral.integral_comp_sub_left (f := g) (a := (0 : ℝ)) (b := 1) 1 using 1
    norm_num
  have hneg : (∫ x in (0 : ℝ)..1, g (1 - x)) = -(∫ x in (0 : ℝ)..1, g x) := by
    rw [show (fun x : ℝ => g (1 - x)) = fun x => -g x by
      funext x
      exact hreflect x, intervalIntegral.integral_neg]
  change (∫ x in (0 : ℝ)..1, g x) = 0
  linarith

/-- The source kernel has no sine Fourier component at any integer mode. -/
theorem connesVanSuijlekomA2_alpha_sin_coefficient (n : ℤ) :
    (∫ x in (0 : ℝ)..1,
      connesVanSuijlekomA2Alpha x * Real.sin (2 * Real.pi * (n : ℝ) * x)) = 0 := by
  have hraw :
      (∫ x in (0 : ℝ)..1,
        (x - 1 / 2) * Real.sin (2 * Real.pi * x) * Real.sin (2 * Real.pi * (n : ℝ) * x)) = 0 := by
    rw [show (fun x : ℝ =>
        (x - 1 / 2) * Real.sin (2 * Real.pi * x) * Real.sin (2 * Real.pi * (n : ℝ) * x)) =
        fun x => ((x - 1 / 2) * Real.cos (2 * Real.pi * ((1 - n : ℤ) : ℝ) * x) -
          (x - 1 / 2) * Real.cos (2 * Real.pi * ((1 + n : ℤ) : ℝ) * x)) / 2 by
      funext x
      rw [show 2 * Real.pi * ((1 - n : ℤ) : ℝ) * x =
          2 * Real.pi * x - 2 * Real.pi * (n : ℝ) * x by
        push_cast
        ring,
        show 2 * Real.pi * ((1 + n : ℤ) : ℝ) * x =
          2 * Real.pi * x + 2 * Real.pi * (n : ℝ) * x by
        push_cast
        ring,
        Real.cos_sub, Real.cos_add]
      ring]
    rw [intervalIntegral.integral_div]
    have hContMinus : Continuous (fun x : ℝ =>
        (x - 1 / 2) * Real.cos (2 * Real.pi * ((1 - n : ℤ) : ℝ) * x)) := by
      fun_prop
    have hContPlus : Continuous (fun x : ℝ =>
        (x - 1 / 2) * Real.cos (2 * Real.pi * ((1 + n : ℤ) : ℝ) * x)) := by
      fun_prop
    rw [intervalIntegral.integral_sub (hContMinus.intervalIntegrable (μ := volume) 0 1)
      (hContPlus.intervalIntegrable (μ := volume) 0 1),
      connesVanSuijlekomA2_weighted_cos_integral (1 - n),
      connesVanSuijlekomA2_weighted_cos_integral (1 + n)]
    norm_num
  rw [show (fun x : ℝ => connesVanSuijlekomA2Alpha x * Real.sin (2 * Real.pi * (n : ℝ) * x)) =
      fun x => (-4 * Real.pi) *
        ((x - 1 / 2) * Real.sin (2 * Real.pi * x) * Real.sin (2 * Real.pi * (n : ℝ) * x)) by
    funext x
    rw [connesVanSuijlekomA2Alpha]
    ring, intervalIntegral.integral_const_mul, hraw]
  ring

/-- The complex Fourier coefficient of the periodic kernel is exactly the
diagonal symbol appearing in Appendix A.2. -/
theorem connesVanSuijlekomA2_alpha_complex_coefficient (n : ℤ) :
    (∫ x in (0 : ℝ)..1,
      (connesVanSuijlekomA2Alpha x : ℂ) *
        Complex.exp (-2 * Real.pi * Complex.I * (n : ℂ) * (x : ℂ))) =
      (connesVanSuijlekomA2Diagonal n : ℂ) := by
  have hcos := connesVanSuijlekomA2_alpha_cos_coefficient n
  have hsin := connesVanSuijlekomA2_alpha_sin_coefficient n
  rw [show (fun x : ℝ =>
      (connesVanSuijlekomA2Alpha x : ℂ) *
        Complex.exp (-2 * Real.pi * Complex.I * (n : ℂ) * (x : ℂ))) =
      fun x => (connesVanSuijlekomA2Alpha x : ℂ) *
        (Real.cos (2 * Real.pi * (n : ℝ) * x) - Complex.I * Real.sin (2 * Real.pi * (n : ℝ) * x)) by
    funext x
    rw [show (-2 * Real.pi * Complex.I * (n : ℂ) * (x : ℂ)) =
      (-(2 * Real.pi * (n : ℝ) * x) : ℂ) * Complex.I by
      push_cast
      ring, Complex.exp_mul_I]
    rw [Complex.cos_neg, Complex.sin_neg]
    rw [show (2 * (Real.pi : ℂ) * ((n : ℝ) : ℂ) * (x : ℂ)) =
      ((2 * Real.pi * (n : ℝ) * x : ℝ) : ℂ) by
      norm_cast]
    rw [Complex.ofReal_cos, Complex.ofReal_sin]
    ring]
  rw [show (fun x : ℝ => (connesVanSuijlekomA2Alpha x : ℂ) *
      (Real.cos (2 * Real.pi * (n : ℝ) * x) - Complex.I * Real.sin (2 * Real.pi * (n : ℝ) * x))) =
      fun x => (connesVanSuijlekomA2Alpha x * Real.cos (2 * Real.pi * (n : ℝ) * x) : ℂ) -
        Complex.I * (connesVanSuijlekomA2Alpha x * Real.sin (2 * Real.pi * (n : ℝ) * x) : ℂ) by
    funext x
    push_cast
    ring]
  have hcos' : (∫ x in (0 : ℝ)..1,
      (connesVanSuijlekomA2Alpha x : ℂ) *
        (Real.cos (2 * Real.pi * (n : ℝ) * x) : ℂ)) =
      (connesVanSuijlekomA2Diagonal n : ℂ) := by
    rw [show (fun x : ℝ => (connesVanSuijlekomA2Alpha x : ℂ) *
        (Real.cos (2 * Real.pi * (n : ℝ) * x) : ℂ)) =
        fun x => (connesVanSuijlekomA2Alpha x * Real.cos (2 * Real.pi * (n : ℝ) * x) : ℂ) by
      funext x
      push_cast
      ring]
    calc
      _ = ∫ x in (0 : ℝ)..1,
          ((connesVanSuijlekomA2Alpha x * Real.cos (2 * Real.pi * (n : ℝ) * x) : ℝ) : ℂ) := by
            apply intervalIntegral.integral_congr
            intro x _
            push_cast
            ring
      _ = _ := by rw [intervalIntegral.integral_ofReal, hcos]
  have hsin' : (∫ x in (0 : ℝ)..1,
      (connesVanSuijlekomA2Alpha x : ℂ) *
        (Real.sin (2 * Real.pi * (n : ℝ) * x) : ℂ)) = 0 := by
    rw [show (fun x : ℝ => (connesVanSuijlekomA2Alpha x : ℂ) *
        (Real.sin (2 * Real.pi * (n : ℝ) * x) : ℂ)) =
        fun x => (connesVanSuijlekomA2Alpha x * Real.sin (2 * Real.pi * (n : ℝ) * x) : ℂ) by
      funext x
      push_cast
      ring]
    calc
      _ = ∫ x in (0 : ℝ)..1,
          ((connesVanSuijlekomA2Alpha x * Real.sin (2 * Real.pi * (n : ℝ) * x) : ℝ) : ℂ) := by
            apply intervalIntegral.integral_congr
            intro x _
            push_cast
            ring
      _ = _ := by rw [intervalIntegral.integral_ofReal, hsin]; simp
  rw [intervalIntegral.integral_sub]
  · rw [intervalIntegral.integral_const_mul, hcos', hsin']
    simp
  all_goals
    apply Continuous.intervalIntegrable
    simp [connesVanSuijlekomA2Alpha]
    fun_prop

/-- The source kernel, periodized on the additive circle of length one. -/
def connesVanSuijlekomA2AlphaCircle : AddCircle (1 : ℝ) → ℂ :=
  AddCircle.liftIoc 1 0 fun x => (connesVanSuijlekomA2Alpha x : ℂ)

/-- The Fourier coefficients of the periodized source kernel are the entries of `D`. -/
theorem connesVanSuijlekomA2_alphaCircle_fourierCoeff (n : ℤ) :
    fourierCoeff connesVanSuijlekomA2AlphaCircle n =
      (connesVanSuijlekomA2Diagonal n : ℂ) := by
  rw [connesVanSuijlekomA2AlphaCircle, fourierCoeff_liftIoc_eq,
    fourierCoeffOn_eq_integral]
  norm_num
  rw [show (fun x : ℝ => (starRingEnd ℂ)
      (Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) * (x : ℂ))) *
      (connesVanSuijlekomA2Alpha x : ℂ)) =
      fun x => (connesVanSuijlekomA2Alpha x : ℂ) *
        Complex.exp (-2 * Real.pi * Complex.I * (n : ℂ) * (x : ℂ)) by
    funext x
    rw [← Complex.exp_conj]
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
    have htwo : (starRingEnd ℂ) (2 : ℂ) = 2 := by
      rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, Complex.conj_ofReal]
    have hn : (starRingEnd ℂ) (n : ℂ) = n := by
      rw [show (n : ℂ) = ((n : ℝ) : ℂ) by norm_cast, Complex.conj_ofReal]
    rw [htwo, hn]
    ring_nf]
  exact connesVanSuijlekomA2_alpha_complex_coefficient n

/-- Haar convolution by the periodized source kernel acts on every Fourier mode by the
corresponding source diagonal entry. -/
theorem connesVanSuijlekomA2_alphaCircle_convolution_fourier (n : ℤ) :
    connesVanSuijlekomA2AlphaCircle ⋆[ContinuousLinearMap.mul ℂ ℂ,
      AddCircle.haarAddCircle] fourier n =
      fun x => (connesVanSuijlekomA2Diagonal n : ℂ) * fourier n x := by
  funext x
  have harg (u v : AddCircle (1 : ℝ)) :
      fourier n (u + v) = fourier n u * fourier n v := by
    simp only [fourier_apply, zsmul_add, AddCircle.toCircle_add, Circle.coe_mul]
  have hinv (u : AddCircle (1 : ℝ)) :
      fourier n u * fourier (-n) u = (1 : ℂ) := by
    rw [← fourier_add]
    norm_num
  have hchar (u v : AddCircle (1 : ℝ)) :
      fourier n v = fourier n u * fourier (-n) (u - v) := by
    calc
      fourier n v = (fourier n (u - v) * fourier (-n) (u - v)) * fourier n v := by
        rw [hinv]
        ring
      _ = (fourier n (u - v) * fourier n v) * fourier (-n) (u - v) := by ring
      _ = fourier n ((u - v) + v) * fourier (-n) (u - v) := by rw [harg]
      _ = fourier n u * fourier (-n) (u - v) := by rw [sub_add_cancel]
  rw [convolution_mul_swap]
  rw [show (fun t : AddCircle (1 : ℝ) =>
      connesVanSuijlekomA2AlphaCircle (x - t) * fourier n t) =
      fun t => fourier n x *
        (connesVanSuijlekomA2AlphaCircle (x - t) * fourier (-n) (x - t)) by
    funext t
    rw [hchar x t]
    ring, MeasureTheory.integral_const_mul]
  rw [show (fun a : AddCircle (1 : ℝ) =>
      connesVanSuijlekomA2AlphaCircle (x - a) * fourier (-n) (x - a)) =
      fun a => (fun u => connesVanSuijlekomA2AlphaCircle u * fourier (-n) u) (x - a) by
    rfl]
  rw [integral_sub_left_eq_self
    (fun u : AddCircle (1 : ℝ) => connesVanSuijlekomA2AlphaCircle u * fourier (-n) u)
    AddCircle.haarAddCircle x]
  have hcoeff : (∫ u : AddCircle (1 : ℝ),
      connesVanSuijlekomA2AlphaCircle u * fourier (-n) u ∂AddCircle.haarAddCircle) =
      (connesVanSuijlekomA2Diagonal n : ℂ) := by
    rw [show (fun u : AddCircle (1 : ℝ) =>
        connesVanSuijlekomA2AlphaCircle u * fourier (-n) u) =
        fun u => fourier (-n) u • connesVanSuijlekomA2AlphaCircle u by
      funext u
      simp only [smul_eq_mul]
      ring]
    exact connesVanSuijlekomA2_alphaCircle_fourierCoeff n
  rw [hcoeff]
  ring

/-- The periodized source kernel is continuous on the circle. -/
theorem connesVanSuijlekomA2_alphaCircle_continuous :
    Continuous connesVanSuijlekomA2AlphaCircle := by
  apply AddCircle.liftIoc_zero_continuous
  · simp [connesVanSuijlekomA2Alpha]
  · have h : Continuous fun x : ℝ => (connesVanSuijlekomA2Alpha x : ℂ) := by
      unfold connesVanSuijlekomA2Alpha
      fun_prop
    exact h.continuousOn

/-- A finite Fourier polynomial on the period-one additive circle. -/
def connesVanSuijlekomA2FourierPolynomial (s : Finset ℤ) (c : ℤ → ℂ) :
    AddCircle (1 : ℝ) → ℂ :=
  fun x => ∑ n ∈ s, c n * fourier n x

/-- The diagonal `D` applied to a finite Fourier polynomial. -/
def connesVanSuijlekomA2DiagonalFourierPolynomial (s : Finset ℤ) (c : ℤ → ℂ) :
    AddCircle (1 : ℝ) → ℂ :=
  fun x => ∑ n ∈ s, c n * (connesVanSuijlekomA2Diagonal n : ℂ) * fourier n x

/-- On every finite Fourier polynomial, Haar convolution by `α` is exactly the diagonal
operator `D` from Lemma A.2(ii). -/
theorem connesVanSuijlekomA2_alphaCircle_convolution_fourierPolynomial
    (s : Finset ℤ) (c : ℤ → ℂ) :
    connesVanSuijlekomA2AlphaCircle ⋆[ContinuousLinearMap.mul ℂ ℂ,
      AddCircle.haarAddCircle] connesVanSuijlekomA2FourierPolynomial s c =
      connesVanSuijlekomA2DiagonalFourierPolynomial s c := by
  have hAlpha : Continuous connesVanSuijlekomA2AlphaCircle :=
    connesVanSuijlekomA2_alphaCircle_continuous
  funext x
  rw [convolution_mul]
  rw [show (fun t : AddCircle (1 : ℝ) =>
      connesVanSuijlekomA2AlphaCircle t *
        connesVanSuijlekomA2FourierPolynomial s c (x - t)) =
      fun t => ∑ n ∈ s,
        connesVanSuijlekomA2AlphaCircle t * (c n * fourier n (x - t)) by
    funext t
    simp only [connesVanSuijlekomA2FourierPolynomial]
    rw [Finset.mul_sum]]
  rw [MeasureTheory.integral_finsetSum]
  · rw [show (fun n : ℤ => ∫ t : AddCircle (1 : ℝ),
        connesVanSuijlekomA2AlphaCircle t * (c n * fourier n (x - t))
          ∂AddCircle.haarAddCircle) =
      fun n => c n * ∫ t : AddCircle (1 : ℝ),
        connesVanSuijlekomA2AlphaCircle t * fourier n (x - t)
          ∂AddCircle.haarAddCircle by
      funext n
      rw [show (fun t : AddCircle (1 : ℝ) =>
          connesVanSuijlekomA2AlphaCircle t * (c n * fourier n (x - t))) =
          fun t => c n * (connesVanSuijlekomA2AlphaCircle t * fourier n (x - t)) by
        funext t
        ring, MeasureTheory.integral_const_mul]]
    simp only [connesVanSuijlekomA2DiagonalFourierPolynomial]
    apply Finset.sum_congr rfl
    intro n hn
    rw [show (∫ t : AddCircle (1 : ℝ),
        connesVanSuijlekomA2AlphaCircle t * fourier n (x - t)
          ∂AddCircle.haarAddCircle) =
        (connesVanSuijlekomA2Diagonal n : ℂ) * fourier n x by
      exact congrFun (connesVanSuijlekomA2_alphaCircle_convolution_fourier n) x]
    ring
  · intro n hn
    apply Continuous.integrable_of_hasCompactSupport
    · exact hAlpha.mul (by fun_prop)
    · exact isCompact_univ.of_isClosed_subset (isClosed_tsupport _) (Set.subset_univ _)

end

end GaloisForLFunctions.HTGeometry
