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
  2 * if n = m then 1 else 0 + b * connesVanSuijlekomA1Mu n m

/-- Literal formula of Appendix A, Lemma A.1, once the paper's analytic
quadratic form has been identified with `connesVanSuijlekomA1QEntry`. -/
theorem connesVanSuijlekomA1_qEntry_eq (b : ℝ) (n m : ℤ) :
    connesVanSuijlekomA1QEntry b n m =
      2 * if n = m then 1 else 0 + b * connesVanSuijlekomA1Mu n m := rfl

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
    connesVanSuijlekomA2Eta n * if m = 1 then 1 else 0
  + (if n = 1 then 1 else 0) * connesVanSuijlekomA2Eta m
  - connesVanSuijlekomA2Xi n * if m = -1 then 1 else 0
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
  rw [show (-1 - (m : ℝ)) = -(1 + (m : ℝ)) by ring]
  simp

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
      connesVanSuijlekomA2Xi, connesVanSuijlekomA2Eta, hm, hm', hm0, hm1,
      connesVanSuijlekomA2_neg_xi]
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
      connesVanSuijlekomA2Xi, connesVanSuijlekomA2Eta, hn, hn0, hn1,
      connesVanSuijlekomA2_neg_xi]
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

end

end GaloisForLFunctions.HTGeometry
