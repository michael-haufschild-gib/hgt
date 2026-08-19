import Mathlib
import GaloisForLFunctions.HTGeometry.LpDiagonalMultiplier

/-!
# Connes--van Suijlekom, Appendix A: literal truncation matrix

This module formalizes the exact bi-infinite matrix `μ` displayed in Lemma A.1
of arXiv:2511.23257v1, on the source Fourier index set `ℤ`, including its
identification with the paper's distributional quadratic form for
`δ₀ + 2π b sin(2πx)`.
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

/-- The real kernel `K_{n,m}` in Appendix A, immediately after Lemma A.1. -/
def connesVanSuijlekomA1Kernel (n m : ℤ) (y : ℝ) : ℝ :=
  if n = m then 2 * (1 - y) * Real.cos (2 * Real.pi * (n : ℝ) * y) else
    (Real.sin (2 * Real.pi * (n : ℝ) * y) -
      Real.sin (2 * Real.pi * (m : ℝ) * y)) / (Real.pi * ((m - n : ℤ) : ℝ))

/-- The Appendix A scalar quadratic-form entry for
`δ₀ + 2π b sin(2πx)`, after evaluating the Dirac term at the kernel. -/
def connesVanSuijlekomA1SourceEntry (b : ℝ) (n m : ℤ) : ℝ :=
  (if n = m then 2 else 0) + 2 * Real.pi * b *
    (∫ y in (0 : ℝ)..1, connesVanSuijlekomA1Kernel n m y * Real.sin (2 * Real.pi * y))

/-- Literal formula of Appendix A, Lemma A.1, once the paper's analytic
quadratic form has been identified with `connesVanSuijlekomA1QEntry`. -/
theorem connesVanSuijlekomA1_qEntry_eq (b : ℝ) (n m : ℤ) :
    connesVanSuijlekomA1QEntry b n m =
      2 * (if n = m then 1 else 0) + b * connesVanSuijlekomA1Mu n m := rfl

/-- Integral of an integer Fourier cosine over one period. -/
theorem connesVanSuijlekomA1_integer_cos_integral (k : ℤ) :
    (∫ x in (0 : ℝ)..1, Real.cos (2 * Real.pi * (k : ℝ) * x)) =
      if k = 0 then 1 else 0 := by
  by_cases hk : k = 0
  · subst k
    norm_num
  rw [if_neg hk]
  have hκ : 2 * Real.pi * (k : ℝ) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) (by exact_mod_cast hk)
  let F : ℝ → ℝ := fun x => Real.sin (2 * Real.pi * (k : ℝ) * x) /
    (2 * Real.pi * (k : ℝ))
  have hF : ∀ x : ℝ, HasDerivAt (𝕜 := ℝ) F
      (Real.cos (2 * Real.pi * (k : ℝ) * x)) x := by
    intro x
    dsimp [F]
    have harg : HasDerivAt (𝕜 := ℝ) (fun y : ℝ => 2 * Real.pi * (k : ℝ) * y)
        (2 * Real.pi * (k : ℝ)) x := by
      exact hasDerivAt_const_mul _
    have hs := (Real.hasDerivAt_sin (2 * Real.pi * (k : ℝ) * x)).comp x harg
    convert! hs.div_const (2 * Real.pi * (k : ℝ)) using 1
    field_simp [hκ]
  have hInt : (∫ x in (0 : ℝ)..1, Real.cos (2 * Real.pi * (k : ℝ) * x)) = F 1 - F 0 := by
    apply integral_eq_sub_of_hasDerivAt
    · intro x _
      exact hF x
    · exact (by fun_prop : Continuous fun x : ℝ =>
        Real.cos (2 * Real.pi * (k : ℝ) * x)).intervalIntegrable 0 1
  rw [hInt]
  dsimp [F]
  have hsin : Real.sin (2 * Real.pi * (k : ℝ)) = 0 := by
    rw [show 2 * Real.pi * (k : ℝ) = (k : ℝ) * (2 * Real.pi) by ring]
    simpa using Real.sin_add_int_mul_two_pi 0 k
  simp [hsin]

/-- Orthogonality of the source sine frequency against every integer sine mode. -/
theorem connesVanSuijlekomA1_sinOne_integral (k : ℤ) :
    (∫ x in (0 : ℝ)..1,
      Real.sin (2 * Real.pi * (k : ℝ) * x) * Real.sin (2 * Real.pi * x)) =
      if k = 1 then 1 / 2 else if k = -1 then -(1 / 2) else 0 := by
  rw [show (fun x : ℝ =>
      Real.sin (2 * Real.pi * (k : ℝ) * x) * Real.sin (2 * Real.pi * x)) =
      fun x => (Real.cos (2 * Real.pi * ((k - 1 : ℤ) : ℝ) * x) -
        Real.cos (2 * Real.pi * ((k + 1 : ℤ) : ℝ) * x)) / 2 by
    funext x
    rw [show 2 * Real.pi * ((k - 1 : ℤ) : ℝ) * x =
        2 * Real.pi * (k : ℝ) * x - 2 * Real.pi * x by
        push_cast
        ring,
      show 2 * Real.pi * ((k + 1 : ℤ) : ℝ) * x =
        2 * Real.pi * (k : ℝ) * x + 2 * Real.pi * x by
        push_cast
        ring,
      Real.cos_sub, Real.cos_add]
    ring, intervalIntegral.integral_div]
  have hcontMinus : Continuous (fun x : ℝ =>
      Real.cos (2 * Real.pi * ((k - 1 : ℤ) : ℝ) * x)) := by
    fun_prop
  have hcontPlus : Continuous (fun x : ℝ =>
      Real.cos (2 * Real.pi * ((k + 1 : ℤ) : ℝ) * x)) := by
    fun_prop
  rw [intervalIntegral.integral_sub (hcontMinus.intervalIntegrable (μ := volume) 0 1)
    (hcontPlus.intervalIntegrable (μ := volume) 0 1),
    connesVanSuijlekomA1_integer_cos_integral (k - 1),
    connesVanSuijlekomA1_integer_cos_integral (k + 1)]
  by_cases hkOne : k = 1
  · subst k
    norm_num
  by_cases hkNegOne : k = -1
  · subst k
    norm_num
  have hminus : k - 1 ≠ 0 := by omega
  have hplus : k + 1 ≠ 0 := by omega
  simp [hkOne, hkNegOne, hminus, hplus]

/-- The non-diagonal Appendix A kernel evaluates to the corresponding
non-diagonal entry of the displayed matrix. -/
theorem connesVanSuijlekomA1_sourceEntry_offdiag (b : ℝ) (n m : ℤ) (hnm : n ≠ m) :
    connesVanSuijlekomA1SourceEntry b n m = b * connesVanSuijlekomA1Mu n m := by
  simp only [connesVanSuijlekomA1SourceEntry, if_neg hnm, connesVanSuijlekomA1Kernel]
  rw [show (fun y : ℝ =>
      ((Real.sin (2 * Real.pi * (n : ℝ) * y) -
        Real.sin (2 * Real.pi * (m : ℝ) * y)) / (Real.pi * ((m - n : ℤ) : ℝ))) *
        Real.sin (2 * Real.pi * y)) =
      fun y => (1 / (Real.pi * ((m - n : ℤ) : ℝ))) *
        (Real.sin (2 * Real.pi * (n : ℝ) * y) * Real.sin (2 * Real.pi * y) -
          Real.sin (2 * Real.pi * (m : ℝ) * y) * Real.sin (2 * Real.pi * y)) by
    funext y
    ring, intervalIntegral.integral_const_mul]
  have hcontN : Continuous (fun y : ℝ =>
      Real.sin (2 * Real.pi * (n : ℝ) * y) * Real.sin (2 * Real.pi * y)) := by
    fun_prop
  have hcontM : Continuous (fun y : ℝ =>
      Real.sin (2 * Real.pi * (m : ℝ) * y) * Real.sin (2 * Real.pi * y)) := by
    fun_prop
  rw [intervalIntegral.integral_sub (hcontN.intervalIntegrable (μ := volume) 0 1)
    (hcontM.intervalIntegrable (μ := volume) 0 1),
    connesVanSuijlekomA1_sinOne_integral n,
    connesVanSuijlekomA1_sinOne_integral m]
  by_cases hnNeg : n = -1 <;> by_cases hnZero : n = 0 <;> by_cases hnOne : n = 1 <;>
    by_cases hmNeg : m = -1 <;> by_cases hmZero : m = 0 <;> by_cases hmOne : m = 1 <;>
    simp_all [connesVanSuijlekomA1Mu] <;>
    push_cast <;>
    field_simp [Real.pi_ne_zero] <;>
    ring_nf
  all_goals
    first
    | rw [show (-1 - (m : ℝ)) = -(1 + (m : ℝ)) by ring, inv_neg]
      ring
    | rw [show (-1 + (n : ℝ)) = -(1 - (n : ℝ)) by ring, inv_neg]
      ring

/-- Integral of an integer Fourier sine over one period. -/
theorem connesVanSuijlekomA1_integer_sin_integral (k : ℤ) :
    (∫ x in (0 : ℝ)..1, Real.sin (2 * Real.pi * (k : ℝ) * x)) = 0 := by
  by_cases hk : k = 0
  · subst k
    norm_num
  have hκ : 2 * Real.pi * (k : ℝ) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) (by exact_mod_cast hk)
  let F : ℝ → ℝ := fun x => -Real.cos (2 * Real.pi * (k : ℝ) * x) /
    (2 * Real.pi * (k : ℝ))
  have hF : ∀ x : ℝ, HasDerivAt (𝕜 := ℝ) F
      (Real.sin (2 * Real.pi * (k : ℝ) * x)) x := by
    intro x
    dsimp [F]
    have harg : HasDerivAt (𝕜 := ℝ) (fun y : ℝ => 2 * Real.pi * (k : ℝ) * y)
        (2 * Real.pi * (k : ℝ)) x := by
      exact hasDerivAt_const_mul _
    have hc := (Real.hasDerivAt_cos (2 * Real.pi * (k : ℝ) * x)).comp x harg
    convert! hc.neg.div_const (2 * Real.pi * (k : ℝ)) using 1
    field_simp [hκ]
  have hInt : (∫ x in (0 : ℝ)..1, Real.sin (2 * Real.pi * (k : ℝ) * x)) = F 1 - F 0 := by
    apply integral_eq_sub_of_hasDerivAt
    · intro x _
      exact hF x
    · exact (by fun_prop : Continuous fun x : ℝ =>
        Real.sin (2 * Real.pi * (k : ℝ) * x)).intervalIntegrable 0 1
  rw [hInt]
  dsimp [F]
  have hcos : Real.cos (2 * Real.pi * (k : ℝ)) = 1 := by
    rw [show 2 * Real.pi * (k : ℝ) = (k : ℝ) * (2 * Real.pi) by ring]
    exact Real.cos_int_mul_two_pi k
  simp [hcos]

/-- The source sine frequency is orthogonal to every integer cosine mode. -/
theorem connesVanSuijlekomA1_sinOne_cos_integral (n : ℤ) :
    (∫ x in (0 : ℝ)..1,
      Real.sin (2 * Real.pi * x) * Real.cos (2 * Real.pi * (n : ℝ) * x)) = 0 := by
  rw [show (fun x : ℝ =>
      Real.sin (2 * Real.pi * x) * Real.cos (2 * Real.pi * (n : ℝ) * x)) =
      fun x => (Real.sin (2 * Real.pi * ((1 + n : ℤ) : ℝ) * x) +
        Real.sin (2 * Real.pi * ((1 - n : ℤ) : ℝ) * x)) / 2 by
    funext x
    rw [show 2 * Real.pi * ((1 + n : ℤ) : ℝ) * x =
        2 * Real.pi * x + 2 * Real.pi * (n : ℝ) * x by
        push_cast
        ring,
      show 2 * Real.pi * ((1 - n : ℤ) : ℝ) * x =
        2 * Real.pi * x - 2 * Real.pi * (n : ℝ) * x by
        push_cast
        ring,
      Real.sin_add, Real.sin_sub]
    ring, intervalIntegral.integral_div]
  have hcontPlus : Continuous (fun x : ℝ =>
      Real.sin (2 * Real.pi * ((1 + n : ℤ) : ℝ) * x)) := by
    fun_prop
  have hcontMinus : Continuous (fun x : ℝ =>
      Real.sin (2 * Real.pi * ((1 - n : ℤ) : ℝ) * x)) := by
    fun_prop
  rw [intervalIntegral.integral_add (hcontPlus.intervalIntegrable (μ := volume) 0 1)
    (hcontMinus.intervalIntegrable (μ := volume) 0 1),
    connesVanSuijlekomA1_integer_sin_integral (1 + n),
    connesVanSuijlekomA1_integer_sin_integral (1 - n)]
  norm_num

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

/-- The diagonal Appendix A kernel is the diagonal Fourier multiplier from
Lemma A.2. -/
theorem connesVanSuijlekomA1_diagonal_kernel_integral (n : ℤ) :
    2 * Real.pi * (∫ x in (0 : ℝ)..1,
      2 * (1 - x) * Real.cos (2 * Real.pi * (n : ℝ) * x) * Real.sin (2 * Real.pi * x)) =
      connesVanSuijlekomA2Diagonal n := by
  rw [← intervalIntegral.integral_const_mul]
  have hcontAlpha : Continuous (fun x : ℝ =>
      connesVanSuijlekomA2Alpha x * Real.cos (2 * Real.pi * (n : ℝ) * x)) := by
    simp only [connesVanSuijlekomA2Alpha]
    fun_prop
  have hcontSinCos : Continuous (fun x : ℝ =>
      Real.sin (2 * Real.pi * x) * Real.cos (2 * Real.pi * (n : ℝ) * x)) := by
    fun_prop
  calc
    _ = ∫ x in (0 : ℝ)..1,
        connesVanSuijlekomA2Alpha x * Real.cos (2 * Real.pi * (n : ℝ) * x) +
          (2 * Real.pi) *
            (Real.sin (2 * Real.pi * x) * Real.cos (2 * Real.pi * (n : ℝ) * x)) := by
      apply intervalIntegral.integral_congr
      intro x _
      simp only [connesVanSuijlekomA2Alpha]
      ring
    _ = (∫ x in (0 : ℝ)..1,
        connesVanSuijlekomA2Alpha x * Real.cos (2 * Real.pi * (n : ℝ) * x)) +
          (2 * Real.pi) * (∫ x in (0 : ℝ)..1,
            Real.sin (2 * Real.pi * x) * Real.cos (2 * Real.pi * (n : ℝ) * x)) := by
      rw [intervalIntegral.integral_add
        (hcontAlpha.intervalIntegrable (μ := volume) 0 1)
        ((hcontSinCos.const_mul (2 * Real.pi)).intervalIntegrable (μ := volume) 0 1),
        intervalIntegral.integral_const_mul]
    _ = _ := by
      rw [connesVanSuijlekomA2_alpha_cos_coefficient, connesVanSuijlekomA1_sinOne_cos_integral]
      ring

/-- The A.1 and A.2 diagonal symbols agree exactly. -/
theorem connesVanSuijlekomA1_mu_diagonal (n : ℤ) :
    connesVanSuijlekomA1Mu n n = connesVanSuijlekomA2Diagonal n := by
  by_cases hnNeg : n = -1 <;> by_cases hnZero : n = 0 <;> by_cases hnOne : n = 1 <;>
    simp_all [connesVanSuijlekomA1Mu, connesVanSuijlekomA2Diagonal]

/-- The diagonal scalar quadratic-form entry in Appendix A equals its
displayed matrix entry. -/
theorem connesVanSuijlekomA1_sourceEntry_diagonal (b : ℝ) (n : ℤ) :
    connesVanSuijlekomA1SourceEntry b n n = connesVanSuijlekomA1QEntry b n n := by
  simp only [connesVanSuijlekomA1SourceEntry, if_pos, connesVanSuijlekomA1Kernel]
  simp only [connesVanSuijlekomA1QEntry, if_pos]
  calc
    2 + 2 * Real.pi * b *
        (∫ y in (0 : ℝ)..1,
          2 * (1 - y) * Real.cos (2 * Real.pi * (n : ℝ) * y) *
            Real.sin (2 * Real.pi * y)) =
        2 + b * (2 * Real.pi *
          (∫ y in (0 : ℝ)..1,
            2 * (1 - y) * Real.cos (2 * Real.pi * (n : ℝ) * y) *
              Real.sin (2 * Real.pi * y))) := by ring
    _ = 2 + b * connesVanSuijlekomA2Diagonal n := by
      rw [connesVanSuijlekomA1_diagonal_kernel_integral]
    _ = 2 + b * connesVanSuijlekomA1Mu n n := by
      rw [connesVanSuijlekomA1_mu_diagonal]
    _ = 2 * 1 + b * connesVanSuijlekomA1Mu n n := by ring

/-- Lemma A.1: the distributional quadratic form of
`δ₀ + 2π b sin(2πx)` has exactly the matrix displayed in Appendix A. -/
theorem connesVanSuijlekomA1_sourceEntry_eq_qEntry (b : ℝ) (n m : ℤ) :
    connesVanSuijlekomA1SourceEntry b n m = connesVanSuijlekomA1QEntry b n m := by
  by_cases hnm : n = m
  · subst m
    exact connesVanSuijlekomA1_sourceEntry_diagonal b n
  · rw [show connesVanSuijlekomA1SourceEntry b n m = b * connesVanSuijlekomA1Mu n m by
      exact connesVanSuijlekomA1_sourceEntry_offdiag b n m hnm]
    simp [connesVanSuijlekomA1QEntry, hnm]

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

/-- The diagonal symbol in Lemma A.2 is uniformly bounded by two. -/
theorem connesVanSuijlekomA2_norm_diagonal_le_two (n : ℤ) :
    ‖(connesVanSuijlekomA2Diagonal n : ℂ)‖ ≤ 2 := by
  by_cases hnNeg : n = -1
  · subst n
    norm_num [connesVanSuijlekomA2Diagonal]
  by_cases hnOne : n = 1
  · subst n
    norm_num [connesVanSuijlekomA2Diagonal]
  by_cases hnZero : n = 0
  · subst n
    norm_num [connesVanSuijlekomA2Diagonal]
  rw [connesVanSuijlekomA2Diagonal, if_neg hnNeg, if_neg hnOne]
  have hnatPos : 0 < n.natAbs := Int.natAbs_pos.mpr hnZero
  have hnatNeOne : n.natAbs ≠ 1 := by
    intro h
    rcases Int.natAbs_eq_iff.mp h with h' | h'
    · exact hnOne h'
    · exact hnNeg h'
  have hnat : 2 ≤ n.natAbs := by omega
  have hnatR : (2 : ℝ) ≤ (n.natAbs : ℝ) := by exact_mod_cast hnat
  have hnatZ : (2 : ℤ) ≤ |n| := by
    rw [← Int.natCast_natAbs]
    exact_mod_cast hnat
  have habs : (2 : ℝ) ≤ |(n : ℝ)| := by exact_mod_cast hnatZ
  have hsq : (4 : ℝ) ≤ (n : ℝ) ^ 2 := by
    have hsqabs : (4 : ℝ) ≤ |(n : ℝ)| ^ 2 := by nlinarith
    simpa only [sq_abs] using hsqabs
  have hdenNonpos : 1 - (n : ℝ) ^ 2 ≤ 0 := by linarith
  have hdenAbs : (1 : ℝ) ≤ |1 - (n : ℝ) ^ 2| := by
    rw [abs_of_nonpos hdenNonpos]
    linarith
  rw [Complex.norm_real, Real.norm_eq_abs, abs_div,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  rw [div_le_iff₀ (lt_of_lt_of_le zero_lt_one hdenAbs)]
  nlinarith

/-- The bounded `L²` completion of the diagonal operator in Lemma A.2. -/
def connesVanSuijlekomA2DiagonalL2 :
    Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))) →L[ℂ]
      Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))) :=
  (fourierBasis (T := (1 : ℝ))).repr.toContinuousLinearEquiv.symm.toContinuousLinearMap ∘L
    GaloisForLFunctions.lpDiagonalCLM (C := 2)
      (fun n : ℤ => (connesVanSuijlekomA2Diagonal n : ℂ))
      (by norm_num) (by intro n; exact connesVanSuijlekomA2_norm_diagonal_le_two n) ∘L
    (fourierBasis (T := (1 : ℝ))).repr.toContinuousLinearEquiv.toContinuousLinearMap

/-- The bounded completion retains the source diagonal values on every Fourier basis vector. -/
theorem connesVanSuijlekomA2_diagonalL2_fourierLp (j : ℤ) :
    connesVanSuijlekomA2DiagonalL2 (fourierLp 2 j) =
      (connesVanSuijlekomA2Diagonal j : ℂ) • fourierLp 2 j := by
  have hbasis : (fourierLp (T := (1 : ℝ)) 2 j :
      Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))) =
      (fourierBasis (T := (1 : ℝ))) j := by
    rw [coe_fourierBasis]
  have hsingle : lp.single (E := fun _ : ℤ => ℂ) 2 j
      (connesVanSuijlekomA2Diagonal j : ℂ) =
      (connesVanSuijlekomA2Diagonal j : ℂ) • lp.single (E := fun _ : ℤ => ℂ) 2 j (1 : ℂ) := by
    rw [← lp.single_smul]
    congr 1
    rw [smul_eq_mul, mul_one]
  rw [hbasis, connesVanSuijlekomA2DiagonalL2]
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
    ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv]
  rw [HilbertBasis.repr_self, GaloisForLFunctions.lpDiagonalCLM_single, hsingle, map_smul]
  congr 1
  simp

/-- A finite Fourier polynomial as an `L²` vector. -/
def connesVanSuijlekomA2FourierPolynomialLp (s : Finset ℤ) (c : ℤ → ℂ) :
    Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))) :=
  ∑ n ∈ s, c n • fourierLp 2 n

/-- The diagonal image of a finite Fourier polynomial as an `L²` vector. -/
def connesVanSuijlekomA2DiagonalFourierPolynomialLp (s : Finset ℤ) (c : ℤ → ℂ) :
    Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))) :=
  ∑ n ∈ s, (c n * (connesVanSuijlekomA2Diagonal n : ℂ)) • fourierLp 2 n

/-- The bounded `L²` completion agrees with the diagonal formula on every finite polynomial. -/
theorem connesVanSuijlekomA2_diagonalL2_fourierPolynomial
    (s : Finset ℤ) (c : ℤ → ℂ) :
    connesVanSuijlekomA2DiagonalL2 (connesVanSuijlekomA2FourierPolynomialLp s c) =
      connesVanSuijlekomA2DiagonalFourierPolynomialLp s c := by
  rw [connesVanSuijlekomA2FourierPolynomialLp,
    connesVanSuijlekomA2DiagonalFourierPolynomialLp, map_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [map_smul, connesVanSuijlekomA2_diagonalL2_fourierLp, smul_smul]

/-- The finite Fourier polynomial packaged as a continuous map. -/
def connesVanSuijlekomA2FourierPolynomialContinuousMap (s : Finset ℤ) (c : ℤ → ℂ) :
    C(AddCircle (1 : ℝ), ℂ) :=
  ⟨connesVanSuijlekomA2FourierPolynomial s c, by
    unfold connesVanSuijlekomA2FourierPolynomial
    fun_prop⟩

/-- The finite Fourier polynomial as an `L²` vector through its actual periodic function. -/
def connesVanSuijlekomA2FourierPolynomialToLp (s : Finset ℤ) (c : ℤ → ℂ) :
    Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))) :=
  ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ
    (connesVanSuijlekomA2FourierPolynomialContinuousMap s c)

theorem connesVanSuijlekomA2_fourierPolynomialToLp_eq
    (s : Finset ℤ) (c : ℤ → ℂ) :
    connesVanSuijlekomA2FourierPolynomialToLp s c =
      connesVanSuijlekomA2FourierPolynomialLp s c := by
  rw [connesVanSuijlekomA2FourierPolynomialToLp, connesVanSuijlekomA2FourierPolynomialLp]
  have hcm : connesVanSuijlekomA2FourierPolynomialContinuousMap s c =
      ∑ n ∈ s, c n • fourier n := by
    ext x
    simp only [connesVanSuijlekomA2FourierPolynomialContinuousMap, ContinuousMap.coe_mk,
      connesVanSuijlekomA2FourierPolynomial]
    rw [ContinuousMap.sum_apply]
    simp_rw [ContinuousMap.smul_apply, smul_eq_mul]
  rw [hcm, map_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [map_smul]

/-- The diagonal finite Fourier polynomial packaged as a continuous map. -/
def connesVanSuijlekomA2DiagonalFourierPolynomialContinuousMap
    (s : Finset ℤ) (c : ℤ → ℂ) : C(AddCircle (1 : ℝ), ℂ) :=
  ⟨connesVanSuijlekomA2DiagonalFourierPolynomial s c, by
    unfold connesVanSuijlekomA2DiagonalFourierPolynomial
    fun_prop⟩

/-- The diagonal finite Fourier polynomial as an `L²` vector through its actual function. -/
def connesVanSuijlekomA2DiagonalFourierPolynomialToLp (s : Finset ℤ) (c : ℤ → ℂ) :
    Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))) :=
  ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ
    (connesVanSuijlekomA2DiagonalFourierPolynomialContinuousMap s c)

theorem connesVanSuijlekomA2_diagonalFourierPolynomialToLp_eq
    (s : Finset ℤ) (c : ℤ → ℂ) :
    connesVanSuijlekomA2DiagonalFourierPolynomialToLp s c =
      connesVanSuijlekomA2DiagonalFourierPolynomialLp s c := by
  rw [connesVanSuijlekomA2DiagonalFourierPolynomialToLp,
    connesVanSuijlekomA2DiagonalFourierPolynomialLp]
  have hcm : connesVanSuijlekomA2DiagonalFourierPolynomialContinuousMap s c =
      ∑ n ∈ s, (c n * (connesVanSuijlekomA2Diagonal n : ℂ)) • fourier n := by
    ext x
    simp only [connesVanSuijlekomA2DiagonalFourierPolynomialContinuousMap, ContinuousMap.coe_mk,
      connesVanSuijlekomA2DiagonalFourierPolynomial]
    rw [ContinuousMap.sum_apply]
    simp_rw [ContinuousMap.smul_apply, smul_eq_mul]
  rw [hcm, map_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [map_smul]

/-- The bounded `L²` operator is the extension of the genuine Haar-convolution formula on
every finite Fourier polynomial. -/
theorem connesVanSuijlekomA2_diagonalL2_extends_convolution
    (s : Finset ℤ) (c : ℤ → ℂ) :
    connesVanSuijlekomA2DiagonalL2 (connesVanSuijlekomA2FourierPolynomialToLp s c) =
      connesVanSuijlekomA2DiagonalFourierPolynomialToLp s c := by
  rw [connesVanSuijlekomA2_fourierPolynomialToLp_eq,
    connesVanSuijlekomA2_diagonalL2_fourierPolynomial,
    connesVanSuijlekomA2_diagonalFourierPolynomialToLp_eq]

/-- The completed diagonal operator is uniquely determined among bounded `L²` operators by the
Haar-convolution values on the Fourier modes. -/
theorem connesVanSuijlekomA2_diagonalL2_unique
    (T : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))) →L[ℂ]
      Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))))
    (h : ∀ n : ℤ, T (fourierLp 2 n) =
      (connesVanSuijlekomA2Diagonal n : ℂ) • fourierLp 2 n) :
    T = connesVanSuijlekomA2DiagonalL2 := by
  apply ContinuousLinearMap.ext_on
    (show Dense (Submodule.span ℂ (Set.range (fourierLp (T := (1 : ℝ)) 2)) :
      Set (Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))) ) by
      rw [dense_iff_closure_eq, ← Submodule.topologicalClosure_coe,
        span_fourierLp_closure_eq_top (T := (1 : ℝ)) (p := 2) (by simp)]
      rfl)
  rintro _ ⟨n, rfl⟩
  rw [h n, connesVanSuijlekomA2_diagonalL2_fourierLp]

end

end GaloisForLFunctions.HTGeometry
