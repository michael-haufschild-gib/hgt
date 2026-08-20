/-
# Chen--Gupta--Li character-twisted dyadic large-value matrix

Chen--Gupta--Li Theorem 1.1 studies the rows

`n ↦ χ(n) n^{it}`,  N < n ≤ 2N,

over a finite family of character/ordinate pairs.  This module formalizes the
literal finite matrix, identifies its row action with the stated Dirichlet
polynomial, and proves its unconditional Hilbert-energy bound.  The refined
Guth--Maynard correlation bound of Theorem 1.1 is a later layer; it is not
assumed here.
-/

import GaloisForLFunctions.RHTower.ChenGuptaLiFiniteZeroDetector
import GaloisForLFunctions.RHTower.Sieve.HuxleyDyadicRow

open Complex
open scoped InnerProductSpace

noncomputable section

namespace RHTower

/-- One row label in the character-twisted large-value matrix. -/
structure CGLCharacterDyadicRowData (q : ℕ) where
  time : ℝ
  character : DirichletCharacter ℂ q

/-- The literal integer index in the source block `N < n ≤ 2N`. -/
def cglCharacterDyadicIndex (N : ℕ) (j : Fin N) : ℕ := N + j.1 + 1

/-- The oscillatory factor `n^{it}` written as a complex exponential. -/
def cglCharacterDyadicPhase (N : ℕ) (t : ℝ) (j : Fin N) : ℂ :=
  Complex.exp ((((t * Real.log (cglCharacterDyadicIndex N j : ℝ) : ℝ) : ℂ) * Complex.I))

/-- A conjugated row of the Chen--Gupta--Li matrix.  The conjugation is chosen
so the standard Hilbert inner product evaluates directly to the source
polynomial. -/
def cglCharacterDyadicRow (N q : ℕ) (w : CGLCharacterDyadicRowData q) :
    EuclideanSpace ℂ (Fin N) :=
  WithLp.toLp 2 (fun j : Fin N =>
    (starRingEnd ℂ) (w.character (cglCharacterDyadicIndex N j) *
      cglCharacterDyadicPhase N w.time j))

/-- The length-`N` character-twisted Dirichlet polynomial on `N < n ≤ 2N`. -/
def cglCharacterDyadicPolynomial (N q : ℕ) (w : CGLCharacterDyadicRowData q)
    (a : EuclideanSpace ℂ (Fin N)) : ℂ :=
  ∑ j, a j * w.character (cglCharacterDyadicIndex N j) *
    cglCharacterDyadicPhase N w.time j

/-- Matrix-row action is exactly the source Dirichlet polynomial. -/
theorem inner_cglCharacterDyadicRow (N q : ℕ) (w : CGLCharacterDyadicRowData q)
    (a : EuclideanSpace ℂ (Fin N)) :
    ⟪cglCharacterDyadicRow N q w, a⟫_ℂ = cglCharacterDyadicPolynomial N q w a := by
  rw [PiLp.inner_apply]
  simp [cglCharacterDyadicRow, cglCharacterDyadicPolynomial, RCLike.inner_apply]
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- A character-twisted row has coordinate norm at most one.  Nonunit indices
may vanish, which is why this is an inequality rather than an equality. -/
theorem norm_cglCharacterDyadicRow_coord_le_one (N q : ℕ)
    (w : CGLCharacterDyadicRowData q) (j : Fin N) :
    ‖(cglCharacterDyadicRow N q w) j‖ ≤ 1 := by
  simp only [cglCharacterDyadicRow, norm_conj, norm_mul]
  rw [cglCharacterDyadicPhase]
  rw [Complex.norm_exp_ofReal_mul_I]
  simpa using w.character.norm_le_one (cglCharacterDyadicIndex N j)

/-- Closed Hilbert-energy bound for every row of the character matrix. -/
theorem norm_cglCharacterDyadicRow_sq_le (N q : ℕ)
    (w : CGLCharacterDyadicRowData q) :
    ‖cglCharacterDyadicRow N q w‖ ^ 2 ≤ (N : ℝ) := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
  calc
    ∑ j, ‖(cglCharacterDyadicRow N q w) j‖ ^ 2 ≤ ∑ _j : Fin N, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro j hj
      nlinarith [norm_nonneg ((cglCharacterDyadicRow N q w) j),
        norm_cglCharacterDyadicRow_coord_le_one N q w j]
    _ = N := by simp

/-- The unconditional one-row large-value estimate supplied by Hilbert-space
Cauchy--Schwarz. -/
theorem norm_cglCharacterDyadicPolynomial_sq_le (N q : ℕ)
    (w : CGLCharacterDyadicRowData q) (a : EuclideanSpace ℂ (Fin N)) :
    ‖cglCharacterDyadicPolynomial N q w a‖ ^ 2 ≤ (N : ℝ) * ‖a‖ ^ 2 := by
  rw [← inner_cglCharacterDyadicRow]
  have hcs : ‖⟪cglCharacterDyadicRow N q w, a⟫_ℂ‖ ≤
      ‖cglCharacterDyadicRow N q w‖ * ‖a‖ :=
    norm_inner_le_norm _ _
  have hsq := pow_le_pow_left₀ (norm_nonneg ⟪cglCharacterDyadicRow N q w, a⟫_ℂ) hcs 2
  calc
    ‖⟪cglCharacterDyadicRow N q w, a⟫_ℂ‖ ^ 2 ≤
        (‖cglCharacterDyadicRow N q w‖ * ‖a‖) ^ 2 := hsq
    _ = ‖cglCharacterDyadicRow N q w‖ ^ 2 * ‖a‖ ^ 2 := by ring
    _ ≤ (N : ℝ) * ‖a‖ ^ 2 :=
      mul_le_mul_of_nonneg_right (norm_cglCharacterDyadicRow_sq_le N q w) (sq_nonneg ‖a‖)

/-- The rows selected by a nonnegative amplitude threshold.  `NNReal` encodes
threshold nonnegativity as data, leaving the counting theorem premise-free. -/
def cglCharacterDyadicLargeValues (N q R : ℕ)
    (w : Fin R → CGLCharacterDyadicRowData q) (a : EuclideanSpace ℂ (Fin N))
    (V : NNReal) : Finset (Fin R) :=
  Finset.univ.filter (fun r => (V : ℝ) ≤ ‖cglCharacterDyadicPolynomial N q (w r) a‖)

/-- Baseline count of finite character-twisted large values.  This is the exact
Hilbert bound before the paper's refined character-correlation argument. -/
theorem card_cglCharacterDyadicLargeValues_mul_sq_le (N q R : ℕ)
    (w : Fin R → CGLCharacterDyadicRowData q) (a : EuclideanSpace ℂ (Fin N))
    (V : NNReal) :
    ((cglCharacterDyadicLargeValues N q R w a V).card : ℝ) * (V : ℝ) ^ 2 ≤
      (R : ℝ) * (N : ℝ) * ‖a‖ ^ 2 := by
  let S := cglCharacterDyadicLargeValues N q R w a V
  have hlarge : ∀ r ∈ S, (V : ℝ) ^ 2 ≤ ‖cglCharacterDyadicPolynomial N q (w r) a‖ ^ 2 := by
    intro r hr
    have hr' : (V : ℝ) ≤ ‖cglCharacterDyadicPolynomial N q (w r) a‖ :=
      (Finset.mem_filter.mp hr).2
    exact pow_le_pow_left₀ (NNReal.zero_le_coe) hr' 2
  have hsumLarge : (S.card : ℝ) * (V : ℝ) ^ 2 ≤
      ∑ r ∈ S, ‖cglCharacterDyadicPolynomial N q (w r) a‖ ^ 2 := by
    calc
      (S.card : ℝ) * (V : ℝ) ^ 2 = ∑ _r ∈ S, (V : ℝ) ^ 2 := by simp
      _ ≤ ∑ r ∈ S, ‖cglCharacterDyadicPolynomial N q (w r) a‖ ^ 2 :=
        Finset.sum_le_sum hlarge
  have hsub : ∑ r ∈ S, ‖cglCharacterDyadicPolynomial N q (w r) a‖ ^ 2 ≤
      ∑ r : Fin R, ‖cglCharacterDyadicPolynomial N q (w r) a‖ ^ 2 := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    intro r hrS hrU
    exact sq_nonneg ‖cglCharacterDyadicPolynomial N q (w r) a‖
  calc
    (S.card : ℝ) * (V : ℝ) ^ 2 ≤
        ∑ r ∈ S, ‖cglCharacterDyadicPolynomial N q (w r) a‖ ^ 2 := hsumLarge
    _ ≤ ∑ r : Fin R, ‖cglCharacterDyadicPolynomial N q (w r) a‖ ^ 2 := hsub
    _ ≤ ∑ _r : Fin R, (N : ℝ) * ‖a‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro r hr
      exact norm_cglCharacterDyadicPolynomial_sq_le N q (w r) a
    _ = (R : ℝ) * (N : ℝ) * ‖a‖ ^ 2 := by simp [mul_assoc]

/-- Product of two source phases is the phase at the ordinate difference. -/
theorem cglCharacterDyadicPhase_mul_conj (N : ℕ) (t u : ℝ) (j : Fin N) :
    cglCharacterDyadicPhase N t j * (starRingEnd ℂ) (cglCharacterDyadicPhase N u j) =
      cglCharacterDyadicPhase N (t - u) j := by
  unfold cglCharacterDyadicPhase
  rw [← Complex.exp_conj]
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The literal finite character/ordinate correlation which appears in a Gram
entry of the Chen--Gupta--Li matrix. -/
def cglCharacterDyadicCorrelation (N q : ℕ)
    (w v : CGLCharacterDyadicRowData q) : ℂ :=
  ∑ j, w.character (cglCharacterDyadicIndex N j) *
    (starRingEnd ℂ) (v.character (cglCharacterDyadicIndex N j)) *
    cglCharacterDyadicPhase N (w.time - v.time) j

/-- Gram entries are exactly the character-twisted correlation sums at the
ordinate difference. -/
theorem inner_cglCharacterDyadicRows (N q : ℕ)
    (w v : CGLCharacterDyadicRowData q) :
    ⟪cglCharacterDyadicRow N q w, cglCharacterDyadicRow N q v⟫_ℂ =
      cglCharacterDyadicCorrelation N q w v := by
  rw [PiLp.inner_apply]
  simp only [cglCharacterDyadicRow, RCLike.inner_apply, map_mul]
  unfold cglCharacterDyadicCorrelation
  apply Finset.sum_congr rfl
  intro j hj
  have hχ : (starRingEnd ℂ) ((starRingEnd ℂ)
      (w.character (cglCharacterDyadicIndex N j))) =
      w.character (cglCharacterDyadicIndex N j) := by simp
  have hphase : (starRingEnd ℂ) ((starRingEnd ℂ)
      (cglCharacterDyadicPhase N w.time j)) = cglCharacterDyadicPhase N w.time j := by simp
  rw [hχ, hphase]
  calc
    _ = w.character (cglCharacterDyadicIndex N j) *
        (starRingEnd ℂ) (v.character (cglCharacterDyadicIndex N j)) *
        (cglCharacterDyadicPhase N w.time j *
          (starRingEnd ℂ) (cglCharacterDyadicPhase N v.time j)) := by ring
    _ = _ := by
      rw [cglCharacterDyadicPhase_mul_conj]

/-- The finite Gram matrix of a character/ordinate packet. -/
def cglCharacterDyadicGram (N q R : ℕ)
    (w : Fin R → CGLCharacterDyadicRowData q) : Matrix (Fin R) (Fin R) ℂ :=
  fun r s => ⟪cglCharacterDyadicRow N q (w r), cglCharacterDyadicRow N q (w s)⟫_ℂ

/-- Explicit source form of every entry of the finite Gram matrix. -/
theorem cglCharacterDyadicGram_apply (N q R : ℕ)
    (w : Fin R → CGLCharacterDyadicRowData q) (r s : Fin R) :
    cglCharacterDyadicGram N q R w r s = cglCharacterDyadicCorrelation N q (w r) (w s) :=
  inner_cglCharacterDyadicRows N q (w r) (w s)

/-- The literal cubic trace expansion of the finite Gram matrix. -/
def cglCharacterDyadicGramCubicTrace (N q R : ℕ)
    (w : Fin R → CGLCharacterDyadicRowData q) : ℂ :=
  ∑ r, ∑ s, ∑ t,
    cglCharacterDyadicGram N q R w r s *
      cglCharacterDyadicGram N q R w s t *
      cglCharacterDyadicGram N q R w t r

/-- The cubic correlation sum is exactly the trace of the Gram cube. -/
theorem cglCharacterDyadicGramCubicTrace_eq_trace (N q R : ℕ)
    (w : Fin R → CGLCharacterDyadicRowData q) :
    cglCharacterDyadicGramCubicTrace N q R w =
      Matrix.trace ((cglCharacterDyadicGram N q R w) *
        (cglCharacterDyadicGram N q R w) * cglCharacterDyadicGram N q R w) := by
  unfold cglCharacterDyadicGramCubicTrace Matrix.trace Matrix.diag
  simp_rw [Matrix.mul_apply, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro r hr
  rw [Finset.sum_comm]

/-- One labelled triple term in the cubic Gram trace. -/
def cglCharacterDyadicGramCubicTerm (N q R : ℕ)
    (w : Fin R → CGLCharacterDyadicRowData q) (rst : Fin R × Fin R × Fin R) : ℂ :=
  cglCharacterDyadicGram N q R w rst.1 rst.2.1 *
    cglCharacterDyadicGram N q R w rst.2.1 rst.2.2 *
    cglCharacterDyadicGram N q R w rst.2.2 rst.1

/-- The finite cube of row labels. -/
def cglCharacterDyadicGramCubicIndexSet (R : ℕ) : Finset (Fin R × Fin R × Fin R) :=
  Finset.univ ×ˢ (Finset.univ ×ˢ Finset.univ)

/-- Product-index form of the cubic trace. -/
theorem cglCharacterDyadicGramCubicTrace_eq_cubeSum (N q R : ℕ)
    (w : Fin R → CGLCharacterDyadicRowData q) :
    cglCharacterDyadicGramCubicTrace N q R w =
      ∑ rst ∈ cglCharacterDyadicGramCubicIndexSet R,
        cglCharacterDyadicGramCubicTerm N q R w rst := by
  unfold cglCharacterDyadicGramCubicTrace cglCharacterDyadicGramCubicIndexSet
    cglCharacterDyadicGramCubicTerm
  simp only [Finset.sum_product]

/-- All-equal row triples in the cubic trace. -/
def cglCharacterDyadicGramCubicDiagonal (N q R : ℕ)
    (w : Fin R → CGLCharacterDyadicRowData q) : ℂ :=
  ∑ rst ∈ (cglCharacterDyadicGramCubicIndexSet R).filter
      (fun rst => rst.1 = rst.2.1 ∧ rst.2.1 = rst.2.2),
    cglCharacterDyadicGramCubicTerm N q R w rst

/-- The complementary, not-all-equal row triples in the cubic trace. -/
def cglCharacterDyadicGramCubicOffDiagonal (N q R : ℕ)
    (w : Fin R → CGLCharacterDyadicRowData q) : ℂ :=
  ∑ rst ∈ (cglCharacterDyadicGramCubicIndexSet R).filter
      (fun rst => ¬ (rst.1 = rst.2.1 ∧ rst.2.1 = rst.2.2)),
    cglCharacterDyadicGramCubicTerm N q R w rst

/-- Exact diagonal/off-diagonal partition of the cubic trace. -/
theorem cglCharacterDyadicGramCubicTrace_eq_diagonal_add_offDiagonal (N q R : ℕ)
    (w : Fin R → CGLCharacterDyadicRowData q) :
    cglCharacterDyadicGramCubicTrace N q R w =
      cglCharacterDyadicGramCubicDiagonal N q R w +
        cglCharacterDyadicGramCubicOffDiagonal N q R w := by
  rw [cglCharacterDyadicGramCubicTrace_eq_cubeSum]
  unfold cglCharacterDyadicGramCubicDiagonal cglCharacterDyadicGramCubicOffDiagonal
  let P : (Fin R × Fin R × Fin R) → Prop :=
    fun rst => rst.1 = rst.2.1 ∧ rst.2.1 = rst.2.2
  let f : Fin R × Fin R × Fin R → ℂ := cglCharacterDyadicGramCubicTerm N q R w
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (s := cglCharacterDyadicGramCubicIndexSet R) (p := P) f
  simp only [P, f] at hsplit
  exact hsplit.symm

/-- One literal six-label summand obtained by expanding a cubic Gram term into
three row labels and three Dirichlet indices. -/
def cglCharacterDyadicGramCubicExpandedTerm (N q R : ℕ)
    (w : Fin R → CGLCharacterDyadicRowData q) (rst : Fin R × Fin R × Fin R)
    (j₁ j₂ j₃ : Fin N) : ℂ :=
  (w rst.1).character (cglCharacterDyadicIndex N j₁) *
      (starRingEnd ℂ) ((w rst.2.1).character (cglCharacterDyadicIndex N j₁)) *
      cglCharacterDyadicPhase N ((w rst.1).time - (w rst.2.1).time) j₁ *
    ((w rst.2.1).character (cglCharacterDyadicIndex N j₂) *
      (starRingEnd ℂ) ((w rst.2.2).character (cglCharacterDyadicIndex N j₂)) *
      cglCharacterDyadicPhase N ((w rst.2.1).time - (w rst.2.2).time) j₂) *
    ((w rst.2.2).character (cglCharacterDyadicIndex N j₃) *
      (starRingEnd ℂ) ((w rst.1).character (cglCharacterDyadicIndex N j₃)) *
      cglCharacterDyadicPhase N ((w rst.2.2).time - (w rst.1).time) j₃)

/-- Exact expansion of one cubic Gram summand into three finite Dirichlet
indices.  This is the finite source expression before Poisson summation. -/
theorem cglCharacterDyadicGramCubicTerm_expand (N q R : ℕ)
    (w : Fin R → CGLCharacterDyadicRowData q) (rst : Fin R × Fin R × Fin R) :
    cglCharacterDyadicGramCubicTerm N q R w rst =
      ∑ j₁, ∑ j₂, ∑ j₃,
        cglCharacterDyadicGramCubicExpandedTerm N q R w rst j₁ j₂ j₃ := by
  unfold cglCharacterDyadicGramCubicTerm
  rw [cglCharacterDyadicGram_apply, cglCharacterDyadicGram_apply,
    cglCharacterDyadicGram_apply]
  unfold cglCharacterDyadicCorrelation cglCharacterDyadicGramCubicExpandedTerm
  rw [Finset.sum_mul_sum]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j₁ hj₁
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j₂ hj₂
  rw [Finset.mul_sum]

end RHTower
