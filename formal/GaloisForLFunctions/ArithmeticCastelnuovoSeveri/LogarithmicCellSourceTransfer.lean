import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.HighCellRemainder
import GaloisForLFunctions.RHTower.ThetaEulerLogCellResidueChannels

/-!
# Actual translations of complete logarithmic cell sections

The unnormalized logarithmic cell vectors are orthogonal with square norms equal to their
cell widths. Integer translation subdivides each cell exactly. Consequently the mixed
Hilbert-space pairing is the divisibility spine plus every signed successor contribution.
The high-cell estimate bounds the complete prime-weighted error in this actual pairing.
-/

noncomputable section

open Finset MeasureTheory

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri.LogCells

open BiarithmeticGaugeGeometry _root_.RHTower
open GaloisForLFunctions.HTGeometry

local notation "L²₊" => Lp ℂ 2 halfLineMeasure

/-- The indicator of the `n`th logarithmic cell as an actual half-line `L²` vector. -/
def cellAtom (n : ℕ) : L²₊ :=
  if hn : 0 < n then
    (Real.sqrt (logCellWidth n) : ℂ) • logCellVec (n.toPNat hn)
  else 0

/-- A finite section with independent real coefficients on complete logarithmic cells. -/
def cellSection (c : ℕ → ℝ) (A X : ℕ) : L²₊ :=
  ∑ a ∈ Icc A X, (c a : ℂ) • cellAtom a

theorem inner_cellAtom {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    inner ℂ (cellAtom a) (cellAtom b) = if a = b then (logCellWidth a : ℂ) else 0 := by
  classical
  have ha0 : 0 < a := by omega
  have hb0 : 0 < b := by omega
  rw [cellAtom, dif_pos ha0, cellAtom, dif_pos hb0, inner_smul_left, inner_smul_right,
    orthonormal_iff_ite.mp orthonormal_logCellVec]
  by_cases hab : a = b
  · subst b
    simp only [ite_true, mul_one, Complex.conj_ofReal, ← Complex.ofReal_mul]
    rw [← pow_two, Real.sq_sqrt (logCellWidth_pos ha).le]
  · have hab' : a.toPNat ha0 ≠ b.toPNat hb0 := fun h => hab (congrArg PNat.val h)
    simp only [if_neg hab, if_neg hab', mul_zero]

/-- Multiplicative translation preserves the whole cell, including all successor subcells. -/
theorem halfLineRightShift_cellAtom {a m : ℕ} (ha : 1 ≤ a) (hm : 2 ≤ m) :
    halfLineRightShift (Real.log m) (cellAtom a) =
      ∑ r ∈ range m, cellAtom (a * m + r) := by
  have ha0 : 0 < a := by omega
  rw [cellAtom, dif_pos ha0, map_smul, halfLineRightShift_logCellVec hm, Finset.smul_sum,
    ← Fin.sum_univ_eq_sum_range (fun r => cellAtom (a * m + r))]
  apply sum_congr rfl
  intro r _
  have hb : 1 ≤ a * m + (r : ℕ) := by
    have h := Nat.mul_le_mul ha (by omega : 1 ≤ m)
    omega
  have hdiv : (a * m + (r : ℕ)) / m = a := by
    rw [Nat.mul_comm a m, Nat.mul_add_div (by omega : 0 < m),
      Nat.div_eq_of_lt r.isLt, add_zero]
  have hwa := logCellWidth_pos ha
  have hwb := logCellWidth_pos hb
  have hs : Real.sqrt (logCellWidth a) *
      Real.sqrt (logCellWidth (a * m + r) / logCellWidth a) =
      Real.sqrt (logCellWidth (a * m + r)) := by
    have he : (Real.sqrt (logCellWidth a) *
        Real.sqrt (logCellWidth (a * m + r) / logCellWidth a)) ^ 2 =
        logCellWidth (a * m + r) := by
      rw [mul_pow, Real.sq_sqrt hwa.le, Real.sq_sqrt (div_nonneg hwb.le hwa.le)]
      field_simp
    nlinarith only [he, Real.sq_sqrt hwb.le,
      mul_nonneg (Real.sqrt_nonneg (logCellWidth a))
        (Real.sqrt_nonneg (logCellWidth (a * m + r) / logCellWidth a)),
      Real.sqrt_nonneg (logCellWidth (a * m + r))]
  simp only [cellAtom, dif_pos (by omega : 0 < a * m + (r : ℕ)), smul_smul,
    logCellWeight, coe_toPNat, hdiv]
  change ((Real.sqrt (logCellWidth a) : ℂ) *
    (Real.sqrt (logCellWidth (a * m + r) / logCellWidth a) : ℂ)) • _ = _
  rw [← Complex.ofReal_mul, hs]

/-- An individual cell extracts its coefficient, even beyond the finite section's horizon. -/
theorem inner_cellAtom_cellSection (d : ℕ → ℝ) (X : ℕ) {a : ℕ} (ha : 1 ≤ a)
    (hs : ∀ n, X < n → d n = 0) :
    inner ℂ (cellAtom a) (cellSection d 1 X) = (logCellWidth a * d a : ℝ) := by
  classical
  rw [cellSection, inner_sum]
  have hterm : ∀ b ∈ Icc 1 X,
      inner ℂ (cellAtom a) ((d b : ℂ) • cellAtom b) =
        if a = b then ((logCellWidth a * d a : ℝ) : ℂ) else 0 := by
    intro b hb
    rw [inner_smul_right, inner_cellAtom ha (mem_Icc.mp hb).1]
    split_ifs with h
    · subst b
      push_cast
      ring
    · simp only [mul_zero]
  simp_rw [sum_congr rfl hterm]
  by_cases haX : a ≤ X
  · simp only [sum_ite_eq, mem_Icc, ha, haX, and_self, if_true]
  · have hzero := hs a (by omega)
    simp only [sum_ite_eq, mem_Icc, ha, haX, and_false, if_false, hzero, mul_zero,
      Complex.ofReal_zero]

/-- The complete mixed cell sum is the actual translated `L²` pairing. -/
theorem inner_shift_cellSection (c d : ℕ → ℝ) {A : ℕ} (hA : 1 ≤ A)
    (X : ℕ) {m : ℕ} (hm : 2 ≤ m) (hs : ∀ n, X < n → d n = 0) :
    inner ℂ (halfLineRightShift (Real.log m) (cellSection c A X))
      (cellSection d 1 X) = (cellShiftCorr c d A X m : ℝ) := by
  rw [cellSection, map_sum, sum_inner]
  unfold cellShiftCorr
  rw [Complex.ofReal_sum]
  apply sum_congr rfl
  intro a ha
  have ha1 := hA.trans (mem_Icc.mp ha).1
  rw [map_smul, inner_smul_left, halfLineRightShift_cellAtom ha1 hm, sum_inner,
    Complex.conj_ofReal]
  have hterms : ∀ r ∈ range m,
      inner ℂ (cellAtom (a * m + r)) (cellSection d 1 X) =
        (logCellWidth (a * m + r) * d (a * m + r) : ℝ) := by
    intro r _
    apply inner_cellAtom_cellSection d X _ hs
    have h := Nat.mul_le_mul ha1 (by omega : 1 ≤ m)
    omega
  rw [sum_congr rfl hterms]
  simp only [← Complex.ofReal_sum, ← Complex.ofReal_mul]

theorem inner_shift_cellSection_eq (c d : ℕ → ℝ) {A : ℕ} (hA : 1 ≤ A)
    (X : ℕ) {m : ℕ} (hm : 2 ≤ m) (hs : ∀ n, X < n → d n = 0) :
    (inner ℂ (halfLineRightShift (Real.log m) (cellSection c A X))
      (cellSection d 1 X)).re = cellShiftCorr c d A X m := by
  rw [inner_shift_cellSection c d hA X hm hs, Complex.ofReal_re]

/-- The prime-weighted mixed pairing of actual translated sections. -/
def primeSectionPair (c d : ℕ → ℝ) (A X M : ℕ) : ℝ :=
  ∑ m ∈ Icc 1 M, (2 * ArithmeticFunction.vonMangoldt m / Real.sqrt m) *
    (inner ℂ (halfLineRightShift (Real.log m) (cellSection c A X))
      (cellSection d 1 X)).re

/-- The divisibility contribution with the same signed coefficients and prime weights. -/
def primeCellSpine (c d : ℕ → ℝ) (A X M : ℕ) : ℝ :=
  ∑ m ∈ Icc 1 M, (2 * ArithmeticFunction.vonMangoldt m / Real.sqrt m) *
    cellSpine c d A X m

theorem primeSectionPair_sub_spine (c d : ℕ → ℝ) {A : ℕ} (hA : 1 ≤ A)
    (X M : ℕ) (hs : ∀ n, X < n → d n = 0) :
    primeSectionPair c d A X M - primeCellSpine c d A X M =
      primeCellRemainder c d A X M := by
  unfold primeSectionPair primeCellSpine primeCellRemainder
  rw [← sum_sub_distrib]
  apply sum_congr rfl
  intro m hm
  by_cases hm1 : m = 1
  · subst m
    simp
  · have hm2 : 2 ≤ m := by have := (mem_Icc.mp hm).1; omega
    rw [inner_shift_cellSection_eq c d hA X hm2 hs,
      cellShiftCorr_eq_spine_add_remainder c d hA X (by omega : 1 ≤ m)]
    ring

/-- Every signed prime-weighted successor term is paid inside the actual `L²` pairing. -/
theorem abs_primeSectionPair_sub_spine_le (c d : ℕ → ℝ) {A : ℕ} (hA : 1 ≤ A)
    (X M : ℕ) (hs : ∀ n, X < n → d n = 0) :
    |primeSectionPair c d A X M - primeCellSpine c d A X M| ≤
      primeWeightSum M * (Real.sqrt (cellMass c A X) *
        Real.sqrt (biarithmeticSobolevEnergy d X) / A) := by
  rw [primeSectionPair_sub_spine c d hA X M hs]
  exact abs_primeCellRemainder_le c d hA X M hs

/-- Beyond the multiplicative support ratio every translated cell pairing vanishes. -/
theorem cellShiftCorr_eq_zero (c d : ℕ → ℝ) (A X m : ℕ)
    (hX : X < A * m) (hs : ∀ n, X < n → d n = 0) :
    cellShiftCorr c d A X m = 0 := by
  unfold cellShiftCorr
  apply sum_eq_zero
  intro a ha
  have ham : A * m ≤ a * m := Nat.mul_le_mul_right m (mem_Icc.mp ha).1
  have hzero : ∑ r ∈ range m, logCellWidth (a * m + r) * d (a * m + r) = 0 := by
    apply sum_eq_zero
    intro r _
    rw [hs (a * m + r) (by omega), mul_zero]
  rw [hzero, mul_zero]

/-- The full prime series of actual cell-section correlations. -/
def fullPrimeSectionPair (c d : ℕ → ℝ) (A X : ℕ) : ℝ :=
  ∑' m : ℕ, (2 * ArithmeticFunction.vonMangoldt m / Real.sqrt m) *
    (inner ℂ (halfLineRightShift (Real.log m) (cellSection c A X))
      (cellSection d 1 X)).re

/-- The horizon is forced by support; no prime tail is omitted. -/
theorem fullPrimeSectionPair_eq (c d : ℕ → ℝ) {A : ℕ} (hA : 1 ≤ A)
    (X : ℕ) {M : ℕ} (hM : 1 ≤ M) (hX : X ≤ A * M)
    (hs : ∀ n, X < n → d n = 0) :
    fullPrimeSectionPair c d A X = primeSectionPair c d A X M := by
  unfold fullPrimeSectionPair primeSectionPair
  apply tsum_eq_sum
  intro m hm
  by_cases hm0 : m = 0
  · subst m
    simp
  · have hMm : M < m := by simp only [mem_Icc] at hm; omega
    have hAm : A * M < A * m := Nat.mul_lt_mul_of_pos_left hMm (by omega)
    rw [inner_shift_cellSection_eq c d hA X (by omega : 2 ≤ m) hs,
      cellShiftCorr_eq_zero c d A X m (hX.trans_lt hAm) hs, mul_zero]

#print axioms inner_shift_cellSection_eq
#print axioms abs_primeSectionPair_sub_spine_le
#print axioms fullPrimeSectionPair_eq

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri.LogCells
