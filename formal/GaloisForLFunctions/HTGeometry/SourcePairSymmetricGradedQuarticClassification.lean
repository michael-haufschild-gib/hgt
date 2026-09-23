import GaloisForLFunctions.HTGeometry.SourcePairPositiveQuarticGradedRealification

/-!
# Sharp classification of symmetric graded quartic source-pair lifts

For real scales `k,l`, use even nodes `a + k b`, `a - k b` and four odd nodes
`l b,l b,-l b,-l b`. The construction preserves the complete quadratic trace exactly on
the negative Pell conic `k² - 2l² = -1`. On that conic its quartic defect factors as

`(k² + 1)b²(12a² + (k² - 3)b²)`.

Consequently universal quartic nonnegativity starts sharply at `k² = 3`, while faithful
realness detection starts sharply at `k² > 3`. This classifies the full symmetric family
containing both the sign-changing canonical `(1,1)` lift and positive `(7,5)` lift. It is a
finite source-coordinate theorem and does not supply the global theta-stage assembly or
source-side vanishing law required by RH.
-/

open Complex Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Symmetric two-node real even block at scale `k`. -/
def sourcePairSymmetricRealEvenBlock (k a b : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.diagonal ![((a + k * b : ℝ) : ℂ), ((a - k * b : ℝ) : ℂ)]

/-- Symmetric four-node real odd block at scale `l`. -/
def sourcePairSymmetricRealOddBlock (l b : ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.diagonal ![((l * b : ℝ) : ℂ), ((l * b : ℝ) : ℂ),
    ((-l * b : ℝ) : ℂ), ((-l * b : ℝ) : ℂ)]

/-- Power trace of the symmetric real even block. -/
def sourcePairSymmetricRealEvenMoment (n : ℕ) (k a b : ℝ) : ℂ :=
  ((a + k * b : ℝ) : ℂ) ^ n + ((a - k * b : ℝ) : ℂ) ^ n

/-- Power trace of the symmetric real odd block. -/
def sourcePairSymmetricRealOddMoment (n : ℕ) (l b : ℝ) : ℂ :=
  2 * ((l * b : ℝ) : ℂ) ^ n + 2 * ((-l * b : ℝ) : ℂ) ^ n

/-- Complete signed power-trace defect against the complex conjugate source pair. -/
def sourcePairSymmetricGradedAnomaly (n : ℕ) (k l a b : ℝ) : ℂ :=
  sourcePairSymmetricRealEvenMoment n k a b -
    sourcePairSymmetricRealOddMoment n l b - sourcePairMoment n a b

/-- Quartic orientation charge after imposing the negative Pell conic. -/
def sourcePairSymmetricQuarticCharge (k a b : ℝ) : ℝ :=
  (k ^ (2 : ℕ) + 1) * b ^ (2 : ℕ) * (12 * a ^ (2 : ℕ) + (k ^ (2 : ℕ) - 3) * b ^ (2 : ℕ))

/-- Universal preservation of the complete quadratic trace. -/
def SourcePairSymmetricTraceTwoPreserving (k l : ℝ) : Prop :=
  ∀ a b : ℝ, sourcePairSymmetricGradedAnomaly 2 k l a b = 0

/-- Universal nonnegativity of the quartic graded trace. -/
def SourcePairSymmetricQuarticNonnegative (k l : ℝ) : Prop :=
  ∀ a b : ℝ, 0 ≤ (sourcePairSymmetricGradedAnomaly 4 k l a b).re

/-- Universal faithful detection of a nonreal source coordinate by the quartic trace. -/
def SourcePairSymmetricQuarticFaithful (k l : ℝ) : Prop :=
  ∀ a b : ℝ, sourcePairSymmetricGradedAnomaly 4 k l a b = 0 ↔ b = 0

theorem sourcePairSymmetricRealEvenBlock_trace_pow (n : ℕ) (k a b : ℝ) :
    (sourcePairSymmetricRealEvenBlock k a b ^ n).trace =
      sourcePairSymmetricRealEvenMoment n k a b := by
  rw [sourcePairSymmetricRealEvenBlock, Matrix.diagonal_pow,
    Matrix.trace_diagonal, Fin.sum_univ_two]
  simp [sourcePairSymmetricRealEvenMoment]

theorem sourcePairSymmetricRealOddBlock_trace_pow (n : ℕ) (l b : ℝ) :
    (sourcePairSymmetricRealOddBlock l b ^ n).trace =
      sourcePairSymmetricRealOddMoment n l b := by
  rw [sourcePairSymmetricRealOddBlock, Matrix.diagonal_pow,
    Matrix.trace_diagonal, Fin.sum_univ_four]
  simp [sourcePairSymmetricRealOddMoment]
  ring

/-- Complete first trace is preserved for every pair of scales. -/
theorem sourcePairSymmetricGradedAnomaly_one (k l a b : ℝ) :
    sourcePairSymmetricGradedAnomaly 1 k l a b = 0 := by
  simp [sourcePairSymmetricGradedAnomaly, sourcePairSymmetricRealEvenMoment,
    sourcePairSymmetricRealOddMoment, sourcePairMoment]

/-- Exact quadratic defect before imposing any scale relation. -/
theorem sourcePairSymmetricGradedAnomaly_two_formula (k l a b : ℝ) :
    sourcePairSymmetricGradedAnomaly 2 k l a b =
      ((2 * (k ^ (2 : ℕ) - 2 * l ^ (2 : ℕ) + 1) * b ^ (2 : ℕ) : ℝ) : ℂ) := by
  simp [sourcePairSymmetricGradedAnomaly, sourcePairSymmetricRealEvenMoment,
    sourcePairSymmetricRealOddMoment, sourcePairMoment]
  ring_nf
  simp [Complex.I_sq]
  ring

/-- Exact quartic defect before imposing any scale relation. -/
theorem sourcePairSymmetricGradedAnomaly_four_formula (k l a b : ℝ) :
    sourcePairSymmetricGradedAnomaly 4 k l a b =
      ((12 * (k ^ (2 : ℕ) + 1) * a ^ (2 : ℕ) * b ^ (2 : ℕ) +
        (2 * k ^ (4 : ℕ) - 4 * l ^ (4 : ℕ) - 2) * b ^ (4 : ℕ) : ℝ) : ℂ) := by
  simp [sourcePairSymmetricGradedAnomaly, sourcePairSymmetricRealEvenMoment,
    sourcePairSymmetricRealOddMoment, sourcePairMoment]
  ring_nf
  norm_num [Complex.I_sq]
  ring

/-- Universal quadratic exactness is precisely the negative Pell conic. -/
theorem sourcePairSymmetricTraceTwoPreserving_iff (k l : ℝ) :
    SourcePairSymmetricTraceTwoPreserving k l ↔ k ^ (2 : ℕ) - 2 * l ^ (2 : ℕ) = -1 := by
  constructor
  · intro h
    have hz := h 0 1
    rw [sourcePairSymmetricGradedAnomaly_two_formula, Complex.ofReal_eq_zero] at hz
    norm_num at hz
    nlinarith
  · intro h a b
    rw [sourcePairSymmetricGradedAnomaly_two_formula, Complex.ofReal_eq_zero]
    nlinarith

/-- On the trace-preserving conic, the quartic defect has one sharp factored charge. -/
theorem sourcePairSymmetricGradedAnomaly_four_of_pell (k l a b : ℝ)
    (hpell : k ^ (2 : ℕ) - 2 * l ^ (2 : ℕ) = -1) :
    sourcePairSymmetricGradedAnomaly 4 k l a b =
      (sourcePairSymmetricQuarticCharge k a b : ℂ) := by
  have hl2 : 2 * l ^ (2 : ℕ) = k ^ (2 : ℕ) + 1 := by nlinarith
  have hl4 : 4 * l ^ (4 : ℕ) = (k ^ (2 : ℕ) + 1) ^ (2 : ℕ) := by
    calc
      4 * l ^ (4 : ℕ) = (2 * l ^ (2 : ℕ)) ^ (2 : ℕ) := by ring
      _ = (k ^ (2 : ℕ) + 1) ^ (2 : ℕ) := by rw [hl2]
  have hcoeff : 2 * k ^ (4 : ℕ) - 4 * l ^ (4 : ℕ) - 2 =
      (k ^ (2 : ℕ) + 1) * (k ^ (2 : ℕ) - 3) := by
    rw [hl4]
    ring
  rw [sourcePairSymmetricGradedAnomaly_four_formula]
  norm_cast
  simp only [sourcePairSymmetricQuarticCharge]
  rw [hcoeff]
  ring

/-- The factored charge is universally nonnegative exactly at and above the boundary `k²=3`. -/
theorem sourcePairSymmetricQuarticCharge_nonnegative_iff (k : ℝ) :
    (∀ a b : ℝ, 0 ≤ sourcePairSymmetricQuarticCharge k a b) ↔ 3 ≤ k ^ (2 : ℕ) := by
  constructor
  · intro h
    have h01 := h 0 1
    simp [sourcePairSymmetricQuarticCharge] at h01
    nlinarith [sq_nonneg k]
  · intro hk a b
    have hk1 : 0 ≤ k ^ (2 : ℕ) + 1 := by nlinarith [sq_nonneg k]
    have hinner : 0 ≤ 12 * a ^ (2 : ℕ) + (k ^ (2 : ℕ) - 3) * b ^ (2 : ℕ) := by
      positivity
    exact mul_nonneg (mul_nonneg hk1 (sq_nonneg b)) hinner

/-- Above the sharp boundary, charge zero is equivalent to a real source pair. -/
theorem sourcePairSymmetricQuarticCharge_eq_zero_iff_of_gt (k a b : ℝ)
    (hk : 3 < k ^ (2 : ℕ)) :
    sourcePairSymmetricQuarticCharge k a b = 0 ↔ b = 0 := by
  constructor
  · intro h
    by_contra hb
    have hk1 : 0 < k ^ (2 : ℕ) + 1 := by nlinarith [sq_nonneg k]
    have hb2 : 0 < b ^ (2 : ℕ) := sq_pos_of_ne_zero hb
    have hinner : 0 < 12 * a ^ (2 : ℕ) + (k ^ (2 : ℕ) - 3) * b ^ (2 : ℕ) := by
      positivity
    have hpos : 0 < sourcePairSymmetricQuarticCharge k a b := by
      exact mul_pos (mul_pos hk1 hb2) hinner
    exact hpos.ne' h
  · rintro rfl
    simp [sourcePairSymmetricQuarticCharge]

/-- Complete sharp classification of trace-preserving quartic positivity. -/
theorem sourcePairSymmetric_traceTwo_and_quarticNonnegative_iff (k l : ℝ) :
    (SourcePairSymmetricTraceTwoPreserving k l ∧
      SourcePairSymmetricQuarticNonnegative k l) ↔
      k ^ (2 : ℕ) - 2 * l ^ (2 : ℕ) = -1 ∧ 3 ≤ k ^ (2 : ℕ) := by
  constructor
  · rintro ⟨htrace, hnonneg⟩
    have hpell := (sourcePairSymmetricTraceTwoPreserving_iff k l).mp htrace
    refine ⟨hpell, ?_⟩
    rw [← sourcePairSymmetricQuarticCharge_nonnegative_iff]
    intro a b
    have h := hnonneg a b
    rw [sourcePairSymmetricGradedAnomaly_four_of_pell k l a b hpell] at h
    simpa using h
  · rintro ⟨hpell, hk⟩
    refine ⟨(sourcePairSymmetricTraceTwoPreserving_iff k l).mpr hpell, ?_⟩
    intro a b
    rw [sourcePairSymmetricGradedAnomaly_four_of_pell k l a b hpell]
    simpa using (sourcePairSymmetricQuarticCharge_nonnegative_iff k).mpr hk a b

/-- Complete sharp classification of trace-preserving quartic faithfulness.

For the difficult converse, every `k² ≤ 3` admits the explicit nonreal zero-charge witness
`b=1`, `a=sqrt((3-k²)/12)`.
-/
theorem sourcePairSymmetric_traceTwo_and_quarticFaithful_iff (k l : ℝ) :
    (SourcePairSymmetricTraceTwoPreserving k l ∧
      SourcePairSymmetricQuarticFaithful k l) ↔
      k ^ (2 : ℕ) - 2 * l ^ (2 : ℕ) = -1 ∧ 3 < k ^ (2 : ℕ) := by
  constructor
  · rintro ⟨htrace, hfaithful⟩
    have hpell := (sourcePairSymmetricTraceTwoPreserving_iff k l).mp htrace
    refine ⟨hpell, ?_⟩
    by_contra hk
    have hkle : k ^ (2 : ℕ) ≤ 3 := le_of_not_gt hk
    let a : ℝ := Real.sqrt ((3 - k ^ (2 : ℕ)) / 12)
    have hrad : 0 ≤ (3 - k ^ (2 : ℕ)) / 12 := by positivity
    have ha2 : a ^ (2 : ℕ) = (3 - k ^ (2 : ℕ)) / 12 := by
      exact Real.sq_sqrt hrad
    have hinner : 12 * a ^ (2 : ℕ) + (k ^ (2 : ℕ) - 3) = 0 := by
      rw [ha2]
      ring
    have hcharge : sourcePairSymmetricQuarticCharge k a 1 = 0 := by
      simp [sourcePairSymmetricQuarticCharge, hinner]
    have hanomaly : sourcePairSymmetricGradedAnomaly 4 k l a 1 = 0 := by
      rw [sourcePairSymmetricGradedAnomaly_four_of_pell k l a 1 hpell,
        Complex.ofReal_eq_zero]
      exact hcharge
    have hone : (1 : ℝ) = 0 := (hfaithful a 1).mp hanomaly
    norm_num at hone
  · rintro ⟨hpell, hk⟩
    refine ⟨(sourcePairSymmetricTraceTwoPreserving_iff k l).mpr hpell, ?_⟩
    intro a b
    rw [sourcePairSymmetricGradedAnomaly_four_of_pell k l a b hpell,
      Complex.ofReal_eq_zero]
    exact sourcePairSymmetricQuarticCharge_eq_zero_iff_of_gt k a b hk

end

end GaloisForLFunctions.HTGeometry
