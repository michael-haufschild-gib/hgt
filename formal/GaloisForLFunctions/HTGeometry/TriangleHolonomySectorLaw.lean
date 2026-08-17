import Mathlib.Analysis.Matrix.PosDef

/-!
# Exact scalar triangle holonomy law

This file proves the phase-sensitive positive-semidefinite wall for every scalar spectral sector
of a three-context unitary-link kernel.  Coherence amplitudes live intrinsically in `[0,1]` and the
holonomy phase has unit norm.  The final theorem therefore has no external assumptions.

The proof includes the singular boundary `a = 1`: determinant nonnegativity forces the remaining
amplitudes to coincide and, unless they vanish, forces the holonomy phase to equal one.
-/

open Matrix
open scoped ComplexOrder Matrix

namespace GaloisForLFunctions.HTGeometry

/-- Physically admissible scalar coherence amplitude. -/
abbrev CoherenceAmplitude := Set.Icc (0 : ℝ) 1

/-- Unit-modulus scalar holonomy sector. -/
structure UnitaryPhase where
  val : ℂ
  norm_eq_one : ‖val‖ = 1

/-- Complete intrinsic data of one spectral sector of a three-context unitary-link kernel. -/
structure TriangleSectorDatum where
  edge01 : CoherenceAmplitude
  edge12 : CoherenceAmplitude
  edge20 : CoherenceAmplitude
  phase : UnitaryPhase

/-- A scalar spectral sector of a three-context unitary-link kernel. -/
def triangleSectorMatrix (a b c : ℝ) (z : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![1, a, c * star z; a, 1, b; c * z, b, 1]

/-- Determinant margin of a scalar triangle sector. -/
def triangleSectorMargin (a b c : ℝ) (z : ℂ) : ℝ :=
  1 - a ^ 2 - b ^ 2 - c ^ 2 + 2 * a * b * c * z.re

theorem triangleSectorMatrix_isHermitian (a b c : ℝ) (z : ℂ) :
    Matrix.IsHermitian (triangleSectorMatrix a b c z) := by
  apply Matrix.IsHermitian.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [triangleSectorMatrix, mul_comm]

theorem triangleSectorMatrix_det (a b c : ℝ) (z : ℂ) (
    hz : ‖z‖ = 1) :
    (triangleSectorMatrix a b c z).det = triangleSectorMargin a b c z := by
  have hnormSq : Complex.normSq z = 1 := by
    rw [Complex.normSq_eq_norm_sq, hz]
    norm_num
  have hzsq : z.re ^ 2 + z.im ^ 2 = 1 := by
    rw [Complex.normSq_apply] at hnormSq
    nlinarith
  rw [Matrix.det_fin_three]
  apply Complex.ext
  · simp [triangleSectorMatrix, triangleSectorMargin, -Complex.ofReal_pow]
    nlinarith
  · simp [triangleSectorMatrix, triangleSectorMargin, -Complex.ofReal_pow]
    ring

theorem triangleSectorMatrix_posSemidef_implies
    (a b c : ℝ) (z : ℂ) (hz : ‖z‖ = 1)
    (h : Matrix.PosSemidef (triangleSectorMatrix a b c z)) :
    a ≤ 1 ∧ b ≤ 1 ∧ c ≤ 1 ∧ 0 ≤ triangleSectorMargin a b c z := by
  have ha := h.dotProduct_mulVec_nonneg (![1, -1, 0] : Fin 3 → ℂ)
  have hb := h.dotProduct_mulVec_nonneg (![0, 1, -1] : Fin 3 → ℂ)
  have hc := h.dotProduct_mulVec_nonneg (![1, 0, -z] : Fin 3 → ℂ)
  have hdet := h.det_nonneg
  have hnormSq : Complex.normSq z = 1 := by
    rw [Complex.normSq_eq_norm_sq, hz]
    norm_num
  have hunit : star z * z = 1 := by
    change (starRingEnd ℂ) z * z = 1
    rw [← Complex.normSq_eq_conj_mul_self]
    exact_mod_cast hnormSq
  have ha' := (Complex.nonneg_iff.mp ha).1
  have hb' := (Complex.nonneg_iff.mp hb).1
  simp [triangleSectorMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_three] at ha' hb'
  have hcform :
        star (![1, 0, -z] : Fin 3 → ℂ) ⬝ᵥ
          (triangleSectorMatrix a b c z).mulVec (![1, 0, -z] : Fin 3 → ℂ) =
        ((2 * (1 - c) : ℝ) : ℂ) := by
    simp [triangleSectorMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
    linear_combination (1 - 2 * (c : ℂ)) * hunit
  rw [hcform] at hc
  have hc' := (Complex.nonneg_iff.mp hc).1
  change 0 ≤ 2 * (1 - c) at hc'
  rw [triangleSectorMatrix_det a b c z hz] at hdet
  have hdet' := (Complex.nonneg_iff.mp hdet).1
  change 0 ≤ triangleSectorMargin a b c z at hdet'
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  · simpa using hdet'

theorem triangleSectorMatrix_posSemidef_of_margin
    (a b c : ℝ) (z : ℂ) (hz : ‖z‖ = 1)
    (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) (hc0 : 0 ≤ c)
    (ha1 : a ≤ 1) (hb1 : b ≤ 1) (hc1 : c ≤ 1)
    (hmargin : 0 ≤ triangleSectorMargin a b c z) :
    Matrix.PosSemidef (triangleSectorMatrix a b c z) := by
  by_cases ha : a < 1
  · let A : ℝ := 1 - a ^ 2
    let B : ℂ := b - a * c * star z
    let D : ℝ := triangleSectorMargin a b c z
    have hA : 0 < A := by
      dsimp [A]
      nlinarith
    have hAne : (A : ℂ) ≠ 0 := by exact_mod_cast hA.ne'
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
      (triangleSectorMatrix_isHermitian a b c z)
    intro x
    let y₀ : ℂ := x 0 + a * x 1 + c * star z * x 2
    let y₁ : ℂ := x 1 + (B / A) * x 2
    have hnormSq : Complex.normSq z = 1 := by
      rw [Complex.normSq_eq_norm_sq, hz]
      norm_num
    have hform :
        star x ⬝ᵥ (triangleSectorMatrix a b c z).mulVec x =
          ((Complex.normSq y₀ + A * Complex.normSq y₁ +
            (D / A) * Complex.normSq (x 2) : ℝ) : ℂ) := by
      simp [triangleSectorMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
        y₀, y₁, B, D, triangleSectorMargin,
        Complex.normSq_eq_conj_mul_self]
      field_simp [hAne]
      dsimp [A]
      have hunit : (starRingEnd ℂ) z * z = 1 := by
        rw [← Complex.normSq_eq_conj_mul_self]
        exact_mod_cast hnormSq
      have hsum : z + (starRingEnd ℂ) z = ((2 * z.re : ℝ) : ℂ) := by
        apply Complex.ext <;> simp
        ring
      push_cast at hsum ⊢
      linear_combination
        (-((c : ℂ) ^ 2) *
          (starRingEnd ℂ) (x 2) * x 2) * hunit +
        ((a : ℂ) * (b : ℂ) * (c : ℂ) *
          (starRingEnd ℂ) (x 2) * x 2) * hsum
    rw [hform]
    rw [Complex.nonneg_iff]
    constructor
    · simp only [Complex.ofReal_re]
      exact add_nonneg
        (add_nonneg (Complex.normSq_nonneg _)
          (mul_nonneg hA.le (Complex.normSq_nonneg _)))
        (mul_nonneg (div_nonneg hmargin hA.le) (Complex.normSq_nonneg _))
    · simp
  · have haeq : a = 1 := le_antisymm ha1 (le_of_not_gt ha)
    subst a
    have hzre : z.re ≤ 1 := by
      have := Complex.abs_re_le_norm z
      rw [hz] at this
      exact le_trans (le_abs_self z.re) this
    have hdecomp :
        triangleSectorMargin 1 b c z = -(b - c) ^ 2 - 2 * b * c * (1 - z.re) := by
      simp [triangleSectorMargin]
      ring
    have hbc : b = c := by
      rw [hdecomp] at hmargin
      have hsecond : 0 ≤ 2 * b * c * (1 - z.re) := by
        exact mul_nonneg (by positivity) (sub_nonneg.mpr hzre)
      nlinarith [sq_nonneg (b - c)]
    subst b
    by_cases hc : c = 0
    · subst c
      apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
        (triangleSectorMatrix_isHermitian 1 0 0 z)
      intro x
      have hform :
          star x ⬝ᵥ (triangleSectorMatrix 1 0 0 z).mulVec x =
            ((Complex.normSq (x 0 + x 1) + Complex.normSq (x 2) : ℝ) : ℂ) := by
        simp [triangleSectorMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
          Complex.normSq_eq_conj_mul_self]
        ring
      rw [hform, Complex.nonneg_iff]
      constructor
      · change 0 ≤ Complex.normSq (x 0 + x 1) + Complex.normSq (x 2)
        exact add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)
      · norm_num
    · have hcpos : 0 < c := lt_of_le_of_ne hc0 (Ne.symm hc)
      have hzre_eq : z.re = 1 := by
        rw [hdecomp] at hmargin
        simp at hmargin
        have hfac : 0 < 2 * c * c := by positivity
        nlinarith
      have hzim : z.im = 0 := by
        have hnormSq : Complex.normSq z = 1 := by
          rw [Complex.normSq_eq_norm_sq, hz]
          norm_num
        rw [Complex.normSq_apply, hzre_eq] at hnormSq
        nlinarith [sq_nonneg z.im]
      have hzeq : z = 1 := by
        apply Complex.ext
        · simpa using hzre_eq
        · simpa using hzim
      subst z
      apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
        (triangleSectorMatrix_isHermitian 1 c c 1)
      intro x
      have hform :
          star x ⬝ᵥ (triangleSectorMatrix 1 c c 1).mulVec x =
            ((Complex.normSq (x 0 + x 1 + c * x 2) +
              (1 - c ^ 2) * Complex.normSq (x 2) : ℝ) : ℂ) := by
        simp [triangleSectorMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
          Complex.normSq_eq_conj_mul_self]
        ring
      rw [hform, Complex.nonneg_iff]
      constructor
      · simp only [Complex.ofReal_re]
        exact add_nonneg (Complex.normSq_nonneg _)
          (mul_nonneg (by nlinarith) (Complex.normSq_nonneg _))
      · norm_num [← Complex.ofReal_pow]

/-- Matrix carried by an intrinsically admissible triangle sector. -/
def TriangleSectorDatum.matrix (p : TriangleSectorDatum) : Matrix (Fin 3) (Fin 3) ℂ :=
  triangleSectorMatrix p.edge01 p.edge12 p.edge20 p.phase.val

/-- Exact scalar triangle law: positivity is equivalent to a single phase-sensitive cubic wall.
The amplitude interval and unit-holonomy condition are part of the datum, so the theorem has no
external premises. -/
theorem TriangleSectorDatum.posSemidef_iff (p : TriangleSectorDatum) :
    Matrix.PosSemidef p.matrix ↔
      (p.edge01 : ℝ) ^ 2 + (p.edge12 : ℝ) ^ 2 + (p.edge20 : ℝ) ^ 2 -
          2 * p.edge01 * p.edge12 * p.edge20 * p.phase.val.re ≤ 1 := by
  rw [show p.matrix = triangleSectorMatrix p.edge01 p.edge12 p.edge20 p.phase.val from rfl]
  constructor
  · intro h
    have hm := (triangleSectorMatrix_posSemidef_implies
      p.edge01 p.edge12 p.edge20 p.phase.val p.phase.norm_eq_one h).2.2.2
    dsimp [triangleSectorMargin] at hm
    nlinarith
  · intro h
    apply triangleSectorMatrix_posSemidef_of_margin
      p.edge01 p.edge12 p.edge20 p.phase.val p.phase.norm_eq_one
      p.edge01.2.1 p.edge12.2.1 p.edge20.2.1
      p.edge01.2.2 p.edge12.2.2 p.edge20.2.2
    dsimp [triangleSectorMargin]
    nlinarith

end GaloisForLFunctions.HTGeometry
