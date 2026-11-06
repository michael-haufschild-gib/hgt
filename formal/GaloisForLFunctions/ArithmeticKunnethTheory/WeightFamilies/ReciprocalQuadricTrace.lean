import GaloisForLFunctions.ArithmeticKunnethTheory.WeightFamilies.TransverseQuadraticForm
import GaloisForLFunctions.ArithmeticKunnethTheory.WeightFamilies.ProjectiveQuadricCounts

/-!
# The reciprocal quadric at a torus critical point and its trace

At a sign point `x` of `Σxᵢ = 0` with `r` negative coordinates among `n = m + 2`, the reciprocal function
vanishes to second order, with leading form the transverse quadratic form `Q`.  This module computes the
projective zero locus of `Q` over every finite extension.

* **Exceptional directions.**  A chart vector `w` lies on the tangent cone exactly when the reciprocal
  series along `x + t τ(w)` vanishes to order at least three
  (`X_pow_three_dvd_reciprocalSeries_iff`).  So `ProjectiveQuadric Q` is the set of directions of the
  blow-up of the reciprocal locus at `x`.
* **Count.**  For `m = 2k + 2`, `#P(Q = 0) = Σ_{j ≤ 2k} q^j + χ((−1)^{k+r}) q^k`
  (`reciprocalQuadric_card_even`); for `m = 2k + 1`, `#P(Q = 0) = Σ_{j < 2k} q^j`
  (`reciprocalQuadric_card_odd`).
* **Trace.**  Over an extension of degree `d`, the even count is `Σ_{j ≤ 2k} (q^j)^d + α^d` with
  `α = χ((−1)^{k+r}) q^k` (`reciprocalQuadric_card_even_extension`): one eigenvalue of weight `2k`
  beyond the ambient ones, with the sign read at the base field.
-/

open Finset Matrix
open scoped Matrix
noncomputable section
namespace GaloisForLFunctions.ArithmeticKunnethTheory.WeightFamilies

variable {F : Type*} [Field F]

/-- The normalized sign point with negative coordinates `S`. -/
def signPoint {m : ℕ} (S : Finset (Fin (m + 1))) [Fintype F] [DecidableEq F] : Fin (m + 2) → F :=
  Fin.cons 1 (fun i => (signedMomentTorus (F := F) S i : F))

theorem reciprocalTransverseMatrix_isSymm {m : ℕ} (x : Fin (m + 2) → F) :
    (reciprocalTransverseMatrix x).IsSymm := by
  classical
  ext i j
  simp only [transpose_apply, reciprocalTransverseMatrix, Matrix.add_apply, diagonal_apply,
    vecMulVec_apply, mul_one]
  by_cases h : i = j
  · subst h
    rfl
  · rw [if_neg h, if_neg (Ne.symm h)]

/-- The transverse quadratic form as a quadratic map. -/
def reciprocalTransverseForm {m : ℕ} [Invertible (2 : F)] (x : Fin (m + 2) → F) :
    QuadraticForm F (Fin m → F) :=
  (reciprocalTransverseMatrix x).toQuadraticForm'

theorem reciprocalTransverseForm_apply {m : ℕ} [Invertible (2 : F)] (x : Fin (m + 2) → F)
    (w : Fin m → F) :
    reciprocalTransverseForm x w = w ⬝ᵥ (reciprocalTransverseMatrix x).mulVec w := by
  simp [reciprocalTransverseForm, Matrix.toQuadraticForm', LinearMap.BilinMap.toQuadraticMap_apply,
    Matrix.toLinearMap₂'_apply', dotProduct]

/-- The chart form is the reciprocal quadratic coefficient. -/
theorem reciprocalTransverseForm_eq_quadratic {m : ℕ} [Invertible (2 : F)] (x : Fin (m + 2) → F)
    (w : Fin m → F) :
    reciprocalTransverseForm x w = reciprocalQuadratic x (reciprocalTangentVector w) := by
  rw [reciprocalTransverseForm_apply, reciprocalQuadratic_tangentVector_eq_matrix]

/-- **Exceptional directions.**  At a critical sign point, a chart vector is on the tangent cone exactly
when the reciprocal series along it vanishes to order at least three. -/
theorem X_pow_three_dvd_reciprocalSeries_iff {m : ℕ} [Invertible (2 : F)] (x : Fin (m + 2) → F)
    (hx : ∀ i, x i ^ 2 = 1) (hs : (∑ i, x i) = 0) (w : Fin m → F) :
    (PowerSeries.X : PowerSeries F) ^ 3 ∣ reciprocalSeries x (reciprocalTangentVector w) ↔
      reciprocalTransverseForm x w = 0 := by
  have hlow := reciprocalSeries_lower_terms_zero x (reciprocalTangentVector w) hx hs
    (reciprocalTangentVector_sum w)
  rw [PowerSeries.X_pow_dvd_iff, reciprocalTransverseForm_apply,
    ← reciprocalSeries_transverse_quadratic x hx w]
  constructor
  · intro h
    exact h 2 (by norm_num)
  · intro h n hn
    interval_cases n
    · exact hlow.1
    · exact hlow.2
    · exact h

section Count

variable [Fintype F] [DecidableEq F] [Invertible (2 : F)]

/-- The determinant at a critical sign point, in the discriminant of the form. -/
theorem discr_reciprocalTransverseForm {m : ℕ} (S : Finset (Fin (m + 1)))
    (hS : ((m + 2 : ℕ) : F) = 2 * S.card) :
    (reciprocalTransverseForm (m := m) (signPoint (F := F) S)).discr' = (-1) ^ (S.card + 1) := by
  rw [QuadraticForm.discr', reciprocalTransverseForm,
    symmetricMatrix_quadratic_toMatrix _ (reciprocalTransverseMatrix_isSymm _)]
  exact reciprocalTransverseMatrix_det_signs S hS

/-- **The count in even chart dimension.** -/
theorem reciprocalQuadric_card_even (hF : ringChar F ≠ 2) (k : ℕ)
    (S : Finset (Fin (2 * k + 2 + 1))) (hS : ((2 * k + 2 + 2 : ℕ) : F) = 2 * S.card) :
    (Fintype.card (ProjectiveQuadric (reciprocalTransverseForm (m := 2 * k + 2)
        (signPoint (F := F) S))) : ℤ) =
      (∑ j ∈ range (2 * k + 1), (Fintype.card F : ℤ) ^ j) +
        quadraticChar F ((-1) ^ (k + S.card)) * (Fintype.card F : ℤ) ^ k := by
  have hd := discr_reciprocalTransverseForm (F := F) S hS
  have hne : (reciprocalTransverseForm (m := 2 * k + 2) (signPoint (F := F) S)).discr' ≠ 0 := by
    rw [hd]
    exact pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)
  rw [projectiveQuadric_card_even hF k _ hne, hd]
  have hsign : (-1 : F) ^ (k + 1) * (-1) ^ (S.card + 1) = (-1) ^ (k + S.card) := by
    rw [← pow_add, show k + 1 + (S.card + 1) = k + S.card + 2 by ring, pow_add]
    norm_num
  rw [hsign]

/-- **The count in odd chart dimension:** only the ambient classes. -/
theorem reciprocalQuadric_card_odd (hF : ringChar F ≠ 2) (k : ℕ)
    (S : Finset (Fin (2 * k + 1 + 1))) (hS : ((2 * k + 1 + 2 : ℕ) : F) = 2 * S.card) :
    (Fintype.card (ProjectiveQuadric (reciprocalTransverseForm (m := 2 * k + 1)
        (signPoint (F := F) S))) : ℤ) =
      ∑ j ∈ range (2 * k), (Fintype.card F : ℤ) ^ j := by
  have hd := discr_reciprocalTransverseForm (F := F) S hS
  have hne : (reciprocalTransverseForm (m := 2 * k + 1) (signPoint (F := F) S)).discr' ≠ 0 := by
    rw [hd]
    exact pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)
  exact projectiveQuadric_card_odd hF k _ hne

end Count

section Extension

variable [Fintype F] [DecidableEq F] {E : Type*} [Field E] [Fintype E] [DecidableEq E] [Algebra F E]

/-- The quadratic character of a sign over an extension is its power at the base. -/
theorem quadraticChar_extension_sign (hF : ringChar F ≠ 2) (hE : ringChar E ≠ 2) (a : ℕ) :
    quadraticChar E ((-1) ^ a) =
      quadraticChar F ((-1) ^ a) ^ Module.finrank F E := by
  have hcard : Fintype.card E = Fintype.card F ^ Module.finrank F E :=
    Module.card_eq_pow_finrank (K := F) (V := E)
  rw [map_pow, map_pow, quadraticChar_neg_one hE, quadraticChar_neg_one hF, hcard]
  push_cast
  rw [map_pow, ← pow_mul, ← pow_mul, mul_comm]

/-- **The trace over every extension.**  With `q = #F` and `d = [E : F]`, the even count over `E` is
`Σ_{j ≤ 2k} (q^j)^d + α^d`, `α = χ_F((−1)^{k+r}) q^k`. -/
theorem reciprocalQuadric_card_even_extension [Invertible (2 : E)]
    (hF : ringChar F ≠ 2) (hE : ringChar E ≠ 2) (k : ℕ)
    (S : Finset (Fin (2 * k + 2 + 1))) (hS : ((2 * k + 2 + 2 : ℕ) : F) = 2 * S.card) :
    (Fintype.card (ProjectiveQuadric (reciprocalTransverseForm (m := 2 * k + 2)
        (signPoint (F := E) S))) : ℤ) =
      (∑ j ∈ range (2 * k + 1), ((Fintype.card F : ℤ) ^ j) ^ Module.finrank F E) +
        (quadraticChar F ((-1) ^ (k + S.card)) * (Fintype.card F : ℤ) ^ k) ^ Module.finrank F E := by
  have hSE : ((2 * k + 2 + 2 : ℕ) : E) = 2 * S.card := by
    have h := congrArg (algebraMap F E) hS
    simpa only [map_natCast, map_mul, map_ofNat] using h
  have hcard : (Fintype.card E : ℤ) = (Fintype.card F : ℤ) ^ Module.finrank F E := by
    rw [Module.card_eq_pow_finrank (K := F) (V := E)]
    push_cast
    rfl
  rw [reciprocalQuadric_card_even hE k S hSE, quadraticChar_extension_sign hF hE, hcard, mul_pow,
    ← pow_mul, ← pow_mul, mul_comm (Module.finrank F E) k]
  congr 1
  refine sum_congr rfl fun j _ => ?_
  rw [← pow_mul, ← pow_mul, mul_comm]

end Extension

end GaloisForLFunctions.ArithmeticKunnethTheory.WeightFamilies
