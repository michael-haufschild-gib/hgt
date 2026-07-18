import Mathlib.FieldTheory.RatFunc.Luroth
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective

/-!
# Projective classification of rational-function automorphism coordinates

This module proves the ordinary rational endpoint needed by the scalar differential stable-core
classification.  Every coefficient-fixing automorphism of `K(X)` sends `X` to a determinant-
nonzero linear fractional expression.  The proof uses the exact Lüroth degree formula already
available in Mathlib.
-/

noncomputable section

open IntermediateField Polynomial
open scoped MatrixGroups

namespace RatFunc

variable {K : Type*} [Field K]

/-- The value of the linear fractional expression represented by a two-by-two coefficient
matrix. -/
def mobius (a b c d : K) : RatFunc K :=
  (algebraMap K (RatFunc K) a * X + algebraMap K (RatFunc K) b) /
    (algebraMap K (RatFunc K) c * X + algebraMap K (RatFunc K) d)

private theorem mobius_den_ne_zero
    {a b c d : K} (hdet : a * d - b * c ≠ 0) :
    algebraMap K (RatFunc K) c * X + algebraMap K (RatFunc K) d ≠ 0 := by
  have hpoly : Polynomial.C c * Polynomial.X + Polynomial.C d ≠ 0 := by
    by_cases hc : c = 0
    · have hd : d ≠ 0 := by
        intro hd
        apply hdet
        simp [hc, hd]
      simpa [hc] using Polynomial.C_ne_zero.mpr hd
    · intro h
      apply hc
      have hcoeff := congrArg (fun p : K[X] => p.coeff 1) h
      simpa using hcoeff
  simpa using RatFunc.algebraMap_ne_zero hpoly

private theorem mobius_cross_coefficients
    {a b c d A B C D : K}
    (habcd : a * d - b * c ≠ 0)
    (hABCD : A * D - B * C ≠ 0)
    (h : mobius a b c d = mobius A B C D) :
    a * C = A * c ∧
      a * D + b * C = A * d + B * c ∧
      b * D = B * d := by
  have hden₁ := mobius_den_ne_zero habcd
  have hden₂ := mobius_den_ne_zero hABCD
  have hcross :
      (algebraMap K (RatFunc K) a * X + algebraMap K (RatFunc K) b) *
          (algebraMap K (RatFunc K) C * X + algebraMap K (RatFunc K) D) =
        (algebraMap K (RatFunc K) A * X + algebraMap K (RatFunc K) B) *
          (algebraMap K (RatFunc K) c * X + algebraMap K (RatFunc K) d) := by
    exact (div_eq_div_iff hden₁ hden₂).mp h
  have hpoly :
      (Polynomial.C a * Polynomial.X + Polynomial.C b) *
          (Polynomial.C C * Polynomial.X + Polynomial.C D) =
        (Polynomial.C A * Polynomial.X + Polynomial.C B) *
          (Polynomial.C c * Polynomial.X + Polynomial.C d) := by
    apply RatFunc.algebraMap_injective
    simpa using hcross
  have hexpanded :
      Polynomial.C (a * C) * Polynomial.X ^ 2 +
          Polynomial.C (a * D + b * C) * Polynomial.X + Polynomial.C (b * D) =
        Polynomial.C (A * c) * Polynomial.X ^ 2 +
          Polynomial.C (A * d + B * c) * Polynomial.X + Polynomial.C (B * d) := by
    calc
      _ = (Polynomial.C a * Polynomial.X + Polynomial.C b) *
          (Polynomial.C C * Polynomial.X + Polynomial.C D) := by
            simp only [map_mul, map_add]
            ring
      _ = _ := hpoly
      _ = _ := by
            simp only [map_mul, map_add]
            ring
  constructor
  · have h2 := congrArg (fun p : K[X] => p.coeff 2) hexpanded
    simp only [coeff_add, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C,
      if_pos, mul_one] at h2
    norm_num at h2
    exact h2
  constructor
  · have h1 := congrArg (fun p : K[X] => p.coeff 1) hexpanded
    simp only [coeff_add, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C,
      if_pos, mul_one] at h1
    norm_num at h1
    exact h1
  · have h0 := congrArg (fun p : K[X] => p.coeff 0) hexpanded
    simp only [coeff_add, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C,
      if_pos] at h0
    norm_num at h0
    exact h0

/-- Two determinant-nonzero linear fractional expressions define the same rational function
exactly when their coefficient matrices differ by one nonzero scalar. -/
theorem mobius_eq_iff_exists_smul
    {a b c d A B C D : K}
    (habcd : a * d - b * c ≠ 0)
    (hABCD : A * D - B * C ≠ 0) :
    mobius a b c d = mobius A B C D ↔
      ∃ l : K, l ≠ 0 ∧ a = l * A ∧ b = l * B ∧ c = l * C ∧ d = l * D := by
  constructor
  · intro h
    obtain ⟨h2, h1, h0⟩ := mobius_cross_coefficients habcd hABCD h
    let Δ := A * D - B * C
    let l := (D * a - B * c) / Δ
    have ha : a = l * A := by
      dsimp [l, Δ]
      rw [div_mul_eq_mul_div, eq_div_iff hABCD]
      linear_combination -B * h2
    have hc : c = l * C := by
      dsimp [l, Δ]
      rw [div_mul_eq_mul_div, eq_div_iff hABCD]
      linear_combination -D * h2
    have hb : b = l * B := by
      dsimp [l, Δ]
      rw [div_mul_eq_mul_div, eq_div_iff hABCD]
      linear_combination A * h0 - B * h1
    have hd : d = l * D := by
      dsimp [l, Δ]
      rw [div_mul_eq_mul_div, eq_div_iff hABCD]
      linear_combination C * h0 - D * h1
    have hl : l ≠ 0 := by
      intro hl
      apply habcd
      rw [ha, hb, hc, hd, hl]
      simp
    exact ⟨l, hl, ha, hb, hc, hd⟩
  · rintro ⟨l, hl, rfl, rfl, rfl, rfl⟩
    simp only [mobius]
    push_cast
    field_simp [hl]

/-- The image of the rational coordinate under an automorphism still generates the whole rational
function field. -/
theorem algEquiv_adjoin_image_X_eq_top (e : RatFunc K ≃ₐ[K] RatFunc K) :
    K⟮e X⟯ = ⊤ := by
  have hmap :
      (K⟮(X : RatFunc K)⟯ : IntermediateField K (RatFunc K)).map e.toAlgHom =
        K⟮e X⟯ := by
    rw [IntermediateField.adjoin_map, Set.image_singleton]
    simp only [AlgEquiv.toAlgHom_apply]
  have htop : (⊤ : IntermediateField K (RatFunc K)).map e.toAlgHom = ⊤ := by
    rw [← AlgHom.fieldRange_eq_map]
    exact e.fieldRange_eq_top
  rw [RatFunc.adjoin_X, htop] at hmap
  exact hmap.symm

/-- The reduced numerator and denominator of the image of `X` have maximum degree exactly one. -/
theorem max_natDegree_num_denom_image_X (e : RatFunc K ≃ₐ[K] RatFunc K) :
    max (e X).num.natDegree (e X).denom.natDegree = 1 := by
  have hfin := (e X).finrank_eq_max_natDegree
  rw [algEquiv_adjoin_image_X_eq_top e] at hfin
  simpa using hfin.symm

/-- An automorphism cannot send the rational coordinate to a scalar. -/
theorem algEquiv_image_X_ne_algebraMap (e : RatFunc K ≃ₐ[K] RatFunc K) (k : K) :
    e X ≠ algebraMap K (RatFunc K) k := by
  intro h
  have hx : (X : RatFunc K) = algebraMap K (RatFunc K) k := by
    exact e.injective (h.trans (e.commutes k).symm)
  have hnum := congrArg RatFunc.num hx
  exact Polynomial.X_ne_C k (by simpa using hnum)

/-- A nonconstant rational function whose reduced numerator and denominator are linear has a
nonzero determinant of coefficients. -/
theorem det_ne_zero_of_num_denom_eq_linear
    (f : RatFunc K) (hnotC : ∀ k : K, f ≠ algebraMap K (RatFunc K) k)
    (a b c d : K)
    (hnum : f.num = Polynomial.C a * Polynomial.X + Polynomial.C b)
    (hden : f.denom = Polynomial.C c * Polynomial.X + Polynomial.C d) :
    a * d - b * c ≠ 0 := by
  intro hdet
  by_cases hc : c = 0
  · have hd : d ≠ 0 := by
      intro hd
      apply f.denom_ne_zero
      rw [hden, hc, hd]
      simp
    have ha : a = 0 := by
      rw [hc, mul_zero, sub_zero, mul_eq_zero] at hdet
      exact hdet.resolve_right hd
    apply hnotC (b / d)
    rw [← num_div_denom f, hnum, hden, ha, hc]
    simp [map_div₀]
  · have hb : b = a / c * d := by
      field_simp
      linear_combination -hdet
    have hpoly :
        Polynomial.C a * Polynomial.X + Polynomial.C b =
          Polynomial.C (a / c) *
            (Polynomial.C c * Polynomial.X + Polynomial.C d) := by
      rw [hb]
      calc
        Polynomial.C a * Polynomial.X + Polynomial.C (a / c * d) =
            Polynomial.C (a / c * c) * Polynomial.X +
              Polynomial.C (a / c * d) := by rw [div_mul_cancel₀ a hc]
        _ = Polynomial.C (a / c) *
            (Polynomial.C c * Polynomial.X + Polynomial.C d) := by
          simp only [map_mul]
          ring
    have hden0 :
        (algebraMap K[X] (RatFunc K))
            (Polynomial.C c * Polynomial.X + Polynomial.C d) ≠ 0 := by
      exact RatFunc.algebraMap_ne_zero (by rw [← hden]; exact f.denom_ne_zero)
    have hQ0 :
        algebraMap K (RatFunc K) c * X + algebraMap K (RatFunc K) d ≠ 0 := by
      simpa using hden0
    apply hnotC (a / c)
    rw [← num_div_denom f, hnum, hden, hpoly, map_mul]
    field_simp [hc, hQ0]
    exact RatFunc.algebraMap_C (a / c)

/-- Every coefficient-fixing automorphism of `K(X)` sends `X` to a determinant-nonzero Möbius
expression. -/
theorem exists_mobius_image_X (e : RatFunc K ≃ₐ[K] RatFunc K) :
    ∃ a b c d : K, a * d - b * c ≠ 0 ∧ e X = mobius a b c d := by
  have hdeg := max_natDegree_num_denom_image_X e
  have hn : (e X).num.natDegree ≤ 1 :=
    le_trans (Nat.le_max_left _ _) hdeg.le
  have hd : (e X).denom.natDegree ≤ 1 :=
    le_trans (Nat.le_max_right _ _) hdeg.le
  obtain ⟨a, b, hab⟩ := Polynomial.exists_eq_X_add_C_of_natDegree_le_one hn
  obtain ⟨c, d, hcd⟩ := Polynomial.exists_eq_X_add_C_of_natDegree_le_one hd
  refine ⟨a, b, c, d,
    det_ne_zero_of_num_denom_eq_linear (e X)
      (algEquiv_image_X_ne_algebraMap e) a b c d hab hcd, ?_⟩
  rw [← num_div_denom (e X), hab, hcd]
  simp [mobius]

/-- The canonical reduced two-by-two coefficient matrix attached to a rational-function
automorphism. -/
def algEquivMobiusMatrix (e : RatFunc K ≃ₐ[K] RatFunc K) : Matrix (Fin 2) (Fin 2) K :=
  !![(e X).num.coeff 1, (e X).num.coeff 0;
    (e X).denom.coeff 1, (e X).denom.coeff 0]

/-- The canonical reduced coefficient matrix of an automorphism is invertible. -/
theorem det_algEquivMobiusMatrix_ne_zero (e : RatFunc K ≃ₐ[K] RatFunc K) :
    Matrix.det (algEquivMobiusMatrix e) ≠ 0 := by
  have hdeg := max_natDegree_num_denom_image_X e
  have hn : (e X).num.natDegree ≤ 1 :=
    le_trans (Nat.le_max_left _ _) hdeg.le
  have hd : (e X).denom.natDegree ≤ 1 :=
    le_trans (Nat.le_max_right _ _) hdeg.le
  have hnum := Polynomial.eq_X_add_C_of_natDegree_le_one hn
  have hden := Polynomial.eq_X_add_C_of_natDegree_le_one hd
  simpa [algEquivMobiusMatrix, Matrix.det_fin_two] using
    det_ne_zero_of_num_denom_eq_linear (e X)
      (algEquiv_image_X_ne_algebraMap e)
      ((e X).num.coeff 1) ((e X).num.coeff 0)
      ((e X).denom.coeff 1) ((e X).denom.coeff 0) hnum hden

/-- The canonical projective matrix class attached to a rational-function automorphism. -/
def algEquivProjectiveClass (e : RatFunc K ≃ₐ[K] RatFunc K) : PGL(2, K) :=
  Matrix.ProjGenLinGroup.mk
    (Matrix.GeneralLinearGroup.mkOfDetNeZero (algEquivMobiusMatrix e)
      (det_algEquivMobiusMatrix_ne_zero e))

/-- The image of the rational coordinate is the Möbius expression of the canonical reduced
matrix. -/
theorem algEquiv_image_X_eq_canonical_mobius (e : RatFunc K ≃ₐ[K] RatFunc K) :
    e X = mobius
      ((e X).num.coeff 1) ((e X).num.coeff 0)
      ((e X).denom.coeff 1) ((e X).denom.coeff 0) := by
  have hdeg := max_natDegree_num_denom_image_X e
  have hn : (e X).num.natDegree ≤ 1 :=
    le_trans (Nat.le_max_left _ _) hdeg.le
  have hd : (e X).denom.natDegree ≤ 1 :=
    le_trans (Nat.le_max_right _ _) hdeg.le
  have hnum := Polynomial.eq_X_add_C_of_natDegree_le_one hn
  have hden := Polynomial.eq_X_add_C_of_natDegree_le_one hd
  conv_lhs => rw [← num_div_denom (e X), hnum, hden]
  simp [mobius]

/-- Every determinant-nonzero Möbius presentation of the image of `X` is a nonzero scalar
multiple of the canonical reduced coefficient matrix.  Thus the associated projective matrix
class is unique. -/
theorem algEquiv_mobius_coefficients_unique
    (e : RatFunc K ≃ₐ[K] RatFunc K) {a b c d : K}
    (hdet : a * d - b * c ≠ 0)
    (himage : e X = mobius a b c d) :
    ∃ l : K, l ≠ 0 ∧
      a = l * (e X).num.coeff 1 ∧
      b = l * (e X).num.coeff 0 ∧
      c = l * (e X).denom.coeff 1 ∧
      d = l * (e X).denom.coeff 0 := by
  apply (mobius_eq_iff_exists_smul hdet ?_).mp
  · exact himage.symm.trans (algEquiv_image_X_eq_canonical_mobius e)
  · simpa [algEquivMobiusMatrix, Matrix.det_fin_two] using
      det_algEquivMobiusMatrix_ne_zero e

end RatFunc
