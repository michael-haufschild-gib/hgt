import GaloisForLFunctions.HTGeometry.PositiveConeDeterminantMonotone

/-!
# The pencil capacity certificate

Gurvits' square capacity of a completely positive map is the infimum of `det Φ(X)` over positive
`X` of unit determinant.  For a Kraus tuple `(Bᵢ)` and any pencil `B = ∑ᵢ cᵢ Bᵢ`,

`cap (X ↦ ∑ᵢ Bᵢ X Bᵢᴴ) ≥ |det B|² / ‖c‖₂^{2d}`.

Cauchy--Schwarz gives `B X Bᴴ ≤ ‖c‖₂² ∑ᵢ Bᵢ X Bᵢᴴ`, determinant monotonicity on the positive cone
turns that into a determinant inequality, and the determinant of a congruence factorises, so the
competitor value at every admissible `X` is bounded below by the stated constant.
-/

open Finset Matrix
open scoped MatrixOrder ComplexOrder

namespace GaloisForLFunctions.HTGeometry

variable {d ι : Type*} [Fintype d] [DecidableEq d] [Fintype ι]

omit [DecidableEq d] in
/-- A nonnegative real multiple of a positive semidefinite matrix is positive semidefinite. -/
theorem posSemidef_real_smul {A : Matrix d d ℂ} (hA : A.PosSemidef) {t : ℝ} (ht : 0 ≤ t) :
    (((t : ℂ)) • A).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun v => ?_
  · show (_ : Matrix d d ℂ)ᴴ = _
    rw [Matrix.conjTranspose_smul, hA.isHermitian.eq]
    simp [Complex.conj_ofReal]
  · rw [smul_mulVec, dotProduct_smul, smul_eq_mul]
    exact mul_nonneg (Complex.zero_le_real.mpr ht)
      (Matrix.PosSemidef.dotProduct_mulVec_nonneg hA v)

omit [DecidableEq d] in
/-- Every Kraus image of a positive semidefinite state is positive semidefinite. -/
theorem posSemidef_krausSum {X : Matrix d d ℂ} (hX : X.PosSemidef) (B : ι → Matrix d d ℂ) :
    (∑ i, B i * X * (B i)ᴴ).PosSemidef := by
  classical
  refine Finset.sum_induction _ Matrix.PosSemidef (fun a b ha hb => ha.add hb) ?_ ?_
  · exact Matrix.PosSemidef.zero
  · exact fun i _ => Matrix.PosSemidef.mul_mul_conjTranspose_same hX (B i)

/-- **The pencil capacity certificate.**  At every positive state of unit determinant the Kraus sum
has determinant at least `|det B|² / ‖c‖₂^{2d}`, so the square capacity is bounded below by that
constant. -/
theorem pencil_capacity_bound {X : Matrix d d ℂ} (hX : X.PosDef) (hXdet : X.det = 1)
    (c : ι → ℂ) (B : ι → Matrix d d ℂ) (hc : 0 < ∑ i, ‖c i‖ ^ (2 : ℕ)) :
    ((‖(∑ i, c i • B i).det‖ ^ (2 : ℕ) / (∑ i, ‖c i‖ ^ (2 : ℕ)) ^ Fintype.card d : ℝ) : ℂ)
      ≤ (∑ i, B i * X * (B i)ᴴ).det := by
  set r : ℝ := ∑ i, ‖c i‖ ^ (2 : ℕ) with hr
  set Bp : Matrix d d ℂ := ∑ i, c i • B i with hBp
  set P : Matrix d d ℂ := Bp * X * Bpᴴ with hP
  set K : Matrix d d ℂ := ∑ i, B i * X * (B i)ᴴ with hK
  have hrne : r ≠ 0 := ne_of_gt hc
  have hPpsd : P.PosSemidef := Matrix.PosSemidef.mul_mul_conjTranspose_same hX.posSemidef Bp
  have hKpsd : K.PosSemidef := posSemidef_krausSum hX.posSemidef B
  have hD : (((r : ℂ)) • K - P).PosSemidef := posSemidef_pencil_bound hX c B
  have hAlt : ((r⁻¹ : ℝ) : ℂ) • (((r : ℂ)) • K - P) = K - ((r⁻¹ : ℝ) : ℂ) • P := by
    have h1 : ((r⁻¹ : ℝ) : ℂ) * ((r : ℝ) : ℂ) = 1 := by
      push_cast
      field_simp
    rw [smul_sub, smul_smul, h1, one_smul]
  have hscaled : (K - ((r⁻¹ : ℝ) : ℂ) • P).PosSemidef := by
    rw [← hAlt]
    exact posSemidef_real_smul hD (by positivity)
  have hcmp : (((r⁻¹ : ℝ) : ℂ) • P).det ≤ K.det :=
    det_le_det_of_loewner (posSemidef_real_smul hPpsd (by positivity)) hKpsd hscaled
  have hdetP : P.det = ((‖Bp.det‖ ^ (2 : ℕ) : ℝ) : ℂ) := by
    rw [hP, Matrix.det_mul, Matrix.det_mul, hXdet, Matrix.det_conjTranspose, mul_one,
      Complex.star_def, Complex.mul_conj]
    norm_cast
    exact Complex.normSq_eq_norm_sq _
  have hdetsmul : (((r⁻¹ : ℝ) : ℂ) • P).det
      = ((‖Bp.det‖ ^ (2 : ℕ) / r ^ Fintype.card d : ℝ) : ℂ) := by
    have hrc : ((r : ℝ) : ℂ) ≠ 0 := by simpa using hrne
    rw [Matrix.det_smul, hdetP]
    push_cast
    rw [inv_pow, inv_mul_eq_div]
  rwa [hdetsmul] at hcmp

end GaloisForLFunctions.HTGeometry
