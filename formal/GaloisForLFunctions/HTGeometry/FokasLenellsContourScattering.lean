import GaloisForLFunctions.HTGeometry.FokasLenellsContourJost

/-!
# Scattering identities on every Fokas–Lenells contour ray

The analytically constructed Jost bases give the scattering relations
(2.59)–(2.62), the parity and inverse symmetries (2.69), and the initial-time
amplitude reduction of arXiv:2607.19649v1 on all four nonzero rays.
Pauli conjugation exchanges the two transmission entries on imaginary rays
and supplies the exact reflection signs. No scattering identities or
nonvanishing assumptions are supplied as hypotheses.
-/

open Complex Matrix
namespace GaloisForLFunctions.HTGeometry.FokasLenells
noncomputable section

def contourScatteringMatrix (q : SchwartzMap ℝ ℂ) (vertical negative : Bool) (κ : ℝ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  contourConjugator vertical negative*scatteringMatrix (contourSource q vertical) κ*
    contourConjugator vertical negative

/-- The constructed connection has determinant one on every contour ray. -/
theorem contourScatteringMatrix_det (q : SchwartzMap ℝ ℂ) (vertical negative : Bool) (κ : ℝ) :
    (contourScatteringMatrix q vertical negative κ).det = 1 := by
  rw [contourScatteringMatrix, Matrix.det_mul, Matrix.det_mul, scatteringMatrix_det, mul_one]
  have hd := congrArg Matrix.det (contourConjugator_square vertical negative)
  simpa only [Matrix.det_mul, Matrix.det_one] using hd

/-- Equation (2.59) before the free-phase normalization, on all four rays. -/
theorem contourJostMatrix_basis_relation (q : SchwartzMap ℝ ℂ) (vertical negative : Bool)
    (κ x : ℝ) :
    contourJostMatrix q vertical negative κ true x =
      contourJostMatrix q vertical negative κ false x*contourScatteringMatrix q vertical negative κ := by
  simp only [contourJostMatrix, baseJostMatrix, ↓reduceIte, Bool.false_eq_true,
    contourScatteringMatrix, leftJostMatrix_eq_right_mul_scattering, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (contourConjugator vertical negative) (contourConjugator vertical negative),
    contourConjugator_square, one_mul]

/-- Both original Jost bases recover the same position-independent scattering matrix. -/
theorem contourScatteringMatrix_eq_connection (q : SchwartzMap ℝ ℂ) (vertical negative : Bool)
    (κ x : ℝ) :
    (contourJostMatrix q vertical negative κ false x)⁻¹*
      contourJostMatrix q vertical negative κ true x = contourScatteringMatrix q vertical negative κ := by
  rw [contourJostMatrix_basis_relation, ← Matrix.mul_assoc,
    Matrix.nonsing_inv_mul _ (by rw [contourJostMatrix_det]; exact isUnit_one), one_mul]

theorem contourScattering_connection_hasDerivAt_zero (q : SchwartzMap ℝ ℂ) (vertical negative : Bool)
    (κ x : ℝ) (i j : Fin 2) :
    HasDerivAt (fun y => ((contourJostMatrix q vertical negative κ false y)⁻¹*
      contourJostMatrix q vertical negative κ true y) i j) 0 x := by
  simp only [contourScatteringMatrix_eq_connection]
  exact hasDerivAt_const x _

/-- The normalized scattering relation keeps the conjugation by the actual squared spectral parameter. -/
theorem contourJostFunction_basis_relation (q : SchwartzMap ℝ ℂ) (vertical negative : Bool)
    (κ x : ℝ) :
    contourJostFunction q vertical negative κ true x =
      contourJostFunction q vertical negative κ false x*
        (diagonalFrame (-(contourSquaredParameter vertical κ)) x*
          contourScatteringMatrix q vertical negative κ*
            diagonalFrame (contourSquaredParameter vertical κ) x) := by
  have hi : diagonalFrame (contourSquaredParameter vertical κ) x*
      diagonalFrame (-(contourSquaredParameter vertical κ)) x = 1 := by
    simpa only [neg_neg] using diagonalFrame_neg_inverse (-(contourSquaredParameter vertical κ)) x
  simp only [contourJostFunction, contourJostMatrix_basis_relation, ← Matrix.mul_assoc]
  rw [Matrix.mul_assoc (contourJostMatrix q vertical negative κ false x) _
    (diagonalFrame (-(contourSquaredParameter vertical κ)) x), hi, mul_one]

theorem contourScatteringMatrix_eq_normalized_connection (q : SchwartzMap ℝ ℂ)
    (vertical negative : Bool) (κ x : ℝ) :
    diagonalFrame (contourSquaredParameter vertical κ) x*
      ((contourJostFunction q vertical negative κ false x)⁻¹*
        contourJostFunction q vertical negative κ true x)*
          diagonalFrame (-(contourSquaredParameter vertical κ)) x =
            contourScatteringMatrix q vertical negative κ := by
  have hi : diagonalFrame (contourSquaredParameter vertical κ) x*
      diagonalFrame (-(contourSquaredParameter vertical κ)) x = 1 := by
    simpa only [neg_neg] using diagonalFrame_neg_inverse (-(contourSquaredParameter vertical κ)) x
  rw [contourJostFunction_basis_relation,
    ← Matrix.mul_assoc ((contourJostFunction q vertical negative κ false x)⁻¹),
    Matrix.nonsing_inv_mul _ (by rw [contourJostFunction_det]; exact isUnit_one), one_mul]
  simp only [← Matrix.mul_assoc]
  rw [hi, one_mul, Matrix.mul_assoc, hi, mul_one]

/-- The spatial-reflection reduction exposes the three independent positive-ray entries. -/
theorem scatteringMatrix_reduced_entries (q : SchwartzMap ℝ ℂ) (κ : ℝ) :
    scatteringMatrix q κ = !![transmission q κ,-reflectionAmplitude q κ;
      reflectionAmplitude q κ,reverseTransmission q κ] := by
  ext i j
  fin_cases i <;> fin_cases j
  · rfl
  · exact reverseReflectionAmplitude_eq_neg q κ
  · rfl
  · rfl

/-- Imaginary rays exchange the transmission entries; changing ray sign reverses reflection. -/
theorem contourScatteringMatrix_entries (q : SchwartzMap ℝ ℂ) (vertical negative : Bool) (κ : ℝ) :
    contourScatteringMatrix q vertical negative κ =
      !![if vertical then reverseTransmission (contourSource q vertical) κ
            else transmission (contourSource q vertical) κ,
        -(if vertical = negative then reflectionAmplitude (contourSource q vertical) κ
            else -reflectionAmplitude (contourSource q vertical) κ);
        if vertical = negative then reflectionAmplitude (contourSource q vertical) κ
            else -reflectionAmplitude (contourSource q vertical) κ,
        if vertical then transmission (contourSource q vertical) κ
            else reverseTransmission (contourSource q vertical) κ] := by
  rw [contourScatteringMatrix, scatteringMatrix_reduced_entries]
  cases vertical <;> cases negative <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [contourConjugator, _root_.HTGeometry.ConstraintRelativity.pauliX,
      _root_.HTGeometry.ConstraintRelativity.pauliY, _root_.HTGeometry.ConstraintRelativity.pauliZ,
      Matrix.mul_apply, Fin.sum_univ_two] <;> ring_nf <;> simp

def contourTransmission (q : SchwartzMap ℝ ℂ) (vertical negative : Bool) (κ : ℝ) : ℂ :=
  contourScatteringMatrix q vertical negative κ 0 0

def contourReverseTransmission (q : SchwartzMap ℝ ℂ) (vertical negative : Bool) (κ : ℝ) : ℂ :=
  contourScatteringMatrix q vertical negative κ 1 1

def contourReflectionAmplitude (q : SchwartzMap ℝ ℂ) (vertical negative : Bool) (κ : ℝ) : ℂ :=
  contourScatteringMatrix q vertical negative κ 1 0

def contourReverseReflectionAmplitude (q : SchwartzMap ℝ ℂ) (vertical negative : Bool) (κ : ℝ) : ℂ :=
  contourScatteringMatrix q vertical negative κ 0 1

theorem contourTransmission_eq (q : SchwartzMap ℝ ℂ) (vertical negative : Bool) (κ : ℝ) :
    contourTransmission q vertical negative κ =
      if vertical then reverseTransmission (contourSource q vertical) κ
      else transmission (contourSource q vertical) κ := by
  simp [contourTransmission, contourScatteringMatrix_entries]

theorem contourReverseTransmission_eq (q : SchwartzMap ℝ ℂ) (vertical negative : Bool) (κ : ℝ) :
    contourReverseTransmission q vertical negative κ =
      if vertical then transmission (contourSource q vertical) κ
      else reverseTransmission (contourSource q vertical) κ := by
  simp [contourReverseTransmission, contourScatteringMatrix_entries]

theorem contourReflectionAmplitude_eq (q : SchwartzMap ℝ ℂ) (vertical negative : Bool) (κ : ℝ) :
    contourReflectionAmplitude q vertical negative κ =
      if vertical = negative then reflectionAmplitude (contourSource q vertical) κ
      else -reflectionAmplitude (contourSource q vertical) κ := by
  simp [contourReflectionAmplitude, contourScatteringMatrix_entries]

theorem contourReverseReflectionAmplitude_eq_neg (q : SchwartzMap ℝ ℂ)
    (vertical negative : Bool) (κ : ℝ) :
    contourReverseReflectionAmplitude q vertical negative κ =
      -contourReflectionAmplitude q vertical negative κ := by
  simp [contourReverseReflectionAmplitude, contourReflectionAmplitude, contourScatteringMatrix_entries]

theorem contourReflectionAmplitude_norm (q : SchwartzMap ℝ ℂ) (vertical negative : Bool) (κ : ℝ) :
    ‖contourReflectionAmplitude q vertical negative κ‖ = ‖reflectionAmplitude (contourSource q vertical) κ‖ := by
  rw [contourReflectionAmplitude_eq]
  split <;> simp

/-- The determinant reduction `a â + b² = 1` holds on the entire nonzero contour. -/
theorem contourScattering_amplitude_identity (q : SchwartzMap ℝ ℂ) (vertical negative : Bool) (κ : ℝ) :
    contourTransmission q vertical negative κ*contourReverseTransmission q vertical negative κ+
      contourReflectionAmplitude q vertical negative κ^(2 : ℕ) = 1 := by
  have hd := contourScatteringMatrix_det q vertical negative κ
  rw [Matrix.det_fin_two] at hd
  change contourTransmission q vertical negative κ*contourReverseTransmission q vertical negative κ-
    contourReverseReflectionAmplitude q vertical negative κ*contourReflectionAmplitude q vertical negative κ = 1 at hd
  rw [contourReverseReflectionAmplitude_eq_neg] at hd
  simpa only [neg_mul, sub_neg_eq_add, pow_two] using hd

/-- Equation (2.69), the parity symmetry under `k ↦ -k`, for actual scattering matrices. -/
theorem contourScatteringMatrix_parity (q : SchwartzMap ℝ ℂ) (vertical negative : Bool) (κ : ℝ) :
    contourScatteringMatrix q vertical (!negative) κ =
      _root_.HTGeometry.ConstraintRelativity.pauliZ*contourScatteringMatrix q vertical negative κ*
        _root_.HTGeometry.ConstraintRelativity.pauliZ := by
  simp only [contourScatteringMatrix_entries]
  cases vertical <;> cases negative <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [_root_.HTGeometry.ConstraintRelativity.pauliZ, Matrix.mul_apply, Fin.sum_univ_two]

theorem contourParameter_neg (vertical negative : Bool) (κ : ℝ) :
    contourParameter vertical (!negative) κ = -contourParameter vertical negative κ := by
  cases vertical <;> cases negative <;> simp [contourParameter]

theorem contourTransmission_even (q : SchwartzMap ℝ ℂ) (vertical negative : Bool) (κ : ℝ) :
    contourTransmission q vertical (!negative) κ = contourTransmission q vertical negative κ ∧
      contourReverseTransmission q vertical (!negative) κ = contourReverseTransmission q vertical negative κ := by
  simp only [contourTransmission_eq, contourReverseTransmission_eq, and_self]

theorem contourReflectionAmplitude_odd (q : SchwartzMap ℝ ℂ) (vertical negative : Bool) (κ : ℝ) :
    contourReflectionAmplitude q vertical (!negative) κ = -contourReflectionAmplitude q vertical negative κ := by
  cases vertical <;> cases negative <;> simp [contourReflectionAmplitude_eq]

/-- All four rays inherit the paper's spatial-reflection inverse symmetry at initial time. -/
theorem contourScatteringMatrix_inverse_symmetry (q : SchwartzMap ℝ ℂ)
    (vertical negative : Bool) (κ : ℝ) :
    contourScatteringMatrix q vertical negative κ =
      swapMatrix*(contourScatteringMatrix q vertical negative κ)⁻¹*swapMatrix := by
  rw [Matrix.inv_def, contourScatteringMatrix_det]
  simp only [Ring.inverse_one, one_smul, contourScatteringMatrix_entries]
  cases vertical <;> cases negative <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [swapMatrix, Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]

end
end GaloisForLFunctions.HTGeometry.FokasLenells
