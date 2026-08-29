import GaloisForLFunctions.HTGeometry.ColorGramSpecialUnitaryOrbit

/-!
# The global product decomposition of the regular colour locus

Every regular `3 × 2` colour event is recovered from its positive definite Gram record together
with one `SU(3)` frame, and the recovery is a bijection

`{X // (XᴴX).PosDef} ≃ SU(3) × {H // H.PosDef}`

whose second coordinate is the Gram map.  Both directions are written by explicit algebraic
formulas: the Gram record is completed by its Cholesky factor, the resulting canonical event is
completed to a triangular frame by its normal, and that frame is inverted in closed form.
-/

open Matrix
open scoped ComplexOrder Matrix

noncomputable section

namespace GaloisForLFunctions.HTGeometry

section CholeskySection

/-- The first Cholesky diagonal of a positive record. -/
def gramDiagOne (H : Matrix (Fin 2) (Fin 2) ℂ) : ℝ := Real.sqrt (H 0 0).re

/-- The second Cholesky diagonal of a positive record. -/
def gramDiagTwo (H : Matrix (Fin 2) (Fin 2) ℂ) : ℝ := Real.sqrt (H.det.re / (H 0 0).re)

/-- The upper triangular Cholesky factor of a positive definite `2 × 2` record. -/
def gramCholesky (H : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![((gramDiagOne H : ℝ) : ℂ), H 0 1 / ((gramDiagOne H : ℝ) : ℂ);
     0, ((gramDiagTwo H : ℝ) : ℂ)]

/-- The canonical regular colour event carrying a prescribed positive definite Gram record. -/
def gramSection (H : Matrix (Fin 2) (Fin 2) ℂ) : ColorEventMatrix :=
  colorEmbedSquare (gramCholesky H)

/-- A positive definite record has positive first diagonal entry. -/
theorem posDef_diag_zero_re_pos {H : Matrix (Fin 2) (Fin 2) ℂ} (hH : H.PosDef) :
    0 < (H 0 0).re := by
  have hne : (Pi.single (0 : Fin 2) (1 : ℂ) : Fin 2 → ℂ) ≠ 0 := by
    intro hcon
    have h := congrFun hcon 0
    simp at h
  have h := (Matrix.posDef_iff_dotProduct_mulVec.1 hH).2 hne
  have hval : star (Pi.single (0 : Fin 2) (1 : ℂ)) ⬝ᵥ H *ᵥ Pi.single (0 : Fin 2) (1 : ℂ)
      = H 0 0 := by
    simp [Matrix.mulVec_single]
  rw [hval] at h
  simpa using (Complex.lt_def.1 h).1

/-- A positive definite record has real first diagonal entry. -/
theorem posDef_diag_zero_eq_re {H : Matrix (Fin 2) (Fin 2) ℂ} (hH : H.PosDef) :
    H 0 0 = ((H 0 0).re : ℂ) := by
  have hherm := hH.1
  have h := congrFun (congrFun hherm.eq 0) 0
  have him : (H 0 0).im = 0 := by
    have hstar : star (H 0 0) = H 0 0 := by
      simpa [Matrix.conjTranspose_apply] using h
    exact Complex.conj_eq_iff_im.1 hstar
  exact Complex.ext rfl (by simpa using him)

/-- A positive definite record has real second diagonal entry. -/
theorem posDef_diag_one_eq_re {H : Matrix (Fin 2) (Fin 2) ℂ} (hH : H.PosDef) :
    H 1 1 = ((H 1 1).re : ℂ) := by
  have hherm := hH.1
  have h := congrFun (congrFun hherm.eq 1) 1
  have him : (H 1 1).im = 0 := by
    have hstar : star (H 1 1) = H 1 1 := by
      simpa [Matrix.conjTranspose_apply] using h
    exact Complex.conj_eq_iff_im.1 hstar
  exact Complex.ext rfl (by simpa using him)

/-- A positive definite record has conjugate off-diagonal entries. -/
theorem posDef_offDiag_conj {H : Matrix (Fin 2) (Fin 2) ℂ} (hH : H.PosDef) :
    H 1 0 = star (H 0 1) := by
  have h := congrFun (congrFun hH.1.eq 1) 0
  simpa [Matrix.conjTranspose_apply] using h.symm

theorem gramDiagOne_pos {H : Matrix (Fin 2) (Fin 2) ℂ} (hH : H.PosDef) :
    0 < gramDiagOne H :=
  Real.sqrt_pos.2 (posDef_diag_zero_re_pos hH)

theorem gramDiagOne_ne_zero {H : Matrix (Fin 2) (Fin 2) ℂ} (hH : H.PosDef) :
    ((gramDiagOne H : ℝ) : ℂ) ≠ 0 := by
  exact_mod_cast (gramDiagOne_pos hH).ne'

theorem gramDiagOne_sq {H : Matrix (Fin 2) (Fin 2) ℂ} (hH : H.PosDef) :
    ((gramDiagOne H : ℝ) : ℂ) * ((gramDiagOne H : ℝ) : ℂ) = H 0 0 := by
  rw [posDef_diag_zero_eq_re hH]
  exact_mod_cast congrArg (fun t : ℝ => (t : ℂ))
    (Real.mul_self_sqrt (le_of_lt (posDef_diag_zero_re_pos hH)))

theorem posDef_det_re_pos {H : Matrix (Fin 2) (Fin 2) ℂ} (hH : H.PosDef) :
    0 < H.det.re := by
  have h := hH.det_pos
  simpa using (Complex.lt_def.1 h).1

theorem posDef_det_eq_re {H : Matrix (Fin 2) (Fin 2) ℂ} (hH : H.PosDef) :
    H.det = ((H.det.re : ℝ) : ℂ) := by
  have h := hH.det_pos
  have him : H.det.im = 0 := by simpa using ((Complex.lt_def.1 h).2).symm
  exact Complex.ext rfl (by simpa using him)

theorem gramDiagTwo_pos {H : Matrix (Fin 2) (Fin 2) ℂ} (hH : H.PosDef) :
    0 < gramDiagTwo H :=
  Real.sqrt_pos.2 (div_pos (posDef_det_re_pos hH) (posDef_diag_zero_re_pos hH))

theorem gramDiagTwo_ne_zero {H : Matrix (Fin 2) (Fin 2) ℂ} (hH : H.PosDef) :
    ((gramDiagTwo H : ℝ) : ℂ) ≠ 0 := by
  exact_mod_cast (gramDiagTwo_pos hH).ne'

theorem gramDiagTwo_sq {H : Matrix (Fin 2) (Fin 2) ℂ} (hH : H.PosDef) :
    ((gramDiagTwo H : ℝ) : ℂ) * ((gramDiagTwo H : ℝ) : ℂ) = H.det / H 0 0 := by
  have hval : Real.sqrt (H.det.re / (H 0 0).re) * Real.sqrt (H.det.re / (H 0 0).re)
      = H.det.re / (H 0 0).re :=
    Real.mul_self_sqrt (le_of_lt (div_pos (posDef_det_re_pos hH) (posDef_diag_zero_re_pos hH)))
  have hcast : ((gramDiagTwo H : ℝ) : ℂ) * ((gramDiagTwo H : ℝ) : ℂ)
      = ((H.det.re / (H 0 0).re : ℝ) : ℂ) := by
    rw [gramDiagTwo]
    exact_mod_cast congrArg (fun t : ℝ => (t : ℂ)) hval
  rw [hcast, Complex.ofReal_div, ← posDef_det_eq_re hH, ← posDef_diag_zero_eq_re hH]

/-- **The Cholesky factor realizes the record.** -/
theorem gramCholesky_gram {H : Matrix (Fin 2) (Fin 2) ℂ} (hH : H.PosDef) :
    (gramCholesky H)ᴴ * gramCholesky H = H := by
  have hrne := gramDiagOne_ne_zero hH
  have hrsq := gramDiagOne_sq hH
  have htsq := gramDiagTwo_sq hH
  have hconj := posDef_offDiag_conj hH
  have hdet : H.det = H 0 0 * H 1 1 - H 0 1 * H 1 0 := Matrix.det_fin_two H
  have h00ne : H 0 0 ≠ 0 := by
    rw [← hrsq]
    exact mul_ne_zero hrne hrne
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, gramCholesky,
      Fin.sum_univ_two, Fin.zero_eta, Fin.mk_one,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.of_apply,
      Fin.isValue, Complex.star_def, map_div₀, Complex.conj_ofReal, map_zero]
  · simpa using hrsq
  · field_simp
    ring
  · rw [hconj]
    field_simp
    simp
  · rw [htsq, hdet, hconj, ← hrsq]
    field_simp
    simp only [Complex.star_def]
    ring

/-- The canonical section realizes every positive definite Gram record. -/
theorem gramSection_gram {H : Matrix (Fin 2) (Fin 2) ℂ} (hH : H.PosDef) :
    colorGramMatrix (gramSection H) = H := by
  have h := colorEmbedSquare_gram (gramCholesky H)
  rw [gramSection]
  change (colorEmbedSquare (gramCholesky H))ᴴ * colorEmbedSquare (gramCholesky H) = H
  rw [h, gramCholesky_gram hH]

/-- The canonical section is regular. -/
theorem gramSection_posDef {H : Matrix (Fin 2) (Fin 2) ℂ} (hH : H.PosDef) :
    (colorGramMatrix (gramSection H)).PosDef := by
  rw [gramSection_gram hH]
  exact hH

end CholeskySection

section Frame

/-- The explicit inverse of the completed frame of the canonical section. -/
def gramFrameInverse (H : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![(((gramDiagOne H : ℝ) : ℂ))⁻¹,
       -(H 0 1 / (((gramDiagOne H : ℝ) : ℂ) * ((gramDiagOne H : ℝ) : ℂ) *
         ((gramDiagTwo H : ℝ) : ℂ))), 0;
     0, (((gramDiagTwo H : ℝ) : ℂ))⁻¹, 0;
     0, 0, ((((gramDiagOne H : ℝ) : ℂ)) * (((gramDiagTwo H : ℝ) : ℂ)))⁻¹]

@[simp] theorem gramSection_apply_zero (H : Matrix (Fin 2) (Fin 2) ℂ) (j : Fin 2) :
    gramSection H 0 j = gramCholesky H 0 j := by
  simp [gramSection, colorEmbedSquare]

@[simp] theorem gramSection_apply_one (H : Matrix (Fin 2) (Fin 2) ℂ) (j : Fin 2) :
    gramSection H 1 j = gramCholesky H 1 j := rfl

@[simp] theorem gramSection_apply_two (H : Matrix (Fin 2) (Fin 2) ℂ) (j : Fin 2) :
    gramSection H 2 j = 0 := rfl

/-- The completed frame of the canonical section is upper triangular with the two Cholesky
diagonals and their product on the diagonal. -/
theorem colorEventFrame_gramSection (H : Matrix (Fin 2) (Fin 2) ℂ) :
    colorEventFrame (gramSection H) =
      !![((gramDiagOne H : ℝ) : ℂ), H 0 1 / ((gramDiagOne H : ℝ) : ℂ), 0;
         0, ((gramDiagTwo H : ℝ) : ℂ), 0;
         0, 0, ((gramDiagOne H : ℝ) : ℂ) * ((gramDiagTwo H : ℝ) : ℂ)] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [colorEventFrame, colorEventFrameWithThird, colorEventNormal,
      colorMinor01, colorMinor02, colorMinor12, gramCholesky]

/-- The explicit inverse is a right inverse of the section frame. -/
theorem colorEventFrame_gramSection_mul_inverse {H : Matrix (Fin 2) (Fin 2) ℂ} (hH : H.PosDef) :
    colorEventFrame (gramSection H) * gramFrameInverse H = 1 := by
  have hrne := gramDiagOne_ne_zero hH
  have htne := gramDiagTwo_ne_zero hH
  rw [colorEventFrame_gramSection]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gramFrameInverse, Matrix.mul_apply, Fin.sum_univ_three] <;>
    field_simp
  all_goals ring

/-- The explicit inverse is a left inverse of the section frame. -/
theorem gramFrameInverse_mul_colorEventFrame_gramSection
    {H : Matrix (Fin 2) (Fin 2) ℂ} (hH : H.PosDef) :
    gramFrameInverse H * colorEventFrame (gramSection H) = 1 := by
  have hrne := gramDiagOne_ne_zero hH
  have htne := gramDiagTwo_ne_zero hH
  rw [colorEventFrame_gramSection]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gramFrameInverse, Matrix.mul_apply, Fin.sum_univ_three] <;>
    field_simp
  all_goals ring

end Frame

section Transporter

/-- The inclusion of the two event columns into the completed frame. -/
def colorInclusion : Matrix (Fin 3) (Fin 2) ℂ :=
  Matrix.of fun i j => if (i : ℕ) = (j : ℕ) then 1 else 0

theorem colorEventFrameWithThird_mul_inclusion (X : ColorEventMatrix) (w : Fin 3 → ℂ) :
    colorEventFrameWithThird X w * colorInclusion = X := by
  ext i j
  fin_cases j <;>
    simp [colorInclusion, colorEventFrameWithThird, Matrix.mul_apply, Fin.sum_univ_three]

theorem colorEventFrame_mul_inclusion (X : ColorEventMatrix) :
    colorEventFrame X * colorInclusion = X :=
  colorEventFrameWithThird_mul_inclusion X _

/-- The Gram record of a completed frame is the event Gram record bordered by the minor energy. -/
theorem colorEventFrame_conjTranspose_mul_self (X : ColorEventMatrix) :
    (colorEventFrame X)ᴴ * colorEventFrame X =
      !![colorGramMatrix X 0 0, colorGramMatrix X 0 1, 0;
         colorGramMatrix X 1 0, colorGramMatrix X 1 1, 0;
         0, 0, (colorMinorEnergy X : ℂ)] := by
  have hherm : ((colorEventFrame X)ᴴ * colorEventFrame X).IsHermitian :=
    Matrix.isHermitian_conjTranspose_mul_self _
  have hnormal := colorEventNormal_vecMul X
  have hrow0 : ((colorEventFrame X)ᴴ * colorEventFrame X) 2 0 = 0 := by
    have h := congrFun hnormal 0
    simp only [Matrix.vecMul, dotProduct, Pi.star_apply, Pi.zero_apply] at h
    simpa [colorEventFrame, colorEventFrameWithThird, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Fin.sum_univ_three] using h
  have hrow1 : ((colorEventFrame X)ᴴ * colorEventFrame X) 2 1 = 0 := by
    have h := congrFun hnormal 1
    simp only [Matrix.vecMul, dotProduct, Pi.star_apply, Pi.zero_apply] at h
    simpa [colorEventFrame, colorEventFrameWithThird, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Fin.sum_univ_three] using h
  have hcorner : ((colorEventFrame X)ᴴ * colorEventFrame X) 2 2
      = (colorMinorEnergy X : ℂ) := by
    have h := colorEventNormal_rootHermitianNormSq X
    simpa [colorEventFrame, colorEventFrameWithThird, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Fin.sum_univ_three, rootHermitianNormSq,
      dotProduct] using h
  ext i j
  fin_cases i <;> fin_cases j
  · simp [colorEventFrame, colorEventFrameWithThird, Matrix.mul_apply, colorGramMatrix,
      Matrix.conjTranspose_apply, Fin.sum_univ_three]
  · simp [colorEventFrame, colorEventFrameWithThird, Matrix.mul_apply, colorGramMatrix,
      Matrix.conjTranspose_apply, Fin.sum_univ_three]
  · have h2 := congrFun (congrFun hherm.eq 0) 2
    simp only [Matrix.conjTranspose_apply] at h2
    show ((colorEventFrame X)ᴴ * colorEventFrame X) 0 2 = 0
    rw [← h2, hrow0]
    simp
  · simp [colorEventFrame, colorEventFrameWithThird, Matrix.mul_apply, colorGramMatrix,
      Matrix.conjTranspose_apply, Fin.sum_univ_three]
  · simp [colorEventFrame, colorEventFrameWithThird, Matrix.mul_apply, colorGramMatrix,
      Matrix.conjTranspose_apply, Fin.sum_univ_three]
  · have h2 := congrFun (congrFun hherm.eq 1) 2
    simp only [Matrix.conjTranspose_apply] at h2
    show ((colorEventFrame X)ᴴ * colorEventFrame X) 1 2 = 0
    rw [← h2, hrow1]
    simp
  · simpa using hrow0
  · simpa using hrow1
  · simpa using hcorner

/-- Frames of events with the same Gram record have the same frame Gram record. -/
theorem colorEventFrame_gram_congr {X Y : ColorEventMatrix}
    (h : colorGramMatrix X = colorGramMatrix Y) :
    (colorEventFrame X)ᴴ * colorEventFrame X = (colorEventFrame Y)ᴴ * colorEventFrame Y := by
  have hmin : (colorMinorEnergy X : ℂ) = (colorMinorEnergy Y : ℂ) := by
    rw [← colorGramMatrix_det_eq_minorEnergy, ← colorGramMatrix_det_eq_minorEnergy, h]
  rw [colorEventFrame_conjTranspose_mul_self, colorEventFrame_conjTranspose_mul_self, h, hmin]

/-- The canonical transporter carrying the section of an event's Gram record to the event. -/
def colorTransporter (X : ColorEventMatrix) : Matrix (Fin 3) (Fin 3) ℂ :=
  colorEventFrame X * gramFrameInverse (colorGramMatrix X)

theorem colorTransporter_mul_gramSection {X : ColorEventMatrix}
    (hX : (colorGramMatrix X).PosDef) :
    colorTransporter X * gramSection (colorGramMatrix X) = X := by
  have hsec : colorGramMatrix (gramSection (colorGramMatrix X)) = colorGramMatrix X :=
    gramSection_gram hX
  have hframe : colorEventFrame (gramSection (colorGramMatrix X)) * colorInclusion
      = gramSection (colorGramMatrix X) :=
    colorEventFrame_mul_inclusion _
  calc colorTransporter X * gramSection (colorGramMatrix X)
      = colorEventFrame X * (gramFrameInverse (colorGramMatrix X) *
          (colorEventFrame (gramSection (colorGramMatrix X)) * colorInclusion)) := by
        rw [colorTransporter, hframe, Matrix.mul_assoc]
    _ = colorEventFrame X * ((gramFrameInverse (colorGramMatrix X) *
          colorEventFrame (gramSection (colorGramMatrix X))) * colorInclusion) := by
        rw [Matrix.mul_assoc]
    _ = colorEventFrame X * colorInclusion := by
        rw [gramFrameInverse_mul_colorEventFrame_gramSection hX, Matrix.one_mul]
    _ = X := colorEventFrame_mul_inclusion X

theorem colorTransporter_mem_specialUnitary {X : ColorEventMatrix}
    (hX : (colorGramMatrix X).PosDef) :
    colorTransporter X ∈ Matrix.specialUnitaryGroup (Fin 3) ℂ := by
  have hSgram : colorGramMatrix (gramSection (colorGramMatrix X)) = colorGramMatrix X :=
    gramSection_gram hX
  have hgram : (colorEventFrame X)ᴴ * colorEventFrame X
      = (colorEventFrame (gramSection (colorGramMatrix X)))ᴴ *
        colorEventFrame (gramSection (colorGramMatrix X)) :=
    colorEventFrame_gram_congr hSgram.symm
  have hright : colorEventFrame (gramSection (colorGramMatrix X)) *
      gramFrameInverse (colorGramMatrix X) = 1 :=
    colorEventFrame_gramSection_mul_inverse hX
  have hunitary : (colorTransporter X)ᴴ * colorTransporter X = 1 := by
    calc (colorTransporter X)ᴴ * colorTransporter X
        = (gramFrameInverse (colorGramMatrix X))ᴴ *
            (((colorEventFrame X)ᴴ * colorEventFrame X) *
              gramFrameInverse (colorGramMatrix X)) := by
          simp only [colorTransporter, Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = (gramFrameInverse (colorGramMatrix X))ᴴ *
            (((colorEventFrame (gramSection (colorGramMatrix X)))ᴴ *
              colorEventFrame (gramSection (colorGramMatrix X))) *
              gramFrameInverse (colorGramMatrix X)) := by rw [hgram]
      _ = (colorEventFrame (gramSection (colorGramMatrix X)) *
            gramFrameInverse (colorGramMatrix X))ᴴ *
            (colorEventFrame (gramSection (colorGramMatrix X)) *
              gramFrameInverse (colorGramMatrix X)) := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = 1 := by rw [hright]; simp
  have hdetX : (colorEventFrame X).det = (colorGramMatrix X).det := by
    rw [colorEventFrame_det, colorGramMatrix_det_eq_minorEnergy]
  have hdetS : (colorEventFrame (gramSection (colorGramMatrix X))).det
      = (colorGramMatrix X).det := by
    rw [colorEventFrame_det, ← colorGramMatrix_det_eq_minorEnergy, hSgram]
  have hdetinv : (colorEventFrame (gramSection (colorGramMatrix X))).det *
      (gramFrameInverse (colorGramMatrix X)).det = 1 := by
    rw [← Matrix.det_mul, hright, Matrix.det_one]
  rw [Matrix.mem_specialUnitaryGroup_iff]
  refine ⟨by
    rw [Matrix.mem_unitaryGroup_iff']
    simpa [Matrix.star_eq_conjTranspose] using hunitary, ?_⟩
  rw [colorTransporter, Matrix.det_mul, hdetX, ← hdetS]
  exact hdetinv

end Transporter

section Trivialization

/-- **Global product decomposition of the regular colour locus.**  A regular `3 × 2` event is
exactly one `SU(3)` frame together with one positive definite Gram record, and the second
coordinate of the decomposition is the Gram map. -/
def colorRegularTrivialization :
    {X : ColorEventMatrix // (colorGramMatrix X).PosDef} ≃
      (Matrix.specialUnitaryGroup (Fin 3) ℂ ×
        {H : Matrix (Fin 2) (Fin 2) ℂ // H.PosDef}) where
  toFun X :=
    (⟨colorTransporter X.1, colorTransporter_mem_specialUnitary X.2⟩,
      ⟨colorGramMatrix X.1, X.2⟩)
  invFun p :=
    ⟨(p.1 : Matrix (Fin 3) (Fin 3) ℂ) * gramSection p.2.1, by
      have hU : ((p.1 : Matrix (Fin 3) (Fin 3) ℂ))ᴴ *
          (p.1 : Matrix (Fin 3) (Fin 3) ℂ) = 1 := by
        have h := (Matrix.mem_unitaryGroup_iff').mp
          (Matrix.specialUnitaryGroup_le_unitaryGroup p.1.2)
        simpa [Matrix.star_eq_conjTranspose] using h
      rw [colorGramMatrix_left_invariant _ _ hU, gramSection_gram p.2.2]
      exact p.2.2⟩
  left_inv X := Subtype.ext (colorTransporter_mul_gramSection X.2)
  right_inv p := by
    have hU : ((p.1 : Matrix (Fin 3) (Fin 3) ℂ))ᴴ *
        (p.1 : Matrix (Fin 3) (Fin 3) ℂ) = 1 := by
      have h := (Matrix.mem_unitaryGroup_iff').mp
        (Matrix.specialUnitaryGroup_le_unitaryGroup p.1.2)
      simpa [Matrix.star_eq_conjTranspose] using h
    have hgram : colorGramMatrix
        ((p.1 : Matrix (Fin 3) (Fin 3) ℂ) * gramSection p.2.1) = p.2.1 := by
      rw [colorGramMatrix_left_invariant _ _ hU, gramSection_gram p.2.2]
    have hreg : (colorGramMatrix (gramSection p.2.1)).PosDef := gramSection_posDef p.2.2
    apply Prod.ext
    · apply Subtype.ext
      have hmul : colorTransporter ((p.1 : Matrix (Fin 3) (Fin 3) ℂ) * gramSection p.2.1) *
          gramSection p.2.1 = (p.1 : Matrix (Fin 3) (Fin 3) ℂ) * gramSection p.2.1 := by
        have h := colorTransporter_mul_gramSection
          (X := (p.1 : Matrix (Fin 3) (Fin 3) ℂ) * gramSection p.2.1)
          (by rw [hgram]; exact p.2.2)
        rwa [hgram] at h
      exact left_specialUnitary_action_free_on_regular (gramSection p.2.1) hreg _ _
        (colorTransporter_mem_specialUnitary (by rw [hgram]; exact p.2.2)) p.1.2 hmul
    · exact Subtype.ext hgram

@[simp] theorem colorRegularTrivialization_snd
    (X : {X : ColorEventMatrix // (colorGramMatrix X).PosDef}) :
    ((colorRegularTrivialization X).2 : Matrix (Fin 2) (Fin 2) ℂ) = colorGramMatrix X.1 :=
  rfl

@[simp] theorem colorRegularTrivialization_symm_apply
    (p : Matrix.specialUnitaryGroup (Fin 3) ℂ ×
      {H : Matrix (Fin 2) (Fin 2) ℂ // H.PosDef}) :
    ((colorRegularTrivialization.symm p : {X : ColorEventMatrix //
      (colorGramMatrix X).PosDef}) : ColorEventMatrix)
      = (p.1 : Matrix (Fin 3) (Fin 3) ℂ) * gramSection p.2.1 :=
  rfl

end Trivialization

section Continuity

/-- Notation for the regular colour locus as a topological subspace. -/
abbrev ColorRegularLocus := {X : ColorEventMatrix // (colorGramMatrix X).PosDef}

/-- Notation for the positive definite Gram records as a topological subspace. -/
abbrev PositiveGramRecord := {H : Matrix (Fin 2) (Fin 2) ℂ // H.PosDef}

theorem continuous_colorEventNormal : Continuous colorEventNormal := by
  refine continuous_pi fun i => ?_
  fin_cases i <;>
    simp only [colorEventNormal, colorMinor01, colorMinor02, colorMinor12,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Fin.isValue,
      Matrix.cons_val_two, Matrix.tail_cons] <;>
    fun_prop

theorem continuous_colorEventFrame : Continuous colorEventFrame := by
  refine continuous_matrix fun i j => ?_
  fin_cases j <;>
    simp only [colorEventFrame, colorEventFrameWithThird, Fin.isValue, if_true, if_false,
      reduceCtorEq, one_ne_zero] <;>
    first
      | fun_prop
      | exact (continuous_apply i).comp continuous_colorEventNormal

theorem continuous_posDef_gramDiagOne :
    Continuous fun H : PositiveGramRecord => ((gramDiagOne H.1 : ℝ) : ℂ) := by
  have : Continuous fun H : Matrix (Fin 2) (Fin 2) ℂ => ((gramDiagOne H : ℝ) : ℂ) := by
    unfold gramDiagOne
    fun_prop
  exact this.comp continuous_subtype_val

theorem continuous_posDef_gramDiagTwo :
    Continuous fun H : PositiveGramRecord => ((gramDiagTwo H.1 : ℝ) : ℂ) := by
  have hdet : Continuous fun H : Matrix (Fin 2) (Fin 2) ℂ => H.det := by
    have : (fun H : Matrix (Fin 2) (Fin 2) ℂ => H.det)
        = fun H => H 0 0 * H 1 1 - H 0 1 * H 1 0 := by
      funext H
      exact Matrix.det_fin_two H
    rw [this]
    fun_prop
  have hzero : ∀ H : PositiveGramRecord, ((H.1 : Matrix (Fin 2) (Fin 2) ℂ) 0 0).re ≠ 0 :=
    fun H => (posDef_diag_zero_re_pos H.2).ne'
  unfold gramDiagTwo
  refine Complex.continuous_ofReal.comp (Real.continuous_sqrt.comp ?_)
  refine Continuous.div ?_ ?_ hzero
  · exact (Complex.continuous_re.comp hdet).comp continuous_subtype_val
  · exact (Complex.continuous_re.comp ((continuous_apply_apply 0 0))).comp continuous_subtype_val

theorem continuous_posDef_gramCholesky :
    Continuous fun H : PositiveGramRecord => gramCholesky H.1 := by
  have hrne : ∀ H : PositiveGramRecord, ((gramDiagOne H.1 : ℝ) : ℂ) ≠ 0 :=
    fun H => gramDiagOne_ne_zero H.2
  refine continuous_matrix fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp only [gramCholesky, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Fin.zero_eta, Fin.mk_one, Fin.isValue]
  · exact continuous_posDef_gramDiagOne
  · exact Continuous.div
      (((continuous_apply_apply (0 : Fin 2) (1 : Fin 2)).comp continuous_subtype_val))
      continuous_posDef_gramDiagOne hrne
  · exact continuous_const
  · exact continuous_posDef_gramDiagTwo

theorem continuous_posDef_gramSection :
    Continuous fun H : PositiveGramRecord => gramSection H.1 :=
  continuous_colorEmbedSquare.comp continuous_posDef_gramCholesky

theorem continuous_posDef_gramFrameInverse :
    Continuous fun H : PositiveGramRecord => gramFrameInverse H.1 := by
  have hrne : ∀ H : PositiveGramRecord, ((gramDiagOne H.1 : ℝ) : ℂ) ≠ 0 :=
    fun H => gramDiagOne_ne_zero H.2
  have htne : ∀ H : PositiveGramRecord, ((gramDiagTwo H.1 : ℝ) : ℂ) ≠ 0 :=
    fun H => gramDiagTwo_ne_zero H.2
  have hrrt : ∀ H : PositiveGramRecord,
      ((gramDiagOne H.1 : ℝ) : ℂ) * ((gramDiagOne H.1 : ℝ) : ℂ) *
        ((gramDiagTwo H.1 : ℝ) : ℂ) ≠ 0 :=
    fun H => mul_ne_zero (mul_ne_zero (hrne H) (hrne H)) (htne H)
  have hrt : ∀ H : PositiveGramRecord,
      ((gramDiagOne H.1 : ℝ) : ℂ) * ((gramDiagTwo H.1 : ℝ) : ℂ) ≠ 0 :=
    fun H => mul_ne_zero (hrne H) (htne H)
  refine continuous_matrix fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp only [gramFrameInverse, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Fin.zero_eta, Fin.mk_one, Fin.isValue, Matrix.cons_val_two,
      Matrix.tail_cons]
  · exact continuous_posDef_gramDiagOne.inv₀ hrne
  · exact ((((continuous_apply_apply (0 : Fin 2) (1 : Fin 2)).comp
      continuous_subtype_val)).div
      ((continuous_posDef_gramDiagOne.mul continuous_posDef_gramDiagOne).mul
        continuous_posDef_gramDiagTwo) hrrt).neg
  · exact continuous_const
  · exact continuous_const
  · exact continuous_posDef_gramDiagTwo.inv₀ htne
  · exact continuous_const
  · exact continuous_const
  · exact continuous_const
  · exact (continuous_posDef_gramDiagOne.mul continuous_posDef_gramDiagTwo).inv₀ hrt

theorem continuous_colorTransporter :
    Continuous fun X : ColorRegularLocus => colorTransporter X.1 := by
  have hgram : Continuous fun X : ColorRegularLocus =>
      (⟨colorGramMatrix X.1, X.2⟩ : PositiveGramRecord) :=
    Continuous.subtype_mk (continuous_colorGramMatrix.comp continuous_subtype_val) _
  exact (continuous_colorEventFrame.comp continuous_subtype_val).mul
    (continuous_posDef_gramFrameInverse.comp hgram)

/-- **The global product decomposition is a homeomorphism.** -/
def colorRegularHomeomorph :
    ColorRegularLocus ≃ₜ (Matrix.specialUnitaryGroup (Fin 3) ℂ × PositiveGramRecord) where
  toEquiv := colorRegularTrivialization
  continuous_toFun := by
    refine Continuous.prodMk ?_ ?_
    · exact Continuous.subtype_mk continuous_colorTransporter _
    · exact Continuous.subtype_mk (continuous_colorGramMatrix.comp continuous_subtype_val) _
  continuous_invFun := by
    refine Continuous.subtype_mk ?_ _
    exact (continuous_subtype_val.comp continuous_fst).mul
      (continuous_posDef_gramSection.comp continuous_snd)

end Continuity

end GaloisForLFunctions.HTGeometry
