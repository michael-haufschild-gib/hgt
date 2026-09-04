import GaloisForLFunctions.HTGeometry.NumberFieldRankTwoCuspFrame

/-!
# Transitivity within a rank-two number-field cusp class

The pseudo-basis frame of a vector has one column in its coordinate ideal and one column in the
inverse ideal.  For two vectors with the same coordinate ideal, the product of one frame with the
inverse of the other therefore has algebraic-integer entries.  It has determinant one and sends the
first vector to the second.  After Steinitz normalization this gives projective transitivity of
`SL₂(𝓞_K)` within each ideal-class cusp.
-/

namespace GaloisForLFunctions.HTGeometry

open NumberField
open scoped Classical NumberField

noncomputable section

variable (K : Type*) [Field K] [NumberField K]

/-- Explicit inverse of the determinant-one cusp frame. -/
def numberFieldRankTwoCuspFrameInv
    (v : Fin 2 → K) (hv : v ≠ 0) : Matrix (Fin 2) (Fin 2) K :=
  !![numberFieldRankTwoCuspDual K v hv 0,
      numberFieldRankTwoCuspDual K v hv 1;
    -v 1, v 0]

@[simp]
theorem numberFieldRankTwoCuspFrameInv_mul
    (v : Fin 2 → K) (hv : v ≠ 0) :
    numberFieldRankTwoCuspFrameInv K v hv *
      numberFieldRankTwoCuspFrame K v hv = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [numberFieldRankTwoCuspFrameInv, numberFieldRankTwoCuspFrame,
      Matrix.mul_apply, Fin.sum_univ_two]
  · calc
      numberFieldRankTwoCuspDual K v hv 0 * v 0 +
          numberFieldRankTwoCuspDual K v hv 1 * v 1 =
        v 0 * numberFieldRankTwoCuspDual K v hv 0 +
          v 1 * numberFieldRankTwoCuspDual K v hv 1 := by ring
      _ = 1 := numberFieldRankTwoCuspDual_pairing K v hv
  · ring
  · ring
  · calc
      v 1 * numberFieldRankTwoCuspDual K v hv 1 +
          v 0 * numberFieldRankTwoCuspDual K v hv 0 =
        v 0 * numberFieldRankTwoCuspDual K v hv 0 +
          v 1 * numberFieldRankTwoCuspDual K v hv 1 := by ring
      _ = 1 := numberFieldRankTwoCuspDual_pairing K v hv

@[simp]
theorem numberFieldRankTwoCuspFrame_mul_inv
    (v : Fin 2 → K) (hv : v ≠ 0) :
    numberFieldRankTwoCuspFrame K v hv *
      numberFieldRankTwoCuspFrameInv K v hv = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [numberFieldRankTwoCuspFrameInv, numberFieldRankTwoCuspFrame,
      Matrix.mul_apply, Fin.sum_univ_two]
  · calc
      v 0 * numberFieldRankTwoCuspDual K v hv 0 +
          numberFieldRankTwoCuspDual K v hv 1 * v 1 =
        v 0 * numberFieldRankTwoCuspDual K v hv 0 +
          v 1 * numberFieldRankTwoCuspDual K v hv 1 := by ring
      _ = 1 := numberFieldRankTwoCuspDual_pairing K v hv
  · ring
  · ring
  · calc
      v 1 * numberFieldRankTwoCuspDual K v hv 1 +
          numberFieldRankTwoCuspDual K v hv 0 * v 0 =
        v 0 * numberFieldRankTwoCuspDual K v hv 0 +
          v 1 * numberFieldRankTwoCuspDual K v hv 1 := by ring
      _ = 1 := numberFieldRankTwoCuspDual_pairing K v hv

/-- Field-valued transition between two cusp pseudo-basis frames. -/
def numberFieldRankTwoCuspTransition
    (v : Fin 2 → K) (hv : v ≠ 0)
    (w : Fin 2 → K) (hw : w ≠ 0) : Matrix (Fin 2) (Fin 2) K :=
  numberFieldRankTwoCuspFrame K w hw *
    numberFieldRankTwoCuspFrameInv K v hv

@[simp]
theorem numberFieldRankTwoCuspTransition_det
    (v : Fin 2 → K) (hv : v ≠ 0)
    (w : Fin 2 → K) (hw : w ≠ 0) :
    (numberFieldRankTwoCuspTransition K v hv w hw).det = 1 := by
  rw [numberFieldRankTwoCuspTransition, Matrix.det_mul,
    numberFieldRankTwoCuspFrame_det]
  rw [Matrix.det_fin_two]
  dsimp [numberFieldRankTwoCuspFrameInv]
  calc
    1 * (numberFieldRankTwoCuspDual K v hv 0 * v 0 -
        numberFieldRankTwoCuspDual K v hv 1 * -v 1) =
      v 0 * numberFieldRankTwoCuspDual K v hv 0 +
        v 1 * numberFieldRankTwoCuspDual K v hv 1 := by ring
    _ = 1 := numberFieldRankTwoCuspDual_pairing K v hv

/-- The field-valued cusp transition sends the source vector to the target vector. -/
theorem numberFieldRankTwoCuspTransition_mulVec
    (v : Fin 2 → K) (hv : v ≠ 0)
    (w : Fin 2 → K) (hw : w ≠ 0) :
    (numberFieldRankTwoCuspTransition K v hv w hw).mulVec v = w := by
  have hvcol :
      (numberFieldRankTwoCuspFrame K v hv).mulVec (![1, 0] : Fin 2 → K) = v := by
    funext i
    fin_cases i <;>
      simp [numberFieldRankTwoCuspFrame, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have hwcol :
      (numberFieldRankTwoCuspFrame K w hw).mulVec (![1, 0] : Fin 2 → K) = w := by
    funext i
    fin_cases i <;>
      simp [numberFieldRankTwoCuspFrame, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have hinvcol :
      (numberFieldRankTwoCuspFrameInv K v hv).mulVec v = (![1, 0] : Fin 2 → K) := by
    calc
      (numberFieldRankTwoCuspFrameInv K v hv).mulVec v =
          (numberFieldRankTwoCuspFrameInv K v hv).mulVec
            ((numberFieldRankTwoCuspFrame K v hv).mulVec ![1, 0]) := by rw [hvcol]
      _ = (numberFieldRankTwoCuspFrameInv K v hv *
          numberFieldRankTwoCuspFrame K v hv).mulVec ![1, 0] :=
        Matrix.mulVec_mulVec _ _ _
      _ = ![1, 0] := by rw [numberFieldRankTwoCuspFrameInv_mul, Matrix.one_mulVec]
  rw [numberFieldRankTwoCuspTransition, ← Matrix.mulVec_mulVec, hinvcol, hwcol]

/-- If two nonzero rank-two vectors generate the same fractional ideal, every entry of their cusp
transition is an algebraic integer. -/
theorem exists_ringOfIntegers_eq_numberFieldRankTwoCuspTransition_entry
    (v : Fin 2 → K) (hv : v ≠ 0)
    (w : Fin 2 → K) (hw : w ≠ 0)
    (hI : numberFieldRankTwoCoordinateIdeal K v =
      numberFieldRankTwoCoordinateIdeal K w)
    (i j : Fin 2) :
    ∃ a : 𝓞 K,
      (a : K) = numberFieldRankTwoCuspTransition K v hv w hw i j := by
  have hunit : numberFieldRankTwoCoordinateIdealUnit K v hv =
      numberFieldRankTwoCoordinateIdealUnit K w hw := by
    apply Units.ext
    exact hI
  have hwmem (q : Fin 2) : w q ∈ numberFieldRankTwoCoordinateIdeal K v := by
    rw [hI]
    exact numberFieldRankTwo_mem_coordinateIdeal K w q
  have hvmem (q : Fin 2) : v q ∈ numberFieldRankTwoCoordinateIdeal K v :=
    numberFieldRankTwo_mem_coordinateIdeal K v q
  have hdvmem (q : Fin 2) : numberFieldRankTwoCuspDual K v hv q ∈
      (↑((numberFieldRankTwoCoordinateIdealUnit K v hv)⁻¹) :
        FractionalIdeal (nonZeroDivisors (𝓞 K)) K) :=
    numberFieldRankTwoCuspDual_mem_inv K v hv q
  have hdwmem (q : Fin 2) : numberFieldRankTwoCuspDual K w hw q ∈
      (↑((numberFieldRankTwoCoordinateIdealUnit K v hv)⁻¹) :
        FractionalIdeal (nonZeroDivisors (𝓞 K)) K) := by
    rw [hunit]
    exact numberFieldRankTwoCuspDual_mem_inv K w hw q
  fin_cases i <;> fin_cases j
  · obtain ⟨a, ha⟩ :=
      exists_ringOfIntegers_eq_mul_of_mem_coordinateIdeal_mul_inv K v hv
        (hwmem 0) (hdvmem 0)
    obtain ⟨b, hb⟩ :=
      exists_ringOfIntegers_eq_mul_of_mem_coordinateIdeal_mul_inv K v hv
        (hvmem 1) (hdwmem 1)
    refine ⟨a + b, ?_⟩
    change (a : K) + (b : K) = _
    rw [ha, hb]
    simp [numberFieldRankTwoCuspTransition, numberFieldRankTwoCuspFrame,
      numberFieldRankTwoCuspFrameInv, Matrix.mul_apply, Fin.sum_univ_two]
    ring
  · obtain ⟨a, ha⟩ :=
      exists_ringOfIntegers_eq_mul_of_mem_coordinateIdeal_mul_inv K v hv
        (hwmem 0) (hdvmem 1)
    obtain ⟨b, hb⟩ :=
      exists_ringOfIntegers_eq_mul_of_mem_coordinateIdeal_mul_inv K v hv
        (hvmem 0) (hdwmem 1)
    refine ⟨a - b, ?_⟩
    change (a : K) - (b : K) = _
    rw [ha, hb]
    simp [numberFieldRankTwoCuspTransition, numberFieldRankTwoCuspFrame,
      numberFieldRankTwoCuspFrameInv, Matrix.mul_apply, Fin.sum_univ_two]
    ring
  · obtain ⟨a, ha⟩ :=
      exists_ringOfIntegers_eq_mul_of_mem_coordinateIdeal_mul_inv K v hv
        (hwmem 1) (hdvmem 0)
    obtain ⟨b, hb⟩ :=
      exists_ringOfIntegers_eq_mul_of_mem_coordinateIdeal_mul_inv K v hv
        (hvmem 1) (hdwmem 0)
    refine ⟨a - b, ?_⟩
    change (a : K) - (b : K) = _
    rw [ha, hb]
    simp [numberFieldRankTwoCuspTransition, numberFieldRankTwoCuspFrame,
      numberFieldRankTwoCuspFrameInv, Matrix.mul_apply, Fin.sum_univ_two]
    ring
  · obtain ⟨a, ha⟩ :=
      exists_ringOfIntegers_eq_mul_of_mem_coordinateIdeal_mul_inv K v hv
        (hwmem 1) (hdvmem 1)
    obtain ⟨b, hb⟩ :=
      exists_ringOfIntegers_eq_mul_of_mem_coordinateIdeal_mul_inv K v hv
        (hvmem 0) (hdwmem 0)
    refine ⟨a + b, ?_⟩
    change (a : K) + (b : K) = _
    rw [ha, hb]
    simp [numberFieldRankTwoCuspTransition, numberFieldRankTwoCuspFrame,
      numberFieldRankTwoCuspFrameInv, Matrix.mul_apply, Fin.sum_univ_two]
    ring

/-- Equal coordinate ideals are in one literal `SL₂(𝓞_K)` orbit. -/
theorem exists_numberFieldRankTwoSpecialLinear_map_of_coordinateIdeal_eq
    (v : Fin 2 → K) (hv : v ≠ 0)
    (w : Fin 2 → K) (hw : w ≠ 0)
    (hI : numberFieldRankTwoCoordinateIdeal K v =
      numberFieldRankTwoCoordinateIdeal K w) :
    ∃ g : Matrix.SpecialLinearGroup (Fin 2) (𝓞 K),
      (numberFieldRankTwoMatrixBaseChange K
        (g : Matrix (Fin 2) (Fin 2) (𝓞 K))).mulVec v = w := by
  choose entry hentry using fun i j =>
    exists_ringOfIntegers_eq_numberFieldRankTwoCuspTransition_entry
      K v hv w hw hI i j
  let M : Matrix (Fin 2) (Fin 2) (𝓞 K) := fun i j => entry i j
  have hbase : numberFieldRankTwoMatrixBaseChange K M =
      numberFieldRankTwoCuspTransition K v hv w hw := by
    ext i j
    exact hentry i j
  have hdetK : ((M.det : 𝓞 K) : K) = 1 := by
    have h := congrArg Matrix.det hbase
    rw [numberFieldRankTwoCuspTransition_det] at h
    simpa [numberFieldRankTwoMatrixBaseChange, Matrix.det_fin_two] using h
  have hdet : M.det = 1 := by
    exact_mod_cast hdetK
  let g : Matrix.SpecialLinearGroup (Fin 2) (𝓞 K) := ⟨M, hdet⟩
  refine ⟨g, ?_⟩
  change (numberFieldRankTwoMatrixBaseChange K M).mulVec v = w
  rw [hbase]
  exact numberFieldRankTwoCuspTransition_mulVec K v hv w hw

/-- The ideal-class label is a complete invariant of projective `SL₂(𝓞_K)` cusp orbits. -/
theorem exists_numberFieldRankTwoSpecialLinear_projective_map_of_cuspClass_eq
    (v w : numberFieldRankTwoNonzeroVector K)
    (hclass : numberFieldRankTwoCuspClass K v =
      numberFieldRankTwoCuspClass K w) :
    ∃ g : Matrix.SpecialLinearGroup (Fin 2) (𝓞 K),
      ∃ a : K, a ≠ 0 ∧
        ∀ i, (numberFieldRankTwoMatrixBaseChange K
          (g : Matrix (Fin 2) (Fin 2) (𝓞 K))).mulVec v.1 i = a * w.1 i := by
  let nv := numberFieldRankTwoNormalizedVector K v.1 v.2
  let nw := numberFieldRankTwoNormalizedVector K w.1 w.2
  have hnv : nv ≠ 0 := numberFieldRankTwoNormalizedVector_ne_zero K v.1 v.2
  have hnw : nw ≠ 0 := numberFieldRankTwoNormalizedVector_ne_zero K w.1 w.2
  have hI : numberFieldRankTwoCoordinateIdeal K nv =
      numberFieldRankTwoCoordinateIdeal K nw := by
    rw [show numberFieldRankTwoCoordinateIdeal K nv =
        (↑(numberFieldIdealClassRepresentative K
          (numberFieldRankTwoCuspClass K v)) :
            FractionalIdeal (nonZeroDivisors (𝓞 K)) K) by
      simpa [nv, numberFieldRankTwoCuspClass] using
        numberFieldRankTwoNormalizedVector_coordinateIdeal K v.1 v.2]
    rw [show numberFieldRankTwoCoordinateIdeal K nw =
        (↑(numberFieldIdealClassRepresentative K
          (numberFieldRankTwoCuspClass K w)) :
            FractionalIdeal (nonZeroDivisors (𝓞 K)) K) by
      simpa [nw, numberFieldRankTwoCuspClass] using
        numberFieldRankTwoNormalizedVector_coordinateIdeal K w.1 w.2]
    rw [hclass]
  obtain ⟨g, hg⟩ :=
    exists_numberFieldRankTwoSpecialLinear_map_of_coordinateIdeal_eq
      K nv hnv nw hnw hI
  let av := numberFieldIdealClassNormalizer K
    (numberFieldRankTwoCoordinateIdealUnit K v.1 v.2)
  let aw := numberFieldIdealClassNormalizer K
    (numberFieldRankTwoCoordinateIdealUnit K w.1 w.2)
  have hav : av ≠ 0 := numberFieldIdealClassNormalizer_ne_zero K _
  have haw : aw ≠ 0 := numberFieldIdealClassNormalizer_ne_zero K _
  let a := av * aw⁻¹
  have ha : a ≠ 0 := mul_ne_zero hav (inv_ne_zero haw)
  refine ⟨g, a, ha, ?_⟩
  intro i
  let G := numberFieldRankTwoMatrixBaseChange K
    (g : Matrix (Fin 2) (Fin 2) (𝓞 K))
  have hvrec : (fun q => av * nv q) = v.1 := by
    funext q
    exact numberFieldRankTwo_normalizer_mul_normalizedVector K v.1 v.2 q
  have hwrec : (fun q => aw * nw q) = w.1 := by
    funext q
    exact numberFieldRankTwo_normalizer_mul_normalizedVector K w.1 w.2 q
  calc
    G.mulVec v.1 i = G.mulVec (fun q => av * nv q) i := by rw [hvrec]
    _ = av * G.mulVec nv i := by
      simp [G, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      ring
    _ = av * nw i := by rw [hg]
    _ = a * w.1 i := by
      rw [← hwrec]
      dsimp [a]
      field_simp

end

end GaloisForLFunctions.HTGeometry
