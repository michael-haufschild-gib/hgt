import GaloisForLFunctions.HTGeometry.FiniteSpecialUnitaryHaarTopology

/-!
# Continuous normalization from finite unitary to special-unitary matrices

An explicit diagonal determinant section turns every finite complex unitary
matrix into a special-unitary matrix.  The normalizer is continuous, fixes
`SU(d)`, is left `SU(d)`-equivariant, and transports normalized `U(d)` Haar
measure exactly to normalized `SU(d)` Haar measure.
-/

open Matrix
open MeasureTheory MeasureTheory.Measure TopologicalSpace

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- A unitary diagonal matrix whose determinant is the supplied unit complex
number, using one designated basis coordinate. -/
def unitaryDeterminantSection
    {ι : Type*} [Fintype ι] [DecidableEq ι] (i0 : ι)
    (z : ℂ) (hz : star z * z = 1) : Matrix.unitaryGroup ι ℂ :=
  ⟨Matrix.diagonal (Function.update (fun _ => 1) i0 z), by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
      Matrix.diagonal_conjTranspose,
      Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases hij : i = j
    · subst j
      by_cases hi : i = i0
      · subst i
        rw [Matrix.diagonal_apply_eq]
        simp only [Function.update_self, Pi.star_apply, Matrix.one_apply, if_pos]
        simpa only [starRingEnd_apply, mul_comm] using hz
      · simp [Function.update, hi]
    · simp [hij]
  ⟩

/-- The determinant section has exactly its prescribed determinant. -/
theorem unitaryDeterminantSection_det
    {ι : Type*} [Fintype ι] [DecidableEq ι] (i0 : ι)
    (z : ℂ) (hz : star z * z = 1) :
    (unitaryDeterminantSection i0 z hz : Matrix ι ι ℂ).det = z := by
  unfold unitaryDeterminantSection
  rw [Matrix.det_diagonal]
  rw [Finset.prod_update_of_mem (Finset.mem_univ i0) (fun _ : ι => 1) z]
  simp

/-- The determinant section takes `1` to the identity unitary. -/
theorem unitaryDeterminantSection_one
    {ι : Type*} [Fintype ι] [DecidableEq ι] (i0 : ι) :
    unitaryDeterminantSection i0 1 (by simp) = (1 : Matrix.unitaryGroup ι ℂ) := by
  apply Subtype.ext
  change Matrix.diagonal (Function.update (fun _ : ι => (1 : ℂ)) i0 1) = 1
  rw [Function.update_eq_self]
  rfl

/-- Remove a unitary matrix's determinant using the explicit diagonal
section. -/
def specialUnitaryNormalize
    {ι : Type*} [Fintype ι] [DecidableEq ι] (i0 : ι)
    (U : Matrix.unitaryGroup ι ℂ) : Matrix.specialUnitaryGroup ι ℂ := by
  have hdet : star U.1.det * U.1.det = 1 :=
    (Unitary.mem_iff.mp (Matrix.det_of_mem_unitary U.2)).1
  let D : Matrix.unitaryGroup ι ℂ :=
    unitaryDeterminantSection i0 U.1.det hdet
  refine ⟨U * D⁻¹, ?_⟩
  rw [Matrix.mem_specialUnitaryGroup_iff]
  constructor
  · exact (U * D⁻¹).2
  · change (U.1 * (D⁻¹).1).det = 1
    rw [Matrix.det_mul]
    have hDdet : D.1.det = U.1.det :=
      unitaryDeterminantSection_det i0 U.1.det hdet
    have hDinv : (D⁻¹).1.det = star U.1.det := by
      change (star (D.1 : Matrix ι ι ℂ)).det = star U.1.det
      rw [Matrix.star_eq_conjTranspose, Matrix.det_conjTranspose, hDdet]
    rw [hDinv]
    simpa only [mul_comm] using hdet

/-- Normalization fixes a unitary matrix that already has determinant one. -/
theorem specialUnitaryNormalize_eq_of_det_eq_one
    {ι : Type*} [Fintype ι] [DecidableEq ι] (i0 : ι)
    (U : Matrix.unitaryGroup ι ℂ) (hU : U.1.det = 1) :
    specialUnitaryNormalize i0 U =
      ⟨U.1, Matrix.mem_specialUnitaryGroup_iff.mpr ⟨U.2, hU⟩⟩ := by
  apply Subtype.ext
  unfold specialUnitaryNormalize
  have hdet : star U.1.det * U.1.det = 1 :=
    (Unitary.mem_iff.mp (Matrix.det_of_mem_unitary U.2)).1
  change U.1 * star (unitaryDeterminantSection i0 U.1.det hdet : Matrix ι ι ℂ) = U.1
  have hD : (unitaryDeterminantSection i0 U.1.det hdet : Matrix ι ι ℂ) = 1 := by
    change Matrix.diagonal (Function.update (fun _ : ι => (1 : ℂ)) i0 U.1.det) = 1
    rw [hU, Function.update_eq_self]
    rfl
  rw [hD]
  simp

/-- Forget determinant-one certification. -/
def specialUnitaryToUnitary
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Matrix.specialUnitaryGroup ι ℂ) : Matrix.unitaryGroup ι ℂ :=
  ⟨S.1, (Matrix.mem_specialUnitaryGroup_iff.mp S.2).1⟩

/-- Normalization commutes with left multiplication by a special-unitary
matrix. -/
theorem specialUnitaryNormalize_mul_left
    {ι : Type*} [Fintype ι] [DecidableEq ι] (i0 : ι)
    (S : Matrix.specialUnitaryGroup ι ℂ) (U : Matrix.unitaryGroup ι ℂ) :
    specialUnitaryNormalize i0 (specialUnitaryToUnitary S * U) =
      S * specialUnitaryNormalize i0 U := by
  apply Subtype.ext
  unfold specialUnitaryNormalize
  have hdetSU : (S.1 * U.1).det = U.1.det := by
    rw [Matrix.det_mul, (Matrix.mem_specialUnitaryGroup_iff.mp S.2).2, one_mul]
  have hdetU : star U.1.det * U.1.det = 1 :=
    (Unitary.mem_iff.mp (Matrix.det_of_mem_unitary U.2)).1
  have hdetLeft : star (S.1 * U.1).det * (S.1 * U.1).det = 1 := by
    rw [hdetSU]
    exact hdetU
  change (S.1 * U.1) * star
      (unitaryDeterminantSection i0 (S.1 * U.1).det hdetLeft : Matrix ι ι ℂ) =
    S.1 * (U.1 * star
      (unitaryDeterminantSection i0 U.1.det hdetU : Matrix ι ι ℂ))
  have hsection :
      (unitaryDeterminantSection i0 (S.1 * U.1).det hdetLeft : Matrix ι ι ℂ) =
        (unitaryDeterminantSection i0 U.1.det hdetU : Matrix ι ι ℂ) := by
    change Matrix.diagonal (Function.update (fun _ : ι => (1 : ℂ)) i0 (S.1 * U.1).det) =
      Matrix.diagonal (Function.update (fun _ : ι => (1 : ℂ)) i0 U.1.det)
    rw [hdetSU]
  rw [hsection, Matrix.mul_assoc]

/-- Determinant normalization is continuous. -/
theorem continuous_specialUnitaryNormalize
    {ι : Type*} [Fintype ι] [DecidableEq ι] (i0 : ι) :
    Continuous (specialUnitaryNormalize i0 :
      Matrix.unitaryGroup ι ℂ → Matrix.specialUnitaryGroup ι ℂ) := by
  apply continuous_induced_rng.2
  change Continuous (fun U : Matrix.unitaryGroup ι ℂ =>
    (U.1 : Matrix ι ι ℂ) * star
      (Matrix.diagonal (Function.update (fun _ : ι => (1 : ℂ)) i0 U.1.det)))
  fun_prop

/-- Left `SU(d)` invariance of normalized unitary Haar under determinant
normalization. -/
theorem map_specialUnitaryNormalize_mul_left
    {ι : Type*} [Fintype ι] [DecidableEq ι] (i0 : ι)
    (S : Matrix.specialUnitaryGroup ι ℂ) :
    Measure.map (fun V : Matrix.specialUnitaryGroup ι ℂ => S * V)
      (Measure.map (specialUnitaryNormalize i0) (finiteUnitaryHaar ι)) =
      Measure.map (specialUnitaryNormalize i0) (finiteUnitaryHaar ι) := by
  letI : IsHaarMeasure (finiteUnitaryHaar ι) := by
    unfold finiteUnitaryHaar
    infer_instance
  have hnorm : Measurable (specialUnitaryNormalize i0 :
      Matrix.unitaryGroup ι ℂ → Matrix.specialUnitaryGroup ι ℂ) :=
    (continuous_specialUnitaryNormalize i0).measurable
  have hleft : Measurable (fun U : Matrix.unitaryGroup ι ℂ =>
      specialUnitaryToUnitary S * U) :=
    measurable_const_mul (specialUnitaryToUnitary S)
  have htarget : Measurable (fun V : Matrix.specialUnitaryGroup ι ℂ => S * V) :=
    measurable_const_mul S
  calc
    Measure.map (fun V : Matrix.specialUnitaryGroup ι ℂ => S * V)
        (Measure.map (specialUnitaryNormalize i0) (finiteUnitaryHaar ι)) =
        Measure.map ((fun V : Matrix.specialUnitaryGroup ι ℂ => S * V) ∘
          specialUnitaryNormalize i0) (finiteUnitaryHaar ι) :=
      Measure.map_map htarget hnorm
    _ = Measure.map (specialUnitaryNormalize i0 ∘
          fun U : Matrix.unitaryGroup ι ℂ => specialUnitaryToUnitary S * U)
          (finiteUnitaryHaar ι) := by
      congr 1
      funext U
      exact (specialUnitaryNormalize_mul_left i0 S U).symm
    _ = Measure.map (specialUnitaryNormalize i0)
          (Measure.map (fun U : Matrix.unitaryGroup ι ℂ =>
            specialUnitaryToUnitary S * U) (finiteUnitaryHaar ι)) :=
      (Measure.map_map hnorm hleft).symm
    _ = Measure.map (specialUnitaryNormalize i0) (finiteUnitaryHaar ι) := by
      rw [map_mul_left_eq_self]

/-- Normalization is a retraction from finite unitary matrices onto finite
special-unitary matrices. -/
theorem specialUnitaryNormalize_toUnitary
    {ι : Type*} [Fintype ι] [DecidableEq ι] (i0 : ι)
    (S : Matrix.specialUnitaryGroup ι ℂ) :
    specialUnitaryNormalize i0 (specialUnitaryToUnitary S) = S := by
  rw [specialUnitaryNormalize_eq_of_det_eq_one i0
    (specialUnitaryToUnitary S)
    (Matrix.mem_specialUnitaryGroup_iff.mp S.2).2]
  rfl

/-- The pushforward of finite unitary Haar by the normalizer is Haar on the
special-unitary group. -/
theorem specialUnitaryNormalize_isHaar
    {ι : Type*} [Fintype ι] [DecidableEq ι] (i0 : ι) :
    IsHaarMeasure
      (Measure.map (specialUnitaryNormalize i0) (finiteUnitaryHaar ι)) where
  map_mul_left_eq_self := map_specialUnitaryNormalize_mul_left i0
  lt_top_of_isCompact := by
    intro K _
    exact measure_lt_top _ K
  open_pos := by
    letI : IsHaarMeasure (finiteUnitaryHaar ι) := by
      unfold finiteUnitaryHaar
      infer_instance
    intro s hs hne
    rw [Measure.map_apply (continuous_specialUnitaryNormalize i0).measurable hs.measurableSet]
    apply (continuous_specialUnitaryNormalize i0).isOpen_preimage s hs |>.measure_ne_zero
      (finiteUnitaryHaar ι)
    rcases hne with ⟨S, hS⟩
    exact ⟨specialUnitaryToUnitary S, by
      change specialUnitaryNormalize i0 (specialUnitaryToUnitary S) ∈ s
      rw [specialUnitaryNormalize_toUnitary]
      exact hS⟩

/-- Determinant normalization pushes normalized finite-unitary Haar exactly
to normalized finite-special-unitary Haar. -/
theorem map_specialUnitaryNormalize_finiteUnitaryHaar
    {ι : Type*} [Fintype ι] [DecidableEq ι] (i0 : ι) :
    Measure.map (specialUnitaryNormalize i0) (finiteUnitaryHaar ι) =
      finiteSpecialUnitaryHaar ι := by
  letI : IsHaarMeasure
      (Measure.map (specialUnitaryNormalize i0) (finiteUnitaryHaar ι)) :=
    specialUnitaryNormalize_isHaar i0
  have hprob :
      Measure.map (specialUnitaryNormalize i0) (finiteUnitaryHaar ι) Set.univ = 1 := by
    rw [Measure.map_apply_of_aemeasurable
      (continuous_specialUnitaryNormalize i0).measurable.aemeasurable MeasurableSet.univ]
    exact finiteUnitaryHaar_apply_univ ι
  have hscalar := isMulLeftInvariant_eq_smul_of_regular
    (Measure.map (specialUnitaryNormalize i0) (finiteUnitaryHaar ι))
    (finiteSpecialUnitaryHaar ι)
  have hfactor :
      haarScalarFactor
          (Measure.map (specialUnitaryNormalize i0) (finiteUnitaryHaar ι))
          (finiteSpecialUnitaryHaar ι) = 1 := by
    have huniv := congrArg
      (fun μ : Measure (Matrix.specialUnitaryGroup ι ℂ) => μ Set.univ) hscalar
    rw [hprob, Measure.smul_apply, finiteSpecialUnitaryHaar_apply_univ] at huniv
    simpa using huniv.symm
  rw [hfactor] at hscalar
  simpa using hscalar

end

end GaloisForLFunctions.HTGeometry
