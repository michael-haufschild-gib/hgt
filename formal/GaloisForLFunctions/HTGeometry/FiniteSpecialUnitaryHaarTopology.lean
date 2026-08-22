import GaloisForLFunctions.HTGeometry.FiniteSpecialUnitaryHaarMeasure

/-!
# Topological support of finite special-unitary Haar measure

The normalized Haar law on a finite special-unitary group gives positive mass
to every nonempty open set.  This is the topological measure input required
by any local-coordinate Haar transfer.
-/

open MeasureTheory MeasureTheory.Measure TopologicalSpace

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The normalized finite special-unitary Haar law has Mathlib's full Haar
interface, including left invariance, compact finiteness, and open-set
positivity. -/
noncomputable instance finiteSpecialUnitaryHaarIsHaarMeasure
    (ι : Type*) [Fintype ι] [DecidableEq ι] :
    IsHaarMeasure (finiteSpecialUnitaryHaar ι) := by
  let K : PositiveCompacts (Matrix.specialUnitaryGroup ι ℂ) :=
    ⟨⟨Set.univ, isCompact_univ⟩, by simp⟩
  change IsHaarMeasure (haarMeasure K)
  exact isHaarMeasure_haarMeasure K

/-- Right translation preserves normalized finite-special-unitary Haar
measure.  This gives the bi-invariance needed to translate any eventual
local-coordinate null-set statement across the group. -/
theorem map_finiteSpecialUnitaryHaar_mul_right
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (V : Matrix.specialUnitaryGroup ι ℂ) :
    Measure.map (fun U : Matrix.specialUnitaryGroup ι ℂ => U * V)
        (finiteSpecialUnitaryHaar ι) = finiteSpecialUnitaryHaar ι := by
  have hprob :
      Measure.map (fun U : Matrix.specialUnitaryGroup ι ℂ => U * V)
          (finiteSpecialUnitaryHaar ι) Set.univ = 1 := by
    rw [Measure.map_apply_of_aemeasurable
      (measurable_mul_const V).aemeasurable MeasurableSet.univ]
    exact finiteSpecialUnitaryHaar_apply_univ ι
  have hscalar := isMulLeftInvariant_eq_smul_of_regular
    (Measure.map (fun U : Matrix.specialUnitaryGroup ι ℂ => U * V)
      (finiteSpecialUnitaryHaar ι))
    (finiteSpecialUnitaryHaar ι)
  have hfactor :
      haarScalarFactor
          (Measure.map (fun U : Matrix.specialUnitaryGroup ι ℂ => U * V)
            (finiteSpecialUnitaryHaar ι))
          (finiteSpecialUnitaryHaar ι) = 1 := by
    have huniv := congrArg
      (fun μ : Measure (Matrix.specialUnitaryGroup ι ℂ) => μ Set.univ)
      hscalar
    rw [hprob, Measure.smul_apply, finiteSpecialUnitaryHaar_apply_univ] at huniv
    simpa using huniv.symm
  rw [hfactor] at hscalar
  simpa using hscalar

/-- Normalized finite-special-unitary Haar measure is right invariant. -/
noncomputable instance finiteSpecialUnitaryHaarIsMulRightInvariant
    (ι : Type*) [Fintype ι] [DecidableEq ι] :
    IsMulRightInvariant (finiteSpecialUnitaryHaar ι) where
  map_mul_right_eq_self := map_finiteSpecialUnitaryHaar_mul_right

/-- Right multiplication preserves every normalized finite-special-unitary
Haar integral. -/
theorem integral_finiteSpecialUnitaryHaar_mul_right
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : Matrix.specialUnitaryGroup ι ℂ → ℝ)
    (V : Matrix.specialUnitaryGroup ι ℂ) :
    (∫ U, f (U * V) ∂finiteSpecialUnitaryHaar ι) =
      ∫ U, f U ∂finiteSpecialUnitaryHaar ι := by
  exact MeasurePreserving.integral_comp
    (show MeasurePreserving
      (fun U : Matrix.specialUnitaryGroup ι ℂ => U * V)
      (finiteSpecialUnitaryHaar ι) (finiteSpecialUnitaryHaar ι) from
      ⟨measurable_mul_const V,
        map_finiteSpecialUnitaryHaar_mul_right V⟩)
    (MeasurableEquiv.mulRight V).measurableEmbedding f

/-- Every nonempty open subset of a finite special-unitary group has positive
normalized Haar mass. -/
theorem finiteSpecialUnitaryHaar_pos_of_isOpen_nonempty
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {s : Set (Matrix.specialUnitaryGroup ι ℂ)}
    (hs : IsOpen s) (hne : s.Nonempty) :
    0 < finiteSpecialUnitaryHaar ι s :=
  hs.measure_pos (finiteSpecialUnitaryHaar ι) hne

/-- Every nonempty open subset of a finite special-unitary group has nonzero
normalized Haar mass. -/
theorem finiteSpecialUnitaryHaar_ne_zero_of_isOpen_nonempty
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {s : Set (Matrix.specialUnitaryGroup ι ℂ)}
    (hs : IsOpen s) (hne : s.Nonempty) :
    finiteSpecialUnitaryHaar ι s ≠ 0 :=
  (finiteSpecialUnitaryHaar_pos_of_isOpen_nonempty hs hne).ne'

end

end GaloisForLFunctions.HTGeometry
