import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Operator.Compact.Basic

/-!
# Source Grushin inverse spectralization

An invertible source-augmented map `G₀` and its spectral injection `J` canonically produce the
relative operator `B = J G₀⁻¹`.  Eliminating the source channel factors the affine pencil as

`G_z G₀⁻¹ = I + z B`.

Thus a nonzero kernel of the source pencil at `z ≠ 0` is exactly an eigenvector of `B` with
eigenvalue `-z⁻¹`.  Compactness transfers from the injection to the relative operator.  This is the
bounded algebraic core of the Hedenmalm theta-source compressed-inverse construction; no spectral
set or target eigenvalue is used in the operator definition.
-/

open ContinuousLinearMap

namespace HTGeometry

noncomputable section

variable {E H : Type*}
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup H] [NormedSpace ℂ H]

/-- Relative operator of an invertible source-augmented Grushin map. -/
def sourceGrushinRelativeOperator
    (G0 : E ≃L[ℂ] H) (J : E →L[ℂ] H) : H →L[ℂ] H :=
  J.comp G0.symm.toContinuousLinearMap

/-- Affine Grushin pencil before source elimination. -/
def sourceGrushinPencil
    (G0 : E ≃L[ℂ] H) (J : E →L[ℂ] H) (z : ℂ) : E →L[ℂ] H :=
  G0.toContinuousLinearMap + z • J

/-- Exact elimination of the source channel. -/
theorem sourceGrushinPencil_factor
    (G0 : E ≃L[ℂ] H) (J : E →L[ℂ] H) (z : ℂ) :
    ((ContinuousLinearMap.id ℂ H +
        z • sourceGrushinRelativeOperator G0 J).comp
          G0.toContinuousLinearMap) =
      sourceGrushinPencil G0 J z := by
  ext x
  simp [sourceGrushinRelativeOperator, sourceGrushinPencil]

/-- The source pencil has a nonzero kernel exactly when its bounded relative pencil does. -/
theorem exists_sourceGrushinPencil_kernel_iff
    (G0 : E ≃L[ℂ] H) (J : E →L[ℂ] H) (z : ℂ) :
    (∃ x : E, x ≠ 0 ∧ sourceGrushinPencil G0 J z x = 0) ↔
      ∃ f : H, f ≠ 0 ∧
        (ContinuousLinearMap.id ℂ H +
          z • sourceGrushinRelativeOperator G0 J) f = 0 := by
  constructor
  · rintro ⟨x, hx, hker⟩
    refine ⟨G0 x, by simpa using G0.injective.ne hx, ?_⟩
    have hfactor := congrArg
      (fun T : E →L[ℂ] H => T x)
      (sourceGrushinPencil_factor G0 J z)
    simpa [hker] using hfactor
  · rintro ⟨f, hf, hker⟩
    refine ⟨G0.symm f, by simpa using G0.symm.injective.ne hf, ?_⟩
    have hfactor := congrArg
      (fun T : E →L[ℂ] H => T (G0.symm f))
      (sourceGrushinPencil_factor G0 J z)
    have hfactor' :
        (ContinuousLinearMap.id ℂ H +
          z • sourceGrushinRelativeOperator G0 J) f =
        sourceGrushinPencil G0 J z (G0.symm f) := by
      simpa using hfactor
    exact hfactor'.symm.trans hker

/-- Away from the origin, kernel of `I + zB` is exactly the `-z⁻¹` eigenspace of `B`. -/
theorem sourceGrushin_shift_kernel_iff_eigen
    (G0 : E ≃L[ℂ] H) (J : E →L[ℂ] H) {z : ℂ} (hz : z ≠ 0) (f : H) :
    (ContinuousLinearMap.id ℂ H +
        z • sourceGrushinRelativeOperator G0 J) f = 0 ↔
      sourceGrushinRelativeOperator G0 J f = (-z⁻¹) • f := by
  constructor
  · intro h
    have h' : f + z • sourceGrushinRelativeOperator G0 J f = 0 := by
      simpa using h
    have hswap : z • sourceGrushinRelativeOperator G0 J f + f = 0 := by
      simpa [add_comm] using h'
    have hzb : z • sourceGrushinRelativeOperator G0 J f = -f :=
      eq_neg_of_add_eq_zero_left hswap
    calc
      sourceGrushinRelativeOperator G0 J f =
          z⁻¹ • (z • sourceGrushinRelativeOperator G0 J f) := by
            symm
            simp [smul_smul, hz]
      _ = z⁻¹ • (-f) := by rw [hzb]
      _ = (-z⁻¹) • f := by simp
  · intro h
    change f + z • sourceGrushinRelativeOperator G0 J f = 0
    rw [h]
    simp [smul_smul, hz]

/-- Source-pencil nullity is faithful point spectrum of the relative operator. -/
theorem exists_sourceGrushinPencil_kernel_iff_eigen
    (G0 : E ≃L[ℂ] H) (J : E →L[ℂ] H) {z : ℂ} (hz : z ≠ 0) :
    (∃ x : E, x ≠ 0 ∧ sourceGrushinPencil G0 J z x = 0) ↔
      ∃ f : H, f ≠ 0 ∧
        sourceGrushinRelativeOperator G0 J f = (-z⁻¹) • f := by
  rw [exists_sourceGrushinPencil_kernel_iff]
  constructor <;> rintro ⟨f, hf, h⟩
  · exact ⟨f, hf, (sourceGrushin_shift_kernel_iff_eigen G0 J hz f).mp h⟩
  · exact ⟨f, hf, (sourceGrushin_shift_kernel_iff_eigen G0 J hz f).mpr h⟩

/-- Compact source injection gives a compact source-derived relative operator. -/
theorem sourceGrushinRelativeOperator_isCompact
    (G0 : E ≃L[ℂ] H) (J : E →L[ℂ] H)
    (hJ : IsCompactOperator J) :
    IsCompactOperator (sourceGrushinRelativeOperator G0 J) := by
  exact hJ.comp_clm G0.symm.toContinuousLinearMap

end

end HTGeometry
