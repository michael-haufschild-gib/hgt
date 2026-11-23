import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ProjectiveProjectionFunctionField
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ProjectiveGenericRatios
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ProjectiveFiniteCover

/-! The pulled-back projective coordinates give a transcendence basis,
and their pairwise ratios record the generic germs on every chart. -/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open UpperTheory.Cb GlobalTheory.PD

namespace GlobalTheory.SchemeCohomology

variable {K : Type} [Field K] {X : Scheme.{0}} [IsIntegral X]
  {s : X ⟶ Spec (CommRingCat.of K)} {d : ℕ} {f : X ⟶ PSpace K d}

private abbrev Chart (i : Fin (d + 1)) := f ⁻¹ᵁ PSpace.coordinateOpen K d i

theorem projectionCoordinate_eq_genericProjectiveRatio (hf : f ≫ PSpace.str K d = s)
    (h₀ : genericPoint X ∈ Chart (f := f) 0) (j : {j : Fin (d + 1) // j ≠ 0}) :
    projectionCoordinate hf h₀ j = genericProjectiveRatio f 0 h₀ j.1 := by
  letI : Nonempty (Chart (f := f) 0) := ⟨⟨genericPoint X, h₀⟩⟩
  change (X.presheaf.germ (Chart (f := f) 0) (genericPoint X) h₀).hom
    (chartPolynomialPullback hf 0 (MvPolynomial.X j)) = _
  rw [chartPolynomialPullback_X]
  rfl

/-- The homogeneous generic coordinates, normalized so that the first is one. -/
def projectionCoordinates (hf : f ≫ PSpace.str K d = s)
    (h₀ : genericPoint X ∈ Chart (f := f) 0) : Fin (d + 1) → projectionField hf h₀ := by
  letI := sectionFunctionFieldAlgebra s
  exact Fin.cases 1 fun j =>
    ⟨projectionCoordinate hf h₀ ⟨j.succ, Fin.succ_ne_zero j⟩,
      IntermediateField.subset_adjoin K _ (Set.mem_range_self _)⟩

theorem projectionCoordinates_val (hf : f ≫ PSpace.str K d = s)
    (h₀ : genericPoint X ∈ Chart (f := f) 0) (j : Fin (d + 1)) :
    (projectionCoordinates hf h₀ j : X.functionField) = genericProjectiveRatio f 0 h₀ j := by
  induction j using Fin.cases with
  | zero =>
    change (1 : X.functionField) = genericProjectiveRatio f 0 h₀ 0
    have h := genericProjectiveRatio_mul f 0 0 0 h₀ h₀
    exact (mul_left_cancel₀ (genericProjectiveRatio_ne_zero f 0 0 h₀ h₀)
      (h.trans (mul_one _).symm)).symm
  | succ j =>
    change projectionCoordinate hf h₀ ⟨j.succ, Fin.succ_ne_zero j⟩ = _
    exact projectionCoordinate_eq_genericProjectiveRatio hf h₀ _

theorem projectionCoordinates_ratio (hf : f ≫ PSpace.str K d = s)
    (h₀ : genericPoint X ∈ Chart (f := f) 0) (i j : Fin (d + 1))
    (hi : genericPoint X ∈ Chart (f := f) i) :
    ((projectionCoordinates hf h₀ j / projectionCoordinates hf h₀ i : projectionField hf h₀) :
      X.functionField) = genericProjectiveRatio f i hi j := by
  letI := sectionFunctionFieldAlgebra s
  change (projectionField hf h₀).val (_ / _) = _
  rw [map_div₀]
  change (projectionCoordinates hf h₀ j : X.functionField) /
    (projectionCoordinates hf h₀ i : X.functionField) = _
  rw [projectionCoordinates_val, projectionCoordinates_val]
  exact (genericProjectiveRatio_eq_div f i j h₀ hi).symm

/-- The normalized nonconstant coordinates form a transcendence basis of
the subfield they generate. -/
theorem isPd_projectionCoordinates [IsAlgClosed K] [IsFinite f] [SmoothOfRelativeDimension d s]
    (hf : f ≫ PSpace.str K d = s) (hgen : ∀ i, genericPoint X ∈ Chart (f := f) i) :
    letI := sectionFunctionFieldAlgebra s
    IsPd K (projectionCoordinates hf (hgen 0)) := by
  letI := sectionFunctionFieldAlgebra s
  let h₀ := hgen 0
  let F := projectionField hf h₀
  let x := projectionCoordinates hf h₀
  have h1 : x 0 = 1 := rfl
  change IsPd K x
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    apply genericProjectiveRatio_ne_zero f 0 i h₀ (hgen i)
    rw [← projectionCoordinates_val hf h₀ i]
    exact congrArg (fun a : F => (a : X.functionField)) hi
  · simp only [h1, div_one]
    apply AlgebraicIndependent.of_comp F.val
    let e (j : Fin d) : {j : Fin (d + 1) // j ≠ 0} := ⟨j.succ, Fin.succ_ne_zero j⟩
    have hinj : Function.Injective e :=
      fun _ _ eq => Fin.succ_injective _ (congrArg Subtype.val eq)
    exact (algebraicIndependent_projectionCoordinate hf h₀).comp e hinj
  · simp only [h1, div_one]
    let A := IntermediateField.adjoin K (Set.range fun j : Fin d => x j.succ)
    change A = ⊤
    have hle : F ≤ A.map F.val := by
      apply IntermediateField.adjoin_le_iff.mpr
      rintro _ ⟨j, rfl⟩
      let k := j.1.pred j.2
      refine (IntermediateField.mem_map _).mpr
        ⟨x k.succ, IntermediateField.subset_adjoin K _ (Set.mem_range_self k), ?_⟩
      change projectionCoordinate hf h₀ ⟨k.succ, Fin.succ_ne_zero k⟩ = projectionCoordinate hf h₀ j
      congr 1
      exact Subtype.ext (Fin.succ_pred j.1 j.2)
    rw [eq_top_iff]
    intro z _
    obtain ⟨w, hw, hwz⟩ := (IntermediateField.mem_map _).mp (hle z.2)
    exact (Subtype.ext hwz : w = z) ▸ hw

end GlobalTheory.SchemeCohomology
