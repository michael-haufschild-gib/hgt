import GaloisForLFunctions.RHTower.SchanuelStageTwoDegree
import GaloisForLFunctions.HTGeometry.TranscendenceDegreeOneVariable

/-!
# The concrete stage-two value field

The abstract degree statements are instantiated at the field the cards actually use: the algebraic
numbers inside `ℂ`, extended by a pair of complex numbers and their exponentials.

Hermite--Lindemann puts a transcendental element in that field whenever the first exponent is
nonzero, so a stage-two configuration of transcendence degree below two has degree exactly one.
-/

open IntermediateField

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- The algebraic numbers inside `ℂ`. -/
abbrev AlgNum : IntermediateField ℚ ℂ := algebraicClosure ℚ ℂ

instance : Algebra.IsAlgebraic ℚ AlgNum := algebraicClosure.isAlgebraic ℚ ℂ

/-- The value field of a stage-two exponential configuration. -/
def stageTwoValueField (x₁ x₂ : ℂ) : IntermediateField AlgNum ℂ :=
  IntermediateField.adjoin AlgNum {x₁, x₂, Complex.exp x₁, Complex.exp x₂}

theorem x₁_mem_stageTwoValueField (x₁ x₂ : ℂ) : x₁ ∈ stageTwoValueField x₁ x₂ :=
  IntermediateField.subset_adjoin _ _ (by simp)

theorem exp_x₁_mem_stageTwoValueField (x₁ x₂ : ℂ) :
    Complex.exp x₁ ∈ stageTwoValueField x₁ x₂ :=
  IntermediateField.subset_adjoin _ _ (by simp)

/-- Transcendence of a complex number transfers to its copy in any subfield containing it. -/
theorem transcendental_mk {K : IntermediateField AlgNum ℂ} {z : ℂ} (hz : z ∈ K)
    (h : Transcendental ℚ z) : Transcendental ℚ (⟨z, hz⟩ : K) := by
  have hinj : Function.Injective (algebraMap K ℂ) := (algebraMap K ℂ).injective
  have hmap : (algebraMap K ℂ) (⟨z, hz⟩ : K) = z := rfl
  rw [← hmap] at h
  exact (transcendental_algebraMap_iff (R := ℚ) (S := K) (A := ℂ) hinj).mp h

/-- **Clause 1, at the concrete value field.**  A stage-two configuration with nonzero first
exponent and transcendence degree below two has transcendence degree exactly one. -/
theorem trdeg_stageTwoValueField_eq_one {x₁ x₂ : ℂ} (hx : x₁ ≠ 0)
    (hlt : Algebra.trdeg AlgNum (stageTwoValueField x₁ x₂) < 2) :
    Algebra.trdeg AlgNum (stageTwoValueField x₁ x₂) = 1 := by
  rcases transcendental_or_transcendental_exp hx with h | h
  · exact trdeg_eq_one_of_transcendental_of_lt_two
      (transcendental_mk (x₁_mem_stageTwoValueField x₁ x₂) h) hlt
  · exact trdeg_eq_one_of_transcendental_of_lt_two
      (transcendental_mk (exp_x₁_mem_stageTwoValueField x₁ x₂) h) hlt

/-- The same conclusion from rational linear independence of the exponent pair. -/
theorem trdeg_stageTwoValueField_eq_one_of_linearIndependent {x : Fin 2 → ℂ}
    (hx : LinearIndependent ℚ x)
    (hlt : Algebra.trdeg AlgNum (stageTwoValueField (x 0) (x 1)) < 2) :
    Algebra.trdeg AlgNum (stageTwoValueField (x 0) (x 1)) = 1 :=
  trdeg_stageTwoValueField_eq_one (ne_zero_of_linearIndependent hx 0) hlt

/-! ## Adjoining the period -/

section Period

open scoped IntermediateField.algebraAdjoinAdjoin

variable {K : IntermediateField AlgNum ℂ} {τ : ℂ}

/-- **Case I of the dichotomy, concretely.**  If the period is transcendental over the value field,
the completed field has transcendence degree two. -/
theorem trdeg_periodField_eq_two (hK : Algebra.trdeg AlgNum K = 1)
    (hτ : Transcendental K τ) :
    Algebra.trdeg AlgNum ↥(IntermediateField.adjoin K ({τ} : Set ℂ)) = 2 := by
  haveI hfaith₁ : FaithfulSMul (↥AlgNum) (↥K) :=
    (faithfulSMul_iff_algebraMap_injective (↥AlgNum) (↥K)).mpr
      (algebraMap (↥AlgNum) (↥K)).injective
  haveI hfaith₂ : FaithfulSMul (↥K) ↥(IntermediateField.adjoin K ({τ} : Set ℂ)) :=
    (faithfulSMul_iff_algebraMap_injective (↥K)
      ↥(IntermediateField.adjoin K ({τ} : Set ℂ))).mpr
      (algebraMap (↥K) ↥(IntermediateField.adjoin K ({τ} : Set ℂ))).injective
  rw [← _root_.trdeg_add_eq AlgNum K (A := ↥(IntermediateField.adjoin K ({τ} : Set ℂ))),
    GaloisForLFunctions.HTGeometry.trdeg_adjoin_simple_eq_one hτ, hK]
  norm_num

/-- **Case II of the dichotomy, concretely.**  If the period is algebraic over the value field, the
completed field keeps transcendence degree one. -/
theorem trdeg_periodField_eq_one (hK : Algebra.trdeg AlgNum K = 1)
    (hτ : IsAlgebraic K τ) :
    Algebra.trdeg AlgNum ↥(IntermediateField.adjoin K ({τ} : Set ℂ)) = 1 := by
  haveI : FiniteDimensional K ↥(IntermediateField.adjoin K ({τ} : Set ℂ)) :=
    IntermediateField.adjoin.finiteDimensional hτ.isIntegral
  haveI : Algebra.IsAlgebraic K ↥(IntermediateField.adjoin K ({τ} : Set ℂ)) :=
    Algebra.IsAlgebraic.of_finite K _
  rw [GaloisForLFunctions.HTGeometry.trdeg_eq_of_isAlgebraic
    (A := AlgNum) (K := K) (L := ↥(IntermediateField.adjoin K ({τ} : Set ℂ))), hK]

end Period

end

end GaloisForLFunctions.RHTower
