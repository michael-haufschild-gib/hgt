import GaloisForLFunctions.HTGeometry.ChronologicalTensor.CubicHilbertExtension

/-!
# The half-retraction and physical recovery costs force the graded inner product

Consider real bilinear forms on the actual algebraic defect, fixing only the
physical squared norms of its monomial classes and symmetry of the single
half-flow. Distinct half-flow eigenvalues force every cross term to vanish.
These conditions therefore select exactly the already constructed graded inner
product; positivity and definiteness need not be assumed in the conditions.
-/

namespace GaloisForLFunctions.HTGeometry.ChronologicalTensor
noncomputable section
open Set Polynomial


def cubicCuspGradedInnerForm : LinearMap.BilinForm ℝ
    (Polynomial (Polynomial ℝ) ⧸ cubicCuspAlgebra.toSubmodule) := by
  letI := cubicCuspGradedNormedGroup
  letI := cubicCuspGradedInnerProductSpace
  exact {
    toFun := fun x => {
      toFun := fun y => inner ℝ x y
      map_add' := fun y z => inner_add_right x y z
      map_smul' := fun r y => inner_smul_right x y r }
    map_add' := fun x y => by
      apply LinearMap.ext
      intro z
      exact inner_add_left x y z
    map_smul' := fun r x => by
      apply LinearMap.ext
      intro y
      change inner ℝ (r • x) y=r*inner ℝ x y
      rw [inner_smul_left]
      rfl }

def cubicCompatibleInnerForms : Set (LinearMap.BilinForm ℝ
    (Polynomial (Polynomial ℝ) ⧸ cubicCuspAlgebra.toSubmodule)) :=
  {B | (∀ k, B (cubicCuspDefectBasis k) (cubicCuspDefectBasis k)=(cubicGradedRecoveryGap k)^(2 : ℕ)) ∧
    ∀ x y, B (cubicCuspDefectFlow (1/2) x) y=B x (cubicCuspDefectFlow (1/2) y)}

theorem cubicCuspGradedInnerForm_mem : cubicCuspGradedInnerForm ∈ cubicCompatibleInnerForms := by
  letI := cubicCuspGradedNormedGroup
  letI := cubicCuspGradedInnerProductSpace
  constructor
  · intro k
    change inner ℝ (cubicCuspDefectBasis k) (cubicCuspDefectBasis k)=_
    rw [real_inner_self_eq_norm_sq,cubicCuspGradedBasis_norm]
  · intro x y
    exact cubicCuspDefectFlow_graded_inner ⟨1/2,by constructor <;> linarith⟩ x y

theorem cubicCompatibleInnerForms_basis
    (B : LinearMap.BilinForm ℝ (Polynomial (Polynomial ℝ) ⧸ cubicCuspAlgebra.toSubmodule)) :
    B ∈ cubicCompatibleInnerForms → ∀ i j,
      B (cubicCuspDefectBasis i) (cubicCuspDefectBasis j)=
        if i=j then (cubicGradedRecoveryGap i)^(2 : ℕ) else 0 := by
  rintro ⟨hd,hs⟩ i j
  by_cases hij : i=j
  · subst j
    rw [if_pos rfl]
    exact hd i
  · rw [if_neg hij]
    have h := hs (cubicCuspDefectBasis i) (cubicCuspDefectBasis j)
    simp only [cubicCuspDefectFlow_spectrum,map_smul,LinearMap.smul_apply,smul_eq_mul] at h
    have hn : (1/2:ℝ)^(i+1) ≠ (1/2:ℝ)^(j+1) := by
      intro he
      have he' := pow_right_injective₀ (by positivity : (0:ℝ)<1/2)
        (by linarith : (1/2:ℝ)≠1) he
      apply hij
      omega
    have hz : ((1/2:ℝ)^(i+1)-(1/2:ℝ)^(j+1))*
        B (cubicCuspDefectBasis i) (cubicCuspDefectBasis j)=0 := by
      linear_combination h
    exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hn)

theorem cubicCompatibleInnerForms_unique : cubicCompatibleInnerForms={cubicCuspGradedInnerForm} := by
  ext B
  constructor
  · intro h
    apply Set.mem_singleton_iff.mpr
    apply cubicCuspDefectBasis.ext
    intro i
    apply cubicCuspDefectBasis.ext
    intro j
    rw [cubicCompatibleInnerForms_basis B h i j,
      cubicCompatibleInnerForms_basis cubicCuspGradedInnerForm cubicCuspGradedInnerForm_mem i j]
  · intro h
    obtain rfl := Set.mem_singleton_iff.mp h
    exact cubicCuspGradedInnerForm_mem

theorem cubicCuspGradedInnerForm_definite
    (x : Polynomial (Polynomial ℝ) ⧸ cubicCuspAlgebra.toSubmodule) :
    0 ≤ cubicCuspGradedInnerForm x x ∧ (cubicCuspGradedInnerForm x x=0 ↔ x=0) := by
  letI := cubicCuspGradedNormedGroup
  letI := cubicCuspGradedInnerProductSpace
  change 0 ≤ inner ℝ x x ∧ (inner ℝ x x=0 ↔ x=0)
  rw [real_inner_self_eq_norm_sq]
  constructor
  · positivity
  · rw [sq_eq_zero_iff,norm_eq_zero]

end
end GaloisForLFunctions.HTGeometry.ChronologicalTensor
