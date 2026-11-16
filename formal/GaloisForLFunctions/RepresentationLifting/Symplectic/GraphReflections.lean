import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheNullSpaceOfACompressionIsTheCrossingOfAGraphWithAConormal
import Mathlib.LinearAlgebra.Eigenspace.Basic

/-!
# Antisymplectic graph reflections

Symmetrizing any bounded operator gives an explicit antisymplectic
involution of phase space. Its positive eigenspace is the operator graph;
its negative eigenspace is vertical. Both are copies of the original
space. Products of two such reflections are shears, and their common
fixed space is the kernel of the difference of the symmetrized operators.
This realizes the equal-eigenspace mechanism in Zehavi, Proposition 4.16,
arXiv:2611.18218, without assuming an involution or a compatible pairing.
-/

noncomputable section
namespace GaloisForLFunctions.RepresentationLifting.Symplectic

open GaloisForLFunctions.AbsoluteGeometryOfSpecZ
open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The self-adjoint operator canonically supplied by any bounded operator. -/
def graphSymmetrization (T : H →L[ℂ] H) : H →L[ℂ] H := T + T.adjoint

/-- Reflection across the graph along the vertical subspace. -/
def graphReflection (T : H →L[ℂ] H) : (H × H) ≃ₗ[ℂ] (H × H) where
  toFun p := (p.1, (2 : ℂ) • graphSymmetrization T p.1 - p.2)
  invFun p := (p.1, (2 : ℂ) • graphSymmetrization T p.1 - p.2)
  left_inv p := by ext <;> simp
  right_inv p := by ext <;> simp
  map_add' p q := by ext <;> simp <;> module
  map_smul' c p := by ext <;> simp <;> module

@[simp] theorem graphReflection_apply (T : H →L[ℂ] H) (p : H × H) :
    graphReflection T p = (p.1, (2 : ℂ) • graphSymmetrization T p.1 - p.2) := rfl

/-- The constructed reflection is involutive for every input operator. -/
theorem graphReflection_involutive (T : H →L[ℂ] H) : Function.Involutive (graphReflection T) := by
  intro p
  ext <;> simp

/-- Symmetrization is symmetric for the Hilbert pairing. -/
theorem graphSymmetrization_inner (T : H →L[ℂ] H) (x y : H) :
    ⟪graphSymmetrization T x, y⟫_ℂ = ⟪x, graphSymmetrization T y⟫_ℂ := by
  simp only [graphSymmetrization, ContinuousLinearMap.add_apply, inner_add_left, inner_add_right]
  rw [ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_right]
  exact add_comm _ _

/-- The reflection reverses the actual phase-space form in the corpus. -/
theorem graphReflection_antisymplectic (T : H →L[ℂ] H) (p q : H × H) :
    sympForm (graphReflection T p) (graphReflection T q) = -sympForm p q := by
  simp only [sympForm, graphReflection_apply, inner_sub_left, inner_sub_right,
    inner_smul_left, inner_smul_right, graphSymmetrization_inner]
  simp only [map_ofNat]
  ring

/-- Positive eigenvectors are exactly the graph of the symmetrized operator. -/
theorem graphReflection_fixed_iff (T : H →L[ℂ] H) (p : H × H) :
    graphReflection T p = p ↔ p ∈ operatorGraph (graphSymmetrization T) := by
  rw [graphReflection_apply, Prod.mk_inj, mem_operatorGraph]
  simp only [true_and]
  constructor
  · intro h
    have he : (2 : ℂ) • (graphSymmetrization T p.1 - p.2) = 0 := by
      have h' : graphSymmetrization T p.1 + graphSymmetrization T p.1 = p.2 + p.2 := by
        simpa only [two_smul] using sub_eq_iff_eq_add.mp h
      rw [smul_sub, two_smul, two_smul, h', sub_self]
    exact (sub_eq_zero.mp ((smul_eq_zero.mp he).resolve_left (by norm_num))).symm
  · intro h
    rw [h]
    simp [two_smul]

/-- Negative eigenvectors form the vertical copy of the original space. -/
theorem graphReflection_neg_iff (T : H →L[ℂ] H) (p : H × H) :
    graphReflection T p = -p ↔ p.1 = 0 := by
  constructor
  · intro h
    have he : p.1 = -p.1 := congrArg Prod.fst h
    have hz : (2 : ℂ) • p.1 = 0 := by
      rw [two_smul]
      calc
        p.1 + p.1 = -p.1 + p.1 := congrArg (fun z => z + p.1) he
        _ = 0 := neg_add_cancel _
    exact (smul_eq_zero.mp hz).resolve_left (by norm_num)
  · intro h
    ext <;> simp [h]

/-- Two graph reflections compose to the shear given by the difference of their operators. -/
theorem graphReflection_comp (S T : H →L[ℂ] H) (p : H × H) :
    graphReflection S (graphReflection T p) =
      (p.1, p.2 + (2 : ℂ) • ((graphSymmetrization S - graphSymmetrization T) p.1)) := by
  ext <;> simp <;> module

/-- Common fixed vectors are precisely graph vectors over the kernel of the difference. -/
theorem graphReflection_common_fixed (S T : H →L[ℂ] H) (p : H × H) :
    (graphReflection S p = p ∧ graphReflection T p = p) ↔
      p.2 = graphSymmetrization T p.1 ∧
        p.1 ∈ LinearMap.ker ((graphSymmetrization S - graphSymmetrization T).toLinearMap) := by
  rw [graphReflection_fixed_iff, graphReflection_fixed_iff, mem_operatorGraph, mem_operatorGraph,
    LinearMap.mem_ker]
  simp only [ContinuousLinearMap.coe_coe, ContinuousLinearMap.sub_apply, sub_eq_zero]
  constructor
  · rintro ⟨hS, hT⟩
    exact ⟨hT, hS.symm.trans hT⟩
  · rintro ⟨hT, hST⟩
    exact ⟨hT.trans hST.symm, hT⟩

/-- The positive eigenspace, expressed as the kernel of reflection minus identity. -/
def graphReflectionPositive (T : H →L[ℂ] H) : Submodule ℂ (H × H) :=
  LinearMap.ker ((graphReflection T).toLinearMap - LinearMap.id)

/-- The negative eigenspace, expressed as the kernel of reflection plus identity. -/
def graphReflectionNegative (T : H →L[ℂ] H) : Submodule ℂ (H × H) :=
  LinearMap.ker ((graphReflection T).toLinearMap + LinearMap.id)

@[simp] theorem mem_graphReflectionPositive (T : H →L[ℂ] H) (p : H × H) :
    p ∈ graphReflectionPositive T ↔ p.2 = graphSymmetrization T p.1 := by
  change graphReflection T p - p = 0 ↔ _
  rw [sub_eq_zero, graphReflection_fixed_iff, mem_operatorGraph]

@[simp] theorem mem_graphReflectionNegative (T : H →L[ℂ] H) (p : H × H) :
    p ∈ graphReflectionNegative T ↔ p.1 = 0 := by
  change graphReflection T p + p = 0 ↔ _
  rw [add_eq_zero_iff_eq_neg, graphReflection_neg_iff]

/-- Graph coordinates identify the positive eigenspace with the original space. -/
def graphReflectionPositiveEquiv (T : H →L[ℂ] H) : H ≃ₗ[ℂ] graphReflectionPositive T where
  toFun x := ⟨(x, graphSymmetrization T x), by simp⟩
  invFun p := p.val.1
  left_inv _ := rfl
  right_inv p := by
    apply Subtype.ext
    exact Prod.ext rfl ((mem_graphReflectionPositive T p.val).mp p.property).symm
  map_add' _ _ := by apply Subtype.ext; ext <;> simp
  map_smul' _ _ := by apply Subtype.ext; ext <;> simp

/-- Vertical coordinates identify the negative eigenspace with the same original space. -/
def graphReflectionNegativeEquiv (T : H →L[ℂ] H) : H ≃ₗ[ℂ] graphReflectionNegative T where
  toFun y := ⟨(0, y), by simp⟩
  invFun p := p.val.2
  left_inv _ := rfl
  right_inv p := by
    apply Subtype.ext
    exact Prod.ext ((mem_graphReflectionNegative T p.val).mp p.property).symm rfl
  map_add' _ _ := by apply Subtype.ext; ext <;> simp
  map_smul' _ _ := by apply Subtype.ext; ext <;> simp

/-- The two eigenvalue sectors have exactly equal dimensions. -/
theorem graphReflection_eigenspace_finrank (T : H →L[ℂ] H) :
    Module.finrank ℂ (graphReflectionPositive T) = Module.finrank ℂ H ∧
      Module.finrank ℂ (graphReflectionNegative T) = Module.finrank ℂ H :=
  ⟨(graphReflectionPositiveEquiv T).finrank_eq.symm,
    (graphReflectionNegativeEquiv T).finrank_eq.symm⟩

/-- The common positive sector retains precisely the kernel of the operator difference. -/
def graphReflectionCommonEquiv (S T : H →L[ℂ] H) :
    LinearMap.ker ((graphSymmetrization S - graphSymmetrization T).toLinearMap) ≃ₗ[ℂ]
      (graphReflectionPositive S ⊓ graphReflectionPositive T : Submodule ℂ (H × H)) where
  toFun x := ⟨(x.val, graphSymmetrization T x.val), by
    have hx : graphSymmetrization S x.val = graphSymmetrization T x.val :=
      sub_eq_zero.mp x.property
    simp only [Submodule.mem_inf, mem_graphReflectionPositive]
    exact ⟨hx.symm, trivial⟩⟩
  invFun p := ⟨p.val.1, by
    obtain ⟨hS, hT⟩ := p.property
    have heS := (mem_graphReflectionPositive S p.val).mp hS
    have heT := (mem_graphReflectionPositive T p.val).mp hT
    change graphSymmetrization S p.val.1 - graphSymmetrization T p.val.1 = 0
    rw [← heS, ← heT, sub_self]⟩
  left_inv _ := rfl
  right_inv p := by
    apply Subtype.ext
    exact Prod.ext rfl ((mem_graphReflectionPositive T p.val).mp p.property.2).symm
  map_add' _ _ := by apply Subtype.ext; ext <;> simp
  map_smul' _ _ := by apply Subtype.ext; ext <;> simp

/-- The dimension of the common fixed space is the nullity of the operator difference. -/
theorem graphReflection_common_finrank (S T : H →L[ℂ] H) :
    Module.finrank ℂ (graphReflectionPositive S ⊓ graphReflectionPositive T :
      Submodule ℂ (H × H)) =
        Module.finrank ℂ (LinearMap.ker ((graphSymmetrization S - graphSymmetrization T).toLinearMap)) :=
  (graphReflectionCommonEquiv S T).finrank_eq.symm

end GaloisForLFunctions.RepresentationLifting.Symplectic

#print axioms GaloisForLFunctions.RepresentationLifting.Symplectic.graphReflection_antisymplectic
#print axioms GaloisForLFunctions.RepresentationLifting.Symplectic.graphReflection_fixed_iff
#print axioms GaloisForLFunctions.RepresentationLifting.Symplectic.graphReflection_common_fixed

#print axioms GaloisForLFunctions.RepresentationLifting.Symplectic.graphReflection_eigenspace_finrank
#print axioms GaloisForLFunctions.RepresentationLifting.Symplectic.graphReflection_common_finrank
