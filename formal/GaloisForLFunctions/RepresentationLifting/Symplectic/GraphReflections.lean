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
  norm_num
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

end GaloisForLFunctions.RepresentationLifting.Symplectic

#print axioms GaloisForLFunctions.RepresentationLifting.Symplectic.graphReflection_antisymplectic
#print axioms GaloisForLFunctions.RepresentationLifting.Symplectic.graphReflection_fixed_iff
#print axioms GaloisForLFunctions.RepresentationLifting.Symplectic.graphReflection_common_fixed
