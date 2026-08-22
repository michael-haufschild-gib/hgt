import GaloisForLFunctions.HTGeometry.HilbertSchmidtSpace

/-!
# The real Hilbert space of self-adjoint Hilbert–Schmidt operators

Viewing the complex Hilbert space `HSpace ℂ E` of Hilbert–Schmidt operators as a real inner
product space through `re ⟪·,·⟫`, the self-adjoint elements form a closed real subspace and hence
a real Hilbert space.  This is the space `S²(ℋ)` of Kim–Mer–Pálfia (arXiv:2607.29142).
-/

open scoped BigOperators InnerProductSpace
open Filter Topology ContinuousLinearMap

attribute [local instance] InnerProductSpace.complexToReal

namespace GaloisForLFunctions.HTGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

namespace HSpace

/-- The underlying-operator map is a bounded complex-linear map of norm at most one. -/
noncomputable def opCLM (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] : HSpace ℂ E →L[ℂ] (E →L[ℂ] E) :=
  LinearMap.mkContinuous
    { toFun := op, map_add' := op_add, map_smul' := op_smul } 1
    (fun S => by simpa using norm_le_hsNorm S.isHS)

@[simp] lemma opCLM_apply (S : HSpace ℂ E) : opCLM E S = S.op := rfl

lemma continuous_op : Continuous (op : HSpace ℂ E → E →L[ℂ] E) := (opCLM E).continuous

end HSpace

variable (E)

/-- The self-adjoint Hilbert–Schmidt operators as a real submodule. -/
def slSubmodule : Submodule ℝ (HSpace ℂ E) where
  carrier := {S | IsSelfAdjoint S.op}
  add_mem' h1 h2 := by
    show IsSelfAdjoint (_ : E →L[ℂ] E)
    rw [HSpace.op_add]
    exact IsSelfAdjoint.add h1 h2
  zero_mem' := by
    show IsSelfAdjoint (_ : E →L[ℂ] E)
    rw [HSpace.op_zero]
    exact IsSelfAdjoint.zero _
  smul_mem' c S h := by
    show IsSelfAdjoint (((c : ℝ) • S).op)
    have hval : ((c : ℝ) • S).op = (c : ℝ) • S.op := rfl
    rw [hval]
    exact IsSelfAdjoint.smul (star_trivial c) h

lemma isClosed_slSubmodule : IsClosed (slSubmodule E : Set (HSpace ℂ E)) := by
  have heq : (slSubmodule E : Set (HSpace ℂ E)) = {S : HSpace ℂ E | star S.op = S.op} := rfl
  rw [heq]
  exact isClosed_eq (continuous_star.comp HSpace.continuous_op) HSpace.continuous_op

/-- **The real Hilbert space of self-adjoint Hilbert–Schmidt operators.** -/
def SLSpace : Type _ := ↥(slSubmodule E)

namespace SLSpace

variable {E}

noncomputable instance : NormedAddCommGroup (SLSpace E) :=
  inferInstanceAs (NormedAddCommGroup ↥(slSubmodule E))

noncomputable instance : InnerProductSpace ℝ (SLSpace E) :=
  inferInstanceAs (InnerProductSpace ℝ ↥(slSubmodule E))

instance : CompleteSpace (SLSpace E) :=
  haveI hcl : IsClosed (slSubmodule E : Set (HSpace ℂ E)) := isClosed_slSubmodule E
  hcl.completeSpace_coe

/-- The underlying Hilbert–Schmidt operator. -/
noncomputable def toHS (S : SLSpace E) : HSpace ℂ E := (S : ↥(slSubmodule E)).1

/-- The underlying bounded operator. -/
noncomputable def op (S : SLSpace E) : E →L[ℂ] E := S.toHS.op

lemma isSelfAdjoint (S : SLSpace E) : IsSelfAdjoint S.op := (S : ↥(slSubmodule E)).2

lemma isHS (S : SLSpace E) : IsHilbertSchmidt S.op := S.toHS.isHS

@[ext] lemma ext {S T : SLSpace E} (h : S.op = T.op) : S = T :=
  Subtype.ext (HSpace.ext h)

@[simp] lemma op_add (S T : SLSpace E) : (S + T).op = S.op + T.op := rfl
@[simp] lemma op_zero : (0 : SLSpace E).op = 0 := rfl
@[simp] lemma op_neg (S : SLSpace E) : (-S).op = -S.op := rfl
@[simp] lemma op_sub (S T : SLSpace E) : (S - T).op = S.op - T.op := rfl
@[simp] lemma op_smul (c : ℝ) (S : SLSpace E) : (c • S).op = (c : ℂ) • S.op := rfl

@[simp] lemma norm_def (S : SLSpace E) : ‖S‖ = hsNorm S.op := rfl

@[simp] lemma inner_def (S T : SLSpace E) :
    (inner ℝ S T : ℝ) = RCLike.re (hsInner S.op T.op) := rfl

end SLSpace

end GaloisForLFunctions.HTGeometry
