import GaloisForLFunctions.RHTower.SelbergMaassGLCorrespondence

/-!
# Finite-index trace of Maass-invariant functions

For `𝒢` of finite relative index in `ℋ`, this file constructs the literal finite
trace of a `𝒢`-invariant upper-half-plane function over
`ℋ / (𝒢 ∩ ℋ)` and proves `ℋ`-invariance. It is the group-theoretic Hecke trace;
analytic preservation is established separately for the principal-congruence
target, whose representatives are integral matrices.
-/

namespace GaloisForLFunctions.RHTower

open Complex Set Filter Topology UpperHalfPlane ModularGroup
open scoped MatrixGroups ContDiff

noncomputable section

variable {𝒢 ℋ : Subgroup (GL (Fin 2) ℝ)}

/-- The finite quotient indexing trace summands from `𝒢` to `ℋ`. -/
local notation "𝒬" => ℋ ⧸ (𝒢.subgroupOf ℋ)

local instance : MulAction ℋ ℋ := Monoid.toMulAction ..
local instance : MulAction ℋ 𝒬 := .quotient ..

/-- The summand indexed by a relative coset. -/
def maassTraceQuotientFunc
    (f : upperHalfPlaneInvariantFunctions 𝒢) (q : 𝒬) (z : ℍ) : ℂ :=
  q.liftOn (fun h => f.1 (h.val⁻¹ • z)) (fun h h' hhh' => by
    obtain ⟨j, hj, hj'⟩ : ∃ j ∈ 𝒢, h' = h * j := by
      rw [← Quotient.eq_iff_equiv, Quotient.eq, QuotientGroup.leftRel_apply] at hhh'
      exact ⟨h⁻¹ * h', hhh', mod_cast (mul_inv_cancel_left h h').symm⟩
    rw [hj', mul_inv_rev, mul_smul]
    exact f.2 ⟨j⁻¹, inv_mem hj⟩ _)

/-- A trace summand at a literal target-group representative. -/
@[simp] theorem maassTraceQuotientFunc_mk
    (f : upperHalfPlaneInvariantFunctions 𝒢) (h : ℋ) (z : ℍ) :
    maassTraceQuotientFunc f (QuotientGroup.mk h) z = f.1 (h.val⁻¹ • z) :=
  rfl

/-- Target translation only permutes the finite trace summands. -/
theorem maassTraceQuotientFunc_smul
    (f : upperHalfPlaneInvariantFunctions 𝒢) (h : ℋ) (q : 𝒬) (z : ℍ) :
    maassTraceQuotientFunc f q (h.val • z) =
      maassTraceQuotientFunc f (h⁻¹ • q) z := by
  induction q using Quotient.inductionOn with
  | h r => simp [maassTraceQuotientFunc, mul_inv_rev, mul_smul]

variable [𝒢.IsFiniteRelIndex ℋ]

/-- The literal finite trace over relative cosets. -/
def maassTraceFunction (f : upperHalfPlaneInvariantFunctions 𝒢) (z : ℍ) : ℂ :=
  letI := Fintype.ofFinite 𝒬
  ∑ q : 𝒬, maassTraceQuotientFunc f q z

/-- The finite Maass trace is invariant under its target group. -/
def maassTraceInvariant (f : upperHalfPlaneInvariantFunctions 𝒢) :
    upperHalfPlaneInvariantFunctions ℋ :=
  ⟨maassTraceFunction f, by
    intro h z
    letI := Fintype.ofFinite 𝒬
    unfold maassTraceFunction
    simp_rw [maassTraceQuotientFunc_smul f h]
    exact Equiv.sum_comp (MulAction.toPerm h⁻¹)
      (fun q : 𝒬 => maassTraceQuotientFunc f q z)⟩

end

end GaloisForLFunctions.RHTower
