import GaloisForLFunctions.RHTower.SelbergMaassGLCorrespondence

/-!
# Finite-index trace of Maass-invariant functions

For `G` of finite relative index in `H`, this file constructs the literal finite
trace of a `G`-invariant upper-half-plane function over
`H / (G ∩ H)` and proves `H`-invariance. It is the group-theoretic Hecke trace;
analytic preservation is established separately for the principal-congruence
target, whose representatives are integral matrices.
-/

namespace GaloisForLFunctions.RHTower

open Complex Set Filter Topology UpperHalfPlane ModularGroup
open scoped MatrixGroups ContDiff

noncomputable section

variable {G H : Subgroup (GL (Fin 2) ℝ)}

/-- The finite quotient indexing trace summands from `G` to `H`. -/
local notation "𝒬" => H ⧸ (G.subgroupOf H)

local instance : MulAction H H := Monoid.toMulAction ..
local instance : MulAction H 𝒬 := .quotient ..

/-- The summand indexed by a relative coset. -/
def maassTraceQuotientFunc
    (f : glUpperHalfPlaneInvariantFunctions G) (q : 𝒬) (z : ℍ) : ℂ :=
  q.liftOn (fun h => f.1 (h.val⁻¹ • z)) (fun h h' hhh' => by
    obtain ⟨j, hj, hj'⟩ : ∃ j ∈ G, h' = h * j := by
      rw [← Quotient.eq_iff_equiv, Quotient.eq, QuotientGroup.leftRel_apply] at hhh'
      exact ⟨h⁻¹ * h', hhh', mod_cast (mul_inv_cancel_left h h').symm⟩
    rw [hj', mul_inv_rev, mul_smul]
    exact (f.2 ⟨j⁻¹, inv_mem hj⟩ _).symm)

/-- A trace summand at a literal target-group representative. -/
@[simp] theorem maassTraceQuotientFunc_mk
    (f : glUpperHalfPlaneInvariantFunctions G) (h : H) (z : ℍ) :
    maassTraceQuotientFunc f (QuotientGroup.mk h) z = f.1 (h.val⁻¹ • z) :=
  rfl

/-- Target translation only permutes the finite trace summands. -/
theorem maassTraceQuotientFunc_smul
    (f : glUpperHalfPlaneInvariantFunctions G) (h : H) (q : 𝒬) (z : ℍ) :
    maassTraceQuotientFunc f q (h.val • z) =
      maassTraceQuotientFunc f (h⁻¹ • q) z := by
  induction q using Quotient.inductionOn with
  | h r => simp [maassTraceQuotientFunc, mul_inv_rev, mul_smul]

variable [G.IsFiniteRelIndex H]

/-- The literal finite trace over relative cosets. -/
def maassTraceFunction (f : glUpperHalfPlaneInvariantFunctions G) (z : ℍ) : ℂ :=
  letI := Fintype.ofFinite 𝒬
  ∑ q : 𝒬, maassTraceQuotientFunc f q z

/-- The finite Maass trace is invariant under its target group. -/
def maassTraceInvariant (f : glUpperHalfPlaneInvariantFunctions G) :
    glUpperHalfPlaneInvariantFunctions H :=
  ⟨maassTraceFunction f, by
    intro h z
    letI := Fintype.ofFinite 𝒬
    unfold maassTraceFunction
    calc
      ∑ q : 𝒬, maassTraceQuotientFunc f q (h.val • z) =
          ∑ q : 𝒬, maassTraceQuotientFunc f (h⁻¹ • q) z := by
        apply Finset.sum_congr rfl
        intro q _
        exact maassTraceQuotientFunc_smul f h q z
      _ = ∑ q : 𝒬, maassTraceQuotientFunc f q z :=
        Equiv.sum_comp (MulAction.toPerm h⁻¹)
          (fun q : 𝒬 => maassTraceQuotientFunc f q z)⟩

end

end GaloisForLFunctions.RHTower
