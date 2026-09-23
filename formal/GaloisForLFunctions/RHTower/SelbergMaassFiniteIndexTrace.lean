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

local instance selbergMaassFiniteIndexTraceInst1 : MulAction H H := Monoid.toMulAction ..
local instance selbergMaassFiniteIndexTraceInst2 : MulAction H 𝒬 := .quotient ..

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

/-- A quotient trace summand is linear in its invariant function. -/
theorem maassTraceQuotientFunc_add
    (f g : glUpperHalfPlaneInvariantFunctions G) (q : 𝒬) (z : ℍ) :
    maassTraceQuotientFunc (f + g) q z =
      maassTraceQuotientFunc f q z + maassTraceQuotientFunc g q z := by
  induction q using Quotient.inductionOn with
  | h h =>
    change f.1 (h.val⁻¹ • z) + g.1 (h.val⁻¹ • z) =
      f.1 (h.val⁻¹ • z) + g.1 (h.val⁻¹ • z)
    rfl

/-- A quotient trace summand commutes with complex scalar multiplication. -/
theorem maassTraceQuotientFunc_csmul
    (c : ℂ) (f : glUpperHalfPlaneInvariantFunctions G) (q : 𝒬) (z : ℍ) :
    maassTraceQuotientFunc (c • f) q z = c • maassTraceQuotientFunc f q z := by
  induction q using Quotient.inductionOn with
  | h h =>
    change c • f.1 (h.val⁻¹ • z) = c • f.1 (h.val⁻¹ • z)
    rfl

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


/-- The literal finite trace is additive. -/
theorem maassTraceFunction_add
    (f g : glUpperHalfPlaneInvariantFunctions G) :
    maassTraceFunction (H := H) (f + g) =
      maassTraceFunction (H := H) f + maassTraceFunction (H := H) g := by
  funext z
  letI := Fintype.ofFinite 𝒬
  unfold maassTraceFunction
  simp_rw [maassTraceQuotientFunc_add]
  exact Finset.sum_add_distrib

/-- The literal finite trace commutes with complex scalar multiplication. -/
theorem maassTraceFunction_smul
    (c : ℂ) (f : glUpperHalfPlaneInvariantFunctions G) :
    maassTraceFunction (H := H) (c • f) =
      c • maassTraceFunction (H := H) f := by
  funext z
  letI := Fintype.ofFinite 𝒬
  unfold maassTraceFunction
  simp_rw [maassTraceQuotientFunc_csmul]
  exact Finset.smul_sum.symm

/-- The finite relative-coset trace as a complex-linear map of invariant functions. -/
def maassTraceLinear :
    glUpperHalfPlaneInvariantFunctions G →ₗ[ℂ] glUpperHalfPlaneInvariantFunctions H where
  toFun := maassTraceInvariant
  map_add' f g := by
    apply Subtype.ext
    exact maassTraceFunction_add f g
  map_smul' c f := by
    apply Subtype.ext
    exact maassTraceFunction_smul c f

/-- Tracing from a group to itself is the identity: its relative-coset quotient has one class. -/
theorem maassTraceFunction_self [G.IsFiniteRelIndex G]
    (f : glUpperHalfPlaneInvariantFunctions G) :
    maassTraceFunction (G := G) (H := G) f = f := by
  funext z
  letI : Unique (G ⧸ (G.subgroupOf G)) :=
    { default := QuotientGroup.mk (1 : G)
      uniq := by
        intro q
        induction q using Quotient.inductionOn with
        | h h =>
          apply Quotient.sound'
          rw [QuotientGroup.leftRel_apply, Subgroup.subgroupOf_self]
          exact Subgroup.mem_top _ }
  letI : Fintype (G ⧸ (G.subgroupOf G)) := Fintype.ofFinite _
  unfold maassTraceFunction
  rw [Finset.univ_unique, Finset.sum_singleton]
  change f.1 ((1 : G).val⁻¹ • z) = f.1 z
  simp

/-- The finite relative-coset trace has the expected unit law. -/
theorem maassTraceLinear_self [G.IsFiniteRelIndex G] :
    maassTraceLinear (G := G) (H := G) = LinearMap.id := by
  ext f z
  change maassTraceFunction f z = f.1 z
  exact congrFun (maassTraceFunction_self f) z

end

end GaloisForLFunctions.RHTower
