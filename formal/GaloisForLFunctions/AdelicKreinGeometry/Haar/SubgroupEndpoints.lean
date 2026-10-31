import GaloisForLFunctions.HeckeKreinToeplitz.Index.SubgroupJumpKernels

/-!
# Positive endpoints for subgroup-indicator successors

The trivial and full additive subgroups of the rationals admit positive affine
carriers with constant dilation reading. The trivial subgroup uses the indicator
of all dilations, obtained by positive extension from that subgroup.
-/

open Complex Finset
open scoped ComplexConjugate Classical
open GaloisForLFunctions.ArithmeticPositiveDuality
open GaloisForLFunctions.HeckeKreinToeplitz
noncomputable section
namespace GaloisForLFunctions.AdelicKreinGeometry

/-- A translation reading equal to the indicator of an additive rational subgroup. -/
def HasSubgroupSuccessor (H : AddSubgroup ℚ) (k : AffineGroupQ → ℂ) : Prop :=
  ∀ b : ℚ, k (translation b) = if b ∈ H then 1 else 0

/-- Every subgroup-indicator successor normalizes its carrier at the identity. -/
theorem hasSubgroupSuccessor_one {H : AddSubgroup ℚ} {k : AffineGroupQ → ℂ}
    (hs : HasSubgroupSuccessor H k) : k 1 = 1 := by
  simpa only [translation_zero, if_pos H.zero_mem] using hs 0

/-- The full dilation subgroup, allowing either sign of the rational slope. -/
def fullDilationSubgroup : Subgroup AffineGroupQ := (⊤ : Subgroup ℚˣ).map dilation

theorem mem_fullDilationSubgroup (g : AffineGroupQ) :
    g ∈ fullDilationSubgroup ↔ affShift g = 0 := by
  constructor
  · intro h
    obtain ⟨u, _, rfl⟩ := Subgroup.mem_map.mp h
    exact affShift_dilation u
  · intro h
    apply Subgroup.mem_map.mpr
    refine ⟨Units.mk0 (affSlope g) (affSlope_ne_zero g), Subgroup.mem_top _, ?_⟩
    exact affine_ext (affSlope_dilation _) ((affShift_dilation _).trans h.symm)

/-- The dilation-subgroup indicator has a trivial translation successor. -/
def zeroShiftIndicator : AffineGroupQ → ℂ :=
  subgroupIndicatorKernel fullDilationSubgroup

theorem zeroShiftIndicator_apply (g : AffineGroupQ) :
    zeroShiftIndicator g = if affShift g = 0 then 1 else 0 := by
  rw [zeroShiftIndicator, subgroupIndicatorKernel_apply]
  simp only [mem_fullDilationSubgroup]

/-- Subgroup extension proves positivity without any analytic premise. -/
theorem zeroShiftIndicator_posDef : IsPosDefKernel zeroShiftIndicator :=
  subgroupIndicatorKernel_posDef fullDilationSubgroup

theorem zeroShiftIndicator_translation (b : ℚ) :
    zeroShiftIndicator (translation b) = if b = 0 then 1 else 0 := by
  rw [zeroShiftIndicator_apply, affShift_translation]

theorem zeroShiftIndicator_dilation (u : ℚˣ) : zeroShiftIndicator (dilation u) = 1 := by
  rw [zeroShiftIndicator_apply, affShift_dilation, if_pos rfl]

theorem negIndex_zeroShiftIndicator : negIndex zeroShiftIndicator = 0 :=
  zeroShiftIndicator_posDef.negIndex_eq_zero

/-- Both endpoint subgroups admit a positive carrier whose dilation coefficient is constant. -/
theorem exists_positive_subgroup_successor_endpoints (H : AddSubgroup ℚ)
    (hH : H = ⊥ ∨ H = ⊤) :
    ∃ k : AffineGroupQ → ℂ, IsPosDefKernel k ∧ HasSubgroupSuccessor H k ∧
      negIndex k = 0 ∧ ∀ u : ℚˣ, k (dilation u) = 1 := by
  rcases hH with rfl | rfl
  · refine ⟨zeroShiftIndicator, zeroShiftIndicator_posDef, ?_,
      negIndex_zeroShiftIndicator, zeroShiftIndicator_dilation⟩
    intro b
    simpa only [AddSubgroup.mem_bot] using zeroShiftIndicator_translation b
  · refine ⟨fun _ => 1, positive_constant_one, ?_,
      positive_constant_one.negIndex_eq_zero, fun _ => rfl⟩
    intro b
    simp only [AddSubgroup.mem_top, if_true]

#print axioms zeroShiftIndicator_posDef
#print axioms exists_positive_subgroup_successor_endpoints
end GaloisForLFunctions.AdelicKreinGeometry
