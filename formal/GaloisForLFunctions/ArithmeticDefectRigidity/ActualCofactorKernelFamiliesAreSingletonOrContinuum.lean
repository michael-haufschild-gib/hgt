import GaloisForLFunctions.ArithmeticDefectRigidity.CommonCofactorLimitsExistAlongPrescribedHorizons
import GaloisForLFunctions.ArithmeticDefectRigidity.ActualCofactorGramsHaveVanishingSteps
import GaloisForLFunctions.HTGeometry.VanishingStepsFillIntermediateClusterValues
import Mathlib.Analysis.Real.Cardinality

/-!
# Actual common kernels form a singleton or a continuum

Vanishing successive Gram increments force each intermediate value of two
coordinate limits to occur in an actual common kernel. A nontrivial real
interval then injects into the family of countable real Gram tables.
-/

noncomputable section
set_option autoImplicit false
open Filter Topology

namespace GaloisForLFunctions.ArithmeticDefectRigidity.ActualCofactorLimit

/-- Every intermediate value of a differing coordinate is realized by an actual common kernel. -/
theorem exists_kernel_with_intermediate_coordinate {ε : SubcriticalDamping}
    (L M : ActualCofactorLimit ε) (j k : ℕ+) {c : ℝ}
    (hLc : L.kernel j k < c) (hcM : c < M.kernel j k) :
    ∃ N : ActualCofactorLimit ε, N.kernel j k = c := by
  obtain ⟨T, hT, hTc⟩ := HTGeometry.exists_strictMono_subseq_tendsto_between
    (fun n => cofactorGram ε n j k) L.subsequence M.subsequence L.strictMono M.strictMono
    (L.converges j k) (M.converges j k) (cofactorGram_succ_sub_tendsto_zero ε j k) hLc hcM
  obtain ⟨ns, hns, N, hN⟩ := exists_actualCofactorLimit_along ε T hT
  refine ⟨N, tendsto_nhds_unique (N.converges j k) ?_⟩
  apply (hTc.comp hns.tendsto_atTop).congr
  intro m
  simp only [Function.comp_apply, hN]

end GaloisForLFunctions.ArithmeticDefectRigidity.ActualCofactorLimit

namespace GaloisForLFunctions.ArithmeticDefectRigidity

/-- The actual common Gram kernels, forgetting the choice of witnessing subsequence. -/
def actualCofactorKernelSet (ε : SubcriticalDamping) : Set (ℕ+ → ℕ+ → ℝ) :=
  Set.range (fun L : ActualCofactorLimit ε => L.kernel)

/-- A countable real table bounds the size of the family of actual common kernels. -/
theorem cardinal_actualCofactorKernelSet_le_continuum (ε : SubcriticalDamping) :
    Cardinal.mk (actualCofactorKernelSet ε) ≤ Cardinal.continuum := by
  let F (K : actualCofactorKernelSet ε) (n m : ℕ) : ℝ :=
    K.val ⟨n + 1, Nat.succ_pos n⟩ ⟨m + 1, Nat.succ_pos m⟩
  have hinj : Function.Injective F := by
    intro K J h
    apply Subtype.ext
    funext p q
    have hp : (⟨(p : ℕ) - 1 + 1, Nat.succ_pos _⟩ : ℕ+) = p :=
      Subtype.ext (Nat.sub_add_cancel p.property)
    have hq : (⟨(q : ℕ) - 1 + 1, Nat.succ_pos _⟩ : ℕ+) = q :=
      Subtype.ext (Nat.sub_add_cancel q.property)
    have hh := congrFun (congrFun h ((p : ℕ) - 1)) ((q : ℕ) - 1)
    simpa only [F, hp, hq] using hh
  have h := Cardinal.mk_le_of_injective hinj
  simpa only [Cardinal.mk_arrow, Cardinal.mk_real, Cardinal.mk_nat,
    Cardinal.lift_id, Cardinal.continuum_power_aleph0] using h

namespace ActualCofactorLimit

/-- A nontrivial interval in one actual coordinate yields continuum many actual kernels. -/
theorem cardinal_actualKernelSet_eq_continuum_of_coordinate_lt
    {ε : SubcriticalDamping} (L M : ActualCofactorLimit ε) (j k : ℕ+)
    (hlt : L.kernel j k < M.kernel j k) :
    Cardinal.mk (actualCofactorKernelSet ε) = Cardinal.continuum := by
  classical
  let C := Set.Ioo (L.kernel j k) (M.kernel j k)
  have hex (c : C) : ∃ N : ActualCofactorLimit ε, N.kernel j k = (c : ℝ) :=
    exists_kernel_with_intermediate_coordinate L M j k c.property.1 c.property.2
  choose N hN using hex
  let F (c : C) : actualCofactorKernelSet ε := ⟨(N c).kernel, ⟨N c, rfl⟩⟩
  have hinj : Function.Injective F := by
    intro c d h
    apply Subtype.ext
    have hh := congrArg (fun K : actualCofactorKernelSet ε => K.val j k) h
    change (N c).kernel j k = (N d).kernel j k at hh
    simpa only [hN] using hh
  apply le_antisymm (cardinal_actualCofactorKernelSet_le_continuum ε)
  have h := Cardinal.mk_le_of_injective hinj
  change Cardinal.mk (Set.Ioo (L.kernel j k) (M.kernel j k)) ≤ _ at h
  rwa [Cardinal.mk_Ioo_real hlt] at h

/-- Two different actual common kernels force continuum many, without identifying module classes. -/
theorem cardinal_actualKernelSet_eq_continuum_of_ne
    {ε : SubcriticalDamping} (L M : ActualCofactorLimit ε) (hne : L.kernel ≠ M.kernel) :
    Cardinal.mk (actualCofactorKernelSet ε) = Cardinal.continuum := by
  classical
  have hex : ∃ j k : ℕ+, L.kernel j k ≠ M.kernel j k := by
    by_contra h
    push Not at h
    exact hne (funext fun j => funext fun k => h j k)
  obtain ⟨j, k, hjk⟩ := hex
  rcases lt_or_gt_of_ne hjk with h | h
  · exact cardinal_actualKernelSet_eq_continuum_of_coordinate_lt L M j k h
  · exact cardinal_actualKernelSet_eq_continuum_of_coordinate_lt M L j k h

/-- Nonuniqueness of actual common kernels is an arithmetic escape witness. -/
theorem not_admits_of_kernel_ne {ε : SubcriticalDamping}
    (L M : ActualCofactorLimit ε) (hne : L.kernel ≠ M.kernel) :
    ¬ GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.Admits
      GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.dampedMobiusEnergy ε := by
  intro hpaid
  exact hne (kernel_eq_of_admits L M hpaid)

end ActualCofactorLimit

/-- The actual common-kernel family is a singleton or has exactly continuum cardinality. -/
theorem actualCofactorKernelSet_singleton_or_continuum (ε : SubcriticalDamping) :
    (∃ K, actualCofactorKernelSet ε = {K}) ∨
      Cardinal.mk (actualCofactorKernelSet ε) = Cardinal.continuum := by
  classical
  obtain ⟨_, _, L, _⟩ := exists_actualCofactorLimit_along ε id strictMono_id
  by_cases hall : ∀ M : ActualCofactorLimit ε, M.kernel = L.kernel
  · left
    refine ⟨L.kernel, ?_⟩
    ext K
    constructor
    · rintro ⟨M, rfl⟩
      exact hall M
    · intro h
      exact ⟨L, (Set.mem_singleton_iff.mp h).symm⟩
  · right
    push Not at hall
    obtain ⟨M, hM⟩ := hall
    exact M.cardinal_actualKernelSet_eq_continuum_of_ne L hM

end GaloisForLFunctions.ArithmeticDefectRigidity

#print axioms GaloisForLFunctions.ArithmeticDefectRigidity.ActualCofactorLimit.exists_kernel_with_intermediate_coordinate
#print axioms GaloisForLFunctions.ArithmeticDefectRigidity.cardinal_actualCofactorKernelSet_le_continuum
#print axioms GaloisForLFunctions.ArithmeticDefectRigidity.ActualCofactorLimit.cardinal_actualKernelSet_eq_continuum_of_ne
#print axioms GaloisForLFunctions.ArithmeticDefectRigidity.actualCofactorKernelSet_singleton_or_continuum
#print axioms GaloisForLFunctions.ArithmeticDefectRigidity.ActualCofactorLimit.not_admits_of_kernel_ne

end
