import GaloisForLFunctions.RepresentationLifting.CyclicRegularCoordinates
import GaloisForLFunctions.RepresentationLifting.NormGluing
import Mathlib.Data.ZMod.Basic

/-!
# Integral gluing in the cyclic regular module

The regular cyclic norm complex is exact over the integers, but its invariant
and norm-zero lattices need not sum to the whole lattice. Their sum consists
exactly of vectors whose augmentation is divisible by the group order.
This realizes the group-order obstruction of Auel–Shaikh, Lemma 1.1(d), inside
the cyclic norm-difference construction.
-/

noncomputable section
namespace GaloisForLFunctions.RepresentationLifting

variable (G : Type) [CommGroup G] [Fintype G] [IsCyclic G]

/-- Integral invariant-plus-moving lattice for the cyclic regular representation. -/
def cyclicIntegralGluingSubmodule : Submodule ℤ (CyclicRegular ℤ G) :=
  LinearMap.ker (cyclicRegularDelta ℤ G) ⊔ LinearMap.ker (cyclicRegularNorm ℤ G)

/-- The cyclic kernels are precisely the general invariant/norm gluing construction. -/
theorem cyclicIntegralGluing_eq_normGluing :
    cyclicIntegralGluingSubmodule G =
      normGluingSubmodule (Representation.leftRegular ℤ G) := by
  unfold cyclicIntegralGluingSubmodule normGluingSubmodule
  congr 1
  ext v
  change (Representation.leftRegular ℤ G (cyclicRegularGenerator G) v - v = 0) ↔ _
  rw [sub_eq_zero]
  exact (Representation.mem_invariants_iff_of_forall_mem_zpowers
    (Representation.leftRegular ℤ G) (cyclicRegularGenerator G)
    (cyclicRegularGenerator_generates G) v).symm

omit [IsCyclic G] in
/-- Augmentation of the invariant norm vector is the group order. -/
theorem cyclicAugmentation_normVector :
    cyclicAugmentation ℤ G (cyclicNormVector ℤ G) = (Fintype.card G : ℤ) := by
  simp [cyclicAugmentation, cyclicNormVector_coeff]

omit [IsCyclic G] in
/-- The integral norm kernel is exactly the augmentation kernel. -/
theorem cyclicRegularNorm_eq_zero_iff (v : CyclicRegular ℤ G) :
    cyclicRegularNorm ℤ G v = 0 ↔ cyclicAugmentation ℤ G v = 0 := by
  rw [cyclicRegularNorm_eq_smul]
  constructor
  · intro h
    have hc := congrArg (fun w : CyclicRegular ℤ G => w.coeff 1) h
    rw [MonoidAlgebra.coeff_smul] at hc
    change cyclicAugmentation ℤ G v * (cyclicNormVector ℤ G).coeff 1 = 0 at hc
    simpa only [cyclicNormVector_coeff, mul_one] using hc
  · intro h
    rw [h, zero_smul]

/-- Divisibility of augmentation completely characterizes the integral gluing lattice. -/
theorem mem_cyclicIntegralGluingSubmodule_iff (v : CyclicRegular ℤ G) :
    v ∈ cyclicIntegralGluingSubmodule G ↔
      (Fintype.card G : ℤ) ∣ cyclicAugmentation ℤ G v := by
  rw [cyclicIntegralGluingSubmodule, ← cyclicRegular_norm_delta_exact]
  constructor
  · intro hv
    obtain ⟨x, ⟨a, rfl⟩, y, hy, rfl⟩ := Submodule.mem_sup.mp hv
    have hy0 := (cyclicRegularNorm_eq_zero_iff G y).mp hy
    rw [map_add, hy0, add_zero, cyclicRegularNorm_eq_smul, map_smul,
      cyclicAugmentation_normVector, smul_eq_mul]
    exact ⟨cyclicAugmentation ℤ G a, mul_comm _ _⟩
  · rintro ⟨a, ha⟩
    have hn : a • cyclicNormVector ℤ G ∈ LinearMap.range (cyclicRegularNorm ℤ G) := by
      refine ⟨MonoidAlgebra.single 1 a, ?_⟩
      rw [cyclicRegularNorm_eq_smul, cyclicAugmentation_single]
    refine Submodule.mem_sup.mpr ⟨a • cyclicNormVector ℤ G, hn,
      v - a • cyclicNormVector ℤ G, ?_, by abel⟩
    change cyclicRegularNorm ℤ G (v - a • cyclicNormVector ℤ G) = 0
    rw [cyclicRegularNorm_eq_zero_iff, map_sub, map_smul,
      cyclicAugmentation_normVector, smul_eq_mul, ha, mul_comm a, sub_self]

/-- The norm and difference kernels together miss precisely the augmentation residue. -/
theorem cyclicIntegralGluing_class_eq_zero_iff (v : CyclicRegular ℤ G) :
    (cyclicIntegralGluingSubmodule G).mkQ v = 0 ↔
      (Fintype.card G : ℤ) ∣ cyclicAugmentation ℤ G v := by
  change v ∈ LinearMap.ker (cyclicIntegralGluingSubmodule G).mkQ ↔ _
  rw [Submodule.ker_mkQ, mem_cyclicIntegralGluingSubmodule_iff]

/-- The class of a regular basis vector has exact annihilator `|G|ℤ`. -/
theorem cyclicIntegralGluing_generator_annihilator (a : ℤ) :
    a • (cyclicIntegralGluingSubmodule G).mkQ (MonoidAlgebra.single 1 1) = 0 ↔
      (Fintype.card G : ℤ) ∣ a := by
  rw [← map_smul, cyclicIntegralGluing_class_eq_zero_iff,
    map_smul, cyclicAugmentation_single, smul_eq_mul, mul_one]

/-- Augmentation reduced modulo the group order. -/
def cyclicAugmentationResidue : CyclicRegular ℤ G →ₗ[ℤ] ZMod (Fintype.card G) :=
  AddMonoidHom.toIntLinearMap
    { toFun := fun v => (cyclicAugmentation ℤ G v : ZMod (Fintype.card G))
      map_zero' := by simp
      map_add' := fun v w => by simp }

/-- The residue map detects precisely the invariant-plus-moving lattice. -/
theorem cyclicAugmentationResidue_ker :
    (cyclicAugmentationResidue G).ker = cyclicIntegralGluingSubmodule G := by
  ext v
  change ((cyclicAugmentation ℤ G v : ℤ) : ZMod (Fintype.card G)) = 0 ↔ _
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd, mem_cyclicIntegralGluingSubmodule_iff]

omit [IsCyclic G] in
/-- Every residue occurs on an integral regular basis vector. -/
theorem cyclicAugmentationResidue_surjective :
    Function.Surjective (cyclicAugmentationResidue G) := by
  intro z
  obtain ⟨a, ha⟩ := ZMod.intCast_surjective z
  refine ⟨MonoidAlgebra.single 1 a, ?_⟩
  change ((cyclicAugmentation ℤ G (MonoidAlgebra.single 1 a) : ℤ) :
    ZMod (Fintype.card G)) = z
  rw [cyclicAugmentation_single, ha]

/-- The integral gluing group of the regular cyclic lattice is exactly `ℤ/|G|ℤ`. -/
def cyclicIntegralGluingEquiv :
    (CyclicRegular ℤ G ⧸ cyclicIntegralGluingSubmodule G) ≃ₗ[ℤ]
      ZMod (Fintype.card G) :=
  (Submodule.quotEquivOfEq _ _ (cyclicAugmentationResidue_ker G).symm).trans
    ((cyclicAugmentationResidue G).quotKerEquivOfSurjective
      (cyclicAugmentationResidue_surjective G))

end GaloisForLFunctions.RepresentationLifting

#print axioms GaloisForLFunctions.RepresentationLifting.mem_cyclicIntegralGluingSubmodule_iff
#print axioms GaloisForLFunctions.RepresentationLifting.cyclicIntegralGluing_class_eq_zero_iff

#print axioms GaloisForLFunctions.RepresentationLifting.cyclicIntegralGluingEquiv
#print axioms GaloisForLFunctions.RepresentationLifting.cyclicIntegralGluing_eq_normGluing
#print axioms GaloisForLFunctions.RepresentationLifting.cyclicIntegralGluing_generator_annihilator
