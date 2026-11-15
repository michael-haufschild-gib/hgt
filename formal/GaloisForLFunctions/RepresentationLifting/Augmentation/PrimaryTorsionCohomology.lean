import GaloisForLFunctions.RepresentationLifting.Augmentation.PrimaryTorsionCompletion
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree

/-!
# Higher extensions of the primary torsion character group

Multiplication by `p` on the primary part of `ℚ/ℤ` is surjective, with
kernel canonically `𝔽ₚ`, but has no additive section. Choosing roots
therefore produces a two-cocycle whose class is nonzero in native group
cohomology and in the corresponding degree-two Ext group. First
cohomology with the same trivial coefficients vanishes by divisibility.

Thus vanishing first-order augmentation data can coexist with a genuine
higher extension. These statements concern group cohomology and Ext;
they do not identify a derived completion.
-/

noncomputable section
namespace GaloisForLFunctions.RepresentationLifting
open HTGeometry.ABHN
variable (p : ℕ) [Fact p.Prime]

/-- Embed `𝔽ₚ` as the order-`p` subgroup of the primary character group. -/
def primaryScalarEmbedding : ZMod p →+ PrimePrimaryRatModInt p :=
  (zmodRatModIntAddHom p (Fact.out : p.Prime).ne_zero).codRestrict _ fun a =>
    ⟨1, by
      rw [pow_one]
      exact zmodRatModIntAddHom_mem_ratModIntNTorsion p (Fact.out : p.Prime).ne_zero a⟩

/-- The standard local-invariant embedding remains faithful in the primary subgroup. -/
theorem primaryScalarEmbedding_injective : Function.Injective (primaryScalarEmbedding p) := by
  intro a b h
  exact zmodRatModIntAddHom_injective p (Fact.out : p.Prime).ne_zero (congrArg Subtype.val h)

/-- Scalar labels lie in the kernel of multiplication by `p`. -/
theorem primaryScalarEmbedding_smul (a : ZMod p) : p • primaryScalarEmbedding p a = 0 := by
  rw [← map_nsmul, nsmul_eq_mul, ZMod.natCast_self, zero_mul, map_zero]

/-- An additive section would send a nonzero `p`-torsion element to an impossible lift. -/
theorem primary_smul_has_no_additive_section :
    ¬ ∃ s : PrimePrimaryRatModInt p →+ PrimePrimaryRatModInt p, ∀ x, p • s x = x := by
  rintro ⟨s, hs⟩
  have hz : primaryScalarEmbedding p 1 = 0 := by
    rw [← hs (primaryScalarEmbedding p 1), ← map_nsmul,
      primaryScalarEmbedding_smul, map_zero]
  have h1 : (1 : ZMod p) = 0 := primaryScalarEmbedding_injective p
    (hz.trans (map_zero (primaryScalarEmbedding p)).symm)
  exact one_ne_zero h1

/-- The kernel of multiplication by `p` is canonically the additive group of `𝔽ₚ`. -/
def primaryScalarKernelEquiv :
    ZMod p ≃+ (nsmulAddMonoidHom p : PrimePrimaryRatModInt p →+ PrimePrimaryRatModInt p).ker :=
  AddEquiv.ofBijective
    ((primaryScalarEmbedding p).codRestrict _ (primaryScalarEmbedding_smul p))
    ⟨fun a b h => primaryScalarEmbedding_injective p (congrArg Subtype.val h), by
      intro x
      have hx : x.val.val ∈ ratModIntNTorsion p := congrArg Subtype.val x.property
      rw [← zmodRatModIntAddHom_range_eq_ratModIntNTorsion p (Fact.out : p.Prime).ne_zero] at hx
      obtain ⟨a, ha⟩ := hx
      exact ⟨a, Subtype.ext (Subtype.ext ha)⟩⟩

/-- The scalar kernel and multiplication by `p` form the actual nonsplit short exact sequence. -/
theorem primaryScalar_shortExact :
    Function.Injective (primaryScalarEmbedding p) ∧
      Function.Exact (primaryScalarEmbedding p)
        (nsmulAddMonoidHom p : PrimePrimaryRatModInt p →+ PrimePrimaryRatModInt p) ∧
      Function.Surjective
        (nsmulAddMonoidHom p : PrimePrimaryRatModInt p →+ PrimePrimaryRatModInt p) := by
  refine ⟨primaryScalarEmbedding_injective p, ?_, primePrimaryRatModInt_smul_surjective p⟩
  intro x
  constructor
  · intro hx
    refine ⟨(primaryScalarKernelEquiv p).symm ⟨x, hx⟩, ?_⟩
    exact congrArg Subtype.val ((primaryScalarKernelEquiv p).apply_symm_apply _)
  · rintro ⟨a, rfl⟩
    exact primaryScalarEmbedding_smul p a

/-- A set-theoretic choice of a `p`th root for each primary character. -/
def primaryRootLift : PrimePrimaryRatModInt p → PrimePrimaryRatModInt p :=
  Function.surjInv (primePrimaryRatModInt_smul_surjective p)

/-- The chosen roots map back to their characters. -/
theorem primaryRootLift_spec (x : PrimePrimaryRatModInt p) :
    p • primaryRootLift p x = x :=
  Function.surjInv_eq (primePrimaryRatModInt_smul_surjective p) x

/-- Failure of the root choice to be additive, expressed in its exact scalar kernel. -/
def primaryRootDefect (x y : PrimePrimaryRatModInt p) : ZMod p :=
  (primaryScalarKernelEquiv p).symm
    ⟨primaryRootLift p x + primaryRootLift p y - primaryRootLift p (x + y), by
      change p • (primaryRootLift p x + primaryRootLift p y - primaryRootLift p (x + y)) = 0
      rw [nsmul_sub, nsmul_add, primaryRootLift_spec, primaryRootLift_spec, primaryRootLift_spec,
        sub_self]⟩

/-- Including the scalar defect recovers the additive defect of the chosen roots. -/
theorem primaryScalarEmbedding_rootDefect (x y : PrimePrimaryRatModInt p) :
    primaryScalarEmbedding p (primaryRootDefect p x y) =
      primaryRootLift p x + primaryRootLift p y - primaryRootLift p (x + y) :=
  congrArg Subtype.val ((primaryScalarKernelEquiv p).apply_symm_apply _)

/-- Trivial `𝔽ₚ` coefficients for the primary character group. -/
abbrev primaryTrivialRepresentation :
    Rep (ZMod p) (Multiplicative (PrimePrimaryRatModInt p)) :=
  Rep.trivial (ZMod p) (Multiplicative (PrimePrimaryRatModInt p)) (ZMod p)

/-- Associativity makes the root defect a native degree-two group cocycle. -/
def primaryRootCocycle : groupCohomology.cocycles₂ (primaryTrivialRepresentation p) :=
  ⟨fun g => primaryRootDefect p g.1.toAdd g.2.toAdd, by
    apply (groupCohomology.mem_cocycles₂_def _).mpr
    intro g h j
    change primaryRootDefect p h.toAdd j.toAdd -
      primaryRootDefect p (g.toAdd + h.toAdd) j.toAdd +
      primaryRootDefect p g.toAdd (h.toAdd + j.toAdd) -
      primaryRootDefect p g.toAdd h.toAdd = 0
    apply primaryScalarEmbedding_injective p
    rw [map_sub, map_add, map_sub, map_zero,
      primaryScalarEmbedding_rootDefect, primaryScalarEmbedding_rootDefect,
      primaryScalarEmbedding_rootDefect, primaryScalarEmbedding_rootDefect]
    rw [add_assoc]
    abel⟩

#print axioms primaryRootCocycle
#print axioms primary_smul_has_no_additive_section
#print axioms primaryScalar_shortExact

/-- A scalar coboundary correction would give the forbidden additive section. -/
theorem primaryRootCocycle_not_coboundary :
    (primaryRootCocycle p : _ → ZMod p) ∉
      groupCohomology.coboundaries₂ (primaryTrivialRepresentation p) := by
  rintro ⟨b, hb⟩
  have hdefect (x y : PrimePrimaryRatModInt p) :
      primaryScalarEmbedding p (b (Multiplicative.ofAdd y)) -
        primaryScalarEmbedding p (b (Multiplicative.ofAdd (x + y))) +
        primaryScalarEmbedding p (b (Multiplicative.ofAdd x)) =
      primaryRootLift p x + primaryRootLift p y - primaryRootLift p (x + y) := by
    have h := congrFun hb (Multiplicative.ofAdd x, Multiplicative.ofAdd y)
    change b (Multiplicative.ofAdd y) - b (Multiplicative.ofAdd (x + y)) +
      b (Multiplicative.ofAdd x) = primaryRootDefect p x y at h
    have he := congrArg (primaryScalarEmbedding p) h
    simpa only [map_add, map_sub, primaryScalarEmbedding_rootDefect] using he
  let s : PrimePrimaryRatModInt p → PrimePrimaryRatModInt p :=
    fun x => primaryRootLift p x - primaryScalarEmbedding p (b (Multiplicative.ofAdd x))
  have hsadd (x y : PrimePrimaryRatModInt p) : s (x + y) = s x + s y := by
    dsimp only [s]
    calc
      _ = (primaryScalarEmbedding p (b (Multiplicative.ofAdd y)) -
          primaryScalarEmbedding p (b (Multiplicative.ofAdd (x + y))) +
          primaryScalarEmbedding p (b (Multiplicative.ofAdd x))) +
          primaryRootLift p (x + y) - primaryScalarEmbedding p (b (Multiplicative.ofAdd x)) -
          primaryScalarEmbedding p (b (Multiplicative.ofAdd y)) := by abel
      _ = (primaryRootLift p x + primaryRootLift p y - primaryRootLift p (x + y)) +
          primaryRootLift p (x + y) - primaryScalarEmbedding p (b (Multiplicative.ofAdd x)) -
          primaryScalarEmbedding p (b (Multiplicative.ofAdd y)) := by rw [hdefect]
      _ = _ := by abel
  have hs0 : s 0 = 0 := by
    have h := hsadd 0 0
    rw [zero_add] at h
    exact add_left_cancel (h.symm.trans (add_zero (s 0)).symm)
  apply primary_smul_has_no_additive_section p
  refine ⟨{ toFun := s, map_zero' := hs0, map_add' := hsadd }, ?_⟩
  intro x
  change p • (primaryRootLift p x - primaryScalarEmbedding p (b (Multiplicative.ofAdd x))) = x
  rw [nsmul_sub, primaryRootLift_spec, primaryScalarEmbedding_smul, sub_zero]

/-- The degree-two class of the nonsplit root extension. -/
def primaryH2Class : groupCohomology.H2 (primaryTrivialRepresentation p) :=
  groupCohomology.H2π (primaryTrivialRepresentation p) (primaryRootCocycle p)

/-- The primary root extension gives a nonzero native group-cohomology class. -/
theorem primaryH2Class_ne_zero : primaryH2Class p ≠ 0 := by
  intro h
  exact primaryRootCocycle_not_coboundary p
    ((groupCohomology.H2π_eq_zero_iff (primaryRootCocycle p)).mp h)

#print axioms primaryH2Class_ne_zero

/-- Divisibility annihilates every additive map from primary characters to `𝔽ₚ`. -/
theorem primary_addHom_zmod_eq_zero (f : PrimePrimaryRatModInt p →+ ZMod p) : f = 0 := by
  ext x
  obtain ⟨y, rfl⟩ := primePrimaryRatModInt_smul_surjective p x
  rw [map_nsmul, nsmul_eq_mul, ZMod.natCast_self, zero_mul]
  rfl

/-- First cohomology vanishes for the same trivial coefficients. -/
theorem primaryH1_eq_zero (x : groupCohomology.H1 (primaryTrivialRepresentation p)) : x = 0 := by
  let e := groupCohomology.H1IsoOfIsTrivial (primaryTrivialRepresentation p)
  have hz : e.hom x = 0 := primary_addHom_zmod_eq_zero p (e.hom x)
  calc
    x = e.inv (e.hom x) := by simp
    _ = e.inv 0 := congrArg e.inv hz
    _ = 0 := map_zero _

/-- The root class transported to the native degree-two Ext of representations. -/
def primaryExt2Class :=
  (groupCohomologyIsoExt (primaryTrivialRepresentation p) 2).hom (primaryH2Class p)

/-- Degree-two Ext retains a nonzero class despite vanishing first cohomology. -/
theorem primaryExt2Class_ne_zero : primaryExt2Class p ≠ 0 := by
  let e := groupCohomologyIsoExt (primaryTrivialRepresentation p) 2
  intro h
  apply primaryH2Class_ne_zero p
  calc
    primaryH2Class p = e.inv (e.hom (primaryH2Class p)) := by simp
    _ = e.inv 0 := congrArg e.inv h
    _ = 0 := map_zero _

#print axioms primaryH1_eq_zero
#print axioms primaryExt2Class_ne_zero
end GaloisForLFunctions.RepresentationLifting
