import GaloisForLFunctions.HTGeometry.ImageCoverLift
import GaloisForLFunctions.Bottcher.ModularLambdaProperness
import GaloisForLFunctions.RHTower.XiMarkedSourceSpace

/-!
# The actual marked Xi map factors through its exact image cover

Transport the corpus modular-lambda universal cover to the marked target
`ℂ ∖ {0, -1}`. The subgroup quotient construction then gives an actual covering
factor for each marked Xi coordinate and a source lift whose induced
fundamental-group map is onto. The untwisted Xi specialization has no premises.

This does not assert that the original Xi map is onto on fundamental groups.
Analytic capping and intrinsic uniformization remain separate obligations.
-/

open Topology Set Function
open scoped UpperHalfPlane

namespace RHTower.XiMarkedMonodromy

open GaloisForLFunctions.HTGeometry

noncomputable section

/-- Negation identifies the modular-lambda target with the actual Xi marked target. -/
def puncturedTargetHomeomorph : Bottcher.Punctured ≃ₜ Target where
  toFun z := ⟨-z.val, neg_ne_zero.mpr (Bottcher.mem_compl01.mp z.property).1,
    fun h => (Bottcher.mem_compl01.mp z.property).2 (neg_injective h)⟩
  invFun z := ⟨-z.val, Bottcher.mem_compl01.mpr ⟨neg_ne_zero.mpr z.property.1,
    fun h => z.property.2 (by simpa only [neg_neg] using congrArg Neg.neg h)⟩⟩
  left_inv z := Subtype.ext (neg_neg z.val)
  right_inv z := Subtype.ext (neg_neg z.val)
  continuous_toFun := continuous_subtype_val.neg.subtype_mk _
  continuous_invFun := continuous_subtype_val.neg.subtype_mk _

/-- The existing modular-lambda cover transported to the Xi target. -/
def markedUniversalCover : ℍ → Target := puncturedTargetHomeomorph ∘ Bottcher.lambdaPunct

theorem isCoveringMap_markedUniversalCover : IsCoveringMap markedUniversalCover :=
  Bottcher.isCoveringMap_lambdaPunct.homeomorph_comp puncturedTargetHomeomorph

theorem markedUniversalCover_surjective : Surjective markedUniversalCover :=
  puncturedTargetHomeomorph.surjective.comp Bottcher.lambdaPunct_surjective

theorem isOpen_target : IsOpen {z : ℂ | z ≠ 0 ∧ z ≠ -1} :=
  isOpen_ne.inter isOpen_ne

instance target_locallyPathConnectedSpace : LocallyPathConnectedSpace Target :=
  isOpen_target.locallyPathConnectedSpace

/-- Removing the finitely many marked fibers leaves an open source surface. -/
theorem isOpen_sourceSet (A : Finset ℝ) : IsOpen (sourceSet A) := by
  have h : IsOpen (⋂ a ∈ A, {s : ℂ | value a s ≠ -1}) :=
    isOpen_biInter_finset fun a _ => isOpen_ne.preimage (value_differentiable a).continuous
  have h0 : IsOpen {s : ℂ | xi s ≠ 0} := isOpen_ne.preimage xi_differentiable.continuous
  convert h0.inter h using 1
  ext s
  simp [sourceSet]

instance source_locallyPathConnectedSpace (A : Finset ℝ) : LocallyPathConnectedSpace (Source A) :=
  (isOpen_sourceSet A).locallyPathConnectedSpace

/-- The intrinsic deck action presents the transported modular covering. -/
theorem markedUniversalCover_quotient :
    IsQuotientCoveringMap markedUniversalCover (coveringDeckGroup markedUniversalCover) :=
  isQuotientCoveringMap_coveringDeckGroup
    isCoveringMap_markedUniversalCover markedUniversalCover_surjective

/-- A fixed sheet over the actual common Xi basepoint. -/
def markedUniversalCoverPoint : markedUniversalCover ⁻¹' {targetHalf} :=
  ⟨(markedUniversalCover_surjective targetHalf).choose,
    (markedUniversalCover_surjective targetHalf).choose_spec⟩

/-- Every actual marked Xi coordinate has an exact-image covering factorization.
The lifted map induces a surjection on fundamental groups. -/
theorem coordinate_exact_image_cover_factorization (A : Finset ℝ) (a : A) :
    ∃ H : Subgroup (coveringDeckGroup markedUniversalCover),
      ∃ F : C(Source A, SubgroupCover (E := ℍ) H),
      ∃ hF : F (sourceZero A) = Quotient.mk (MulAction.orbitRel H ℍ) markedUniversalCoverPoint.val,
      subgroupCoverProjection (E := ℍ) (B := Target) (p := markedUniversalCover) markedUniversalCover_quotient H ∘ F = coordinate A a ∧
      Surjective (FundamentalGroup.mapOfEq F hF) := by
  let e : markedUniversalCover ⁻¹' {coordinate A a (sourceZero A)} :=
    ⟨markedUniversalCoverPoint.val, by rw [coordinate_sourceZero]; exact markedUniversalCoverPoint.property⟩
  exact exists_subgroup_cover_lift_surjective_fundamentalGroup
    markedUniversalCover_quotient (coordinate A a) (sourceZero A) e

/-- The actual untwisted Xi map has an exact image cover and a loop-surjective lift. -/
theorem xi_exact_image_cover_factorization :
    ∃ H : Subgroup (coveringDeckGroup markedUniversalCover),
      ∃ F : C(Source ({0} : Finset ℝ), SubgroupCover (E := ℍ) H),
      ∃ hF : F (sourceZero {0}) = Quotient.mk (MulAction.orbitRel H ℍ) markedUniversalCoverPoint.val,
      (∀ s : Source ({0} : Finset ℝ), (subgroupCoverProjection (E := ℍ) (B := Target) (p := markedUniversalCover) markedUniversalCover_quotient H (F s) : ℂ) = xi s) ∧
      Surjective (FundamentalGroup.mapOfEq F hF) := by
  obtain ⟨H, F, hF, hcomp, hsurj⟩ :=
    coordinate_exact_image_cover_factorization {0} ⟨0, Finset.mem_singleton_self 0⟩
  refine ⟨H, F, hF, ?_, hsurj⟩
  intro s
  have h := congrArg Subtype.val (congrFun hcomp s)
  simpa only [Function.comp_apply, coordinate, ContinuousMap.coe_mk, value, neg_zero, Complex.ofReal_zero,
    zero_mul, Complex.exp_zero, mul_one] using h

end
end RHTower.XiMarkedMonodromy
