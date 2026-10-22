import GaloisForLFunctions.RHTower.Deninger.DeningerMeyerStrongLogOperatorContinuity

/-!
# Strict solvability for every finitely coupled Meyer generator word

The finite packet range classification becomes a closed-range theorem in the
natural source topology. Fréchet open mapping then makes the canonical inverse
modulo the actual homogeneous kernel continuous. Thus limits of solvable data
remain solvable, and the finite-rank repaired words are open surjections on
the literal Poisson cohomology.

No vanishing of the jet-invisible sector or choice of a continuous arithmetic
complement is assumed. In particular, the homogeneous kernel is retained.
-/

open Filter Set Topology TopologicalSpace

namespace RHTower
noncomputable section
open scoped DeningerMeyerNaturalTopology

/-- Finite packet compatibility is closed in the actual source topology. -/
theorem deningerMeyerCoupledSourceOperator_range_isClosed (L : List ℂ)
    (B : Module.End ℂ (DeningerMeyerFiniteXiJetPacket (deningerMeyerWordXiSupport L))) :
    IsClosed (LinearMap.range
      (deningerMeyerCoupledSourceOperator (deningerMeyerWordXiSupport L) L B) :
        Set DeningerMeyerStrongLogCohomology) := by
  rw [deningerMeyerCoupledSourceOperator_range]
  have hclosed := (LinearMap.range
    (deningerMeyerCoupledPacketOperator (deningerMeyerWordXiSupport L) L B)).closed_of_finiteDimensional
  exact hclosed.preimage
    (deningerMeyerFiniteXiJetPacketLM_continuous (deningerMeyerWordXiSupport L))

/-- The actual coupled operator is open onto its exact range. -/
theorem deningerMeyerCoupledSourceOperator_rangeRestrict_isOpenMap (L : List ℂ)
    (B : Module.End ℂ (DeningerMeyerFiniteXiJetPacket (deningerMeyerWordXiSupport L))) :
    IsOpenMap
      (deningerMeyerCoupledSourceOperator (deningerMeyerWordXiSupport L) L B).rangeRestrict := by
  let T := deningerMeyerCoupledSourceOperator (deningerMeyerWordXiSupport L) L B
  haveI : IsUniformAddGroup ↥(LinearMap.range T) :=
    inferInstanceAs (IsUniformAddGroup ↥(LinearMap.range T).toAddSubgroup)
  haveI : IsCompletelyPseudoMetrizableSpace ↥(LinearMap.range T) :=
    (deningerMeyerCoupledSourceOperator_range_isClosed L B).isCompletelyPseudoMetrizableSpace
  exact GaloisForLFunctions.isOpenMap_of_surjective T.rangeRestrict
    ((deningerMeyerCoupledSourceOperator_continuous _ L B).subtype_mk _)
    T.surjective_rangeRestrict

/-- Continuous solution classes for every finite word and arbitrary finite coupling.
The topology and quotient on the left are the actual source quotient topology. -/
def deningerMeyerCoupledSourceStrictEquiv (L : List ℂ)
    (B : Module.End ℂ (DeningerMeyerFiniteXiJetPacket (deningerMeyerWordXiSupport L))) :
    (DeningerMeyerStrongLogCohomology ⧸ LinearMap.ker
      (deningerMeyerCoupledSourceOperator (deningerMeyerWordXiSupport L) L B)) ≃L[ℂ]
        LinearMap.range
          (deningerMeyerCoupledSourceOperator (deningerMeyerWordXiSupport L) L B) := by
  let T := deningerMeyerCoupledSourceOperator (deningerMeyerWordXiSupport L) L B
  have hcont := deningerMeyerCoupledSourceOperator_continuous (deningerMeyerWordXiSupport L) L B
  refine
    { toLinearEquiv := T.quotKerEquivRange
      continuous_toFun := ?_
      continuous_invFun := ?_ }
  · apply T.ker.isQuotientMap_mkQ.continuous_iff.mpr
    exact hcont.subtype_mk _
  · have hopen := deningerMeyerCoupledSourceOperator_rangeRestrict_isOpenMap L B
    have hquot := hopen.isQuotientMap (hcont.subtype_mk _) T.surjective_rangeRestrict
    apply hquot.continuous_iff.mpr
    convert T.ker.mkQL.continuous using 1
    funext u
    exact T.quotKerEquivRange_symm_apply_image u _

@[simp] theorem deningerMeyerCoupledSourceStrictEquiv_apply_mk (L : List ℂ)
    (B : Module.End ℂ (DeningerMeyerFiniteXiJetPacket (deningerMeyerWordXiSupport L)))
    (u : DeningerMeyerStrongLogCohomology) :
    (deningerMeyerCoupledSourceStrictEquiv L B (Submodule.Quotient.mk u) :
      DeningerMeyerStrongLogCohomology) =
        deningerMeyerCoupledSourceOperator (deningerMeyerWordXiSupport L) L B u := rfl

@[simp] theorem deningerMeyerCoupledSourceStrictEquiv_symm_image (L : List ℂ)
    (B : Module.End ℂ (DeningerMeyerFiniteXiJetPacket (deningerMeyerWordXiSupport L)))
    (u : DeningerMeyerStrongLogCohomology) :
    (deningerMeyerCoupledSourceStrictEquiv L B).symm
      ⟨deningerMeyerCoupledSourceOperator (deningerMeyerWordXiSupport L) L B u, ⟨u, rfl⟩⟩ =
        Submodule.Quotient.mk u :=
  LinearMap.quotKerEquivRange_symm_apply_image
    (deningerMeyerCoupledSourceOperator (deningerMeyerWordXiSupport L) L B) u _

/-- Approximating by solvable outputs produces an exact solution at the limit,
even when the chosen preimages themselves have no limit. -/
theorem deningerMeyerCoupledSourceOperator_solve_limit (L : List ℂ)
    (B : Module.End ℂ (DeningerMeyerFiniteXiJetPacket (deningerMeyerWordXiSupport L)))
    {ι : Type*} {l : Filter ι} [l.NeBot]
    (u : ι → DeningerMeyerStrongLogCohomology) (f : DeningerMeyerStrongLogCohomology)
    (h : Tendsto
      (fun i => deningerMeyerCoupledSourceOperator (deningerMeyerWordXiSupport L) L B (u i))
        l (𝓝 f)) :
    ∃ v, deningerMeyerCoupledSourceOperator (deningerMeyerWordXiSupport L) L B v = f :=
  (deningerMeyerCoupledSourceOperator_range_isClosed L B).mem_of_tendsto h
    (Eventually.of_forall fun i => ⟨u i, rfl⟩)

/-- Finite-rank repair gives an open surjection on the full literal cohomology. -/
theorem deningerMeyerRegularizedSourceWord_isOpenMap (L : List ℂ) :
    IsOpenMap (deningerMeyerRegularizedSourceWord L) :=
  GaloisForLFunctions.isOpenMap_of_surjective _
    (deningerMeyerCoupledSourceOperator_continuous _ L _)
    (deningerMeyerRegularizedSourceWord_surjective L)

/-- Every source neighbourhood can solve all data in another source neighbourhood. -/
theorem deningerMeyerRegularizedSourceWord_image_mem_nhds (L : List ℂ)
    (U : Set DeningerMeyerStrongLogCohomology) (hU : U ∈ 𝓝 0) :
    deningerMeyerRegularizedSourceWord L '' U ∈ 𝓝 0 := by
  have hmap := (deningerMeyerRegularizedSourceWord_isOpenMap L).map_nhds_eq
    (x := 0) (deningerMeyerCoupledSourceOperator_continuous _ L _).continuousAt
  rw [map_zero] at hmap
  rw [← hmap]
  exact Filter.mem_map.mpr (Filter.mem_of_superset hU fun u hu => ⟨u, hu, rfl⟩)

end
end RHTower
