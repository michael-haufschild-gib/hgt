import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmClosedWeightedDerivative
import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaEigenMonopole

/-!
# Every translate of the closed Hedenmalm derivative

This file constructs the literal closed translate `A + α` on the unchanged domain of the
weighted derivative.  In graph coordinates it is the compact perturbation

`k ↦ k + α B k`,

where `B` is the centered compact source inverse.  The nonzero-monopole theorem for every
eigenvector of the full source inverse proves injectivity for every complex `α`.
-/

open Complex Function MeasureTheory Set Filter Topology Module
open scoped ENNReal

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry

namespace HedenmalmClosedWeightedDerivative

open HedenmalmQuantile HedenmalmHilbertSchmidt HedenmalmThetaSource

private abbrev H := Lp ℂ 2 unitIntervalMeasure

private abbrev HS := SourceSpace thetaSource

local instance hedenmalmShiftedClosedWeightedDerivativeLocalInst1 : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩

local instance hedenmalmShiftedClosedWeightedDerivativeLocalInst2 : CompleteSpace thetaCentered := thetaCentered_isClosed.completeSpace_coe

/-- Bounded range-coordinate map of the literal translate `A + α`. -/
def thetaShiftedRangeMap (α : ℂ) : thetaCentered →L[ℂ] H :=
  thetaCentered.subtypeL + α • thetaCenteredSourceInverse

theorem thetaShiftedRangeMap_apply (α : ℂ) (k : thetaCentered) :
    thetaShiftedRangeMap α k = (k : H) + α • thetaCenteredSourceInverse k := by
  simp [thetaShiftedRangeMap]

/-- The translated closed derivative on the same domain as `thetaWeightedDerivative`. -/
def thetaShiftedWeightedDerivative (α : ℂ) : H →ₗ.[ℂ] H :=
  closedGraphTransform thetaCentered thetaCenteredSourceInverse (thetaShiftedRangeMap α)

theorem thetaShiftedWeightedDerivative_domain (α : ℂ) :
    (thetaShiftedWeightedDerivative α).domain = thetaWeightedDerivative.domain := by
  rw [thetaShiftedWeightedDerivative, closedGraphTransform_domain,
    thetaWeightedDerivative, closedHyperplaneInverse_domain]

theorem thetaShiftedWeightedDerivative_apply (α : ℂ)
    (x : (thetaShiftedWeightedDerivative α).domain) :
    thetaShiftedWeightedDerivative α x =
      thetaWeightedDerivative
          ⟨(x : H), by simpa [thetaShiftedWeightedDerivative_domain] using x.property⟩ +
        α • (x : H) := by
  have hxrange : (x : H) ∈ thetaCenteredSourceInverse.range := by
    simpa only [thetaShiftedWeightedDerivative, closedGraphTransform_domain] using x.property
  rcases hxrange with ⟨k, hk⟩
  have hxShift : x =
      ⟨thetaCenteredSourceInverse k,
        (closedGraphTransform_apply_B thetaCentered thetaCenteredSourceInverse
          (thetaShiftedRangeMap α) thetaCenteredSourceInverse_injective k).1⟩ :=
    Subtype.ext hk.symm
  have hxA : thetaCenteredSourceInverse k ∈ thetaWeightedDerivative.domain :=
    (closedHyperplaneInverse_apply_B thetaCentered thetaCenteredSourceInverse
      thetaCenteredSourceInverse_injective k).1
  have hxeqA :
      (⟨(x : H), by simpa [thetaShiftedWeightedDerivative_domain] using x.property⟩ :
        thetaWeightedDerivative.domain) =
      ⟨thetaCenteredSourceInverse k, hxA⟩ := Subtype.ext hk.symm
  have hshiftApply := (closedGraphTransform_apply_B thetaCentered
    thetaCenteredSourceInverse (thetaShiftedRangeMap α)
      thetaCenteredSourceInverse_injective k).2
  have hAapply := (closedHyperplaneInverse_apply_B thetaCentered
    thetaCenteredSourceInverse thetaCenteredSourceInverse_injective k).2
  have hAapply' :
      thetaWeightedDerivative ⟨thetaCenteredSourceInverse k, hxA⟩ = (k : H) := by
    change closedHyperplaneInverse thetaCentered thetaCenteredSourceInverse
      ⟨thetaCenteredSourceInverse k, hxA⟩ = (k : H)
    exact hAapply
  calc
    thetaShiftedWeightedDerivative α x =
        thetaShiftedWeightedDerivative α
          ⟨thetaCenteredSourceInverse k,
            (closedGraphTransform_apply_B thetaCentered thetaCenteredSourceInverse
              (thetaShiftedRangeMap α) thetaCenteredSourceInverse_injective k).1⟩ :=
      congrArg (thetaShiftedWeightedDerivative α) hxShift
    _ = thetaShiftedRangeMap α k := hshiftApply
    _ = (k : H) + α • thetaCenteredSourceInverse k :=
      thetaShiftedRangeMap_apply α k
    _ = thetaWeightedDerivative ⟨thetaCenteredSourceInverse k, hxA⟩ +
        α • thetaCenteredSourceInverse k := by rw [hAapply']
    _ = thetaWeightedDerivative
          ⟨(x : H), by simpa [thetaShiftedWeightedDerivative_domain] using x.property⟩ +
        α • (x : H) := by
      rw [hxeqA]
      exact congrArg (fun y : H =>
        thetaWeightedDerivative ⟨thetaCenteredSourceInverse k, hxA⟩ + α • y) hk

theorem thetaShiftedRangeMap_injective (α : ℂ) :
    Function.Injective (thetaShiftedRangeMap α) := by
  suffices hzero : ∀ k : thetaCentered, thetaShiftedRangeMap α k = 0 → k = 0 by
    intro x y hxy
    apply sub_eq_zero.mp
    apply hzero (x - y)
    rw [map_sub, hxy, sub_self]
  intro k hk
  by_cases hα : α = 0
  · subst α
    apply Subtype.ext
    simpa [thetaShiftedRangeMap_apply] using hk
  have hkEq :
      thetaCompactSourceInverse (k : H) = (-α⁻¹) • (k : H) := by
    change thetaCenteredSourceInverse k = (-α⁻¹) • (k : H)
    have hsum : (k : H) + α • thetaCenteredSourceInverse k = 0 := by
      simpa [thetaShiftedRangeMap_apply] using hk
    have hαB : α • thetaCenteredSourceInverse k = -(k : H) :=
      eq_neg_of_add_eq_zero_right hsum
    calc
      thetaCenteredSourceInverse k = 1 • thetaCenteredSourceInverse k := by simp
      _ = (α⁻¹ * α) • thetaCenteredSourceInverse k := by
        simp [inv_mul_cancel₀ hα]
      _ = α⁻¹ • (α • thetaCenteredSourceInverse k) := by rw [smul_smul]
      _ = α⁻¹ • (-(k : H)) := by rw [hαB]
      _ = (-α⁻¹) • (k : H) := by simp
  by_contra hk0
  have hkH0 : (k : H) ≠ 0 := by
    intro h
    exact hk0 (Subtype.ext h)
  have hmean := pinnedMean_ne_zero_of_thetaCompactSourceInverse_eigen
    (neg_ne_zero.mpr (inv_ne_zero hα)) hkH0 hkEq
  exact hmean ((mem_thetaCentered_iff (k : H)).mp k.property)

theorem thetaShiftedRangeMap_antilipschitz (α : ℂ) :
    ∃ c : NNReal, AntilipschitzWith c (thetaShiftedRangeMap α) := by
  have hcompact : IsCompactOperator thetaCenteredSourceInverse :=
    isCompactOperator_thetaCompactSourceInverse.comp_clm thetaCentered.subtypeL
  simpa only [thetaShiftedRangeMap] using
    (antilipschitz_subtype_add_smul_of_compact_of_injective
      thetaCentered thetaCentered_isClosed thetaCenteredSourceInverse hcompact α
        (thetaShiftedRangeMap_injective α))

theorem thetaShiftedRangeMap_isClosed_range (α : ℂ) :
    IsClosed (Set.range (thetaShiftedRangeMap α)) := by
  rcases thetaShiftedRangeMap_antilipschitz α with ⟨c, hc⟩
  exact hc.isClosed_range (thetaShiftedRangeMap α).uniformContinuous

theorem thetaShiftedGraphMap_antilipschitz (α : ℂ) :
    ∃ c : NNReal, AntilipschitzWith c
      (thetaCenteredSourceInverse.prod (thetaShiftedRangeMap α)) := by
  let c : NNReal := ⟨1 + ‖α‖, by positivity⟩
  refine ⟨c, (thetaCenteredSourceInverse.prod
    (thetaShiftedRangeMap α)).antilipschitz_of_bound ?_⟩
  intro k
  have hdecomp : (k : H) = thetaShiftedRangeMap α k -
      α • thetaCenteredSourceInverse k := by
    rw [thetaShiftedRangeMap_apply]
    module
  calc
    ‖k‖ = ‖thetaShiftedRangeMap α k - α • thetaCenteredSourceInverse k‖ := by
      rw [← hdecomp]
      rfl
    _ ≤ ‖thetaShiftedRangeMap α k‖ + ‖α • thetaCenteredSourceInverse k‖ :=
      norm_sub_le _ _
    _ = ‖thetaShiftedRangeMap α k‖ + ‖α‖ * ‖thetaCenteredSourceInverse k‖ := by
      rw [norm_smul]
    _ ≤ ‖(thetaCenteredSourceInverse.prod (thetaShiftedRangeMap α)) k‖ +
        ‖α‖ * ‖(thetaCenteredSourceInverse.prod (thetaShiftedRangeMap α)) k‖ := by
      gcongr
      · simpa using norm_snd_le
          ((thetaCenteredSourceInverse.prod (thetaShiftedRangeMap α)) k)
      · simpa using norm_fst_le
          ((thetaCenteredSourceInverse.prod (thetaShiftedRangeMap α)) k)
    _ = (c : ℝ) *
        ‖(thetaCenteredSourceInverse.prod (thetaShiftedRangeMap α)) k‖ := by
      change _ = (1 + ‖α‖) *
        ‖(thetaCenteredSourceInverse.prod (thetaShiftedRangeMap α)) k‖
      ring

theorem thetaShiftedWeightedDerivative_isClosed (α : ℂ) :
    (thetaShiftedWeightedDerivative α).IsClosed := by
  rcases thetaShiftedGraphMap_antilipschitz α with ⟨c, hc⟩
  exact closedGraphTransform_isClosed thetaCentered thetaCenteredSourceInverse
    (thetaShiftedRangeMap α) thetaCenteredSourceInverse_injective hc

theorem thetaShiftedWeightedDerivative_dense_domain (α : ℂ) :
    Dense ((thetaShiftedWeightedDerivative α).domain : Set H) := by
  rw [thetaShiftedWeightedDerivative_domain]
  exact thetaWeightedDerivative_dense_domain

/-! ### The unchanged literal smooth core -/

theorem thetaDerivativeCoreSubmodule_le_shifted_domain (α : ℂ) :
    thetaDerivativeCoreSubmodule ≤ (thetaShiftedWeightedDerivative α).domain := by
  rw [thetaShiftedWeightedDerivative_domain]
  exact thetaDerivativeCoreSubmodule_le_domain

/-- Restriction of `A + α` to the same literal `C_c^∞(ℝ)` core. -/
def thetaShiftedDerivativeCore (α : ℂ) : H →ₗ.[ℂ] H :=
  (thetaShiftedWeightedDerivative α).domRestrict thetaDerivativeCoreSubmodule

theorem thetaShiftedDerivativeCore_graph_closure (α : ℂ) :
    closure ((thetaShiftedDerivativeCore α).graph : Set (H × H)) =
      ((thetaShiftedWeightedDerivative α).graph : Set (H × H)) := by
  let F : thetaCentered →L[ℂ] H × H :=
    thetaCenteredSourceInverse.prod (thetaShiftedRangeMap α)
  have hMaps : MapsTo F thetaDerivativeCoreOutput
      (thetaShiftedDerivativeCore α).graph := by
    intro k hk
    rcases hk with ⟨g, hg, hgs, hk⟩
    let f : HS := (memLp_sourceD hg hgs).toLp (sourceD g)
    let u : HS := (memLp_smooth hg hgs).toLp g
    have hfCentered : quantileUnitary thetaSource f ∈ thetaCentered :=
      quantile_sourceD_mem_centered hg hgs
    have hkSub : k = ⟨quantileUnitary thetaSource f, hfCentered⟩ := Subtype.ext hk
    have hB : thetaCenteredSourceInverse k = quantileUnitary thetaSource u := by
      rw [hkSub]
      exact thetaCompactSourceInverse_quantile_sourceD hg hgs
    have huSmooth : u ∈ thetaSmoothSourceSubmodule :=
      ⟨g, (memLp_smooth hg hgs).coeFn_toLp, hgs, hg⟩
    have hcoreSub : thetaCenteredSourceInverse k ∈ thetaDerivativeCoreSubmodule := by
      refine ⟨u, huSmooth, ?_⟩
      exact hB.symm
    have hTdom :
        thetaCenteredSourceInverse k ∈ (thetaShiftedWeightedDerivative α).domain :=
      (closedGraphTransform_apply_B thetaCentered thetaCenteredSourceInverse
        (thetaShiftedRangeMap α) thetaCenteredSourceInverse_injective k).1
    change F k ∈ (thetaShiftedDerivativeCore α).graph
    rw [LinearPMap.mem_graph_iff]
    let xcore : (thetaShiftedDerivativeCore α).domain :=
      ⟨thetaCenteredSourceInverse k, ⟨hcoreSub, hTdom⟩⟩
    refine ⟨xcore, rfl, ?_⟩
    exact (LinearPMap.domRestrict_apply
      (y := (⟨thetaCenteredSourceInverse k, hTdom⟩ :
        (thetaShiftedWeightedDerivative α).domain)) rfl).trans
      (closedGraphTransform_apply_B thetaCentered thetaCenteredSourceInverse
        (thetaShiftedRangeMap α) thetaCenteredSourceInverse_injective k).2
  apply le_antisymm
  · apply closure_minimal
      (LinearPMap.le_graph_of_le
        (LinearPMap.domRestrict_le : thetaShiftedDerivativeCore α ≤
          thetaShiftedWeightedDerivative α))
    exact thetaShiftedWeightedDerivative_isClosed α
  · intro p hp
    change p ∈ (thetaShiftedWeightedDerivative α).graph at hp
    rw [LinearPMap.mem_graph_iff] at hp
    rcases hp with ⟨x, hx, hout⟩
    have hxRange : (x : H) ∈ thetaCenteredSourceInverse.range := by
      rw [← closedGraphTransform_domain thetaCentered thetaCenteredSourceInverse
        (thetaShiftedRangeMap α)]
      exact x.property
    rcases hxRange with ⟨k, hk⟩
    have hTapply : thetaShiftedWeightedDerivative α x = thetaShiftedRangeMap α k := by
      have h := (closedGraphTransform_apply_B thetaCentered thetaCenteredSourceInverse
        (thetaShiftedRangeMap α) thetaCenteredSourceInverse_injective k).2
      have heq : x = ⟨thetaCenteredSourceInverse k,
          (closedGraphTransform_apply_B thetaCentered thetaCenteredSourceInverse
            (thetaShiftedRangeMap α) thetaCenteredSourceInverse_injective k).1⟩ :=
        Subtype.ext hk.symm
      simpa only [thetaShiftedWeightedDerivative, heq] using h
    have hpEq : F k = p := by
      apply Prod.ext
      · exact hk.trans hx
      · exact hTapply.symm.trans hout
    rw [← hpEq]
    have hkClosure : k ∈ closure thetaDerivativeCoreOutput := by
      rw [dense_thetaDerivativeCoreOutput.closure_eq]
      exact Set.mem_univ k
    exact map_mem_closure F.continuous hkClosure hMaps

theorem thetaShiftedDerivativeCore_isClosable (α : ℂ) :
    (thetaShiftedDerivativeCore α).IsClosable :=
  (thetaShiftedWeightedDerivative_isClosed α).isClosable.leIsClosable
    (LinearPMap.domRestrict_le : thetaShiftedDerivativeCore α ≤
      thetaShiftedWeightedDerivative α)

theorem thetaShiftedDerivativeCore_closure_eq (α : ℂ) :
    (thetaShiftedDerivativeCore α).closure = thetaShiftedWeightedDerivative α := by
  apply LinearPMap.eq_of_eq_graph
  rw [← (thetaShiftedDerivativeCore_isClosable α).graph_closure_eq_closure_graph]
  apply SetLike.coe_injective
  simpa only [Submodule.topologicalClosure_coe] using
    thetaShiftedDerivativeCore_graph_closure α

theorem thetaShiftedWeightedDerivative_hasCore (α : ℂ) :
    (thetaShiftedWeightedDerivative α).HasCore thetaDerivativeCoreSubmodule := by
  refine ⟨thetaDerivativeCoreSubmodule_le_shifted_domain α, ?_⟩
  exact thetaShiftedDerivativeCore_closure_eq α

theorem thetaShiftedWeightedDerivative_kernel_eq_bot (α : ℂ) :
    (thetaShiftedWeightedDerivative α).kernel = ⊥ :=
  closedGraphTransform_kernel_eq_bot thetaCentered thetaCenteredSourceInverse
    (thetaShiftedRangeMap α) thetaCenteredSourceInverse_injective
      (thetaShiftedRangeMap_injective α)

theorem thetaShiftedWeightedDerivative_range (α : ℂ) :
    (thetaShiftedWeightedDerivative α).rangeSubmodule =
      LinearMap.range (thetaShiftedRangeMap α).toLinearMap :=
  closedGraphTransform_range thetaCentered thetaCenteredSourceInverse
    (thetaShiftedRangeMap α) thetaCenteredSourceInverse_injective

/-! ### Compact inverse on the translated closed range -/

/-- Actual closed range of `A + α`. -/
abbrev thetaShiftedRange (α : ℂ) : Submodule ℂ H :=
  (thetaShiftedRangeMap α).range

theorem thetaShiftedRange_isClosed (α : ℂ) :
    IsClosed (thetaShiftedRange α : Set H) := by
  change IsClosed (Set.range (thetaShiftedRangeMap α))
  exact thetaShiftedRangeMap_isClosed_range α

noncomputable instance thetaShiftedRange_completeSpace (α : ℂ) :
    CompleteSpace (thetaShiftedRange α) :=
  (thetaShiftedRange_isClosed α).completeSpace_coe

/-- Compact inverse from the translated range to the unchanged operator domain. -/
def thetaShiftedSourceInverse (α : ℂ) : thetaShiftedRange α →L[ℂ] H :=
  thetaCenteredSourceInverse.comp
    ((thetaShiftedRangeMap α).equivRange
      (thetaShiftedRangeMap_injective α)
      (thetaShiftedRangeMap_isClosed_range α)).symm.toContinuousLinearMap

theorem thetaShiftedSourceInverse_apply_rangeMap (α : ℂ) (k : thetaCentered) :
    thetaShiftedSourceInverse α
      ⟨thetaShiftedRangeMap α k, by simp⟩ = thetaCenteredSourceInverse k := by
  rw [thetaShiftedSourceInverse, ContinuousLinearMap.comp_apply]
  apply congrArg thetaCenteredSourceInverse
  exact ContinuousLinearMap.equivRange_symm_apply
    (thetaShiftedRangeMap_injective α)
      (thetaShiftedRangeMap_isClosed_range α) k

theorem thetaShiftedSourceInverse_injective (α : ℂ) :
    Function.Injective (thetaShiftedSourceInverse α) := by
  intro x y hxy
  apply ((thetaShiftedRangeMap α).equivRange
    (thetaShiftedRangeMap_injective α)
      (thetaShiftedRangeMap_isClosed_range α)).symm.injective
  apply thetaCenteredSourceInverse_injective
  exact hxy

theorem thetaShiftedSourceInverse_range (α : ℂ) :
    LinearMap.range (thetaShiftedSourceInverse α).toLinearMap =
      LinearMap.range thetaCenteredSourceInverse.toLinearMap := by
  apply le_antisymm
  · rintro y ⟨r, rfl⟩
    exact ⟨((thetaShiftedRangeMap α).equivRange
      (thetaShiftedRangeMap_injective α)
        (thetaShiftedRangeMap_isClosed_range α)).symm r, rfl⟩
  · rintro y ⟨k, rfl⟩
    exact ⟨⟨thetaShiftedRangeMap α k, by simp⟩,
      thetaShiftedSourceInverse_apply_rangeMap α k⟩

theorem thetaShiftedSourceInverse_dense_range (α : ℂ) :
    Dense (LinearMap.range (thetaShiftedSourceInverse α).toLinearMap : Set H) := by
  rw [thetaShiftedSourceInverse_range]
  exact thetaCenteredSourceInverse_dense_range

theorem thetaShiftedSourceInverse_compact (α : ℂ) :
    IsCompactOperator (thetaShiftedSourceInverse α) := by
  exact (isCompactOperator_thetaCompactSourceInverse.comp_clm
    thetaCentered.subtypeL).comp_clm
      ((thetaShiftedRangeMap α).equivRange
        (thetaShiftedRangeMap_injective α)
          (thetaShiftedRangeMap_isClosed_range α)).symm.toContinuousLinearMap

/-- Hyperplane-inverse presentation of the already constructed literal translate. -/
def thetaShiftedWeightedDerivativeModel (α : ℂ) : H →ₗ.[ℂ] H :=
  closedHyperplaneInverse (thetaShiftedRange α) (thetaShiftedSourceInverse α)

theorem thetaShiftedWeightedDerivativeModel_eq (α : ℂ) :
    thetaShiftedWeightedDerivativeModel α = thetaShiftedWeightedDerivative α := by
  apply LinearPMap.ext
  · rw [thetaShiftedWeightedDerivativeModel, closedHyperplaneInverse_domain,
      thetaShiftedWeightedDerivative, closedGraphTransform_domain,
      thetaShiftedSourceInverse_range]
  · intro x hxModel hxShift
    have hxRange : x ∈ LinearMap.range thetaCenteredSourceInverse.toLinearMap := by
      simpa only [thetaShiftedWeightedDerivative, closedGraphTransform_domain] using hxShift
    rcases hxRange with ⟨k, hk⟩
    let r : thetaShiftedRange α := ⟨thetaShiftedRangeMap α k, by simp⟩
    have hBr : thetaShiftedSourceInverse α r = thetaCenteredSourceInverse k :=
      thetaShiftedSourceInverse_apply_rangeMap α k
    have hModelApply := (closedHyperplaneInverse_apply_B (thetaShiftedRange α)
      (thetaShiftedSourceInverse α) (thetaShiftedSourceInverse_injective α) r).2
    have hShiftApply := (closedGraphTransform_apply_B thetaCentered
      thetaCenteredSourceInverse (thetaShiftedRangeMap α)
        thetaCenteredSourceInverse_injective k).2
    have hxModelEq :
        (⟨x, hxModel⟩ : (thetaShiftedWeightedDerivativeModel α).domain) =
          ⟨thetaShiftedSourceInverse α r,
            (closedHyperplaneInverse_apply_B (thetaShiftedRange α)
              (thetaShiftedSourceInverse α)
                (thetaShiftedSourceInverse_injective α) r).1⟩ := by
      apply Subtype.ext
      exact hk.symm.trans hBr.symm
    have hxShiftEq :
        (⟨x, hxShift⟩ : (thetaShiftedWeightedDerivative α).domain) =
          ⟨thetaCenteredSourceInverse k,
            (closedGraphTransform_apply_B thetaCentered thetaCenteredSourceInverse
              (thetaShiftedRangeMap α) thetaCenteredSourceInverse_injective k).1⟩ := by
      exact Subtype.ext hk.symm
    calc
      thetaShiftedWeightedDerivativeModel α ⟨x, hxModel⟩ = (r : H) := by
        rw [hxModelEq]
        exact hModelApply
      _ = thetaShiftedRangeMap α k := rfl
      _ = thetaShiftedWeightedDerivative α ⟨x, hxShift⟩ := by
        rw [hxShiftEq]
        exact hShiftApply.symm

/-! ### Strictly positive translated Witten square -/

/-- Bounded inverse of the natural-domain square `(A + α)†(A + α)`. -/
def thetaShiftedWittenResolvent (α : ℂ) : H →L[ℂ] H :=
  (thetaShiftedSourceInverse α).comp (thetaShiftedSourceInverse α).adjoint

theorem thetaShiftedSourceInverse_adjoint_injective (α : ℂ) :
    Function.Injective (thetaShiftedSourceInverse α).adjoint := by
  apply continuousLinearMap_adjoint_injective_of_dense_range
  simpa only [ContinuousLinearMap.coe_coe] using thetaShiftedSourceInverse_dense_range α

theorem thetaShiftedWittenResolvent_injective (α : ℂ) :
    Function.Injective (thetaShiftedWittenResolvent α) := by
  simpa only [thetaShiftedWittenResolvent, ContinuousLinearMap.coe_comp] using
    ((thetaShiftedSourceInverse α).self_comp_adjoint_injective_iff.mpr
      (thetaShiftedSourceInverse_adjoint_injective α))

theorem thetaShiftedWittenResolvent_isSelfAdjoint (α : ℂ) :
    IsSelfAdjoint (thetaShiftedWittenResolvent α) := by
  change (thetaShiftedWittenResolvent α).adjoint = thetaShiftedWittenResolvent α
  rw [thetaShiftedWittenResolvent, ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_adjoint]

theorem thetaShiftedWittenResolvent_dense_range (α : ℂ) :
    Dense ((thetaShiftedWittenResolvent α).range : Set H) := by
  have horth : (thetaShiftedWittenResolvent α).rangeᗮ = ⊥ := by
    rw [(thetaShiftedWittenResolvent α).orthogonal_range,
      show (thetaShiftedWittenResolvent α).adjoint = thetaShiftedWittenResolvent α from
        thetaShiftedWittenResolvent_isSelfAdjoint α]
    exact LinearMap.ker_eq_bot.mpr (thetaShiftedWittenResolvent_injective α)
  rw [Submodule.dense_iff_topologicalClosure_eq_top]
  apply Submodule.orthogonal_eq_bot_iff.mp
  simpa using horth

theorem thetaShiftedWittenResolvent_compact (α : ℂ) :
    IsCompactOperator (thetaShiftedWittenResolvent α) :=
  (thetaShiftedSourceInverse_compact α).comp_clm
    (thetaShiftedSourceInverse α).adjoint

/-- Positive self-adjoint translated Witten Hamiltonian. -/
def thetaShiftedWittenHamiltonian (α : ℂ) : H →ₗ.[ℂ] H :=
  closedDenseInverse (thetaShiftedWittenResolvent α)

theorem thetaShiftedWittenHamiltonian_isClosed (α : ℂ) :
    (thetaShiftedWittenHamiltonian α).IsClosed :=
  closedDenseInverse_isClosed (thetaShiftedWittenResolvent α)
    (thetaShiftedWittenResolvent_injective α)

theorem thetaShiftedWittenHamiltonian_dense_domain (α : ℂ) :
    Dense ((thetaShiftedWittenHamiltonian α).domain : Set H) :=
  closedDenseInverse_dense_domain (thetaShiftedWittenResolvent α)
    (thetaShiftedWittenResolvent_dense_range α)

theorem thetaShiftedWittenHamiltonian_isSelfAdjoint (α : ℂ) :
    IsSelfAdjoint (thetaShiftedWittenHamiltonian α) :=
  closedDenseInverse_isSelfAdjoint (thetaShiftedWittenResolvent α)
    (thetaShiftedWittenResolvent_injective α)
      (thetaShiftedWittenResolvent_dense_range α)
        (thetaShiftedWittenResolvent_isSelfAdjoint α)

theorem thetaShiftedWittenHamiltonian_eq_adjointSquare (α : ℂ) :
    thetaShiftedWittenHamiltonian α =
      LinearPMap.adjointSquare (thetaShiftedWeightedDerivative α) := by
  rw [← thetaShiftedWeightedDerivativeModel_eq α]
  exact (closedHyperplaneInverse_adjointSquare_eq_closedDenseInverse
    (thetaShiftedRange α) (thetaShiftedSourceInverse α)
      (thetaShiftedSourceInverse_injective α)
        (by simpa only [ContinuousLinearMap.coe_coe] using
          thetaShiftedSourceInverse_dense_range α)).symm

theorem thetaShiftedWittenHamiltonian_kernel_eq_bot (α : ℂ) :
    (thetaShiftedWittenHamiltonian α).kernel = ⊥ :=
  closedDenseInverse_kernel_eq_bot (thetaShiftedWittenResolvent α)
    (thetaShiftedWittenResolvent_injective α)

theorem thetaShiftedWittenHamiltonian_hasCompactResolventAt_zero (α : ℂ) :
    LinearPMap.HasCompactResolventAt (thetaShiftedWittenHamiltonian α) 0 :=
  closedDenseInverse_hasCompactResolventAt_zero (thetaShiftedWittenResolvent α)
    (thetaShiftedWittenResolvent_injective α)
      (thetaShiftedWittenResolvent_compact α)

theorem thetaShiftedWittenHamiltonian_nonnegative (α : ℂ)
    (x : (thetaShiftedWittenHamiltonian α).domain) :
    0 ≤ (inner ℂ (thetaShiftedWittenHamiltonian α x) (x : H)).re := by
  have hxRange : (x : H) ∈ (thetaShiftedWittenResolvent α).range := by
    rw [← closedDenseInverse_domain (thetaShiftedWittenResolvent α)]
    exact x.property
  rcases hxRange with ⟨y, hy⟩
  have hApply := (closedDenseInverse_apply_C (thetaShiftedWittenResolvent α)
    (thetaShiftedWittenResolvent_injective α) y).2
  have heq : x = ⟨thetaShiftedWittenResolvent α y,
      (closedDenseInverse_apply_C (thetaShiftedWittenResolvent α)
        (thetaShiftedWittenResolvent_injective α) y).1⟩ := Subtype.ext hy.symm
  have hTx : thetaShiftedWittenHamiltonian α x = y := by
    exact (congrArg (thetaShiftedWittenHamiltonian α) heq).trans hApply
  calc
    0 ≤ (inner ℂ ((thetaShiftedSourceInverse α).adjoint y)
        ((thetaShiftedSourceInverse α).adjoint y)).re :=
      (inner_self_nonneg (𝕜 := ℂ)
        (x := (thetaShiftedSourceInverse α).adjoint y))
    _ = (inner ℂ y (thetaShiftedSourceInverse α
        ((thetaShiftedSourceInverse α).adjoint y))).re := by
      rw [(thetaShiftedSourceInverse α).adjoint_inner_left]
    _ = (inner ℂ (thetaShiftedWittenHamiltonian α x) (x : H)).re := by
      congr 2
      exact hTx.symm

/-- Exact strict positivity used in the card: nonnegative quadratic form and trivial kernel. -/
theorem thetaShiftedWittenHamiltonian_strictlyPositive (α : ℂ) :
    (∀ x : (thetaShiftedWittenHamiltonian α).domain,
      0 ≤ (inner ℂ (thetaShiftedWittenHamiltonian α x) (x : H)).re) ∧
      (thetaShiftedWittenHamiltonian α).kernel = ⊥ :=
  ⟨thetaShiftedWittenHamiltonian_nonnegative α,
    thetaShiftedWittenHamiltonian_kernel_eq_bot α⟩

end HedenmalmClosedWeightedDerivative

end

end RHTower
