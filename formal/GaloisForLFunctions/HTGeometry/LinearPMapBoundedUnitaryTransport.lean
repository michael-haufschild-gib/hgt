import GaloisForLFunctions.HTGeometry.MaximalRealL2Multiplication

/-!
# Closed linear partial maps under bounded perturbation and unitary transport

This module supplies graph-level infrastructure for closed unbounded operators. Adding an
everywhere-defined bounded operator, multiplying by a nonzero scalar, and conjugating by a unitary
all preserve closedness. The unitary-conjugate operator retains its exact pulled-back domain.
-/

open Set
open scoped LinearPMap

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]

/-- Adding a bounded everywhere-defined operator preserves closedness and the original domain. -/
theorem LinearPMap.IsClosed.continuousLinearMap_vadd
    {T : H →ₗ.[ℂ] H} (hT : T.IsClosed) (B : H →L[ℂ] H) :
    (B.toLinearMap +ᵥ T).IsClosed := by
  rw [LinearPMap.IsClosed]
  have hgraph : ((B.toLinearMap +ᵥ T).graph : Set (H × H)) =
      (fun p : H × H => (p.1, p.2 - B p.1)) ⁻¹' (T.graph : Set (H × H)) := by
    ext p
    change p ∈ (B.toLinearMap +ᵥ T).graph ↔ (p.1, p.2 - B p.1) ∈ T.graph
    rw [LinearPMap.mem_graph_iff, LinearPMap.mem_graph_iff]
    constructor
    · rintro ⟨x, hx, hval⟩
      let xT : T.domain := ⟨(x : H), by
        simpa only [LinearPMap.vadd_domain] using x.property⟩
      refine ⟨xT, hx, ?_⟩
      change B (x : H) + T xT = p.2 at hval
      rw [← hx]
      exact eq_sub_of_add_eq' hval
    · rintro ⟨x, hx, hval⟩
      let xBT : (B.toLinearMap +ᵥ T).domain := ⟨(x : H), by
        simpa only [LinearPMap.vadd_domain] using x.property⟩
      refine ⟨xBT, hx, ?_⟩
      change T x = p.2 - B p.1 at hval
      change B (x : H) + T x = p.2
      rw [hx, hval]
      abel
  rw [hgraph]
  exact hT.preimage
    (continuous_fst.prodMk (continuous_snd.sub (B.continuous.comp continuous_fst)))

/-- Nonzero scalar multiplication preserves closedness of a partial linear operator. -/
theorem LinearPMap.IsClosed.smul_of_ne {T : H →ₗ.[ℂ] H} (hT : T.IsClosed)
    {c : ℂ} (hc : c ≠ 0) : (c • T).IsClosed := by
  rw [LinearPMap.IsClosed]
  have hgraph : ((c • T).graph : Set (H × H)) =
      (fun p : H × H => (p.1, c⁻¹ • p.2)) ⁻¹' (T.graph : Set (H × H)) := by
    ext p
    change p ∈ (c • T).graph ↔ (p.1, c⁻¹ • p.2) ∈ T.graph
    rw [LinearPMap.mem_graph_iff, LinearPMap.mem_graph_iff]
    constructor
    · rintro ⟨x, hx, hval⟩
      let xT : T.domain := ⟨(x : H), by
        simpa only [LinearPMap.smul_domain] using x.property⟩
      refine ⟨xT, hx, ?_⟩
      change c • T xT = p.2 at hval
      rw [← hval, inv_smul_smul₀ hc]
    · rintro ⟨x, hx, hval⟩
      let xcT : (c • T).domain := ⟨(x : H), by
        simpa only [LinearPMap.smul_domain] using x.property⟩
      refine ⟨xcT, hx, ?_⟩
      change T x = c⁻¹ • p.2 at hval
      change c • T x = p.2
      rw [hval, smul_inv_smul₀ hc]
  rw [hgraph]
  exact hT.preimage
    (continuous_fst.prodMk (continuous_const.smul continuous_snd))

def unitaryConjugateDomainMap {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (U : H ≃ₗᵢ[ℂ] K) (T : K →ₗ.[ℂ] K) :
    T.domain.comap U.toLinearEquiv.toLinearMap →ₗ[ℂ] T.domain where
  toFun := fun f => ⟨U f, f.property⟩
  map_add' f g := by
    apply Subtype.ext
    simp
  map_smul' c f := by
    apply Subtype.ext
    simp

/-- Unitary conjugation of a partially defined Hilbert-space operator. -/
def unitaryConjugateLinearPMap {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (U : H ≃ₗᵢ[ℂ] K) (T : K →ₗ.[ℂ] K) : H →ₗ.[ℂ] H where
  domain := T.domain.comap U.toLinearEquiv.toLinearMap
  toFun := U.symm.toLinearEquiv.toLinearMap.comp
    (T.toFun.comp (unitaryConjugateDomainMap U T))

theorem unitaryConjugateLinearPMap_domain {K : Type*} [NormedAddCommGroup K]
    [InnerProductSpace ℂ K] (U : H ≃ₗᵢ[ℂ] K) (T : K →ₗ.[ℂ] K) :
    (unitaryConjugateLinearPMap U T).domain =
      T.domain.comap U.toLinearEquiv.toLinearMap := rfl

@[simp] theorem unitaryConjugateLinearPMap_apply {K : Type*} [NormedAddCommGroup K]
    [InnerProductSpace ℂ K] (U : H ≃ₗᵢ[ℂ] K) (T : K →ₗ.[ℂ] K)
    (f : (unitaryConjugateLinearPMap U T).domain) :
    unitaryConjugateLinearPMap U T f =
      U.symm (T (unitaryConjugateDomainMap U T f)) := rfl

theorem LinearPMap.IsClosed.unitaryConjugate {K : Type*} [NormedAddCommGroup K]
    [InnerProductSpace ℂ K] {U : H ≃ₗᵢ[ℂ] K} {T : K →ₗ.[ℂ] K}
    (hT : T.IsClosed) : (unitaryConjugateLinearPMap U T).IsClosed := by
  rw [LinearPMap.IsClosed]
  have hgraph : ((unitaryConjugateLinearPMap U T).graph : Set (H × H)) =
      (fun p : H × H => (U p.1, U p.2)) ⁻¹' (T.graph : Set (K × K)) := by
    ext p
    change p ∈ (unitaryConjugateLinearPMap U T).graph ↔ (U p.1, U p.2) ∈ T.graph
    rw [LinearPMap.mem_graph_iff, LinearPMap.mem_graph_iff]
    constructor
    · rintro ⟨x, hx, hval⟩
      let xT : T.domain := unitaryConjugateDomainMap U T x
      refine ⟨xT, congrArg U hx, ?_⟩
      change U.symm (T xT) = p.2 at hval
      calc
        T xT = U (U.symm (T xT)) := (U.apply_symm_apply _).symm
        _ = U p.2 := congrArg U hval
    · rintro ⟨x, hx, hval⟩
      let xU : (unitaryConjugateLinearPMap U T).domain :=
        ⟨U.symm x, by
          change U (U.symm (x : K)) ∈ T.domain
          simpa only [LinearIsometryEquiv.apply_symm_apply] using x.property⟩
      refine ⟨xU, ?_, ?_⟩
      · simpa only [LinearIsometryEquiv.symm_apply_apply] using congrArg U.symm hx
      · apply U.injective
        simp only [unitaryConjugateLinearPMap_apply, LinearIsometryEquiv.apply_symm_apply]
        have hxdom : unitaryConjugateDomainMap U T xU = x := by
          apply Subtype.ext
          simp only [unitaryConjugateDomainMap, LinearMap.coe_mk, AddHom.coe_mk,
            xU, LinearIsometryEquiv.apply_symm_apply]
        rw [hxdom]
        exact hval
  rw [hgraph]
  exact hT.preimage
    ((U.continuous.comp continuous_fst).prodMk (U.continuous.comp continuous_snd))

end

end GaloisForLFunctions.HTGeometry

