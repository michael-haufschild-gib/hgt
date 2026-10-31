import GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticLoopCarrier
import GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticUnipotentIntegrality

/-!
# Actual restricted adelic unipotents and uniform coefficient streams

Evaluation in every completion identifies uniformly integral unipotent
matrices over the adele ring with the actual restricted positive unipotent
loop group. The exceptional finite-place set is common to all coefficients.
-/

namespace GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase
open HTGeometry.LoopEisenstein Filter
open scoped WithZero WithZeroMulInt
noncomputable section

/-- Evaluation of an actual adele at a finite place. -/
def finiteAdeleEvaluation (v : FinitePlace) : Adeles →+* v.adicCompletion K :=
  (RestrictedProduct.evalRingHom _ v).comp (RingHom.fst FiniteAdeles InfinityCompletion)

/-- Evaluate coefficients and take the canonical positive central lift. -/
def unipotentLocalLoopMap {F : Type*} [Field F] (f : Adeles →+* F) :
    unipotentCoefficientGroup Adeles →* LoopSL2 F :=
  (LoopSL2.positiveEmbedding F).comp
    ((unipotentCoefficientGroup F).subtype.comp (unipotentCoefficientMap f))

/-- Uniform coefficient integrality gives the actual full integral-loop restriction. -/
theorem unipotentLocalLoopMap_integral (v : FinitePlace)
    (g : unipotentCoefficientGroup Adeles)
    (hg : ∀ n, unipotentCoefficientStreamEquiv Adeles g n ∈ adeleIntegralAt v) :
    unipotentLocalLoopMap (finiteAdeleEvaluation v) g ∈ finiteIntegralLoop v := by
  apply (LoopSL2.positiveUnipotent_mem_integralLoop_iff
    (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰)
    (unipotentCoefficientMap (finiteAdeleEvaluation v) g)).mpr
  have hc := (unipotentStream_mem_subring_iff (adeleIntegralAt v) g).mp hg
  intro i j n
  change (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰)
    (PowerSeries.coeff n (PowerSeries.map (finiteAdeleEvaluation v) (g.1 i j))) ≤ 1
  rw [PowerSeries.coeff_map]
  exact hc i j n

/-- Actual positive unipotents inside the restricted central loop carrier. -/
def adelicPositiveUnipotent : Subgroup AdelicLoop where
  carrier := {g | (∀ v : FinitePlace,
      g.1 v ∈ LoopSL2.positiveUnipotent (v.adicCompletion K)) ∧
    g.2 ∈ LoopSL2.positiveUnipotent InfinityCompletion}
  one_mem' := ⟨fun v => (LoopSL2.positiveUnipotent (v.adicCompletion K)).one_mem,
    (LoopSL2.positiveUnipotent InfinityCompletion).one_mem⟩
  mul_mem' := by
    intro g h hg hh
    exact ⟨fun v => (LoopSL2.positiveUnipotent (v.adicCompletion K)).mul_mem (hg.1 v) (hh.1 v),
      (LoopSL2.positiveUnipotent InfinityCompletion).mul_mem hg.2 hh.2⟩
  inv_mem' := by
    intro g hg
    exact ⟨fun v => (LoopSL2.positiveUnipotent (v.adicCompletion K)).inv_mem (hg.1 v),
      (LoopSL2.positiveUnipotent InfinityCompletion).inv_mem hg.2⟩

/-- The actual restricted loop determined by a uniformly integral coefficient matrix. -/
def adelicUnipotentEmbedding : uniformlyIntegralUnipotent →* AdelicLoop where
  toFun g :=
    (⟨fun v => unipotentLocalLoopMap (finiteAdeleEvaluation v) g,
      ((mem_uniformlyIntegralUnipotent g).mp g.property).mono
        (fun v hv => unipotentLocalLoopMap_integral v g hv)⟩,
      unipotentLocalLoopMap (RingHom.snd FiniteAdeles InfinityCompletion) g)
  map_one' := by
    apply Prod.ext
    · apply RestrictedProduct.ext
      intro v
      exact (unipotentLocalLoopMap (finiteAdeleEvaluation v)).map_one
    · exact (unipotentLocalLoopMap (RingHom.snd FiniteAdeles InfinityCompletion)).map_one
  map_mul' g h := by
    apply Prod.ext
    · apply RestrictedProduct.ext
      intro v
      exact (unipotentLocalLoopMap (finiteAdeleEvaluation v)).map_mul g h
    · exact (unipotentLocalLoopMap (RingHom.snd FiniteAdeles InfinityCompletion)).map_mul g h

theorem adelicUnipotentEmbedding_mem (g : uniformlyIntegralUnipotent) :
    adelicUnipotentEmbedding g ∈ adelicPositiveUnipotent := by
  constructor
  · intro v
    exact ⟨unipotentCoefficientMap (finiteAdeleEvaluation v) g,
      (unipotentCoefficientMap (finiteAdeleEvaluation v) g).property, rfl⟩
  · exact ⟨unipotentCoefficientMap (RingHom.snd FiniteAdeles InfinityCompletion) g,
      (unipotentCoefficientMap (RingHom.snd FiniteAdeles InfinityCompletion) g).property, rfl⟩

/-- Finite and infinite local central lifts jointly distinguish every adele coefficient. -/
theorem unipotentLocalLoopMap_ext (g h : unipotentCoefficientGroup Adeles)
    (hf : ∀ v, unipotentLocalLoopMap (finiteAdeleEvaluation v) g =
      unipotentLocalLoopMap (finiteAdeleEvaluation v) h)
    (hi : unipotentLocalLoopMap (RingHom.snd FiniteAdeles InfinityCompletion : Adeles →+* InfinityCompletion) g =
      unipotentLocalLoopMap (RingHom.snd FiniteAdeles InfinityCompletion) h) : g = h := by
  apply (unipotentCoefficientStreamEquiv Adeles).injective
  funext n
  apply Prod.ext
  · apply RestrictedProduct.ext
    intro v
    have hm : unipotentCoefficientMap (finiteAdeleEvaluation v) g =
        unipotentCoefficientMap (finiteAdeleEvaluation v) h := by
      apply Subtype.ext
      exact LoopSL2.positiveEmbedding_injective (v.adicCompletion K)
        (hf v)
    have hs := congrArg
      (fun u => unipotentCoefficientStreamEquiv (v.adicCompletion K) u n) hm
    rw [unipotentStream_map, unipotentStream_map] at hs
    change (unipotentCoefficientStreamEquiv Adeles g n).1 v =
      (unipotentCoefficientStreamEquiv Adeles h n).1 v at hs
    exact hs
  · have hm : unipotentCoefficientMap (RingHom.snd FiniteAdeles InfinityCompletion : Adeles →+* InfinityCompletion) g =
        unipotentCoefficientMap (RingHom.snd FiniteAdeles InfinityCompletion) h := by
      apply Subtype.ext
      exact LoopSL2.positiveEmbedding_injective InfinityCompletion hi
    have hs := congrArg (fun u => unipotentCoefficientStreamEquiv InfinityCompletion u n) hm
    rw [unipotentStream_map, unipotentStream_map] at hs
    change (unipotentCoefficientStreamEquiv Adeles g n).2 =
      (unipotentCoefficientStreamEquiv Adeles h n).2 at hs
    exact hs

/-- No coefficient information is lost in the actual restricted central loop carrier. -/
theorem adelicUnipotentEmbedding_injective : Function.Injective adelicUnipotentEmbedding := by
  intro g h he
  apply Subtype.ext
  exact unipotentLocalLoopMap_ext g h
    (fun v => congrArg (fun z : AdelicLoop => z.1 v) he)
    (congrArg (fun z : AdelicLoop => z.2) he)

/-- Every actual restricted positive unipotent loop comes from one uniformly integral adele matrix. -/
theorem adelicUnipotentEmbedding_surjective (g : adelicPositiveUnipotent) :
    ∃ u : uniformlyIntegralUnipotent, adelicUnipotentEmbedding u = (g : AdelicLoop) := by
  choose uv huv hev using g.property.1
  obtain ⟨ui, hui, hei⟩ := g.property.2
  let uf (v : FinitePlace) : unipotentCoefficientGroup (v.adicCompletion K) := ⟨uv v, huv v⟩
  let uinf : unipotentCoefficientGroup InfinityCompletion := ⟨ui, hui⟩
  have hi : ∀ᶠ v : FinitePlace in cofinite, ∀ n,
      unipotentCoefficientStreamEquiv (v.adicCompletion K) (uf v) n ∈ v.adicCompletionIntegers K := by
    filter_upwards [g.1.1.property] with v hv
    have hc := (LoopSL2.positiveUnipotent_mem_integralLoop_iff
      (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰) (uf v)).mp
        (show LoopSL2.positiveEmbedding (v.adicCompletion K) (uf v) ∈ finiteIntegralLoop v by
          change LoopSL2.positiveEmbedding (v.adicCompletion K) (uv v) ∈ finiteIntegralLoop v
          rw [hev v]
          exact hv)
    exact (unipotentStream_mem_subring_iff (v.adicCompletionIntegers K).toSubring (uf v)).mpr hc
  let x : ℕ → Adeles := fun n =>
    (⟨fun v => unipotentCoefficientStreamEquiv (v.adicCompletion K) (uf v) n,
      hi.mono fun v hv => hv n⟩,
      unipotentCoefficientStreamEquiv InfinityCompletion uinf n)
  let u := (unipotentCoefficientStreamEquiv Adeles).symm x
  have hu : u ∈ uniformlyIntegralUnipotent := by
    apply (mem_uniformlyIntegralUnipotent u).mpr
    filter_upwards [hi] with v hv
    intro n
    change unipotentCoefficientStreamEquiv Adeles
      ((unipotentCoefficientStreamEquiv Adeles).symm x) n ∈ adeleIntegralAt v
    rw [Equiv.apply_symm_apply]
    exact hv n
  refine ⟨⟨u, hu⟩, ?_⟩
  apply Prod.ext
  · apply RestrictedProduct.ext
    intro v
    have hm : unipotentCoefficientMap (finiteAdeleEvaluation v) u = uf v := by
      apply (unipotentCoefficientStreamEquiv (v.adicCompletion K)).injective
      funext n
      rw [unipotentStream_map]
      change finiteAdeleEvaluation v
        (unipotentCoefficientStreamEquiv Adeles ((unipotentCoefficientStreamEquiv Adeles).symm x) n) = _
      rw [Equiv.apply_symm_apply]
      rfl
    change LoopSL2.positiveEmbedding (v.adicCompletion K)
      (unipotentCoefficientMap (finiteAdeleEvaluation v) u) = g.1.1 v
    rw [hm]
    exact hev v
  · have hm : unipotentCoefficientMap (RingHom.snd FiniteAdeles InfinityCompletion : Adeles →+* InfinityCompletion) u = uinf := by
      apply (unipotentCoefficientStreamEquiv InfinityCompletion).injective
      funext n
      rw [unipotentStream_map]
      change (unipotentCoefficientStreamEquiv Adeles
        ((unipotentCoefficientStreamEquiv Adeles).symm x) n).2 = _
      rw [Equiv.apply_symm_apply]
    change LoopSL2.positiveEmbedding InfinityCompletion
      (unipotentCoefficientMap (RingHom.snd FiniteAdeles InfinityCompletion) u) = g.1.2
    rw [hm]
    exact hei

/-- The uniform coefficient model and actual restricted unipotent carrier are isomorphic. -/
def adelicUnipotentEquiv : uniformlyIntegralUnipotent ≃* adelicPositiveUnipotent :=
  MulEquiv.ofBijective (adelicUnipotentEmbedding.codRestrict
    adelicPositiveUnipotent adelicUnipotentEmbedding_mem) ⟨by
      intro g h he
      exact adelicUnipotentEmbedding_injective (congrArg Subtype.val he), by
      intro g
      obtain ⟨u, hu⟩ := adelicUnipotentEmbedding_surjective g
      exact ⟨u, Subtype.ext hu⟩⟩

end
end GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase

#print axioms GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase.adelicUnipotentEmbedding_injective
#print axioms GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase.adelicUnipotentEmbedding_surjective
#print axioms GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase.adelicUnipotentEquiv
