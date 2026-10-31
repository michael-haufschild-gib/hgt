import GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticUnipotentCarrier
import GaloisForLFunctions.HTGeometry.LoopEisenstein.PositiveUnipotentFieldMap

/-!
# The actual arithmetic intersection of elliptic unipotents

Faithful descent at infinity forces an arithmetic positive unipotent loop
to have a rational positive matrix lift. Joint local injectivity identifies
its diagonal coefficients, including their single finite exceptional set.
-/

namespace GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase
open HTGeometry.LoopEisenstein Filter
noncomputable section

private theorem unipotentLocalLoop_diagonal {F : Type*} [Field F]
    (ι : K →+* F) (f : Adeles →+* F) (hf : ∀ z, f (adeleEmbedding z) = ι z)
    (r : unipotentCoefficientGroup K) :
    unipotentLocalLoopMap f (unipotentCoefficientMap adeleEmbedding r) =
      LoopSL2.fieldMap ι (LoopSL2.positiveEmbedding K r) := by
  have hm : unipotentCoefficientMap f (unipotentCoefficientMap adeleEmbedding r) =
      unipotentCoefficientMap ι r := by
    apply (unipotentCoefficientStreamEquiv F).injective
    funext n
    rw [unipotentStream_map, unipotentStream_map, unipotentStream_map]
    exact hf _
  change LoopSL2.positiveEmbedding F
    (unipotentCoefficientMap f (unipotentCoefficientMap adeleEmbedding r)) = _
  rw [hm]
  exact (LoopSL2.fieldMap_positiveEmbedding ι r).symm

/-- The actual arithmetic intersection contains exactly the uniformly integral rational matrices. -/
theorem adelicUnipotentEmbedding_mem_arithmetic_iff (g : uniformlyIntegralUnipotent) :
    adelicUnipotentEmbedding g ∈ arithmeticLoopGroup ↔
      ∃ r : uniformlyIntegralRationalUnipotent,
        unipotentCoefficientMap adeleEmbedding r = (g : unipotentCoefficientGroup Adeles) := by
  constructor
  · rintro ⟨r, hr⟩
    have hi : LoopSL2.fieldMap infinityEmbedding (r : LoopSL2 K) ∈
        LoopSL2.positiveUnipotent InfinityCompletion := by
      have h := (adelicUnipotentEmbedding_mem g).2
      have he := congrArg (fun z : AdelicLoop => z.2) hr
      change LoopSL2.fieldMap infinityEmbedding (r : LoopSL2 K) =
        (adelicUnipotentEmbedding g).2 at he
      rw [he]
      exact h
    have hu := (LoopSL2.fieldMap_mem_positiveUnipotent_iff infinityEmbedding r).mp hi
    obtain ⟨u, hu, he⟩ := hu
    let q : unipotentCoefficientGroup K := ⟨u, hu⟩
    have hq : unipotentCoefficientMap adeleEmbedding q = (g : unipotentCoefficientGroup Adeles) := by
      apply unipotentLocalLoopMap_ext
      · intro v
        exact (unipotentLocalLoop_diagonal (algebraMap K (v.adicCompletion K))
          (finiteAdeleEvaluation v) (fun _ => rfl) q).trans
          ((congrArg (LoopSL2.fieldMap (algebraMap K (v.adicCompletion K))) he).trans
            (congrArg (fun z : AdelicLoop => z.1 v) hr))
      · exact (unipotentLocalLoop_diagonal infinityEmbedding
          (RingHom.snd FiniteAdeles InfinityCompletion) (fun _ => rfl) q).trans
          ((congrArg (LoopSL2.fieldMap infinityEmbedding) he).trans
            (congrArg (fun z : AdelicLoop => z.2) hr))
    have hqu : q ∈ uniformlyIntegralRationalUnipotent := by
      change unipotentCoefficientMap adeleEmbedding q ∈ uniformlyIntegralUnipotent
      rw [hq]
      exact g.property
    exact ⟨⟨q, hqu⟩, hq⟩
  · rintro ⟨r, hr⟩
    let k : LoopSL2 K := LoopSL2.positiveEmbedding K r
    have hf (v : FinitePlace) : LoopSL2.fieldMap (algebraMap K (v.adicCompletion K)) k =
        unipotentLocalLoopMap (finiteAdeleEvaluation v) g :=
      (unipotentLocalLoop_diagonal (algebraMap K (v.adicCompletion K))
        (finiteAdeleEvaluation v) (fun _ => rfl) r).symm.trans
          (congrArg (unipotentLocalLoopMap (finiteAdeleEvaluation v)) hr)
    have hi : LoopSL2.fieldMap infinityEmbedding k =
        unipotentLocalLoopMap (RingHom.snd FiniteAdeles InfinityCompletion : Adeles →+* InfinityCompletion) g :=
      (unipotentLocalLoop_diagonal infinityEmbedding
        (RingHom.snd FiniteAdeles InfinityCompletion) (fun _ => rfl) r).symm.trans
          (congrArg (unipotentLocalLoopMap (RingHom.snd FiniteAdeles InfinityCompletion : Adeles →+* InfinityCompletion)) hr)
    have hk : k ∈ restrictedRationalLoop := by
      change ∀ᶠ v : FinitePlace in cofinite, diagonalFiniteLoop k v ∈ finiteIntegralLoop v
      filter_upwards [(adelicUnipotentEmbedding g).1.property] with v hv
      change LoopSL2.fieldMap (algebraMap K (v.adicCompletion K)) k ∈ finiteIntegralLoop v
      rw [hf v]
      exact hv
    refine ⟨⟨k, hk⟩, ?_⟩
    apply Prod.ext
    · apply RestrictedProduct.ext
      exact hf
    · exact hi

end
end GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase

#print axioms GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase.adelicUnipotentEmbedding_mem_arithmetic_iff
