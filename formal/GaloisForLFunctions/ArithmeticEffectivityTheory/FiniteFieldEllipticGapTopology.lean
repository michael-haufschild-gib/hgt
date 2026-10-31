import GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticQuotientHaar
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# Second countability of the actual elliptic additive domain

Finite generation makes the actual set of finite places countable. The
compact additive domain embeds in the countable product of proper local
completions, giving second countability and jointly measurable addition.
-/

namespace GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase
open IsDedekindDomain
noncomputable section


/-- Finite generation makes the ideals of the actual countable integer ring countable. -/
instance idealRingOfIntegers_countable : Countable (Ideal RingOfIntegers) := by
  have hs : Function.Surjective (fun s : Finset RingOfIntegers => Ideal.span (s : Set RingOfIntegers)) := by
    intro I
    exact IsNoetherian.noetherian I
  exact hs.countable

/-- The actual finite places form a countable set. -/
instance finitePlace_countable : Countable FinitePlace := by
  have hi : Function.Injective (fun v : FinitePlace => v.asIdeal) := by
    intro v w h
    exact HeightOneSpectrum.ext h
  exact hi.countable

/-- The actual finite completion inherits second countability from its proper metric. -/
instance finiteCompletion_secondCountable (v : FinitePlace) : SecondCountableTopology (v.adicCompletion K) := by
  letI : NormedField (v.valuation K).Completion :=
    HTGeometry.DiscreteValuedCompletion.completedNormedField (WithVal (v.valuation K))
  letI : ProperSpace (v.valuation K).Completion :=
    HTGeometry.DiscreteValuedCompletion.completedProperSpace (WithVal (v.valuation K))
  letI : SecondCountableTopology (v.valuation K).Completion := secondCountable_of_proper
  exact (HeightOneSpectrum.adicCompletion.uniformEquiv K v).toHomeomorph.isEmbedding.secondCountableTopology

/-- The actual infinity completion has a countable topology basis. -/
instance infinityCompletion_secondCountable : SecondCountableTopology InfinityCompletion := by
  letI : NormedField InfinityCompletion :=
    HTGeometry.DiscreteValuedCompletion.completedNormedField (WithVal infinityValuation)
  letI : ProperSpace InfinityCompletion :=
    HTGeometry.DiscreteValuedCompletion.completedProperSpace (WithVal infinityValuation)
  exact secondCountable_of_proper

/-- The compact additive domain embeds into the countable product of actual completions. -/
instance ellipticAdditiveDomain_secondCountable : SecondCountableTopology ellipticAdditiveDomain := by
  let f : ellipticAdditiveDomain → ((v : FinitePlace) → v.adicCompletion K) × InfinityCompletion :=
    fun d => ((fun v => (d : Adeles).1 v), (d : Adeles).2)
  have hf : Continuous f :=
    (RestrictedProduct.continuous_coe.comp (continuous_fst.comp continuous_subtype_val)).prodMk
      (continuous_snd.comp continuous_subtype_val)
  have hi : Function.Injective f := by
    intro d e h
    apply Subtype.ext
    apply Prod.ext
    · apply RestrictedProduct.ext
      intro v
      exact congrArg (fun x : ((v : FinitePlace) → v.adicCompletion K) × InfinityCompletion => x.1 v) h
    · exact congrArg (fun x : ((v : FinitePlace) → v.adicCompletion K) × InfinityCompletion => x.2) h
  exact (hf.isClosedEmbedding hi).isEmbedding.secondCountableTopology

/-- Addition is jointly measurable for the actual domain Borel structure. -/
instance ellipticAdditiveDomain_measurableAdd₂ : MeasurableAdd₂ ellipticAdditiveDomain := ⟨continuous_add.measurable⟩

end
end GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase

#print axioms GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase.finitePlace_countable
#print axioms GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase.ellipticAdditiveDomain_secondCountable
#print axioms GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase.ellipticAdditiveDomain_measurableAdd₂
