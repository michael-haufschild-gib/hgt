import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.PadicCompletionNormalization

/-! A continuous p-adic identification of a number-field completion
determines the prime by residue cardinality and the map by density. -/

noncomputable section

open NumberField IsDedekindDomain WindowedLandauTheory.ConjugateSelfDual

namespace GlobalTheory.Reciprocity

variable {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
  {p q : ℕ} [Fact p.Prime] [Fact q.Prime]

theorem padicPrime_eq_of_continuous_completionEquiv
    (i : ℚ_[p] ≃+* v.adicCompletion K) (j : ℚ_[q] ≃+* v.adicCompletion K)
    (hi : Continuous i) (hj : Continuous j) : p = q :=
  (padicIso_place_normalization v i hi).2.2.1.symm.trans
    (padicIso_place_normalization v j hj).2.2.1

theorem padicCompletionEquiv_eq_of_continuous
    (i j : ℚ_[p] ≃+* v.adicCompletion K) (hi : Continuous i) (hj : Continuous j) : i = j := by
  have h : (i : ℚ_[p] → v.adicCompletion K) = (j : ℚ_[p] → v.adicCompletion K) :=
    (Padic.denseRange_ratCast (p := p)).equalizer hi hj (funext fun r => by
      change i (r : ℚ_[p]) = j (r : ℚ_[p])
      rw [map_ratCast, map_ratCast])
  exact RingEquiv.ext (congrFun h)

end GlobalTheory.Reciprocity

#print axioms GlobalTheory.Reciprocity.padicPrime_eq_of_continuous_completionEquiv
#print axioms GlobalTheory.Reciprocity.padicCompletionEquiv_eq_of_continuous
