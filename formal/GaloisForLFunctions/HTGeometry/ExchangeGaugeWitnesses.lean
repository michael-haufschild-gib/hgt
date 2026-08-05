import GaloisForLFunctions.HTGeometry.KolchinExchangeGaugeObstruction

/-!
# Exchange gauges exist

Two exchange laws are gauge equivalent when a nonzero differentially algebraic multiplier carries
one to the other.  The relation is realized by the embedded coefficients: every nonzero scalar of
the coefficient field is a legitimate gauge, because embedded coefficients are differentially
algebraic and the automorphism fixes them.  In particular the relation is reflexive, so the
obstruction theorems it feeds are never vacuous, and a gauge scales an exchange law by any nonzero
coefficient ratio.
-/

open scoped Differential

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Differential E]

/-- **Every nonzero coefficient is an exchange gauge.**  It is differentially algebraic and fixed by
the automorphism, so it carries an exchange law to itself. -/
theorem daExchangeGaugeEquivalent_self_of_algebraMap (σ : DifferentialAlgEquiv F E)
    {c : F} (hc : c ≠ 0) (S : E) :
    DAExchangeGaugeEquivalent σ S S := by
  have hne : algebraMap F E c ≠ 0 := (map_ne_zero_iff _ (algebraMap F E).injective).mpr hc
  refine ⟨algebraMap F E c, hne, differentialAlgebraicOver_algebraMap c, ?_⟩
  rw [AlgEquiv.commutes]
  field_simp

/-- The exchange-gauge relation is reflexive. -/
theorem daExchangeGaugeEquivalent_refl (σ : DifferentialAlgEquiv F E) (S : E) :
    DAExchangeGaugeEquivalent σ S S :=
  daExchangeGaugeEquivalent_self_of_algebraMap σ one_ne_zero S

/-- Every exchange law is gauge equivalent to something. -/
theorem exists_daExchangeGaugeEquivalent (σ : DifferentialAlgEquiv F E) (S : E) :
    ∃ T, DAExchangeGaugeEquivalent σ S T :=
  ⟨S, daExchangeGaugeEquivalent_refl σ S⟩

end

end GaloisForLFunctions.HTGeometry
