import GaloisForLFunctions.HTGeometry.GenericJetInjectivity

/-!
# Hasse detection by universal formal jets

A finite differential polynomial is evaluated on the formal jet vector of every complex power
series.  The resulting universal profile is faithful, so equality of every formal-jet evaluation
detects equality of the global differential polynomials.
-/

namespace GaloisForLFunctions

noncomputable section

/-- Simultaneous evaluation of a finite differential polynomial on the formal jets of all complex
power series. -/
def formalJetsEvaluationAlgHom (n : ℕ) :
    MvPolynomial (Fin (n + 2)) ℂ →ₐ[ℂ]
      (PowerSeries ℂ → PowerSeries ℂ) where
  toFun P G := MvPolynomial.aeval (formalJets n G) P
  map_one' := by funext G; exact map_one _
  map_mul' P Q := by funext G; exact map_mul _ _ _
  map_zero' := by funext G; exact map_zero _
  map_add' P Q := by funext G; exact map_add _ _ _
  commutes' c := by funext G; simp

/-- The universal formal-jet evaluation profile is faithful. -/
theorem formalJetsEvaluationAlgHom_injective (n : ℕ) :
    Function.Injective (formalJetsEvaluationAlgHom n) := by
  intro P Q h
  rw [← sub_eq_zero]
  apply formalJets_substitution_injective
  intro G
  have hG := congrFun h G
  change MvPolynomial.aeval (formalJets n G) P =
    MvPolynomial.aeval (formalJets n G) Q at hG
  rw [map_sub, hG, sub_self]

/-- Finite differential polynomials are algebra-equivalent to the universal formal-jet profiles
they realize. -/
noncomputable def formalJetsEvaluationHasseEquivRange (n : ℕ) :
    MvPolynomial (Fin (n + 2)) ℂ ≃ₐ[ℂ]
      AlgHom.range (formalJetsEvaluationAlgHom n) :=
  AlgEquiv.ofBijective (AlgHom.rangeRestrict (formalJetsEvaluationAlgHom n))
    ⟨fun _ _ h => formalJetsEvaluationAlgHom_injective n (congrArg Subtype.val h),
      AlgHom.rangeRestrict_surjective _⟩

/-- The realized-profile equivalence evaluates by universal formal-jet substitution. -/
@[simp] theorem formalJetsEvaluationHasseEquivRange_apply
    (n : ℕ) (P : MvPolynomial (Fin (n + 2)) ℂ) :
    (formalJetsEvaluationHasseEquivRange n P).1 = formalJetsEvaluationAlgHom n P := by
  rfl

/-- Two finite differential polynomials agree exactly when all their formal-jet evaluations on
complex power series agree. -/
theorem formalJets_congr_hasse_iff
    (n : ℕ) (P Q : MvPolynomial (Fin (n + 2)) ℂ) :
    (∀ G : PowerSeries ℂ,
      MvPolynomial.aeval (formalJets n G) P =
        MvPolynomial.aeval (formalJets n G) Q) ↔ P = Q := by
  constructor
  · intro h
    apply formalJetsEvaluationAlgHom_injective n
    funext G
    exact h G
  · rintro rfl G
    rfl

end


end GaloisForLFunctions
