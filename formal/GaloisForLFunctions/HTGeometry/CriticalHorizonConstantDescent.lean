import GaloisForLFunctions.HTGeometry.CriticalHorizonCharZeroConstants
import GaloisForLFunctions.HTGeometry.ConstantExtensionSheetDescent
import GaloisForLFunctions.HTGeometry.CriticalGeometricMonodromyAllFields

/-!
# The critical horizon over an arbitrary characteristic-zero base

Let `F` be a field of characteristic zero.  Coefficient extension to an algebraic closure `K`
carries the critical source and observation fields over `F` to those over `K`, sends the raw
coordinates to the raw coordinates and the observation to the observation, and both images are
algebraically independent over `K`.  The descent of the sheet action along the algebraic
extension `K/F` therefore applies:

* the degree of the critical source over the critical observation is the binomial multiplicity
  `choose(m+n, m)` over `F`;
* the normal-closure Galois group acts on the geometric sheets as the full symmetric group;
* no field lies strictly between the critical observation field and the critical source field.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The critical source field as a vector space over the critical observation field. -/
instance criticalObservationSourceModule (K : Type*) [Field K] (m n : ℕ) :
    Module (criticalObservationField K m n) (criticalSourceField K m n) :=
  Algebra.toModule

/-- The observation field sits in the source field by inclusion. -/
theorem coe_algebraMap_criticalObservationSource (K : Type*) [Field K] (m n : ℕ)
    (z : criticalObservationField K m n) :
    ((algebraMap (criticalObservationField K m n) (criticalSourceField K m n) z :
      criticalSourceField K m n) : genericJetField K (m + n)) = z :=
  IntermediateField.coe_inclusion _ z

variable (F : Type*) [Field F] {m n : ℕ}

private theorem baseChange_comp_criticalAmbientRaw (m n : ℕ) :
    (genericJetFieldBaseChangeAlgHom (k := F) (K := AlgebraicClosure F) (m + n)) ∘
        (fun j : Fin (m + n) => criticalAmbientRaw F m n (j : ℕ)) =
      fun j : Fin (m + n) => criticalAmbientRaw (AlgebraicClosure F) m n (j : ℕ) := by
  funext j
  exact genericJetFieldBaseChange_genericRaw _ (by omega)

private theorem baseChange_comp_criticalFieldObservation (m n : ℕ) :
    (genericJetFieldBaseChangeAlgHom (k := F) (K := AlgebraicClosure F) (m + n)) ∘
        criticalFieldObservation F m n =
      criticalFieldObservation (AlgebraicClosure F) m n := by
  funext s
  rcases s with i | j
  · exact genericJetFieldBaseChange_genericRaw _ (by omega)
  · exact genericJetFieldBaseChange_genericRecip _ _

private theorem criticalSourceField_eq_adjoin_baseChange (m n : ℕ) :
    criticalSourceField (AlgebraicClosure F) m n =
      IntermediateField.adjoin (AlgebraicClosure F) (Set.range
        ((genericJetFieldBaseChangeAlgHom (k := F) (K := AlgebraicClosure F) (m + n)) ∘
          (fun j : Fin (m + n) => criticalAmbientRaw F m n (j : ℕ)))) := by
  rw [baseChange_comp_criticalAmbientRaw]
  rfl

private theorem criticalObservationField_eq_adjoin_baseChange (m n : ℕ) :
    criticalObservationField (AlgebraicClosure F) m n =
      IntermediateField.adjoin (AlgebraicClosure F) (Set.range
        ((genericJetFieldBaseChangeAlgHom (k := F) (K := AlgebraicClosure F) (m + n)) ∘
          criticalFieldObservation F m n)) := by
  rw [baseChange_comp_criticalFieldObservation]
  rfl

private theorem algebraicIndependent_baseChange_criticalAmbientRaw (m n : ℕ) :
    AlgebraicIndependent (AlgebraicClosure F)
      ((genericJetFieldBaseChangeAlgHom (k := F) (K := AlgebraicClosure F) (m + n)) ∘
        (fun j : Fin (m + n) => criticalAmbientRaw F m n (j : ℕ))) := by
  rw [baseChange_comp_criticalAmbientRaw]
  exact algebraicIndependent_criticalAmbientRaw (AlgebraicClosure F) m n

variable [CharZero F]

private theorem algebraicIndependent_baseChange_criticalFieldObservation
    (hm : 0 < m) (hn : 0 < n) :
    AlgebraicIndependent (AlgebraicClosure F)
      ((genericJetFieldBaseChangeAlgHom (k := F) (K := AlgebraicClosure F) (m + n)) ∘
        criticalFieldObservation F m n) := by
  rw [baseChange_comp_criticalFieldObservation]
  exact algebraicIndependent_criticalFieldObservation (AlgebraicClosure F) hm hn

/-- **Descent of the critical horizon to an arbitrary characteristic-zero base.** -/
theorem criticalHorizon_constantDescent (hm : 0 < m) (hn : 0 < n) :
    Module.finrank (criticalObservationField F m n) (criticalSourceField F m n) =
        Module.finrank (criticalObservationField (AlgebraicClosure F) m n)
          (criticalSourceField (AlgebraicClosure F) m n) ∧
      (Function.Bijective (sheetAction (criticalObservationField (AlgebraicClosure F) m n)
          (criticalSourceField (AlgebraicClosure F) m n)) →
        Function.Bijective (sheetAction (criticalObservationField F m n)
          (criticalSourceField F m n))) := by
  haveI := criticalSourceField_finiteDimensional_criticalObservationField_charZero F hm hn
  haveI := criticalSourceField_finiteDimensional_criticalObservationField
    (AlgebraicClosure F) hm hn
  exact sheetAction_descent_of_constantExtension
    (O := criticalObservationField F m n) (S := criticalSourceField F m n)
    (O' := criticalObservationField (AlgebraicClosure F) m n)
    (S' := criticalSourceField (AlgebraicClosure F) m n)
    (genericJetFieldBaseChangeAlgHom (k := F) (K := AlgebraicClosure F) (m + n))
    (fun j : Fin (m + n) => criticalAmbientRaw F m n (j : ℕ)) (criticalFieldObservation F m n)
    rfl rfl (criticalSourceField_eq_adjoin_baseChange F m n)
    (criticalObservationField_eq_adjoin_baseChange F m n)
    (algebraicIndependent_baseChange_criticalAmbientRaw F m n)
    (algebraicIndependent_baseChange_criticalFieldObservation F hm hn)
    (by simp [add_comm]) (coe_algebraMap_criticalObservationSource F m n)
    (coe_algebraMap_criticalObservationSource (AlgebraicClosure F) m n)

/-- **Exact degree over every characteristic-zero base.** -/
theorem finrank_criticalSourceField_eq_criticalHorizonMultiplicity_charZero
    (hm : 0 < m) (hn : 0 < n) :
    Module.finrank (criticalObservationField F m n) (criticalSourceField F m n) =
      criticalHorizonMultiplicity m n :=
  (criticalHorizon_constantDescent F hm hn).1.trans
    (finrank_criticalSourceField_eq_criticalHorizonMultiplicity (AlgebraicClosure F) hm hn)

/-- **Full symmetric sheet action over every characteristic-zero base.** -/
theorem sheetAction_criticalSourceField_bijective_charZero (hm : 0 < m) (hn : 0 < n) :
    Function.Bijective
      (sheetAction (criticalObservationField F m n) (criticalSourceField F m n)) := by
  refine (criticalHorizon_constantDescent F hm hn).2 ⟨?_, ?_⟩
  · exact criticalNormalClosureAction_injective (AlgebraicClosure F) hm hn
  · intro g
    have hg : g ∈ criticalGeometricMonodromy (AlgebraicClosure F) m n := by
      rw [criticalGeometricMonodromy_eq_top_charZero (AlgebraicClosure F) hm hn]
      trivial
    exact hg

/-- **Full symmetric critical geometric monodromy over every characteristic-zero base.** -/
theorem criticalGeometricMonodromy_eq_top_of_charZero_base (hm : 0 < m) (hn : 0 < n) :
    criticalGeometricMonodromy F m n = ⊤ := by
  apply top_unique
  intro g _
  exact (sheetAction_criticalSourceField_bijective_charZero F hm hn).2 g

/-- **No intermediate field over every characteristic-zero base.** -/
theorem eq_bot_or_eq_top_of_le_criticalSourceField_charZero (hm : 0 < m) (hn : 0 < n)
    (M : IntermediateField (criticalObservationField F m n) (criticalSourceField F m n)) :
    M = ⊥ ∨ M = ⊤ := by
  haveI := criticalSourceField_finiteDimensional_criticalObservationField_charZero F hm hn
  haveI : CharZero (criticalObservationField F m n) :=
    charZero_of_injective_algebraMap (algebraMap F _).injective
  exact eq_bot_or_eq_top_of_sheetAction_surjective _ _
    (sheetAction_criticalSourceField_bijective_charZero F hm hn).2 M

end

end GaloisForLFunctions.HTGeometry
