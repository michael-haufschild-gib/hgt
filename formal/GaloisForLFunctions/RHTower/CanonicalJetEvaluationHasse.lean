import GaloisForLFunctions.HTGeometry.FiniteEvaluationHasse
import GaloisForLFunctions.RHTower.ZetaArbitraryJetHilbertReconstruction
import GaloisForLFunctions.RHTower.XiCanonicalJetSuccessorGaussianCurvatureUniversalityLaw

/-!
# Finite evaluation Hasse principles for zeta and completed Xi jets

The unconditional finite reconstruction packets for the initial Riemann-zeta jet and canonical
completed-Xi jet are promoted to explicit Hasse data.  Their chosen complex evaluation places
jointly detect coefficient equality and vanishing, reconstruct all global coefficients, and expose
one local witness whenever two global jet combinations differ.
-/

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry

/-- Chosen finite Hasse evaluation packet for the initial Riemann-zeta jet. -/
noncomputable def riemannZetaInitialJetHasseData (d : ℕ) :=
  finiteEvaluationHasseDataOf
    (GaloisForLFunctions.RHTower.riemannZetaInitialJet_finiteEvaluationHilbertReconstruction d)

/-- Chosen finite Hasse evaluation packet for the canonical completed-Xi jet. -/
noncomputable def xiCanonicalJetHasseData (d : ℕ) :=
  finiteEvaluationHasseDataOf
    (xiCanonicalDerivativeOrder_finiteEvaluationHilbertReconstruction d)

/-- Initial zeta-jet coefficients are recovered exactly from the chosen local values. -/
theorem riemannZetaInitialJetHasse_reconstruct (d : ℕ) (a : Fin d → ℂ) :
    (riemannZetaInitialJetHasseData d).reconstruct
        ((riemannZetaInitialJetHasseData d).localPacket a) = a :=
  (riemannZetaInitialJetHasseData d).reconstruct_localPacket a

/-- Equality of initial zeta jets is detected at every chosen evaluation place. -/
theorem riemannZetaInitialJet_congr_hasse_iff (d : ℕ) (a b : Fin d → ℂ) :
    (∀ i, (riemannZetaInitialJetHasseData d).localPacket a i =
      (riemannZetaInitialJetHasseData d).localPacket b i) ↔ a = b :=
  (riemannZetaInitialJetHasseData d).localPacket_congr_hasse_iff a b

/-- An initial zeta jet is zero exactly when every chosen local value is zero. -/
theorem riemannZetaInitialJet_eq_zero_hasse_iff (d : ℕ) (a : Fin d → ℂ) :
    (∀ i, (riemannZetaInitialJetHasseData d).localPacket a i = 0) ↔ a = 0 :=
  (riemannZetaInitialJetHasseData d).localPacket_eq_zero_hasse_iff a

/-- Distinct initial zeta jets differ at one chosen evaluation place. -/
theorem riemannZetaInitialJet_ne_iff_exists_localWitness
    (d : ℕ) (a b : Fin d → ℂ) :
    a ≠ b ↔ ∃ i, (riemannZetaInitialJetHasseData d).localPacket a i ≠
      (riemannZetaInitialJetHasseData d).localPacket b i :=
  (riemannZetaInitialJetHasseData d).ne_iff_exists_localPacket_ne a b

/-- Every packet at the chosen zeta evaluation places has one unique global initial-jet
coefficient family. -/
theorem riemannZetaInitialJetHasse_existsUnique (d : ℕ) (packet : Fin d → ℂ) :
    ∃! a : Fin d → ℂ, (riemannZetaInitialJetHasseData d).localPacket a = packet :=
  (riemannZetaInitialJetHasseData d).localPacket_existsUnique packet

/-- Canonical completed-Xi jet coefficients are recovered exactly from chosen local values. -/
theorem xiCanonicalJetHasse_reconstruct (d : ℕ) (a : Fin d → ℂ) :
    (xiCanonicalJetHasseData d).reconstruct
        ((xiCanonicalJetHasseData d).localPacket a) = a :=
  (xiCanonicalJetHasseData d).reconstruct_localPacket a

/-- Equality of canonical completed-Xi jets is detected at every chosen evaluation place. -/
theorem xiCanonicalJet_congr_hasse_iff (d : ℕ) (a b : Fin d → ℂ) :
    (∀ i, (xiCanonicalJetHasseData d).localPacket a i =
      (xiCanonicalJetHasseData d).localPacket b i) ↔ a = b :=
  (xiCanonicalJetHasseData d).localPacket_congr_hasse_iff a b

/-- A canonical completed-Xi jet is zero exactly when every chosen local value is zero. -/
theorem xiCanonicalJet_eq_zero_hasse_iff (d : ℕ) (a : Fin d → ℂ) :
    (∀ i, (xiCanonicalJetHasseData d).localPacket a i = 0) ↔ a = 0 :=
  (xiCanonicalJetHasseData d).localPacket_eq_zero_hasse_iff a

/-- Distinct canonical completed-Xi jets differ at one chosen evaluation place. -/
theorem xiCanonicalJet_ne_iff_exists_localWitness
    (d : ℕ) (a b : Fin d → ℂ) :
    a ≠ b ↔ ∃ i, (xiCanonicalJetHasseData d).localPacket a i ≠
      (xiCanonicalJetHasseData d).localPacket b i :=
  (xiCanonicalJetHasseData d).ne_iff_exists_localPacket_ne a b

/-- Every packet at the chosen completed-Xi evaluation places has one unique global canonical-jet
coefficient family. -/
theorem xiCanonicalJetHasse_existsUnique (d : ℕ) (packet : Fin d → ℂ) :
    ∃! a : Fin d → ℂ, (xiCanonicalJetHasseData d).localPacket a = packet :=
  (xiCanonicalJetHasseData d).localPacket_existsUnique packet

end


end RHTower
