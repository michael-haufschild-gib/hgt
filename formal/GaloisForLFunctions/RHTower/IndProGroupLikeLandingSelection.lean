import GaloisForLFunctions.HTGeometry.CyclotomicIndProIntersection
import GaloisForLFunctions.RHTower.GlobalInertiaDivisorSelection

/-!
# Ind–pro landing selection for the Euler-shell divisor

The ind–pro fracture, the crossed Kummer defect and the Calkin properness of the global regular
packet are three shadows of one charge.  Applied to the strict-right local charges of the survival
transfer, ind-formation of every local history — in particular a group-like landing in the
filtered cyclotomic source — is equivalent to the Riemann hypothesis.
-/

open Complex GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-- **(IPT.10).**  Ind-formation of the charge history, vanishing of the charge, universal
ambidextrous flatness, and compactness of both regular packets are the same condition. -/
theorem indPro_tfae (q : ℤ) :
    List.TFAE
      [ (chargeHistory q).IsIndFormed,
        q = 0,
        ∀ (n m : ℕ) (h : n ∣ m), ambidextrousDefect h q = 0,
        IsCompactOperator (globalInertiaDefect q),
        IsCompactOperator (ambPacketDefect q) ] := by
  tfae_have 1 → 2 := (chargeHistory_isIndFormed_iff q).1
  tfae_have 2 → 3 := by
    rintro rfl n m h
    exact ambidextrousDefect_zero h
  tfae_have 3 → 4 := by
    intro h
    refine (isCompactOperator_globalInertiaDefect_iff q).2 ?_
    exact ((ambidextrousDefect_tfae q).out 1 0).1 h
  tfae_have 4 → 5 := by
    intro h
    exact (isCompactOperator_ambPacketDefect_iff q).2
      ((isCompactOperator_globalInertiaDefect_iff q).1 h)
  tfae_have 5 → 1 := by
    intro h
    exact (chargeHistory_isIndFormed_iff q).2 ((isCompactOperator_ambPacketDefect_iff q).1 h)
  tfae_finish

/-- **Corollary 7.1 — the Euler-shell equivalence.**  Ind-formation of every strict-right local
charge history is equivalent to the Riemann hypothesis. -/
theorem riemannHypothesis_iff_forall_indFormed :
    RiemannHypothesis ↔
      ∀ ρ : ℂ, 1 / 2 < ρ.re → ρ ≠ 1 → (chargeHistory (localFormationCharge ρ)).IsIndFormed := by
  constructor
  · intro hrh ρ hρ hρ1
    refine (chargeHistory_isIndFormed_iff _).2 ?_
    exact (localFormationCharge_eq_zero_iff hρ1).2
      (riemannHypothesis_iff_zetaZeroFreeRight.1 hrh ρ hρ hρ1)
  · intro h
    refine riemannHypothesis_iff_zetaZeroFreeRight.2 fun ρ hρ hρ1 => ?_
    exact (localFormationCharge_eq_zero_iff hρ1).1
      ((chargeHistory_isIndFormed_iff _).1 (h ρ hρ hρ1))

/-- **Corollary 7.1 — group-like source landing selection.**  If every strict-right local history
lands as one group-like element of the complex root-group algebra on the cofinal tail of multiples
of its birth depth, then the Riemann hypothesis holds. -/
theorem riemannHypothesis_of_groupLike_landing
    (h : ∀ ρ : ℂ, 1 / 2 < ρ.re → ρ ≠ 1 →
      ∃ x : MonoidAlgebra ℂ ℂˣ, IsGroupLikeElem ℂ x ∧ ∃ d : ℕ, 1 ≤ d ∧
        ∀ m : ℕ, 1 ≤ m → d ∣ m →
          MonoidAlgebra.single (chargeUnit m (localFormationCharge ρ)) (1 : ℂ) = x) :
    RiemannHypothesis := by
  refine riemannHypothesis_iff_forall_indFormed.2 fun ρ hρ hρ1 => ?_
  obtain ⟨x, hx, d, hd, hland⟩ := h ρ hρ hρ1
  exact (chargeHistory_isIndFormed_iff _).2 (eq_zero_of_groupLike_landing x hx d hd hland)

/-- **The functional equation cannot repair the fracture.**  At a strict-right zero of zeta the
local history is not ind-formed, whatever multiplicity-preserving transport is applied. -/
theorem not_isIndFormed_chargeHistory_of_zetaZero {ρ : ℂ} (hρ1 : ρ ≠ 1)
    (hzero : riemannZeta ρ = 0) :
    ¬ (chargeHistory (localFormationCharge ρ)).IsIndFormed := by
  intro h
  exact ((localFormationCharge_eq_zero_iff hρ1).1 ((chargeHistory_isIndFormed_iff _).1 h)) hzero

end

end RHTower
