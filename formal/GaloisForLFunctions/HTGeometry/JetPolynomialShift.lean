import GaloisForLFunctions.HTGeometry.ShiftedGammaMultiplicativeCoboundary

/-!
# The unit shift on the jet polynomial ring

The unit shift sends each digamma jet to itself plus a rational increment, so it is induced by an
endomorphism of `MvPolynomial (Fin M) (RatFunc ℂ)` sending `X k` to `X k + C (increment k)` and
acting on the coefficients by `ratShift`.  This is the algebraic carrier of the shift elimination.
-/

open Set

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher

noncomputable section

local instance jetShiftDomain :
    IsDomain (analyticSubring (Set.univ : Set ℂ)) :=
  Bottcher.isDomain_analyticSubring Set.univ isOpen_univ
    isPreconnected_univ Set.univ_nonempty

local instance jetShiftRatAlgebra : Algebra (RatFunc ℂ) (meroField (Set.univ : Set ℂ)) :=
  (ratfuncToMero Set.univ isOpen_univ isPreconnected_univ
    Set.univ_nonempty Set.infinite_univ).toAlgebra

variable {r : ℕ}

/-- The shift endomorphism of the jet polynomial ring. -/
def jetShiftPoly {M : ℕ} (rj : Fin M → RatFunc ℂ) :
    MvPolynomial (Fin M) (RatFunc ℂ) →+* MvPolynomial (Fin M) (RatFunc ℂ) :=
  MvPolynomial.eval₂Hom
    ((MvPolynomial.C : RatFunc ℂ →+* MvPolynomial (Fin M) (RatFunc ℂ)).comp ratShift)
    (fun k => MvPolynomial.X k + MvPolynomial.C (rj k))

@[simp] theorem jetShiftPoly_C {M : ℕ} (rj : Fin M → RatFunc ℂ) (a : RatFunc ℂ) :
    jetShiftPoly rj (MvPolynomial.C a) = MvPolynomial.C (ratShift a) := by
  rw [jetShiftPoly, MvPolynomial.eval₂Hom_C, RingHom.comp_apply]

@[simp] theorem jetShiftPoly_X {M : ℕ} (rj : Fin M → RatFunc ℂ) (k : Fin M) :
    jetShiftPoly rj (MvPolynomial.X k) = MvPolynomial.X k + MvPolynomial.C (rj k) := by
  rw [jetShiftPoly, MvPolynomial.eval₂Hom_X']

set_option synthInstance.maxHeartbeats 1000000 in
/-- **The polynomial shift induces the unit shift on jet values.** -/
theorem aeval_jetShiftPoly (lam : Fin r → ℂ) {M : ℕ} (idx : Fin M → Fin r × ℕ)
    (P : MvPolynomial (Fin M) (RatFunc ℂ)) :
    MvPolynomial.aeval (fun k => digammaJet lam (idx k))
        (jetShiftPoly (fun k => familyIncrement lam (idx k).1 (idx k).2) P)
      = addTranslationMeroEquiv 1
          (MvPolynomial.aeval (fun k => digammaJet lam (idx k)) P) := by
  classical
  induction P using MvPolynomial.induction_on with
  | C a =>
      rw [jetShiftPoly_C, MvPolynomial.aeval_C, MvPolynomial.aeval_C]
      exact (addTranslationMeroEquiv_ratfuncToMero a).symm
  | add p q hp hq =>
      have hL : MvPolynomial.aeval (fun k => digammaJet lam (idx k))
          ((jetShiftPoly (fun k => familyIncrement lam (idx k).1 (idx k).2)) (p + q))
          = MvPolynomial.aeval (fun k => digammaJet lam (idx k))
              ((jetShiftPoly (fun k => familyIncrement lam (idx k).1 (idx k).2)) p)
            + MvPolynomial.aeval (fun k => digammaJet lam (idx k))
              ((jetShiftPoly (fun k => familyIncrement lam (idx k).1 (idx k).2)) q) := by
        rw [map_add, map_add]
      have hR : addTranslationMeroEquiv 1
            (MvPolynomial.aeval (fun k => digammaJet lam (idx k)) (p + q))
          = addTranslationMeroEquiv 1 (MvPolynomial.aeval (fun k => digammaJet lam (idx k)) p)
            + addTranslationMeroEquiv 1
              (MvPolynomial.aeval (fun k => digammaJet lam (idx k)) q) := by
        rw [map_add, (addTranslationMeroEquiv 1).map_add]
      rw [hL, hR, hp, hq]
  | mul_X p k hp =>
      have hL : MvPolynomial.aeval (fun k => digammaJet lam (idx k))
          ((jetShiftPoly (fun k => familyIncrement lam (idx k).1 (idx k).2))
            (p * MvPolynomial.X k))
          = MvPolynomial.aeval (fun k => digammaJet lam (idx k))
              ((jetShiftPoly (fun k => familyIncrement lam (idx k).1 (idx k).2)) p)
            * (digammaJet lam (idx k)
              + algebraMap (RatFunc ℂ) (meroField (Set.univ : Set ℂ))
                  (familyIncrement lam (idx k).1 (idx k).2)) := by
        rw [map_mul, jetShiftPoly_X, map_mul, map_add, MvPolynomial.aeval_X, MvPolynomial.aeval_C]
      have hR : addTranslationMeroEquiv 1
            (MvPolynomial.aeval (fun k => digammaJet lam (idx k)) (p * MvPolynomial.X k))
          = addTranslationMeroEquiv 1
              (MvPolynomial.aeval (fun k => digammaJet lam (idx k)) p)
            * (digammaJet lam (idx k)
              + algebraMap (RatFunc ℂ) (meroField (Set.univ : Set ℂ))
                  (familyIncrement lam (idx k).1 (idx k).2)) := by
        rw [map_mul, (addTranslationMeroEquiv 1).map_mul, MvPolynomial.aeval_X,
          addTranslationMeroEquiv_digammaJet]
      rw [hL, hR, hp]

end

end GaloisForLFunctions.HTGeometry
