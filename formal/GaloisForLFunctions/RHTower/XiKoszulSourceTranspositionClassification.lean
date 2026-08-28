import GaloisForLFunctions.RHTower.XiKoszulMutualStatisticsSuperselection

/-!
# Source transposition classification for the Xi Koszul lift

The explicit one-prime Green section produces two all-prime degree-one legs whose ordered cup
has any prescribed complex orientation coefficient.  Reversing the legs negates that coefficient.
Consequently the actual source supplies every scalar in the sign representation, while a lift
through a scalar transposition character `χ` exists exactly when `( χ + 1) * c = 0`.

This also gives a source-level obstruction stronger than a zero-specific collision.  No linear
completion of the all-prime center can be both invariant under source-leg transposition and
coefficient-faithful on even one prime orientation section.  Tensoring with another sign removes
the obstruction for every coefficient, so bare sign compensation is nonselective.
-/

open Complex

namespace RHTower

noncomputable section

/-- The transposition-sign lift of a scalar through the actual all-prime source cup. -/
structure DeningerCalderonWittKoszulSignLift (c : ℂ) where
  gradeLeg : DeningerCalderonWittAlgebraicGlobalDegreeOne
  phaseLeg : DeningerCalderonWittAlgebraicGlobalDegreeOne
  gradeThenPhase :
    deningerCalderonWittAlgebraicGlobalCenterTrace
        (deningerCalderonWittAlgebraicGlobalCup gradeLeg phaseLeg) = c
  phaseThenGrade :
    deningerCalderonWittAlgebraicGlobalCenterTrace
        (deningerCalderonWittAlgebraicGlobalCup phaseLeg gradeLeg) = -c

/-- Fixed unit-defect leg at one prime, inserted into the all-prime source. -/
def deningerCalderonWittKoszulSignGradeLeg (p : Nat.Primes) :
    DeningerCalderonWittAlgebraicGlobalDegreeOne :=
  DirectSum.lof ℂ Nat.Primes DeningerCalderonWittAlgebraicDegreeOne p
    (deningerCalderonWittUnitDefect p, 0)

/-- Coefficient leg obtained from the normalized center orientation section. -/
def deningerCalderonWittKoszulSignPhaseLeg (p : Nat.Primes) (c : ℂ) :
    DeningerCalderonWittAlgebraicGlobalDegreeOne :=
  DirectSum.lof ℂ Nat.Primes DeningerCalderonWittAlgebraicDegreeOne p
    (deningerCalderonWittCenterToDegreeOne p
      (deningerCalderonWittAlgebraicCenterOrientationSection p c))

/-- The explicit ordered cup is the normalized prime orientation section itself. -/
theorem deningerCalderonWittKoszulSignCup_eq_primeCenterOrientationSection
    (p : Nat.Primes) (c : ℂ) :
    deningerCalderonWittAlgebraicGlobalCup
          (deningerCalderonWittKoszulSignGradeLeg p)
          (deningerCalderonWittKoszulSignPhaseLeg p c) =
      deningerCalderonWittGlobalPrimeCenterOrientationSection p c := by
  let z := deningerCalderonWittAlgebraicCenterOrientationSection p c
  have hsection := LinearMap.congr_fun
    (deningerCalderonWittGlobalExteriorCup_primeSection p) z
  simpa [z, deningerCalderonWittKoszulSignGradeLeg,
    deningerCalderonWittKoszulSignPhaseLeg,
    deningerCalderonWittGlobalPrimeExteriorCupSection,
    deningerCalderonWittGlobalPrimeCenterOrientationSection,
    LinearMap.comp_apply,
    deningerCalderonWittGlobalExteriorWedgeLeft_apply] using hsection

/-- Forward ordered cup has the prescribed coefficient. -/
theorem deningerCalderonWittKoszulSign_gradeThenPhase
    (p : Nat.Primes) (c : ℂ) :
    deningerCalderonWittAlgebraicGlobalCenterTrace
        (deningerCalderonWittAlgebraicGlobalCup
          (deningerCalderonWittKoszulSignGradeLeg p)
          (deningerCalderonWittKoszulSignPhaseLeg p c)) = c := by
  rw [deningerCalderonWittKoszulSignCup_eq_primeCenterOrientationSection]
  exact deningerCalderonWittAlgebraicGlobalCenterTrace_primeSection p c

/-- Reverse ordered cup has the opposite coefficient. -/
theorem deningerCalderonWittKoszulSign_phaseThenGrade
    (p : Nat.Primes) (c : ℂ) :
    deningerCalderonWittAlgebraicGlobalCenterTrace
        (deningerCalderonWittAlgebraicGlobalCup
          (deningerCalderonWittKoszulSignPhaseLeg p c)
          (deningerCalderonWittKoszulSignGradeLeg p)) = -c := by
  have hskew := congrArg deningerCalderonWittAlgebraicGlobalCenterTrace
    (deningerCalderonWittAlgebraicGlobalCup_skew
      (deningerCalderonWittKoszulSignPhaseLeg p c)
      (deningerCalderonWittKoszulSignGradeLeg p))
  rw [map_neg, deningerCalderonWittKoszulSign_gradeThenPhase] at hskew
  exact hskew

/-- Canonical coefficient-faithful sign-character lift at every prime. -/
def deningerCalderonWittCanonicalKoszulSignLift
    (p : Nat.Primes) (c : ℂ) :
    DeningerCalderonWittKoszulSignLift c where
  gradeLeg := deningerCalderonWittKoszulSignGradeLeg p
  phaseLeg := deningerCalderonWittKoszulSignPhaseLeg p c
  gradeThenPhase := deningerCalderonWittKoszulSign_gradeThenPhase p c
  phaseThenGrade := deningerCalderonWittKoszulSign_phaseThenGrade p c

/-- Lift of one coefficient through a prescribed scalar transposition character. -/
structure DeningerCalderonWittKoszulCharacterLift (χ c : ℂ) where
  gradeLeg : DeningerCalderonWittAlgebraicGlobalDegreeOne
  phaseLeg : DeningerCalderonWittAlgebraicGlobalDegreeOne
  gradeThenPhase :
    deningerCalderonWittAlgebraicGlobalCenterTrace
        (deningerCalderonWittAlgebraicGlobalCup gradeLeg phaseLeg) = c
  phaseThenGrade :
    deningerCalderonWittAlgebraicGlobalCenterTrace
        (deningerCalderonWittAlgebraicGlobalCup phaseLeg gradeLeg) = χ * c

/-- Exhaustive scalar-character classification.  A coefficient can transform by `χ` under
source transposition exactly when its `(χ + 1)`-isotypic obstruction vanishes. -/
theorem nonempty_deningerCalderonWittKoszulCharacterLift_iff
    (p : Nat.Primes) (χ c : ℂ) :
    Nonempty (DeningerCalderonWittKoszulCharacterLift χ c) ↔
      (χ + 1) * c = 0 := by
  constructor
  · rintro ⟨L⟩
    have hskew := congrArg deningerCalderonWittAlgebraicGlobalCenterTrace
      (deningerCalderonWittAlgebraicGlobalCup_skew L.gradeLeg L.phaseLeg)
    rw [map_neg, L.gradeThenPhase, L.phaseThenGrade] at hskew
    calc
      (χ + 1) * c = χ * c + c := by ring
      _ = χ * c + -(χ * c) := congrArg (fun z => χ * c + z) hskew
      _ = 0 := add_neg_cancel (χ * c)
  · intro hisotypic
    have hreverse : -c = χ * c := by
      have hsum : χ * c + c = 0 := by
        calc
          χ * c + c = (χ + 1) * c := by ring
          _ = 0 := hisotypic
      calc
        -c = 0 - c := by ring
        _ = (χ * c + c) - c := by rw [hsum]
        _ = χ * c := by ring
    refine ⟨⟨
      deningerCalderonWittKoszulSignGradeLeg p,
      deningerCalderonWittKoszulSignPhaseLeg p c,
      deningerCalderonWittKoszulSign_gradeThenPhase p c,
      ?_⟩⟩
    rw [deningerCalderonWittKoszulSign_phaseThenGrade, hreverse]

/-- Canonical signed source cup is nonzero exactly for a nonzero coefficient. -/
theorem deningerCalderonWittCanonicalKoszulSignCup_ne_zero_iff
    (p : Nat.Primes) (c : ℂ) :
    deningerCalderonWittAlgebraicGlobalCup
        (deningerCalderonWittKoszulSignGradeLeg p)
        (deningerCalderonWittKoszulSignPhaseLeg p c) ≠ 0 ↔ c ≠ 0 := by
  constructor
  · intro hcup hc
    apply hcup
    subst c
    have hphase : deningerCalderonWittKoszulSignPhaseLeg p 0 = 0 := by
      simp only [deningerCalderonWittKoszulSignPhaseLeg, map_zero]
    rw [hphase, map_zero]
  · intro hc hcup
    have htrace := deningerCalderonWittKoszulSign_gradeThenPhase p c
    rw [hcup, map_zero] at htrace
    exact hc htrace.symm

/-- Scalar lift on which source-leg transposition acts trivially. -/
structure DeningerCalderonWittKoszulTrivialLift (c : ℂ) where
  gradeLeg : DeningerCalderonWittAlgebraicGlobalDegreeOne
  phaseLeg : DeningerCalderonWittAlgebraicGlobalDegreeOne
  gradeThenPhase :
    deningerCalderonWittAlgebraicGlobalCenterTrace
        (deningerCalderonWittAlgebraicGlobalCup gradeLeg phaseLeg) = c
  phaseThenGrade :
    deningerCalderonWittAlgebraicGlobalCenterTrace
        (deningerCalderonWittAlgebraicGlobalCup phaseLeg gradeLeg) = c

/-- A trivial-character source lift has zero coefficient. -/
theorem deningerCalderonWittKoszulTrivialLift_scalar_eq_zero
    (c : ℂ) (L : DeningerCalderonWittKoszulTrivialLift c) : c = 0 := by
  have hskew := congrArg deningerCalderonWittAlgebraicGlobalCenterTrace
    (deningerCalderonWittAlgebraicGlobalCup_skew L.gradeLeg L.phaseLeg)
  rw [map_neg, L.gradeThenPhase, L.phaseThenGrade] at hskew
  have htwo : (2 : ℂ) * c = 0 := by
    calc
      (2 : ℂ) * c = c + c := by ring
      _ = c + -c := congrArg (fun z => c + z) hskew
      _ = 0 := add_neg_cancel c
  exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)

/-- Trivial-character lifts exist exactly for the zero coefficient. -/
theorem nonempty_deningerCalderonWittKoszulTrivialLift_iff (c : ℂ) :
    Nonempty (DeningerCalderonWittKoszulTrivialLift c) ↔ c = 0 := by
  constructor
  · rintro ⟨L⟩
    exact deningerCalderonWittKoszulTrivialLift_scalar_eq_zero c L
  · intro hc
    subst c
    exact ⟨⟨0, 0, by simp, by simp⟩⟩

/-- Sign lifts are universal, while trivial-character lifts are confined to zero. -/
theorem deningerCalderonWittKoszulTranspositionClassification
    (p : Nat.Primes) (c : ℂ) :
    Nonempty (DeningerCalderonWittKoszulSignLift c) ∧
      (Nonempty (DeningerCalderonWittKoszulTrivialLift c) ↔ c = 0) := by
  exact ⟨⟨deningerCalderonWittCanonicalKoszulSignLift p c⟩,
    nonempty_deningerCalderonWittKoszulTrivialLift_iff c⟩

/-- Proposed scalar completion which forgets source-leg order while retaining the normalized
coefficient at one prime. -/
structure DeningerCalderonWittOrderBlindCoefficientFaithfulCompletion
    (p : Nat.Primes) where
  complete : DeningerCalderonWittAlgebraicGlobalDegreeTwo →ₗ[ℂ] ℂ
  orderBlind : ∀ x y,
    complete (deningerCalderonWittAlgebraicGlobalCup x y) =
      complete (deningerCalderonWittAlgebraicGlobalCup y x)
  coefficientFaithful :
    complete.comp (deningerCalderonWittGlobalPrimeCenterOrientationSection p) =
      LinearMap.id

/-- No linear scalar completion is both transposition-invariant and coefficient-faithful on even
one prime orientation section. -/
theorem not_nonempty_deningerCalderonWittOrderBlindCoefficientFaithfulCompletion
    (p : Nat.Primes) :
    ¬ Nonempty (DeningerCalderonWittOrderBlindCoefficientFaithfulCompletion p) := by
  rintro ⟨C⟩
  let g := deningerCalderonWittKoszulSignGradeLeg p
  let h := deningerCalderonWittKoszulSignPhaseLeg p 1
  have hfaith := LinearMap.congr_fun C.coefficientFaithful (1 : ℂ)
  have hforward : C.complete (deningerCalderonWittAlgebraicGlobalCup g h) = 1 := by
    rw [show deningerCalderonWittAlgebraicGlobalCup g h =
        deningerCalderonWittGlobalPrimeCenterOrientationSection p 1 by
      exact deningerCalderonWittKoszulSignCup_eq_primeCenterOrientationSection p 1]
    simpa [LinearMap.comp_apply] using hfaith
  have hreverse : C.complete (deningerCalderonWittAlgebraicGlobalCup h g) = -1 := by
    rw [deningerCalderonWittAlgebraicGlobalCup_skew, map_neg, hforward]
  have hcollision := C.orderBlind g h
  rw [hforward, hreverse] at hcollision
  norm_num at hcollision

/-- Tensoring the source sign with a second `-1` spin makes order independence automatic for
every coefficient.  Bare sign cancellation therefore cannot distinguish the critical line. -/
theorem deningerCalderonWittKoszulThetaSpinCompensation_universal
    (p : Nat.Primes) (c : ℂ) :
    ∃ gradeLeg phaseLeg : DeningerCalderonWittAlgebraicGlobalDegreeOne,
      deningerCalderonWittAlgebraicGlobalCenterTrace
          (deningerCalderonWittAlgebraicGlobalCup gradeLeg phaseLeg) = c ∧
      (-1 : ℂ) *
          deningerCalderonWittAlgebraicGlobalCenterTrace
            (deningerCalderonWittAlgebraicGlobalCup phaseLeg gradeLeg) = c := by
  refine ⟨deningerCalderonWittKoszulSignGradeLeg p,
    deningerCalderonWittKoszulSignPhaseLeg p c,
    deningerCalderonWittKoszulSign_gradeThenPhase p c, ?_⟩
  rw [deningerCalderonWittKoszulSign_phaseThenGrade]
  ring

/-- Canonical signed Xi source cup vanishes exactly on the critical line. -/
theorem xiCanonicalKoszulSignCup_eq_zero_iff_re_eq_half
    (p : Nat.Primes) (q : XiZeroCopy) :
    deningerCalderonWittAlgebraicGlobalCup
        (deningerCalderonWittKoszulSignGradeLeg p)
        (deningerCalderonWittKoszulSignPhaseLeg p
          (xiReflectedPhaseNeutralMixedJet q : ℂ)) = 0 ↔
      (q.1 : ℂ).re = 1 / 2 := by
  constructor
  · intro hcup
    have htrace := deningerCalderonWittKoszulSign_gradeThenPhase p
      (xiReflectedPhaseNeutralMixedJet q : ℂ)
    rw [hcup, map_zero] at htrace
    have hreal : xiReflectedPhaseNeutralMixedJet q = 0 := by
      have hre := congrArg Complex.re htrace
      simpa using hre.symm
    exact (xiNodalDefectSuperselected_iff_re_eq_half q).1
      ((xiNodalDefectSuperselected_iff_mixedSourceJet_eq_zero q).2 hreal)
  · intro hline
    have hreal : xiReflectedPhaseNeutralMixedJet q = 0 :=
      (xiNodalDefectSuperselected_iff_mixedSourceJet_eq_zero q).1
        ((xiNodalDefectSuperselected_iff_re_eq_half q).2 hline)
    have hcomplex : (xiReflectedPhaseNeutralMixedJet q : ℂ) = 0 := by
      simp [hreal]
    by_contra hcup
    exact
      (deningerCalderonWittCanonicalKoszulSignCup_ne_zero_iff p
        (xiReflectedPhaseNeutralMixedJet q : ℂ)).1 hcup hcomplex

/-- Universal vanishing of the canonical signed source cup at one fixed prime. -/
def EveryXiCanonicalKoszulSignCupVanishesAtPrime (p : Nat.Primes) : Prop :=
  ∀ q : XiZeroCopy,
    deningerCalderonWittAlgebraicGlobalCup
        (deningerCalderonWittKoszulSignGradeLeg p)
        (deningerCalderonWittKoszulSignPhaseLeg p
          (xiReflectedPhaseNeutralMixedJet q : ℂ)) = 0

/-- At any fixed prime, universal vanishing of the explicit signed source cups is exactly RH. -/
theorem everyXiCanonicalKoszulSignCupVanishesAtPrime_iff_riemannHypothesis
    (p : Nat.Primes) :
    EveryXiCanonicalKoszulSignCupVanishesAtPrime p ↔ RiemannHypothesis := by
  rw [← xiNodalDefectSuperselection_iff_riemannHypothesis]
  unfold EveryXiCanonicalKoszulSignCupVanishesAtPrime XiNodalDefectSuperselection
  apply forall_congr'
  intro q
  exact (xiCanonicalKoszulSignCup_eq_zero_iff_re_eq_half p q).trans
    (xiNodalDefectSuperselected_iff_re_eq_half q).symm

end

end RHTower
