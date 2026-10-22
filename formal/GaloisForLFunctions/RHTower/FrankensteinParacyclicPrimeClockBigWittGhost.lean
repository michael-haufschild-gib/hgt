import GaloisForLFunctions.RHTower.FrankensteinParacyclicGhostTwoSheetAnomaly
import GaloisForLFunctions.RHTower.Deninger.DeningerBigWittFrobeniusCrossPairStrictGammaBVDescent
import GaloisForLFunctions.RHTower.Deninger.DeningerCalderonWittTwoPrimeOrientationBoundaryWall

/-!
# Prime-clock paracyclic anomaly read through the Big Witt ghost and Calderón–Witt incidence

For a zero `ρ` of `Ξ`, the prime-clock anomaly `a_ρ(p)` is the paracyclic anomaly coefficient
at scale `p` and depth `0`, equal to `(p^{2 Re ρ - 1} - 1) · c(ρ)` with `c(ρ) ≠ 0`. Feeding the
vector `p ↦ a_ρ(p)` into the Frobenius-transgressed Big Witt prime-seam pair source at the primes
`2, 3` gives the first-ghost coefficient `-2 · (1/6) · |a_ρ(2) - a_ρ(3)|²`, which is nonpositive
and vanishes iff `Re ρ = 1/2`. The module reads this coefficient through the boundary of a
Hochschild BV Green chain and through a Calderón–Witt incidence source, and shows that the
existence of a linear descent of the Gamma-polarized boundary reflection defect through the
(vanishing) oriented boundary is again equivalent to `Re ρ = 1/2`.

## Main results

- `frankensteinPrimeClockParacyclicAnomaly_two_eq_three_iff`: `a_ρ(2) = a_ρ(3)` iff `Re ρ = 1/2`.
- `deningerBigWittFrobeniusPrimeSeamPairCoefficient_primeClockParacyclic_two_three_eq_zero_iff`:
  the `(2, 3)` ghost coefficient vanishes iff `Re ρ = 1/2`.
- `deningerBigWittFrobeniusPrimeSeamPairCoefficient_primeClockParacyclic_two_three_re_lt_zero_iff`:
  its real part is negative iff `Re ρ ≠ 1/2`.
- `frankensteinPrimeClockParacyclicSelectedWardDescendsAt_iff`: the selected Ward descent at `ρ`
  exists iff `Re ρ = 1/2`.
- `everyFrankensteinPrimeClockParacyclicTwoThreeBVGroundReadoutVanishes_iff_riemannHypothesis`
  and `everyFrankensteinPrimeClockParacyclicSelectedWardDescends_iff_riemannHypothesis`: the
  corresponding statements for all zeros of `Ξ` are each equivalent to the Riemann hypothesis.

## Hypotheses

Unconditional. The Riemann-hypothesis statements are equivalences, not proofs of either side; the
`Prop`-valued definitions `EveryFrankensteinPrimeClockParacyclicTwoThreeBVGroundReadoutVanishes`,
`FrankensteinPrimeClockParacyclicSelectedWardDescendsAt` and
`EveryFrankensteinPrimeClockParacyclicSelectedWardDescends` appear only as sides of these
equivalences, never as premises.
-/

open Complex Matrix GaloisForLFunctions.HTGeometry
open scoped TensorProduct

namespace RHTower

noncomputable section

/-- Prime-clock anomaly `a_ρ(p)`: the paracyclic anomaly coefficient of `ρ` at scale `p` and
prime-power datum `(p, 0)`. -/
def frankensteinPrimeClockParacyclicAnomaly
    (rho : XiDivisorSupport) (p : Nat.Primes) : ℂ :=
  frankensteinParacyclicAnomalyCoefficient (p : ℕ) rho (p, 0)

/-- `a_ρ(p) = (p^{2 Re ρ - 1} - 1) · c(ρ)`, with `c(ρ)` the leading physical source coefficient. -/
theorem frankensteinPrimeClockParacyclicAnomaly_eq
    (rho : XiDivisorSupport) (p : Nat.Primes) :
    frankensteinPrimeClockParacyclicAnomaly rho p =
      ((deningerHalfDensityMateGain (p : ℕ) (rho : ℂ) : ℂ) - 1) *
        thetaInternalJetLeadingSourceCoefficient rho := by
  rw [frankensteinPrimeClockParacyclicAnomaly,
    frankensteinParacyclicAnomalyCoefficient_eq]

/-- `a_ρ(p) - a_ρ(q) = (p^{2 Re ρ - 1} - q^{2 Re ρ - 1}) · c(ρ)`. -/
theorem frankensteinPrimeClockParacyclicAnomaly_sub_eq
    (rho : XiDivisorSupport) (p q : Nat.Primes) :
    frankensteinPrimeClockParacyclicAnomaly rho p -
        frankensteinPrimeClockParacyclicAnomaly rho q =
      ((deningerHalfDensityMateGain (p : ℕ) (rho : ℂ) : ℂ) -
        deningerHalfDensityMateGain (q : ℕ) (rho : ℂ)) *
          thetaInternalJetLeadingSourceCoefficient rho := by
  rw [frankensteinPrimeClockParacyclicAnomaly_eq,
    frankensteinPrimeClockParacyclicAnomaly_eq]
  ring

/-- The prime-clock anomalies at `2` and `3` agree iff `Re ρ = 1/2`. -/
theorem frankensteinPrimeClockParacyclicAnomaly_two_eq_three_iff
    (rho : XiDivisorSupport) :
    frankensteinPrimeClockParacyclicAnomaly rho deningerCalderonWittPrimeTwo =
        frankensteinPrimeClockParacyclicAnomaly rho deningerCalderonWittPrimeThree ↔
      (rho : ℂ).re = 1 / 2 := by
  rw [frankensteinPrimeClockParacyclicAnomaly_eq,
    frankensteinPrimeClockParacyclicAnomaly_eq]
  change (((deningerHalfDensityMateGain 2 (rho : ℂ) : ℂ) - 1) *
      thetaInternalJetLeadingSourceCoefficient rho =
    ((deningerHalfDensityMateGain 3 (rho : ℂ) : ℂ) - 1) *
      thetaInternalJetLeadingSourceCoefficient rho) ↔ _
  constructor
  · intro h
    have hfactor := mul_right_cancel₀
      (thetaInternalJetLeadingSourceCoefficient_ne_zero rho) h
    have hgainC :
        (deningerHalfDensityMateGain 2 (rho : ℂ) : ℂ) =
          deningerHalfDensityMateGain 3 (rho : ℂ) := by
      linear_combination hfactor
    have hgain :
        deningerHalfDensityMateGain 2 (rho : ℂ) =
          deningerHalfDensityMateGain 3 (rho : ℂ) := by
      exact_mod_cast hgainC
    exact (deningerHalfDensityMateGain_two_eq_three_iff (rho : ℂ)).1 hgain
  · intro hline
    have hgain :=
      (deningerHalfDensityMateGain_two_eq_three_iff (rho : ℂ)).2 hline
    rw [hgain]

/-- The Big Witt `(2, 3)` seam-pair ghost coefficient `-2 · (1/6) · |a_ρ(2) - a_ρ(3)|²` of the
prime-clock anomaly vanishes iff `Re ρ = 1/2`. -/
theorem deningerBigWittFrobeniusPrimeSeamPairCoefficient_primeClockParacyclic_two_three_eq_zero_iff
    (rho : XiDivisorSupport) :
    deningerBigWittFrobeniusPrimeSeamPairCoefficient
        (frankensteinPrimeClockParacyclicAnomaly rho)
        deningerCalderonWittPrimeTwo deningerCalderonWittPrimeThree = 0 ↔
      (rho : ℂ).re = 1 / 2 := by
  rw [deningerBigWittFrobeniusPrimeSeamPairCoefficient_eq,
    Complex.ofReal_eq_zero]
  have hatom :
      deningerBigWittPrimePairExtendedPhysicalAtom
        deningerCalderonWittPrimeTwo deningerCalderonWittPrimeThree ≠ 0 := by
    rw [deningerBigWittPrimePairExtendedPhysicalAtom_eq]
    change (1 / (2 : ℝ)) * (1 / (3 : ℝ)) ≠ 0
    norm_num
  have hweight :
      -2 * deningerBigWittPrimePairExtendedPhysicalAtom
        deningerCalderonWittPrimeTwo deningerCalderonWittPrimeThree ≠ 0 :=
    mul_ne_zero (by norm_num) hatom
  constructor
  · intro h
    have hsq := (mul_eq_zero.mp h).resolve_left hweight
    have hnorm :
        ‖frankensteinPrimeClockParacyclicAnomaly rho deningerCalderonWittPrimeTwo -
          frankensteinPrimeClockParacyclicAnomaly rho deningerCalderonWittPrimeThree‖ = 0 :=
      (sq_eq_zero_iff).1 hsq
    exact (frankensteinPrimeClockParacyclicAnomaly_two_eq_three_iff rho).1
      (sub_eq_zero.mp (norm_eq_zero.mp hnorm))
  · intro hline
    have heq :=
      (frankensteinPrimeClockParacyclicAnomaly_two_eq_three_iff rho).2 hline
    rw [heq, sub_self, norm_zero]
    norm_num

/-- The real part of the `(2, 3)` seam-pair ghost coefficient is strictly negative iff
`Re ρ ≠ 1/2`. -/
theorem deningerBigWittFrobeniusPrimeSeamPairCoefficient_primeClockParacyclic_two_three_re_lt_zero_iff
    (rho : XiDivisorSupport) :
    (deningerBigWittFrobeniusPrimeSeamPairCoefficient
        (frankensteinPrimeClockParacyclicAnomaly rho)
        deningerCalderonWittPrimeTwo deningerCalderonWittPrimeThree).re < 0 ↔
      (rho : ℂ).re ≠ 1 / 2 := by
  rw [deningerBigWittFrobeniusPrimeSeamPairCoefficient_eq,
    Complex.ofReal_re]
  have hatom :
      0 < deningerBigWittPrimePairExtendedPhysicalAtom
        deningerCalderonWittPrimeTwo deningerCalderonWittPrimeThree := by
    rw [deningerBigWittPrimePairExtendedPhysicalAtom_eq]
    change 0 < (1 / (2 : ℝ)) * (1 / (3 : ℝ))
    norm_num
  constructor
  · intro hneg hline
    have heq :=
      (frankensteinPrimeClockParacyclicAnomaly_two_eq_three_iff rho).2 hline
    rw [heq, sub_self, norm_zero] at hneg
    norm_num at hneg
  · intro hoff
    have hne :
        frankensteinPrimeClockParacyclicAnomaly rho deningerCalderonWittPrimeTwo ≠
          frankensteinPrimeClockParacyclicAnomaly rho deningerCalderonWittPrimeThree :=
      (frankensteinPrimeClockParacyclicAnomaly_two_eq_three_iff rho).not.2 hoff
    have hnorm :
        0 < ‖frankensteinPrimeClockParacyclicAnomaly rho deningerCalderonWittPrimeTwo -
          frankensteinPrimeClockParacyclicAnomaly rho deningerCalderonWittPrimeThree‖ :=
      norm_pos_iff.mpr (sub_ne_zero.mpr hne)
    have hprod :
        0 < deningerBigWittPrimePairExtendedPhysicalAtom
            deningerCalderonWittPrimeTwo deningerCalderonWittPrimeThree *
          ‖frankensteinPrimeClockParacyclicAnomaly rho deningerCalderonWittPrimeTwo -
            frankensteinPrimeClockParacyclicAnomaly rho deningerCalderonWittPrimeThree‖ ^ (2 : ℕ) :=
      mul_pos hatom (sq_pos_of_pos hnorm)
    nlinarith

/-- Hochschild BV Green chain of the prime-clock anomaly at the primes `2, 3`. -/
def frankensteinPrimeClockParacyclicTwoThreeBVGreenChain
    (rho : XiDivisorSupport) :
    DeningerOrdinaryIntegerEnd ⊗[ℂ] DeningerOrdinaryIntegerEnd :=
  deningerBigWittFrobeniusPrimeSeamPairBVGreenChain
    (frankensteinPrimeClockParacyclicAnomaly rho)
    deningerCalderonWittPrimeTwo deningerCalderonWittPrimeThree

/-- The ground diagonal coefficient of the Hochschild boundary of the BV Green chain equals the
`(2, 3)` seam-pair ghost coefficient. -/
theorem frankensteinPrimeClockParacyclicTwoThreeBVGreenChain_groundReadout
    (rho : XiDivisorSupport) :
    deningerOrdinaryIntegerDiagonalCoefficient 1
        (hochschildBoundaryOne
          (frankensteinPrimeClockParacyclicTwoThreeBVGreenChain rho)) =
      deningerBigWittFrobeniusPrimeSeamPairCoefficient
        (frankensteinPrimeClockParacyclicAnomaly rho)
        deningerCalderonWittPrimeTwo deningerCalderonWittPrimeThree := by
  rw [frankensteinPrimeClockParacyclicTwoThreeBVGreenChain,
    deningerBigWittFrobeniusPrimeSeamPairBVGreenChain_groundReadout]

/-- The BV ground readout of `ρ` vanishes iff `Re ρ = 1/2`. -/
theorem frankensteinPrimeClockParacyclicTwoThreeBVGreenChain_groundReadout_eq_zero_iff
    (rho : XiDivisorSupport) :
    deningerOrdinaryIntegerDiagonalCoefficient 1
        (hochschildBoundaryOne
          (frankensteinPrimeClockParacyclicTwoThreeBVGreenChain rho)) = 0 ↔
      (rho : ℂ).re = 1 / 2 := by
  rw [frankensteinPrimeClockParacyclicTwoThreeBVGreenChain_groundReadout,
    deningerBigWittFrobeniusPrimeSeamPairCoefficient_primeClockParacyclic_two_three_eq_zero_iff]

/-- The statement that the BV ground readout vanishes for every zero `ρ` of `Ξ`. -/
def EveryFrankensteinPrimeClockParacyclicTwoThreeBVGroundReadoutVanishes : Prop :=
  ∀ rho : XiDivisorSupport,
    deningerOrdinaryIntegerDiagonalCoefficient 1
      (hochschildBoundaryOne
        (frankensteinPrimeClockParacyclicTwoThreeBVGreenChain rho)) = 0

/-- The BV ground readouts of all zeros of `Ξ` vanish iff the Riemann hypothesis holds (an
equivalence, proving neither side). -/
theorem everyFrankensteinPrimeClockParacyclicTwoThreeBVGroundReadoutVanishes_iff_riemannHypothesis :
    EveryFrankensteinPrimeClockParacyclicTwoThreeBVGroundReadoutVanishes ↔
      RiemannHypothesis := by
  rw [← everyFrankensteinParacyclicAnomalyTailFluxTwoSheetCellVanishes_iff_riemannHypothesis
    (n := 2) (by norm_num) (deningerCalderonWittPrimeTwo, 0)]
  unfold EveryFrankensteinPrimeClockParacyclicTwoThreeBVGroundReadoutVanishes
    EveryFrankensteinParacyclicAnomalyTailFluxTwoSheetCellVanishes
  apply forall_congr'
  intro rho
  rw [frankensteinPrimeClockParacyclicTwoThreeBVGreenChain_groundReadout_eq_zero_iff,
    frankensteinParacyclicAnomalyTailFluxTwoSheetCell_eq_zero_iff (by norm_num)]
theorem frankensteinDeningerCalderonWittPrimeTwo_ne_primeThree :
    deningerCalderonWittPrimeTwo ≠ deningerCalderonWittPrimeThree := by
  intro h
  have hv := congrArg Subtype.val h
  norm_num [deningerCalderonWittPrimeTwo,
    deningerCalderonWittPrimeThree] at hv

/-- Calderón–Witt global Milnor incidence source: the `(2, 3)` seam-pair ghost coefficient times
the cross-prime Gamma witness. -/
def frankensteinPrimeClockParacyclicTwoThreeIncidenceSource
    (rho : XiDivisorSupport) : deningerCalderonWittGlobalMilnorIncidence :=
  deningerBigWittFrobeniusPrimeSeamPairIncidenceSource
    (frankensteinPrimeClockParacyclicAnomaly rho)
    frankensteinDeningerCalderonWittPrimeTwo_ne_primeThree

/-- The global oriented boundary of the incidence source is zero, by exactness of the Milnor
incidence complex. -/
theorem deningerCalderonWittGlobalOrientedBoundary_primeClockParacyclicTwoThreeIncidence_zero
    (rho : XiDivisorSupport) :
    deningerCalderonWittGlobalOrientedBoundary
        (frankensteinPrimeClockParacyclicTwoThreeIncidenceSource rho).1 = 0 := by
  have hcup :
      deningerCalderonWittAlgebraicGlobalExteriorCup
        (frankensteinPrimeClockParacyclicTwoThreeIncidenceSource rho).1 = 0 :=
    (deningerCalderonWittGlobalMilnorIncidence_exact
      (frankensteinPrimeClockParacyclicTwoThreeIncidenceSource rho).1).2
      ⟨frankensteinPrimeClockParacyclicTwoThreeIncidenceSource rho, rfl⟩
  rw [deningerCalderonWittGlobalOrientedBoundary, LinearMap.comp_apply,
    hcup, map_zero]

/-- Selected Ward descent at `ρ`: some linear map sends the oriented boundary of the incidence
source to its Gamma-polarized boundary reflection defect at `α = 1`. -/
def FrankensteinPrimeClockParacyclicSelectedWardDescendsAt
    (rho : XiDivisorSupport) : Prop :=
  ∃ F : (DeningerCalderonWittAlgebraicGlobalDegreeTwo × ℂ) →ₗ[ℂ]
      DeningerCalderonWittGammaScalarProfile,
    F (deningerCalderonWittGlobalOrientedBoundary
        (frankensteinPrimeClockParacyclicTwoThreeIncidenceSource rho).1) =
      deningerCalderonWittGammaPolarizedBoundaryReflectionDefect 1
        (frankensteinPrimeClockParacyclicTwoThreeIncidenceSource rho)

/-- The selected Ward descent at `ρ` exists iff `Re ρ = 1/2`: the boundary is zero, so descent
forces the reflection defect, hence the ghost coefficient, to vanish. -/
theorem frankensteinPrimeClockParacyclicSelectedWardDescendsAt_iff
    (rho : XiDivisorSupport) :
    FrankensteinPrimeClockParacyclicSelectedWardDescendsAt rho ↔
      (rho : ℂ).re = 1 / 2 := by
  constructor
  · rintro ⟨F, hF⟩
    rw [deningerCalderonWittGlobalOrientedBoundary_primeClockParacyclicTwoThreeIncidence_zero,
      map_zero] at hF
    have heval := congrFun (congrFun (congrFun (congrFun hF
      deningerCalderonWittPrimeTwo) deningerCalderonWittPrimeThree) 0) 0
    simp only [Pi.zero_apply] at heval
    rw [frankensteinPrimeClockParacyclicTwoThreeIncidenceSource,
      deningerBigWittFrobeniusPrimeSeamPairIncidence_boundaryDefect] at heval
    have hheight :
        xiGammaEulerBoundaryHalfHeight deningerCalderonWittPrimeTwo 0 ≠
          xiGammaEulerBoundaryHalfHeight deningerCalderonWittPrimeThree 0 :=
      xiGammaEulerBoundaryHalfHeight_ne_of_primes_ne_sameDepth
        frankensteinDeningerCalderonWittPrimeTwo_ne_primeThree 0
    have hextR :
        xiGammaEulerPrimitiveReflectionOddExterior 1
          (deningerCalderonWittPrimeTwo, 0)
          (deningerCalderonWittPrimeThree, 0) ≠ 0 :=
      xiGammaEulerPrimitiveReflectionOddExterior_ne_zero
        (by norm_num) _ _ hheight
    have hextC :
        (xiGammaEulerPrimitiveReflectionOddExterior 1
          (deningerCalderonWittPrimeTwo, 0)
          (deningerCalderonWittPrimeThree, 0) : ℂ) ≠ 0 := by
      exact_mod_cast hextR
    have hcoeff :
        deningerBigWittFrobeniusPrimeSeamPairCoefficient
          (frankensteinPrimeClockParacyclicAnomaly rho)
          deningerCalderonWittPrimeTwo deningerCalderonWittPrimeThree = 0 :=
      (mul_eq_zero.mp heval.symm).resolve_right hextC
    exact
      (deningerBigWittFrobeniusPrimeSeamPairCoefficient_primeClockParacyclic_two_three_eq_zero_iff
        rho).1 hcoeff
  · intro hline
    refine ⟨0, ?_⟩
    rw [deningerCalderonWittGlobalOrientedBoundary_primeClockParacyclicTwoThreeIncidence_zero,
      map_zero]
    have hcoeff :
        deningerBigWittFrobeniusPrimeSeamPairCoefficient
          (frankensteinPrimeClockParacyclicAnomaly rho)
          deningerCalderonWittPrimeTwo deningerCalderonWittPrimeThree = 0 :=
      (deningerBigWittFrobeniusPrimeSeamPairCoefficient_primeClockParacyclic_two_three_eq_zero_iff
        rho).2 hline
    rw [frankensteinPrimeClockParacyclicTwoThreeIncidenceSource,
      deningerBigWittFrobeniusPrimeSeamPairIncidenceSource, hcoeff, zero_smul,
      map_zero]

/-- The statement that the selected Ward descent exists for every zero `ρ` of `Ξ`. -/
def EveryFrankensteinPrimeClockParacyclicSelectedWardDescends : Prop :=
  ∀ rho : XiDivisorSupport,
    FrankensteinPrimeClockParacyclicSelectedWardDescendsAt rho

/-- The selected Ward descent exists for all zeros of `Ξ` iff the Riemann hypothesis holds (an
equivalence, proving neither side). -/
theorem everyFrankensteinPrimeClockParacyclicSelectedWardDescends_iff_riemannHypothesis :
    EveryFrankensteinPrimeClockParacyclicSelectedWardDescends ↔
      RiemannHypothesis := by
  rw [← everyFrankensteinPrimeClockParacyclicTwoThreeBVGroundReadoutVanishes_iff_riemannHypothesis]
  unfold EveryFrankensteinPrimeClockParacyclicSelectedWardDescends
    EveryFrankensteinPrimeClockParacyclicTwoThreeBVGroundReadoutVanishes
  apply forall_congr'
  intro rho
  rw [frankensteinPrimeClockParacyclicSelectedWardDescendsAt_iff,
    frankensteinPrimeClockParacyclicTwoThreeBVGreenChain_groundReadout_eq_zero_iff]

end

end RHTower
