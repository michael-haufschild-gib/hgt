import GaloisForLFunctions.HTGeometry.TripticMultiplicativeKernel
import GaloisForLFunctions.HTGeometry.TripticCompleteness

/-!
# The kernel of the multiplicative orbital charge is exactly the differentially algebraic part

A logarithmic derivative carries its whole orbital divisor in order `-1`, where it is the shift
order; so the orbital charge of a multiplicative source is the order `-1` orbital divisor of its
logarithmic derivative.  The additive kernel theorem and its converse therefore transfer verbatim:
the charge vanishes on every orbit exactly when the logarithmic derivative is differentially
algebraic.

* `tripticOrbitCharge_eq_zero_of_differentiallyAlgebraic`;
* `differentiallyAlgebraic_logDeriv_iff_tripticOrbitCharge_eq_zero`.
-/

open Filter Set Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {Y : ℂ → ℂ} {τ σ : ℂ}

/-- **A multiplicative triptic source with differentially algebraic logarithmic derivative has
vanishing orbital charge.** -/
theorem tripticOrbitCharge_eq_zero_of_differentiallyAlgebraic
    (hY : MeromorphicOn Y (Set.univ : Set ℂ)) (hfin : ∀ w : ℂ, meromorphicOrderAt Y w ≠ ⊤)
    (hYper : ∀ z : ℂ, Y (z + 1) = Y z)
    {Cst : ℂ} (hmixed : MixedConstGerm (logDeriv Y) τ σ Cst)
    (hτ : 0 < τ.im) (hσ : 0 < σ.im) (hindep : IndepPeriods τ σ)
    (hindepτ : LinearIndependent ℝ ![(1 : ℂ), τ]) (hindepσ : LinearIndependent ℝ ![(1 : ℂ), σ])
    (hperiods : LinearIndependent ℚ (ellipticGammaSourcePeriods τ σ))
    (hDA : DifferentiallyAlgebraic (toMeromorphicNFOn (logDeriv Y) (Set.univ : Set ℂ)))
    (p : ℂ) : tripticOrbitCharge Y σ p = 0 := by
  have hFmero : MeromorphicOn (logDeriv Y) (Set.univ : Set ℂ) := fun z _ ↦
    ((hY z (Set.mem_univ z)).deriv).div (hY z (Set.mem_univ z))
  have hFper : PeriodicOneGerm (logDeriv Y) := by
    refine periodicOneGerm_of_forall fun z ↦ ?_
    have hfun : (fun w : ℂ ↦ Y (w + 1)) = Y := funext hYper
    have hd : deriv Y (z + 1) = deriv Y z := by
      have hcomp := deriv_comp_add_const (f := Y) (a := (1 : ℂ)) z
      rw [hfun] at hcomp
      exact hcomp.symm
    rw [logDeriv_apply, logDeriv_apply, hd, hYper z]
  have hzero := additiveOrbitalDivisorAt_eq_zero_of_differentiallyAlgebraic hFmero hFper hmixed
    hτ hσ hindep hindepτ hindepσ hperiods hDA p (-1) (by norm_num)
  rw [additiveOrbitalDivisorAt_neg_one, additiveOrbitalDivisor] at hzero
  have hterm : ∀ m : ℤ,
      laurentCoeff (fun z ↦ logDeriv Y (z + σ) - logDeriv Y z) (p + (m : ℂ) * σ) (-1)
        = ((shiftOrder Y σ (p + (m : ℂ) * σ) : ℤ) : ℂ) := fun m ↦
    laurentCoeff_shiftDiff_logDeriv hY hfin σ _
  rw [finsum_congr hterm, ← intCast_finsum] at hzero
  have hval : (∑ᶠ m : ℤ, shiftOrder Y σ (p + (m : ℂ) * σ)) = tripticOrbitCharge Y σ p := rfl
  rw [hval] at hzero
  exact_mod_cast hzero

/-- **The kernel of the multiplicative orbital charge.**  A multiplicative triptic source has a
differentially algebraic logarithmic derivative exactly when its orbital charge vanishes on every
orbit. -/
theorem differentiallyAlgebraic_logDeriv_iff_tripticOrbitCharge_eq_zero
    (hY : MeromorphicOn Y (Set.univ : Set ℂ)) (hfin : ∀ w : ℂ, meromorphicOrderAt Y w ≠ ⊤)
    (hYper : ∀ z : ℂ, Y (z + 1) = Y z)
    {Cst : ℂ} (hmixedPt : ∀ z : ℂ, logDeriv Y (z + τ + σ) - logDeriv Y (z + τ)
      - logDeriv Y (z + σ) + logDeriv Y z = Cst)
    (hτ : 0 < τ.im) (hσ : 0 < σ.im) (hindep : IndepPeriods τ σ)
    (hindepτ : LinearIndependent ℝ ![(1 : ℂ), τ]) (hindepσ : LinearIndependent ℝ ![(1 : ℂ), σ])
    (hperiods : LinearIndependent ℚ (ellipticGammaSourcePeriods τ σ)) :
    DifferentiallyAlgebraic (toMeromorphicNFOn (logDeriv Y) (Set.univ : Set ℂ))
      ↔ ∀ p : ℂ, tripticOrbitCharge Y σ p = 0 := by
  constructor
  · intro hDA p
    exact tripticOrbitCharge_eq_zero_of_differentiallyAlgebraic hY hfin hYper
      (mixedConstGerm_of_forall hmixedPt) hτ hσ hindep hindepτ hindepσ hperiods hDA p
  · intro hcharge
    exact (differentiallyAlgebraic_logDeriv_of_vanishing_orbitCharge hY hfin hYper hmixedPt hτ hσ
      (indepTriple_of_indepPeriods hindep) hindepτ hindepσ hcharge).2

end

end GaloisForLFunctions.HTGeometry
