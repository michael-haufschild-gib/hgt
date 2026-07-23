import GaloisForLFunctions.RHTower.PrimeArchHankelDeterminantCriterion
import GaloisForLFunctions.RHTower.PrimeArchUniversalStrictHankelRayAdjoiningUniversalityLaw

/-!
# Prime--arch exact reconstruction and all strict Hankel rays

The existing adjoining theorem classifies RH after fixing one arbitrary strict Hankel moment ray.
Quantifying that theorem over every strict ray produces a genuinely universal closure phase.
Exact prime--archimedean source reconstruction is precisely this phase: finite Hilbert recovery of
the prescribed source packets controls every further strict `HTGeometry` spectral ray at once.

The complementary law is synchronized.  If exact reconstruction fails, no strict auxiliary ray
can repair the enlarged cone.
-/

namespace RHTower

noncomputable section

/-- A real moment sequence whose Hankel matrices are positive definite at every finite depth. -/
def PrimeArchStrictHankelRay (q : ℕ → ℝ) : Prop :=
  ∀ n : ℕ, (HTGeometry.momentHankelMatrix q n).PosDef

/-- Strict positivity of every nonzero nonnegative mixture after adjoining one moment ray. -/
def PrimeArchStrictHankelRayAdjoiningCone (q : ℕ → ℝ) : Prop :=
  ∀ (scaleLog : ℂ) (alpha beta gamma delta : ℝ),
    0 ≤ alpha → 0 ≤ beta → 0 ≤ gamma → 0 ≤ delta →
      0 < alpha + beta + gamma + delta →
        ∀ n : ℕ,
          (HTGeometry.momentHankelMatrix
            (primeArchAdjoinedStrictHankelMixedClock
              q scaleLog alpha beta gamma delta) n).PosDef

/-- Closure of the prime--archimedean cone under every strict Hankel moment ray. -/
def PrimeArchAllStrictHankelRayAdjoiningPhase : Prop :=
  ∀ q : ℕ → ℝ, PrimeArchStrictHankelRay q →
    PrimeArchStrictHankelRayAdjoiningCone q

/-- Synchronized failure: every strict auxiliary ray yields a non-strict enlarged cone. -/
def PrimeArchAllStrictHankelRayAdjoiningFailurePhase : Prop :=
  ∀ q : ℕ → ℝ, PrimeArchStrictHankelRay q →
    ¬PrimeArchStrictHankelRayAdjoiningCone q

/-- **All-strict-ray universality law.**  Simultaneous adjoining closure for every strict
`HTGeometry` Hankel ray is exactly RH.  The reverse implication uses the unconditional
black-hole far-zone ray, so the universal interface has no existence hypothesis. -/
theorem primeArchAllStrictHankelRayAdjoiningPhase_iff_riemannHypothesis :
    PrimeArchAllStrictHankelRayAdjoiningPhase ↔ RiemannHypothesis := by
  constructor
  · intro hall
    let q : ℕ → ℝ := HTGeometry.normalizedBlackHoleFarZoneJet 0
    have hq : PrimeArchStrictHankelRay q := fun n =>
      HTGeometry.normalizedBlackHoleFarZoneJet_hankel_posDef 0 n
    exact
      (riemannHypothesis_iff_primeArch_adjoin_any_strictHankelRay q hq).2
        (hall q hq)
  · intro hRH q hq
    exact
      (riemannHypothesis_iff_primeArch_adjoin_any_strictHankelRay q hq).1 hRH

/-- **Exact-reconstruction/all-ray connector.**  Exact dual recovery of every finite prescribed
prime--arch source packet is equivalent to closure under every strict Hankel ray. -/
theorem
    primeArchSourceMomentHankelExactReconstructionPhase_iff_allStrictHankelRayAdjoiningPhase :
    PrimeArchSourceMomentHankelExactReconstructionPhase ↔
      PrimeArchAllStrictHankelRayAdjoiningPhase :=
  primeArchSourceMomentHankelExactReconstructionPhase_iff_riemannHypothesis.trans
    primeArchAllStrictHankelRayAdjoiningPhase_iff_riemannHypothesis.symm

/-- **Synchronized all-ray failure law.**  Failure of RH means that every strict auxiliary
Hankel ray still leaves a non-strict enlarged cone. -/
theorem not_riemannHypothesis_iff_primeArchAllStrictHankelRayAdjoiningFailurePhase :
    ¬RiemannHypothesis ↔ PrimeArchAllStrictHankelRayAdjoiningFailurePhase := by
  constructor
  · intro hnotRH q hq hcone
    exact hnotRH
      ((riemannHypothesis_iff_primeArch_adjoin_any_strictHankelRay q hq).2 hcone)
  · intro hfailure hRH
    let q : ℕ → ℝ := HTGeometry.normalizedBlackHoleFarZoneJet 0
    have hq : PrimeArchStrictHankelRay q := fun n =>
      HTGeometry.normalizedBlackHoleFarZoneJet_hankel_posDef 0 n
    exact (hfailure q hq)
      ((riemannHypothesis_iff_primeArch_adjoin_any_strictHankelRay q hq).1 hRH)

/-- Exact reconstruction fails exactly when every strict auxiliary Hankel ray fails to rescue the
enlarged cone. -/
theorem
    not_primeArchSourceMomentHankelExactReconstructionPhase_iff_allStrictHankelRayAdjoiningFailurePhase :
    ¬PrimeArchSourceMomentHankelExactReconstructionPhase ↔
      PrimeArchAllStrictHankelRayAdjoiningFailurePhase :=
  (not_congr
    primeArchSourceMomentHankelExactReconstructionPhase_iff_riemannHypothesis).trans
      not_riemannHypothesis_iff_primeArchAllStrictHankelRayAdjoiningFailurePhase

/-- Failure of closure for merely one strict ray is already synchronized failure for every strict
ray. -/
theorem
    not_primeArchAllStrictHankelRayAdjoiningPhase_iff_allStrictHankelRayAdjoiningFailurePhase :
    ¬PrimeArchAllStrictHankelRayAdjoiningPhase ↔
      PrimeArchAllStrictHankelRayAdjoiningFailurePhase :=
  (not_congr
    primeArchAllStrictHankelRayAdjoiningPhase_iff_riemannHypothesis).trans
      not_riemannHypothesis_iff_primeArchAllStrictHankelRayAdjoiningFailurePhase

end

end RHTower
