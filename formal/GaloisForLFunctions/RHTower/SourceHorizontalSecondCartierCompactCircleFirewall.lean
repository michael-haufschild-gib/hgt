import GaloisForLFunctions.RHTower.SourceHorizontalSecondCartierOrbitCoercivity
import GaloisForLFunctions.HTGeometry.PureSingularCarrierTrichotomy

open Complex Filter Topology MeasureTheory
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-!
# Compact-circle firewall for the literal source-horizontal Xi endpoint

The second-Cartier coercivity leaf proves that every occupied strict-right Xi endpoint has a
non-moderate, coefficient-faithful bilateral ghost.  The HTGeometry corpus supplies the literal
two-sided Fourier moments of a finite positive circle measure.  This leaf identifies the exact
cross-corpus consequence: finite circle moments are uniformly bounded and hence moderate, so no
finite positive circle measure can represent the endpoint ghost on a strict-right Xi fibre.

This rules out compact positive-measure, Toeplitz, and Bochner admission of the already-constructed
endpoint without changing its prime, divisor, clock, conormal coefficient, or Hardy orientation.
Universal representability is exactly RH because RH empties the strict-right support and any
off-line copy violates the finite-measure bound.
-/

/-- The precise circle-measure carrier used by the HTGeometry Fourier-moment construction.
The explicit measurable-space parameter avoids conflating it with Mathlib's independent global
circle measurable-space instance. -/
abbrev SourceHorizontalHTCircleMeasure :=
  @Measure Circle
    GaloisForLFunctions.HTGeometry.instMeasurableSpaceCircle_galoisForLFunctions

/-- Fourier moments of every finite positive circle measure have polynomial two-sided growth
(in fact, they are uniformly bounded by total mass). -/
theorem circleMeasureMomentZ_bilateralModerate
    (mu : SourceHorizontalHTCircleMeasure) [IsFiniteMeasure mu] :
    bilateralModerate (circleMeasureMomentZ mu) := by
  refine ⟨mu.real Set.univ, 0, fun e => ?_⟩
  simp only [pow_zero, mul_one]
  unfold circleMeasureMomentZ
  calc
    ‖∫ z : Circle, (z : ℂ) ^ (-e) ∂mu‖ ≤
        1 * mu.real Set.univ :=
      norm_integral_le_of_norm_le_const
        (Filter.Eventually.of_forall fun z => by simp [norm_zpow])
    _ = mu.real Set.univ := one_mul _

/-- Exact compact-circle representation of the literal coefficient-faithful endpoint ghost.
All arithmetic labels remain parameters of the represented family; no scalar refitting is allowed.
-/
def SourceHorizontalActualXiEndpointCompactCircleRepresentation
    (x u : ℝ) (q : XiRightZeroCopy) (r : ℝ) (N : ℕ)
    (p : Nat.Primes) : Prop :=
  ∃ mu : SourceHorizontalHTCircleMeasure, IsFiniteMeasure mu ∧
    ∀ e : ℤ,
      circleMeasureMomentZ mu e =
        (sourceHorizontalActualXiEndpointSecondJetHardyDescent x u q r N p
          sourceHorizontalBilateralSecondJetGhost) e

/-- No occupied strict-right Xi endpoint has an exact finite positive circle-measure
representation.  This is the coefficient-faithful compact/Toeplitz firewall. -/
theorem not_sourceHorizontalActualXiEndpointCompactCircleRepresentation
    {x u r : ℝ} (q : XiRightZeroCopy)
    (hkappa : routePTwoPrimeJuliaWardNonlocalCoupling x u ≠ 0) (hr : r ≠ 0)
    (N : ℕ) (hjet : 0 < sourceHorizontalWoldBVGreenStokesEndpointThirdJet N)
    (p : Nat.Primes) :
    ¬ SourceHorizontalActualXiEndpointCompactCircleRepresentation x u q r N p := by
  rintro ⟨mu, hmu, heq⟩
  letI : IsFiniteMeasure mu := hmu
  apply not_bilateralModerate_sourceHorizontalActualXiEndpointSecondJetHardyDescent_ghost
    q hkappa hr N hjet p
  have hfun : circleMeasureMomentZ mu =
      sourceHorizontalActualXiEndpointSecondJetHardyDescent x u q r N p
        sourceHorizontalBilateralSecondJetGhost := funext heq
  rw [← hfun]
  exact circleMeasureMomentZ_bilateralModerate mu

/-- The literal non-spectral conormal short cannot coerce the reciprocal orbit.  On every
occupied strict-right Xi fibre, no scalar multiple of its static value `4‖c‖²` bounds the
coefficient-faithful positive two-sided energy. -/
theorem not_exists_sourceHorizontalActualXiLiteralConormalShort_orbit_budget
    {x u r : ℝ} (q : XiRightZeroCopy)
    (hkappa : routePTwoPrimeJuliaWardNonlocalCoupling x u ≠ 0) (hr : r ≠ 0)
    (N : ℕ) (hjet : 0 < sourceHorizontalWoldBVGreenStokesEndpointThirdJet N)
    (p : Nat.Primes) :
    ¬ ∃ C : ℝ, ∀ n : ℕ,
      sourceHorizontalSecondCartierKreinPositiveOrbitEnergy
          (sourceHorizontalSecondCartierKreinPolarizedGhostOrbit
            (sourceHorizontalActualXiSecondCartierKreinPrimeCharacter q p)
            (sourceHorizontalActualXiSecondCartierKreinScale x u q r N) n) ≤
        C * sourceHorizontalLiteralConormalShort
          (sourceHorizontalActualXiConormalCoefficient x u q r) := by
  rintro ⟨C, hC⟩
  have hescape :=
    tendsto_sourceHorizontalActualXiSecondCartierKreinPolarizedGhostOrbit_energy_atTop
      q hkappa hr N hjet p
  obtain ⟨n, hn⟩ :=
    (hescape.eventually_gt_atTop
      (C * sourceHorizontalLiteralConormalShort
        (sourceHorizontalActualXiConormalCoefficient x u q r))).exists
  exact (not_lt_of_ge (hC n)) hn

/-- Simultaneous finite positive circle-measure admission over every strict-right Xi copy. -/
def EverySourceHorizontalActualXiEndpointCompactCircleRepresentation
    (x u r : ℝ) (N : ℕ) (p : Nat.Primes) : Prop :=
  ∀ q : XiRightZeroCopy,
    SourceHorizontalActualXiEndpointCompactCircleRepresentation x u q r N p

/-- Exact global firewall: universal compact positive-measure representation of the literal
endpoint family is RH-equivalent, rather than an unconditional output of existing source order.
-/
theorem everySourceHorizontalActualXiEndpointCompactCircleRepresentation_iff_rh
    {x u r : ℝ}
    (hkappa : routePTwoPrimeJuliaWardNonlocalCoupling x u ≠ 0) (hr : r ≠ 0)
    (N : ℕ) (hjet : 0 < sourceHorizontalWoldBVGreenStokesEndpointThirdJet N)
    (p : Nat.Primes) :
    EverySourceHorizontalActualXiEndpointCompactCircleRepresentation x u r N p ↔
      RiemannHypothesis := by
  constructor
  · intro hrepresentation
    by_contra hRH
    obtain ⟨q⟩ := nonempty_xiRightZeroCopy_of_not_riemannHypothesis hRH
    exact not_sourceHorizontalActualXiEndpointCompactCircleRepresentation
      q hkappa hr N hjet p (hrepresentation q)
  · intro hRH q
    haveI : IsEmpty XiRightZeroCopy := isEmpty_xiRightZeroCopy_of_riemannHypothesis hRH
    exact isEmptyElim q

end

end RHTower
