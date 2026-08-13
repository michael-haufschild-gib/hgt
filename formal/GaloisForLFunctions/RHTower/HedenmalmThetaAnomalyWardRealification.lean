import GaloisForLFunctions.RHTower.HedenmalmThetaAnomalyBurnolCovariantAggregationNoGo
import GaloisForLFunctions.RHTower.HedenmalmThetaAnomalyMultiplicativeJetSameFiberWardConservation

/-!
# Same-fibre Ward current as exact realification anomaly

The completed-Xi theta boundary flux supplies an explicit noncovariant anomaly for the universal
Burnol multiplicative-jet connection.  Scale the two-prime frame by the genuine squared norm of
the completed first-divided Xi vector.  The same-fibre law turns the theta boundary current into
`Im(z)` times that multiplicity energy.  Its imaginary numerator counterterm therefore cancels
exactly the anti-Hermitian part of `J=-zE`.

The adjusted numerator is `-Re(z)` times positive mass, and its normalized connection is `Re(z)`.
This realizes the anomaly class isolated by P-G122, but does not prove RH: Ward realification
absorbs radial charge rather than proving it absent.  Equality of raw and realified connections is
exactly critical-line placement, globally equivalent to RH.
-/

open Complex Real MeasureTheory Set Filter Topology
open scoped ENNReal InnerProductSpace ComplexConjugate

noncomputable section

namespace RHTower

open HedenmalmThetaSource

/-- Genuine multiplicity-scaled mass of the two-prime arithmetic frame. -/
def thetaXiWardRealificationMass (q : XiZeroCopy) : ℝ :=
  burnolTwoPrimeFrameEnergy (xiSpectralPoint q) *
    ‖completedXiFirstDividedL2 q.1‖ ^ 2

/-- Source-derived imaginary numerator counterterm supplied by compact-theta boundary flux. -/
def thetaXiWardRealificationAnomaly (q : XiZeroCopy) : ℂ :=
  Complex.I * ((burnolTwoPrimeFrameEnergy (xiSpectralPoint q) *
    (Real.pi * thetaSource.mass * thetaXiRankTwoBoundaryFlux q) : ℝ) : ℂ)

/-- Raw multiplicative-jet numerator at genuine Xi multiplicity, plus Ward anomaly. -/
def thetaXiWardRealifiedNumerator (q : XiZeroCopy) : ℂ :=
  burnolMultiplicativeJetConnectionNumerator (xiSpectralPoint q) *
      (‖completedXiFirstDividedL2 q.1‖ ^ 2 : ℂ) +
    thetaXiWardRealificationAnomaly q

/-- P-G122 singleton family representing fixed `2*3` arithmetic frame. -/
def thetaXiWardFactorizationFamily : Finset BurnolFactorizationFrameIndex :=
  {(2, 3)}

/-- Genuine Xi multiplicity weight on the singleton factorization family. -/
def thetaXiWardFactorizationWeight (q : XiZeroCopy) :
    BurnolFactorizationFrameIndex → ℂ :=
  fun _ => (‖completedXiFirstDividedL2 q.1‖ ^ 2 : ℂ)

/-- Singleton P-G122 aggregate mass is exactly genuine Ward realification mass. -/
theorem thetaXiWard_aggregateMass_eq (q : XiZeroCopy) :
    burnolFactorizationAggregateMass thetaXiWardFactorizationFamily
        (thetaXiWardFactorizationWeight q) (xiSpectralPoint q) =
      (thetaXiWardRealificationMass q : ℂ) := by
  simp [burnolFactorizationAggregateMass, thetaXiWardFactorizationFamily,
    thetaXiWardFactorizationWeight, burnolFactorizationPairFrameEnergy_two_three,
    thetaXiWardRealificationMass]
  ring

/-- Singleton P-G122 aggregate numerator is raw jet numerator at genuine Xi multiplicity. -/
theorem thetaXiWard_aggregateNumerator_eq (q : XiZeroCopy) :
    burnolFactorizationAggregateNumerator thetaXiWardFactorizationFamily
        (thetaXiWardFactorizationWeight q) (xiSpectralPoint q) =
      burnolMultiplicativeJetConnectionNumerator (xiSpectralPoint q) *
        (‖completedXiFirstDividedL2 q.1‖ ^ 2 : ℂ) := by
  simp [burnolFactorizationAggregateNumerator, thetaXiWardFactorizationFamily,
    thetaXiWardFactorizationWeight, burnolFactorizationJetConnectionNumerator_two_three]
  ring

/-- Multiplicity-scaled Ward mass is strictly positive on every Xi copy. -/
theorem thetaXiWardRealificationMass_pos (q : XiZeroCopy) :
    0 < thetaXiWardRealificationMass q := by
  rw [thetaXiWardRealificationMass]
  exact mul_pos (burnolTwoPrimeFrameEnergy_pos (xiSpectralPoint q))
    (sq_pos_of_pos (norm_pos_iff.mpr (completedXiFirstDividedL2_ne_zero q.1)))

/-! ## Exact anomaly and realification -/

/-- **Source-derived anomaly law.**  Theta boundary flux supplies exactly `i Im(z)` times positive
multiplicity-scaled frame mass. -/
theorem thetaXiWardRealificationAnomaly_eq (q : XiZeroCopy) :
    thetaXiWardRealificationAnomaly q =
      Complex.I * ((xiSpectralPoint q).im : ℂ) *
        (thetaXiWardRealificationMass q : ℂ) := by
  rw [thetaXiWardRealificationAnomaly,
    thetaXiRankTwoBoundaryFlux_completedXi_sameFiber, thetaXiWardRealificationMass]
  push_cast
  ring

/-- Ward counterterm is literally the noncovariant anomaly classified by P-G122, with no mass
counterterm. -/
theorem thetaXiWardRealificationAnomaly_is_pG122_anomaly (q : XiZeroCopy) :
    burnolFactorizationRenormalizationAnomaly
        (xiSpectralPoint q) 0 (thetaXiWardRealificationAnomaly q) =
      thetaXiWardRealificationAnomaly q := by
  rw [burnolFactorizationRenormalizationAnomaly]
  ring

/-- **Division-free Ward realification.**  Adjusted jet numerator is the real spectral coordinate
times positive mass, with conventional connection sign. -/
theorem thetaXiWardRealifiedNumerator_eq (q : XiZeroCopy) :
    thetaXiWardRealifiedNumerator q =
      -((xiSpectralPoint q).re : ℂ) *
        (thetaXiWardRealificationMass q : ℂ) := by
  rw [thetaXiWardRealifiedNumerator, thetaXiWardRealificationAnomaly_eq,
    burnolMultiplicativeJetConnectionNumerator_eq, thetaXiWardRealificationMass]
  push_cast
  have hz := Complex.re_add_im (xiSpectralPoint q)
  nth_rewrite 1 [← hz]
  ring

/-- Normalized Ward-adjusted multiplicative-jet connection. -/
def thetaXiWardRealifiedConnection (q : XiZeroCopy) : ℂ :=
  -thetaXiWardRealifiedNumerator q /
    (thetaXiWardRealificationMass q : ℂ)

/-- **Ward realification theorem.**  Source anomaly projects universal connection `z` exactly to
its real part on every Xi multiplicity copy. -/
theorem thetaXiWardRealifiedConnection_eq (q : XiZeroCopy) :
    thetaXiWardRealifiedConnection q = ((xiSpectralPoint q).re : ℂ) := by
  rw [thetaXiWardRealifiedConnection, thetaXiWardRealifiedNumerator_eq]
  have hmass : (thetaXiWardRealificationMass q : ℂ) ≠ 0 := by
    exact_mod_cast (thetaXiWardRealificationMass_pos q).ne'
  field_simp

/-- Ward realified connection is exactly P-G122 adjusted singleton connection. -/
theorem thetaXiWardRealifiedConnection_is_pG122_adjusted (q : XiZeroCopy) :
    burnolFactorizationAdjustedConnection thetaXiWardFactorizationFamily
        (thetaXiWardFactorizationWeight q) (xiSpectralPoint q) 0
        (thetaXiWardRealificationAnomaly q) =
      thetaXiWardRealifiedConnection q := by
  rw [burnolFactorizationAdjustedConnection, thetaXiWard_aggregateMass_eq,
    thetaXiWard_aggregateNumerator_eq, thetaXiWardRealifiedConnection,
    thetaXiWardRealifiedNumerator]
  ring

/-! ## Exact obstruction boundary -/

/-- Source-derived anomaly vanishes exactly when spectral coordinate is real. -/
theorem thetaXiWardRealificationAnomaly_eq_zero_iff (q : XiZeroCopy) :
    thetaXiWardRealificationAnomaly q = 0 ↔ (xiSpectralPoint q).im = 0 := by
  rw [thetaXiWardRealificationAnomaly_eq]
  have hmass : (thetaXiWardRealificationMass q : ℂ) ≠ 0 := by
    exact_mod_cast (thetaXiWardRealificationMass_pos q).ne'
  constructor
  · intro h
    rcases mul_eq_zero.mp h with hleft | hmasszero
    · rcases mul_eq_zero.mp hleft with hIzero | him
      · exact (Complex.I_ne_zero hIzero).elim
      · exact Complex.ofReal_eq_zero.mp him
    · exact (hmass hmasszero).elim
  · intro him
    rw [him]
    norm_num

/-- Raw and Ward-realified connections agree exactly when anomaly vanishes. -/
theorem thetaXiWardRealifiedConnection_eq_spectral_iff (q : XiZeroCopy) :
    thetaXiWardRealifiedConnection q = xiSpectralPoint q ↔
      (xiSpectralPoint q).im = 0 := by
  rw [thetaXiWardRealifiedConnection_eq]
  constructor
  · intro h
    have hi := congrArg Complex.im h
    simpa using hi.symm
  · intro him
    rw [← Complex.re_add_im (xiSpectralPoint q), him]
    simp

/-- Equality of raw and realified connections on one Xi copy is critical-line placement. -/
theorem thetaXiWardRealifiedConnection_eq_spectral_iff_line (q : XiZeroCopy) :
    thetaXiWardRealifiedConnection q = xiSpectralPoint q ↔
      (q.1 : ℂ).re = 1 / 2 := by
  rw [thetaXiWardRealifiedConnection_eq_spectral_iff, xiSpectralPoint_im_eq]
  constructor <;> intro h <;> linarith

/-- Global raw/realified equality is an exact RH criterion, not an unconditional conclusion. -/
theorem all_thetaXiWardRealifiedConnections_eq_spectral_iff_riemannHypothesis :
    (∀ q : XiZeroCopy,
      thetaXiWardRealifiedConnection q = xiSpectralPoint q) ↔ RiemannHypothesis := by
  rw [← all_thetaXiRankTwoBoundaryFlux_eq_zero_iff_riemannHypothesis]
  constructor
  · intro h q
    apply (thetaXiRankTwoBoundaryFlux_eq_zero_iff_spectralIm_eq_zero q).mpr
    exact (thetaXiWardRealifiedConnection_eq_spectral_iff q).mp (h q)
  · intro h q
    apply (thetaXiWardRealifiedConnection_eq_spectral_iff q).mpr
    exact (thetaXiRankTwoBoundaryFlux_eq_zero_iff_spectralIm_eq_zero q).mp (h q)

end RHTower
