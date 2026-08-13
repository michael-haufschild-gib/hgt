import GaloisForLFunctions.RHTower.HedenmalmThetaAnomalyBurnolGeneralFactorizationJetConnection

/-!
# Covariant aggregation cannot select the critical line

Every valid Burnol multiplicative factorization frame carries the same division-free connection
law `J = -z E`.  Arbitrary finite complex weights preserve that law.  Subtracting a mass
counterterm `C` preserves covariance precisely when the numerator counterterm is `z*C`; every
nondegenerate covariant renormalization still reconstructs `z`.

For an arbitrary numerator counterterm `K`, the unique obstruction is the anomaly `K-z*C`.
Therefore aggregation cannot manufacture a critical-line selector: a successful completion must
supply a source-derived orientation anomaly or a channelwise boundary condition.
-/

open Complex Real Filter Topology

namespace RHTower.HedenmalmThetaSource

noncomputable section

/-- Index of one multiplicative factorization frame. -/
abbrev BurnolFactorizationFrameIndex := ℕ × ℕ

/-- Complex-weighted mass of a finite family of factorization frames. -/
def burnolFactorizationAggregateMass
    (S : Finset BurnolFactorizationFrameIndex)
    (weight : BurnolFactorizationFrameIndex → ℂ) (z : ℂ) : ℂ :=
  ∑ a ∈ S, weight a * (burnolFactorizationPairFrameEnergy a.1 a.2 z : ℂ)

/-- Complex-weighted Hermitian jet numerator of a finite factorization family. -/
def burnolFactorizationAggregateNumerator
    (S : Finset BurnolFactorizationFrameIndex)
    (weight : BurnolFactorizationFrameIndex → ℂ) (z : ℂ) : ℂ :=
  ∑ a ∈ S, weight a * burnolFactorizationJetConnectionNumerator a.1 a.2 z

/-- **Finite aggregation no-go.**  Every finite linear combination of valid factorization frames
still lies on the same universal connection line. -/
theorem burnolFactorizationAggregateNumerator_eq
    {S : Finset BurnolFactorizationFrameIndex}
    {weight : BurnolFactorizationFrameIndex → ℂ}
    (hvalid : ∀ a ∈ S, 1 < a.1 ∧ 1 < a.2) (z : ℂ) :
    burnolFactorizationAggregateNumerator S weight z =
      -z * burnolFactorizationAggregateMass S weight z := by
  rw [burnolFactorizationAggregateNumerator, burnolFactorizationAggregateMass]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  rw [burnolFactorizationJetConnectionNumerator_eq
    (hvalid a ha).1 (hvalid a ha).2]
  ring

/-! ## Covariance-preserving scalar renormalization -/

/-- Aggregate mass after subtracting one scalar counterterm. -/
def burnolFactorizationRenormalizedMass
    (S : Finset BurnolFactorizationFrameIndex)
    (weight : BurnolFactorizationFrameIndex → ℂ) (z counterterm : ℂ) : ℂ :=
  burnolFactorizationAggregateMass S weight z - counterterm

/-- Covariantly renormalized numerator. -/
def burnolFactorizationRenormalizedNumerator
    (S : Finset BurnolFactorizationFrameIndex)
    (weight : BurnolFactorizationFrameIndex → ℂ) (z counterterm : ℂ) : ℂ :=
  burnolFactorizationAggregateNumerator S weight z + z * counterterm

/-- Covariant subtraction preserves the universal division-free connection law exactly. -/
theorem burnolFactorizationRenormalizedNumerator_eq
    {S : Finset BurnolFactorizationFrameIndex}
    {weight : BurnolFactorizationFrameIndex → ℂ}
    (hvalid : ∀ a ∈ S, 1 < a.1 ∧ 1 < a.2) (z counterterm : ℂ) :
    burnolFactorizationRenormalizedNumerator S weight z counterterm =
      -z * burnolFactorizationRenormalizedMass S weight z counterterm := by
  rw [burnolFactorizationRenormalizedNumerator, burnolFactorizationRenormalizedMass,
    burnolFactorizationAggregateNumerator_eq hvalid]
  ring

/-- **Counterterm rigidity.**  Compatibility with a prescribed mass subtraction uniquely forces
the numerator counterterm to be `z*C`. -/
theorem burnolFactorizationCovariantCounterterm_unique
    {S : Finset BurnolFactorizationFrameIndex}
    {weight : BurnolFactorizationFrameIndex → ℂ}
    (hvalid : ∀ a ∈ S, 1 < a.1 ∧ 1 < a.2)
    {z counterterm numeratorCounterterm : ℂ}
    (hcovariant :
      burnolFactorizationAggregateNumerator S weight z + numeratorCounterterm =
        -z * (burnolFactorizationAggregateMass S weight z - counterterm)) :
    numeratorCounterterm = z * counterterm := by
  rw [burnolFactorizationAggregateNumerator_eq hvalid] at hcovariant
  linear_combination hcovariant

/-! ## Exact classification of noncovariant renormalization -/

/-- Unique anomaly left by an arbitrary numerator counterterm. -/
def burnolFactorizationRenormalizationAnomaly
    (z counterterm numeratorCounterterm : ℂ) : ℂ :=
  numeratorCounterterm - z * counterterm

theorem burnolFactorizationRenormalizationAnomaly_eq_zero_iff
    {z counterterm numeratorCounterterm : ℂ} :
    burnolFactorizationRenormalizationAnomaly z counterterm numeratorCounterterm = 0 ↔
      numeratorCounterterm = z * counterterm := by
  rw [burnolFactorizationRenormalizationAnomaly, sub_eq_zero]

/-- Arbitrarily adjusted numerator equals covariant current plus unique anomaly. -/
theorem burnolFactorizationAdjustedNumerator_eq
    {S : Finset BurnolFactorizationFrameIndex}
    {weight : BurnolFactorizationFrameIndex → ℂ}
    (hvalid : ∀ a ∈ S, 1 < a.1 ∧ 1 < a.2)
    (z counterterm numeratorCounterterm : ℂ) :
    burnolFactorizationAggregateNumerator S weight z + numeratorCounterterm =
      -z * (burnolFactorizationAggregateMass S weight z - counterterm) +
        burnolFactorizationRenormalizationAnomaly z counterterm numeratorCounterterm := by
  rw [burnolFactorizationAggregateNumerator_eq hvalid,
    burnolFactorizationRenormalizationAnomaly]
  ring

/-- Normalized connection after arbitrary scalar mass and numerator counterterms. -/
def burnolFactorizationAdjustedConnection
    (S : Finset BurnolFactorizationFrameIndex)
    (weight : BurnolFactorizationFrameIndex → ℂ)
    (z counterterm numeratorCounterterm : ℂ) : ℂ :=
  -(burnolFactorizationAggregateNumerator S weight z + numeratorCounterterm) /
    (burnolFactorizationAggregateMass S weight z - counterterm)

/-- **Exact anomaly quotient.**  Every departure from spectral coordinate is normalized
noncovariant counterterm anomaly, and nothing else. -/
theorem burnolFactorizationAdjustedConnection_eq
    {S : Finset BurnolFactorizationFrameIndex}
    {weight : BurnolFactorizationFrameIndex → ℂ}
    (hvalid : ∀ a ∈ S, 1 < a.1 ∧ 1 < a.2)
    {z counterterm numeratorCounterterm : ℂ}
    (hmass : burnolFactorizationAggregateMass S weight z - counterterm ≠ 0) :
    burnolFactorizationAdjustedConnection S weight z counterterm numeratorCounterterm =
      z - burnolFactorizationRenormalizationAnomaly z counterterm numeratorCounterterm /
        (burnolFactorizationAggregateMass S weight z - counterterm) := by
  rw [burnolFactorizationAdjustedConnection,
    burnolFactorizationAdjustedNumerator_eq hvalid z counterterm numeratorCounterterm]
  field_simp
  ring

/-! ## Presentation independence of covariant renormalization -/

/-- Normalized connection of a covariantly renormalized finite aggregate. -/
def burnolFactorizationRenormalizedConnection
    (S : Finset BurnolFactorizationFrameIndex)
    (weight : BurnolFactorizationFrameIndex → ℂ) (z counterterm : ℂ) : ℂ :=
  -burnolFactorizationRenormalizedNumerator S weight z counterterm /
    burnolFactorizationRenormalizedMass S weight z counterterm

/-- Every nondegenerate covariantly renormalized finite aggregate reconstructs exactly `z`. -/
theorem burnolFactorizationRenormalizedConnection_eq
    {S : Finset BurnolFactorizationFrameIndex}
    {weight : BurnolFactorizationFrameIndex → ℂ}
    (hvalid : ∀ a ∈ S, 1 < a.1 ∧ 1 < a.2)
    {z counterterm : ℂ}
    (hmass : burnolFactorizationRenormalizedMass S weight z counterterm ≠ 0) :
    burnolFactorizationRenormalizedConnection S weight z counterterm = z := by
  rw [burnolFactorizationRenormalizedConnection,
    burnolFactorizationRenormalizedNumerator_eq hvalid]
  field_simp

/-- Family, weights, and scalar counterterm are invisible after covariant normalization. -/
theorem burnolFactorizationRenormalizedConnection_independent
    {S T : Finset BurnolFactorizationFrameIndex}
    {weightS weightT : BurnolFactorizationFrameIndex → ℂ}
    (hvalidS : ∀ a ∈ S, 1 < a.1 ∧ 1 < a.2)
    (hvalidT : ∀ a ∈ T, 1 < a.1 ∧ 1 < a.2)
    {z countertermS countertermT : ℂ}
    (hmassS : burnolFactorizationRenormalizedMass S weightS z countertermS ≠ 0)
    (hmassT : burnolFactorizationRenormalizedMass T weightT z countertermT ≠ 0) :
    burnolFactorizationRenormalizedConnection S weightS z countertermS =
      burnolFactorizationRenormalizedConnection T weightT z countertermT := by
  rw [burnolFactorizationRenormalizedConnection_eq hvalidS hmassS,
    burnolFactorizationRenormalizedConnection_eq hvalidT hmassT]

end

end RHTower.HedenmalmThetaSource
