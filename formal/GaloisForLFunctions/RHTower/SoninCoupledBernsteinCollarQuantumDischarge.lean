import GaloisForLFunctions.RHTower.SoninCoupledQuantumHausdorff
import GaloisForLFunctions.RHTower.SoninCoupledBernsteinCollarComparison

/-!
# Quantum discharge of the coupled-Sonin Bernstein collar premise

The collar comparison was stated with an explicit Hausdorff/Bernstein positivity premise for the
actual coupled source.  Complete positivity of density-operator replica moments proves that
premise automatically.  This file exports the hypothesis-free comparison and collar equivalence.
-/

namespace RHTower

noncomputable section

/-- The source-boundary normalization used by the collar file is the canonical coupled density
replica normalization. -/
theorem soninCoupledNormalizedReplicaMoment_eq_renyi
    (a : SoninPositiveAperture) :
    soninCoupledNormalizedReplicaMoment a =
      soninAllPrimeCoupledRenyiReplicaMoment a := by
  rfl

/-- The collar source's Bernstein positivity premise is discharged by the complete quantum
Hausdorff hierarchy. -/
theorem soninCoupledNormalizedReplicaMoment_hausdorffBernsteinNonnegative
    (a : SoninPositiveAperture) :
    HausdorffBernsteinNonnegative (soninCoupledNormalizedReplicaMoment a) := by
  rw [soninCoupledNormalizedReplicaMoment_eq_renyi]
  exact soninAllPrimeCoupledRenyiReplicaMoment_hausdorffBernsteinNonnegative a

/-- Hypothesis-free forward comparison between endpoint Bernstein purity and the concrete
coupled-Sonin packet mismatch. -/
theorem primeArchEndpointBernsteinPurity_le_two_add_two_soninCoupledMismatch_quantum
    (a : SoninCoupledNondegenerateAperture) (n : ℕ) :
    primeArchEndpointBernsteinPurity n ≤
      2 + 2 * soninCoupledEndpointBernsteinMismatch a n :=
  primeArchEndpointBernsteinPurity_le_two_add_two_soninCoupledMismatch a
    (soninCoupledNormalizedReplicaMoment_hausdorffBernsteinNonnegative a.1) n

/-- Hypothesis-free reverse comparison between concrete coupled-Sonin mismatch and endpoint
Bernstein purity. -/
theorem soninCoupledEndpointBernsteinMismatch_le_two_add_two_primeArchEndpointPurity_quantum
    (a : SoninCoupledNondegenerateAperture) (n : ℕ) :
    soninCoupledEndpointBernsteinMismatch a n ≤
      2 + 2 * primeArchEndpointBernsteinPurity n :=
  soninCoupledEndpointBernsteinMismatch_le_two_add_two_primeArchEndpointPurity a
    (soninCoupledNormalizedReplicaMoment_hausdorffBernsteinNonnegative a.1) n

/-- **Hypothesis-free coupled collar equivalence.**  Quantum density positivity removes the
previously explicit Hausdorff premise from the exact endpoint/source-mismatch equivalence. -/
theorem primeArchEndpoint_unitCollarEnvelope_iff_soninCoupledMismatch_quantum
    (a : SoninCoupledNondegenerateAperture) :
    UnitCollarExponentialEnvelope primeArchEndpointBernsteinPurity ↔
      UnitCollarExponentialEnvelope (soninCoupledEndpointBernsteinMismatch a) :=
  primeArchEndpoint_unitCollarEnvelope_iff_soninCoupledMismatch a
    (soninCoupledNormalizedReplicaMoment_hausdorffBernsteinNonnegative a.1)

end

end RHTower
