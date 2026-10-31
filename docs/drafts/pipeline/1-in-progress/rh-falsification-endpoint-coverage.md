# Distinct RH falsification endpoints

- **Stage:** 1-in-progress
- **Scope:** All distinct missing falsification endpoints implied by the Lean corpus; ongoing conjecture and novelty audit.

## Formalized additions

| Mechanism | Exact witness | Lean owner |
|---|---|---|
| Anchored holomorphic dynamics | A nonanchor upper periodic point of the normalized Xi Donoghue map; period-one Gaussian stationary equation | `Bottcher/HalfPlane/XiDonoghueDynamics.lean` |
| Heat spectral motion | A differentiable Ritz branch in any fixed finite polynomial space with nonnegative velocity at positive heat time | `arithmetic-positivity-theory/MomentFlow/XiRitzVelocity.lean`; actual source audited, generic final source check pending |
| Finite differential jets | A nonsplitting Jensen section after any real translation, derivative order, and finite real first-order differential chain | `arithmetic-positivity-theory/Jensen/XiJetObstruction.lean` |

## Exclusions

Hankel defects, shifted-moment negativity, logarithmic-derivative sign failure, Möbius energy
escape, and positive-time heat multiple zeros already have falsification endpoints. New notation,
contraposition, changed sampling, or an equivalent witness alone does not constitute a new endpoint.
Further Donoghue orbit consequences belong to the existing dynamical family unless they add a
strictly stronger obstruction.

| Candidate | Exact existing result or obstruction | Disposition |
|---|---|---|
| Nonzero compactly supported test with zero Weil energy | `ArithmeticCastelnuovoSeveri.riemannHypothesis_iff_weil_positive_definite` | Already formalized; reject restatement |
| Singular shifted Xi moment block | `xiShiftedMomentHankelMatrix_posDef_of_riemannHypothesis` | Already formalized; reject restatement |
| Finite nonreal zero set at negative heat time | `DeBruijn.riemannHeat_neg_nonreal_zeros_infinite` holds unconditionally | Impossible antecedent; reject vacuous endpoint |
| Interior Abel-susceptibility divergence | `riemannHypothesis_iff_primeArchEndpointBernsteinAbelSusceptibilityFinite` | Already formalized; reject restatement |
| Shifted reciprocal Ritz Riccati gap | `xiShiftedCanonicalAdmissionHardEdgeWorldlineVelocity_pos` and strict shifted Hankel positivity under RH | Existing hard-root motion law; reject coordinate restatement |
| Jordan defects of centered Suzuki screw operators | `suzukiCenteredScrewApertureOperator_isSelfAdjoint` and `suzukiCenteredScrewZeroMeanOperator_isSelfAdjoint` hold unconditionally | Self-adjoint rigidity is already unconditional; no RH-specific witness |
| Positive negative-index count or a failed height truncation | `HeckeKreinToeplitz.riemannHypothesis_iff_negIndex_zetaKernel_eq_zero`, `riemannHypothesis_iff_height_truncations_posDef` | Existing kernel positivity criterion |
| Bounded positive apertures | `SquareRootThreshold.riemannHypothesis_iff_not_bddAbove_windowPositiveApertures` | Existing aperture criterion |
| Failure of cofinal integrated damping-autocorrelation bounds | `ArithmeticContinuationAndCriticalEnergy.riemannHypothesis_iff_cofinal_double_integral_tangentCorrelation` | Existing exact energy equivalence |

## Active candidates

- Strict Jensen roots: exclude repeated nonzero roots through real-factor extraction and multiplicity drop; proof incomplete.
- Asymmetric heat minors: independent ordered time grids; total positivity beyond principal moment minors; proof incomplete.

For the direct Hedenmalm source generator, RH supplies imaginary nonzero spectrum, not an
audited skew-adjointness or semisimplicity theorem. Jordan defects cannot be used as falsification
witnesses from that statement alone.

## Coverage requiring investigation

- Arithmetic continuation, signed energy, prime correlations, and quantitative source bounds.
- Heat dynamics, collision geometry, and zero displacement.
- Moment and approximation geometry beyond existing positivity defects.
- Spectral index, variational bounds, and rigidity of actual arithmetic operators.
- Analytic geometry of Xi and source-formed transforms beyond existing zero/sign receivers.

Each candidate requires exact source statements, a search for existing equivalents, a complete
proof, kernel formalization, and transitive axiom audit. No exhaustive-completion claim is made.
