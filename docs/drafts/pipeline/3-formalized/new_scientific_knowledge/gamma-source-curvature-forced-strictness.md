# Gamma finite source curvature forces the completed factorial reporter

- **ID:** `gamma-source-curvature-forced-strictness`
- **Stage:** 3-formalized
- **Type:** SOURCE-CURVATURE / COFINAL-STRICTNESS COMPARISON THEOREM
- **Scientific status:** `[LEAN-FORMALIZED] [CANDIDATE NEW SCIENTIFIC KNOWLEDGE]`
  `[NOVELTY PRELIMINARY] [SIGNIFICANT SEED, NOT A STANDALONE FIELDS-SCALE THEOREM]`
  `[CURVATURE-ONLY COMPLETENESS FALSE; COLLIGATION SUCCESSOR PROVED]`
  `[NOT AN RH RESULT]`
- **Parents:**
  - `../gamma-periodic-constraint-corona.md`
  - `../not_new_scientific_knowledge/gamma-cofinal-reconstruction-defect.md`
  - `../../1-in-progress/hypertranscendental-polarized-strict-descent-field.md`

## Theorem

Let `T_N` be the finite Taylor shadow of unit translation on the first `N` derivative clocks and
let `p_N` forget the highest clock.  The adjacent-shadow curvature is

```text
Omega_N=p_N T_(N+1)-T_N p_N.                              (1)
```

For `N>0`, `Omega_N` has rank one.  On a vector `a` its complete value is

```text
Omega_N(a)_i=a_top/(N-i)!,       0<=i<N.                  (2)
```

Hence the oriented boundary vector at level `N` is `(1/N!,...,1/1!)`.  The family of all boundary
vectors is jointly faithful: it uniquely reconstructs the infinite factorial conormal

```text
nu_n=1/(n+1)!.                                             (3)
```

On the square-summable clock completion, let `A` be the Gamma factorial reporter.  The new exact
comparison is the coordinate identity

```text
(A x)_n=Omega_(n+1)(e_top)_0 x_n.                          (4)
```

Thus the diagonal coefficient of the completed reporter in every clock direction is exactly the
oriented curvature coefficient exposed by two adjacent finite source shadows.  It is not an
independently selected singular-value sequence.

Combining `(4)` with the already formalized finite and completed theorems gives one natural chain:

```text
finite source-action curvature
  -> unique factorial boundary conormal
  -> raw-stream algebraic equivalence
  -> bijection at every finite clock
  -> injective dense proper completed range
  -> no continuous left inverse.                          (5)
```

The positive statement is not merely that reconstruction fails.  The finite defect current
constructs the exact completed reporter that fails strictness.  This is an explicit change of
representation of one source coefficient system: rank-one truncation curvature at finite depth,
factorial inverse amplification along the clock, and dense nonclosed range after Hilbert
completion.

## Curvature is an edge, not the whole field

The same formal theory proves a decisive no-go: arbitrary dynamics compressed entirely into the
new boundary corner can be added without changing `Omega_N`.  Therefore `(1)--(4)` do not
reconstruct the complete finite source action.

The positive maximal successor is exact.  Relative to a split truncation `p_N i_N=1`, put

```text
B_N=1-i_N p_N,
beta_N=B_N T_(N+1) B_N.
```

For a forward-compatible action, Lean proves

```text
T_(N+1)=i_N T_N p_N+i_N Omega_N+beta_N.                   (6)
```

Thus the lower action, curvature, and boundary self-symbol jointly reconstruct the next action.
The Gamma theorem identifies the curvature-to-strictness edge of this colligation; it does not
erase the flat/holonomy sector `beta_N`.

For the Gamma Taylor tower that sector is not left arbitrary.  Lean proves
`gammaClockBoundaryCompression_eq_projector`: translation compressed to the newly exposed
highest-jet line is exactly the identity.  Gamma therefore supplies the full finite colligation

```text
(inherited Taylor action, factorial outgoing curvature, unit boundary self-symbol),
```

and `(4)` transports its outgoing component into the completed factorial reporter.

## What is proved in Lean

In `formal/GaloisForLFunctions/HTGeometry/GammaPeriodicConstraintCorona.lean`:

- `gammaClockCurvature_apply` proves `(2)`;
- `gammaClockCurvature_eq_outerProduct`, `range_gammaClockCurvature`, and
  `finrank_range_gammaClockCurvature` prove rank one;
- `gammaClockBoundaryCompression_eq_projector` proves the unit boundary self-symbol;
- `gammaCoronaConormal_boundaryCoefficient` identifies every finite boundary coefficient with
  `(3)`;
- `gammaCoronaConormal_ext_of_boundaryCoefficients` proves joint boundary tomography.

In `formal/GaloisForLFunctions/HTGeometry/GammaCofinalReconstructionDefect.lean`:

- `gammaFactorialObservabilityOperator_apply_eq_clockCurvature` proves `(4)`;
- `gammaFactorialObservabilityOperator_eq_streamEquiv_apply` identifies the same diagonal with the
  raw-stream factorial equivalence;
- `gammaFactorialFiniteObservation_bijective` proves finite effectivity;
- `gammaFactorialObservabilityOperator_denseRange` and
  `gammaFactorialObservabilityOperator_not_surjective` prove dense proper range;
- `gammaFactorialObservabilityOperator_no_continuousLeftInverse` proves completed nonsplitting;
- `gammaFactorial_finite_effective_completed_nonsplit` packages the exact completed phenotype.

The new comparison file was verified directly against the cached project environment.  No full
build is required.  The theorem has no project axiom and its prior capstone axiom audit reports
only `propext`, `Classical.choice`, and `Quot.sound`.

## Novelty and significance gate

The ingredients separately are parent mathematics: Taylor translation matrices, truncation
commutators, diagonal compact operators, finite-section instability, and dense nonclosed ranges.
The Gamma coefficients and their periodic ambiguity are classical as well.

The candidate-new content is the exact source-natural identity `(4)` joining two previously
separate obstruction representations.  A preliminary targeted search found no source identifying
the oriented adjacent-jet curvature of the Gamma translation tower with the unique diagonal whose
square-summable completion is injective, dense, non-surjective, and continuously nonsplit.  This
is an absence finding, not a priority claim.

The result is significant as the first proved edge map in the proposed strict-descent field.  It
does not by itself warrant a standalone paper or a Fields-scale claim.  That threshold requires a
presentation-invariant construction and at least one cross-family transport theorem.

## Anti-theatre gate and surviving positive target

The theorem fixes the diagonal coefficients but does not yet prove that `l2` is the unique
source-forced rigging.  It also does not make curvature complete without the boundary self-symbol
in `(6)`.  An arbitrary Hilbert completion or discarded boundary corner would reintroduce choice.
Therefore the next positive theorem is:

> **[CONJECTURE — GAMMA RIGGING INVARIANCE]** The strictness class generated by `(1)--(4)` is
> invariant under every source-admissible completion of the maximal cyclic Gamma conormal domain,
> and its factorial growth class is complete up to boundedly invertible change of clock frame.

Retire the intrinsic-field interpretation if the defect can be removed by a source-admissible
bounded change of rigging.  If the statement fails for the full admissible class, classify the
maximal class on which it holds; that classification is the positive result.

## Gates

- [x] adjacent finite source curvature computed exactly
- [x] curvature rank one at every positive clock depth
- [x] all oriented boundary currents reconstruct the infinite factorial conormal
- [x] completed reporter proved coordinatewise equal to the curvature diagonal
- [x] curvature-only completeness falsified
- [x] exact boundary-colligation successor identified
- [x] Gamma boundary self-symbol proved to be the unit
- [x] raw algebraic equivalence and every finite bijection proved
- [x] dense proper completed range and no continuous left inverse proved
- [x] no project axiom used
- [x] preliminary parent and novelty search completed
- [ ] classify source-admissible Gamma riggings
- [ ] prove invariance under bounded source-frame equivalence
- [ ] construct the analogous curvature-to-strictness edge for a second natural HT family
- [ ] complete specialist literature audit
