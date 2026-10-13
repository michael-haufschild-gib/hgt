# Finite Weil polynomial-tilt realization

Status: dependency-closed paper proof; Lean verification pending.

## Exact target

For every `r,k` and finite law `Q` on `Fin(r+1)`, the measure placing weights
`Q(i)` at the canonical fluctuation points is a first-coordinate polynomial tilt
of the base law with degree less than `r+1` if and only if every `Q(i)>0`.

The polynomial is explicit: interpolate
`log(Q(i)/finiteWeilCanonicalEdgeMass(r,k,i))` at the existing distinct first
coordinates. In particular, a polynomial tilt realizes uniform weights and
attains the previously proved covariance determinant benchmark for every `r,k`.
This is attainment in the polynomial family, not an assertion about the smaller
three-parameter quadratic family.

## Local evidence

- `WeilLogShiftFinitePolynomialInterpolation` and the checked Lagrange APIs give
  exact interpolation on the canonical distinct first coordinates.
- `PaperFourierLawMeasure` realizes every finite law as an atomic probability
  measure and gives integrability and the finite-sum integral for every real
  observable.
- Mathlib's local `WithDensity` gives distribution over measure sums and scalars
  and evaluates density weighting of a Dirac measure without global measurability.
- Local `Tilted` proves reverse absolute continuity whenever the exponential
  is integrable, which is automatic for these finite atomic laws.
- `FinitePowerCovarianceDeterminant` supplies the normalized finite-moment
  determinant identity. Extend its actual-measure bridge to arbitrary finite
  atomic laws, then specialize to uniform weights.
- Cached lexical `atomic tilted` in HTGeometry returned no hits. The
  `polynomial tilt` search in WeilLogShift and focused source searches expose the
  earlier scalar-reduction and moment results, not this target-law classification.
  No external sources or novelty claims are used.

## Closed paper proof

For finite laws `P,Q`, suppose `P(i)*exp(f(phi(i)))=Q(i)` at every atom. The
finite integral formula makes the normalizing integral equal to `sum Q=1`.
Distribute the density over the finite measure sum and evaluate each Dirac:
the tilt is exactly the atomic realization of `Q`.

If `P` is strictly positive and `phi` injective, the base gives positive mass
to every singleton `{phi(i)}`. Its exponential tilt is equivalent to the base
because the exponential is integrable on finite support. Therefore any equal
target atomic law has `Q(i)>0`; a zero target atom would contradict reverse
absolute continuity.

For the canonical base, all masses are already proved positive and the first
coordinate is injective. If every target mass is positive, interpolate the
displayed log ratios. Evaluation at nodes and `exp(log x)=x` give the required
weighted-exponential identity. The interpolant has degree below `r+1`.
Necessity follows from the preceding support argument, regardless of degree.

For any finite atomic law with `r+1` labels, every real observable is L2.
Expand covariance using the existing integral formula and apply the earlier
finite-moment determinant theorem. The determinant of powers one through `r`
is squared Vandermonde times product of atom weights. Taking uniform weights
and using the canonical squared-gap formula gives exactly the existing positive
uniform benchmark. Rewrite by polynomial realization to obtain its actual tilt
attainment, with every helper premise discharged.

## Planned Lean files

- `HTGeometry/AtomicProbabilityTilt.lean`
- `HTGeometry/AtomicPowerCovarianceDeterminant.lean`
- `RHTower/WeilLogShiftPolynomialTiltRealization.lean`
- `RHTower/WeilLogShiftPolynomialTiltMaximum.lean`

## Verification

Pending API checks, native leaf builds, all-declaration axiom audit, umbrella
wiring, and formal lint.


## Formal verification completed — 2026-10-12

Status: FORMALIZED. All four new leaves compile with empty diagnostic logs:
- HTGeometry/AtomicProbabilityTilt
- HTGeometry/AtomicPowerCovarianceDeterminant
- RHTower/WeilLogShiftPolynomialTiltRealization
- RHTower/WeilLogShiftPolynomialTiltMaximum

All 12 declarations (11 theorems and one definition) were audited through the actual maximum root; only propext, Classical.choice, and Quot.sound occur. The final native scratch audit exited 0 with no residual diagnostics. All 10 direct imports and four leaf objects were checked fresh; both umbrellas are wired; source whitespace is clean. Repository formal lint passed.

Exact survivor: finite polynomial tilts realize a target law on the canonical support if and only if every target weight is strictly positive. The explicit degree-at-most-r interpolated log-density realizes every positive law, including the uniform law, whose maximal power-covariance determinant equals the existing uniform benchmark. No claim of uniform attainment by the three-parameter quadratic family is made.

Evidence sources: local Lean corpus only. No web, external papers, or numerical experiments. Verification artifacts: /tmp/hgt-polynomial-tilt-realization-final-audit.lean, /tmp/hgt-polynomial-tilt-realization-final-audit.log, /tmp/hgt-polynomial-tilt-realization-audit.py, /tmp/hgt-polynomial-tilt-realization-lint.log.

Next corpus-only candidate, not proved here: classify all polynomial potentials yielding the same law by additive constants plus the nodal polynomial ideal. Local prior search found the existing finite-node ideal and tilted-equality rigidity ingredients, but no combined polynomial-tilt fibre theorem.
