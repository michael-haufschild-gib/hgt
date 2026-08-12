# Theta prime-translation to faithful Pluecker anomaly

- **ID:** FRANK-THETA-PRIME-TRANSLATION-PLUCKER
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean) + open producer
- **Source:** cross-corpus Frankenstein seam: Hedenmalm theta source × source-horizontal Gamma
  Bockstein × P-G95 physical Pluecker overlap
- **Statement:** Fixed normalized Hedenmalm prime translation has conormal gain `p^(-q)` on every
  multiplicity-exact Xi divisor mode; Fisher-weighted forward/reflected squared-gain imbalance is
  exactly the source-horizontal Gamma Bockstein and hence exactly both admitted physical Pluecker
  carriers. Theta-pencil residual kills its divisor eigenvector, while the faithful P-G95 target
  operator kills the landed carrier exactly on the critical line.

## Goal

Replace divisor-fitted source-to-target transport by a literal source operation and isolate the
smallest non-circular theorem that would force its faithful target anomaly to vanish. Preserve each
ordinary-prime label, valuation-depth label, divisor multiplicity copy, and both reflection
orientations before scalarization.

## Gates

- [x] 0 → 1: source operation, exact coefficients, and target endpoint are explicit.
- [ ] 1 → 2: derive forward/reflected translation-energy balance from completed pre-zero
  Euler--Gamma source geometry.
- [ ] 2 → 3: formalize that independent balance and close `RiemannHypothesis`.
- [ ] 3 → 4: publication audit.

## Heavy conjecture loop

### C1 — literal theta-pencil/P-G95 intertwining

**Failed.** The source pencil residual
`B - thetaXiReciprocalEigenvalue(q) I` kills the nonzero theta divisor eigenmode. P-G95 is
injective and therefore cannot kill a nonzero admitted Xi Pluecker carrier. Literal intertwining is
equivalent to the critical-line conclusion, not an unconditional source law.

**Positive survivor.** The canonical pinned-monopole lift is coefficient-faithful on the complete
off-line divisor eigenspace, and its exact intertwining anomaly is P-G95 applied to the actual Xi
carrier.

### C2 — Gamma nodal positivity cancels the anomaly

**Failed.** Exact filtered Gamma transforms land on RH-equivalent Xi moment minors. Existing
integral representations provide no independent sign that annihilates the physical vector.

**Positive survivor.** Gamma positivity remains a receiver after Xi specialization; any useful
Gamma input must enter before divisor evaluation as a source relation.

### C3 — theta metric trace kills the boundary flux

**Failed.** The exact identity is `G B - B† G = i C`. A Riesz projection commutes with `B`, not
with `B†`; the compressed trace retains the boundary flux. Reflected-pair cancellation is already
unconditional and loses same-fibre orientation.

**Positive survivor.** The missing relation must be same-fibre and first-order; squared or folded
spectralization cannot supply it.

### C4 — actual Xi Pluecker carrier is a P-G95 harmonic mode

**Failed.** Xi admission uses reporter factor `sqrt(node)`, while the local P-G95 kernel uses
`1/sqrt(node)`. Converting them requires an unbounded inverse-gap gauge. Physical overlap forces
the gauge constant, and a nonzero constant section is not in `ell²`.

**Positive survivor.** P-G95 has no Hilbert-space zero mode but has zero in continuous boundary
spectrum. Any transfer must be singular/renormalized at zero; bounded harmonic landing is ruled
out.

### C5 — pinned theta lift exposes an exact target anomaly

**Proved.** `FrankensteinThetaPluckerIntertwiningAnomaly.lean` constructs lower and upper
continuous lifts, proves coefficient faithfulness on every off-line divisor eigenspace, and proves
both target anomalies vanish simultaneously exactly at `Re(q)=1/2`. Both are reflection-odd.

### C6 — prime-translation conormal gains supply the coefficient

**Proved.** `FrankensteinThetaPrimeTranslationPluckerLanding.lean` proves

```text
dirichletExponent(xiSpectralPoint(q)) = q,
E_p(q) = p * |p^(-q)|² = p^(-(2 Re(q)-1)),
E_p(lineConj(q)) = p^(2 Re(q)-1),
Fisher_p * (E_p(q)-E_p(lineConj(q)))
  = sourceZeroHorizontalPrimeCarrier(q,p).
```

The last scalar is then proved to be the literal coefficient of every lower and upper physical
Pluecker coordinate. This is an operator/source provenance theorem, not another equality of zero
sets.

## Exact Lean certificates

Modules:

- `formal/GaloisForLFunctions/RHTower/FrankensteinThetaPluckerIntertwiningAnomaly.lean`
- `formal/GaloisForLFunctions/RHTower/FrankensteinThetaPrimeTranslationPluckerLanding.lean`

Key theorems:

- `frankensteinThetaXiLowerPluckerLift_eq_zero_iff_of_eigen_offline`
- `frankensteinThetaXiUpperPluckerLift_eq_zero_iff_of_eigen_offline`
- `frankensteinThetaXiBothPluckerIntertwiningAnomalies_eq_zero_iff`
- `thetaPrimeTranslation_dirichletExponent_xiSpectralPoint`
- `sourceEvaluation_integerShift_xiSpectralPoint`
- `frankensteinThetaPrimeTranslationEnergy_eq`
- `frankensteinThetaPrimeTranslationImbalance_eq_sourceZeroHorizontalPrimeCarrier`
- `frankensteinXiLowerPhysicalPluckerHilbertCarrier_apply_eq_primeTranslationImbalance`
- `frankensteinXiUpperPhysicalPluckerHilbertCarrier_apply_eq_primeTranslationImbalance`

Verification:

```text
lake env lean GaloisForLFunctions/RHTower/FrankensteinThetaPluckerIntertwiningAnomaly.lean
lake build GaloisForLFunctions.RHTower.FrankensteinThetaPluckerIntertwiningAnomaly
lake env lean GaloisForLFunctions/RHTower/FrankensteinThetaPrimeTranslationPluckerLanding.lean
lake build GaloisForLFunctions.RHTower.FrankensteinThetaPrimeTranslationPluckerLanding
```

Both exact leaf builds pass. Axiom audit reports only `propext`, `Classical.choice`, and
`Quot.sound`. Targeted scan finds no `sorry`, `admit`, `axiom`, `opaque`, or `unsafe` declaration.
Both modules are wired into `formal/GaloisForLFunctions/RHTower.lean`; umbrella was not built.

## Open producer

For one fixed ordinary prime `p`, derive on every actual Xi divisor mode the completed pre-zero
source balance

```text
E_p(q) = E_p(lineConj(q)).
```

The proved identity then kills the Gamma Bockstein, both Pluecker carriers, and both P-G95
intertwining anomalies, forcing `Re(q)=1/2`. This balance cannot be postulated as unitarity,
reflection invariance, self-adjointness, Wold stationarity, or bounded target inversion: corpus
already proves each such specialization is RH-equivalent or impossible. Required theorem is a
completed Euler--Gamma/parity-normal Ward identity for normalized source translation before Xi
specialization, retaining forward and reciprocal orientations separately.

## No-go closure

- **Exact killing mechanism:** source residual alone kills the divisor eigenmode but cannot be
  transported through injective P-G95 off line; positive/trace/reflection folding erases the
  orientation; bounded zero-boundary inversion is impossible.
- **Strongest positive survivor:** fixed-source prime-translation energy imbalance equals the
  actual coefficient-faithful physical carrier, and its target anomaly has exact critical-line
  radical.
- **New insight:** missing source annihilator is not an unspecified Gamma correction. It is the
  parity-normal balance of one explicit normalized prime translation at two conormal characters.
  One prime already suffices; all-prime summability and further carrier infrastructure are not
  needed for the logical endpoint.
- **Status:** survivor dependency-closed and formalized; independent completed balance remains
  open.

## Log

- 2026-08-12 — C1--C4 falsified with positive survivors; C5 and C6 proved and exact-leaf audited.
