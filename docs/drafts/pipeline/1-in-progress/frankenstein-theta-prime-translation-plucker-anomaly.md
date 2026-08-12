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

### C7 — reflection reciprocity plus two-sided contractivity

**Proved reduction; fixed-metric realization failed.** Lean proves

```text
E_p(q) * E_p(lineConj(q)) = 1,
E_p(q) <= 1 and E_p(lineConj(q)) <= 1  iff  Re(q)=1/2.
```

Thus reflection already supplies exact reciprocity, and a completed source theorem only needs
two-sided contractivity at one prime. However `HedenmalmThetaTranslationWeightNoGo.lean` proves
both positive and negative translations are unbounded in every fixed theta-source Hilbert fibre:
the weight ratio has doubly exponential blow-up. Ordinary fixed-metric contractivity is therefore
not the producer.

**Positive survivor.** Required completion must be singular/moving-fibre or a pre-Hilbert
Euler--Gamma Ward quotient. It must prove both contractive inequalities before specializing to the
fixed theta metric; a bounded metric repair is formally excluded.

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
- `frankensteinThetaPrimeTranslationEnergy_mul_lineConj`
- `frankensteinThetaPrimeTranslation_both_energy_le_one_iff`
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

- 2026-08-12 — C1--C4 falsified with positive survivors; C5--C7 proved and exact-leaf audited.

### C8 — prime translation gives both divisor orientations one common forcing vector

**Conjecture, paper-proved; Lean pending.**  Let

```text
f_z = sourceModeF(thetaSource,z),
B   = sourceInverse(thetaSource),
T_n = normalized integer translation,
r_n = integerAnomaly(thetaSource,n).
```

For every theta-source zero `z` in the source strip,

```text
(B + z⁻¹) T_n f_z = r_n.                         (CF)
```

Proof: the exact translation commutator is

```text
B(T_n f) - n^(-1/2) (Bf)(·+log n)
  = (integral f / thetaSource.mass) r_n.
```

The canonical divisor mode has `B f_z = -z⁻¹ f_z` and
`integral f_z = thetaSource.mass`; substitution gives `(CF)` pointwise.  No scalar is chosen from
the zero.  In particular, `z = xiSpectralPoint(q)` and its line-reflected copy have the literal
same right-hand side, retaining divisor multiplicity and integer/prime label.  For every prime
`p`, `r_p` is nonzero because the integer anomaly vanishes identically iff `p = 1`.

**Hostile verdict.**  Shared forcing does not by itself identify the two responses: the two
resolvents use different spectral scalars `-z⁻¹` and `-(z#)⁻¹`.  The positive survivor is sharper:
the missing producer is response uniqueness for one universal, nonzero, source-positive interval
cocycle—not another reflection law or target carrier.  Any theorem identifying the two translated
responses now forces equality of the spectral scalars once nonvanishing is supplied, hence the
critical line.  Lean formalization must expose both the common-forcing equality and its exact
nonvanishing boundary.

### C9 — response identification is exactly horizontal annihilation

**Proved in Lean.**  For every retained Xi multiplicity copy `q` and every positive integer label
`n`,

```text
T_n f_q = T_n f_lineConj(q)  iff  Im(xiSpectralPoint(q)) = 0.
```

The forward proof does not invoke an abstract target injection.  It subtracts the two literal
common-forcing equations, uses the canonical source mass to prove `T_n f_q` is nonzero, and then
forces equality of reciprocal eigenvalues.  Equality of the spectral point and its conjugate is
horizontal annihilation.  Consequently, one source theorem identifying these responses for all
Xi copies at any single positive integer label implies `RiemannHypothesis`.

**Hostile verdict.**  This is a sharp endpoint bridge, not the producer.  Source involution only
exchanges the two responses.  Sesquilinear Weil compatibility also permits conjugate eigenvalues,
and the theta Green commutator measures their horizontal boundary flux instead of killing it.

### C10 — universal anomaly is a flat rank-one prime connection

**Proved in Lean.**  Define

```text
K_n(g) = B(g) -
  (sourceFunctional(g)/(n^(-1/2) thetaSource.mass)) r_n.
```

For every integrable source vector and every positive integer `n`,

```text
K_n(T_n f) = T_n(B f).
```

Moreover the connection is multiplicatively flat:

```text
K_(mn)(T_(mn) f) = T_m(K_n(T_n f)).
```

Thus both retained Xi orientations are genuine eigenmodes of one literal, coefficient-faithful
prime covariant operator.  Prime label, divisor multiplicity, and both reflection orientations
survive in one fixed source carrier.  The common nonzero residual is nevertheless annihilated by
every retained Xi conormal character, exposing the exact quotient blindness that prevented prior
target-only arguments.

**Hostile verdict.**  Flat covariance removes the different-target/fibre ambiguity but does not
select between the two conjugate eigenvalues.  The remaining producer is an independent arithmetic
fixed-frame law forcing equality of the two translated Xi responses (equivalently equality of the
two eigenvalues) at one positive integer label.  Operator construction, reflection covariance,
sesquilinear pairing, and conormal evaluation cannot supply that selection.

## C8--C10 Lean certificate

Module:

- `formal/GaloisForLFunctions/RHTower/FrankensteinThetaPrimeTranslationCommonForcing.lean`

Key theorems:

- `thetaPrimeTranslatedSourceResidual_eq_integerAnomaly`
- `thetaIntegerCovariantSourceInverse_integerShift`
- `thetaIntegerCovariantSourceInverse_flat`
- `thetaIntegerCovariantSourceInverse_thetaXi_both_eigen`
- `thetaXiPrimeTranslatedSourceMode_eq_lineConj_iff`
- `riemannHypothesis_of_thetaXiPrimeTranslatedSourceMode_eq_lineConj`
- `integral_thetaXiPrimeTranslatedSourceResidual_mul_sourceChar_eq_zero`

Verification:

```text
lake env lean GaloisForLFunctions/RHTower/FrankensteinThetaPrimeTranslationCommonForcing.lean
lake build GaloisForLFunctions.RHTower.FrankensteinThetaPrimeTranslationCommonForcing
```

Both exact checks pass.  Axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`;
targeted forbidden-declaration scan is empty.  Module is wired into
`formal/GaloisForLFunctions/RHTower.lean`; no umbrella build was run.
