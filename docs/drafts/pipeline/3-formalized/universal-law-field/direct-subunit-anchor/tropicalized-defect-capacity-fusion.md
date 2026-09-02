# Tropicalized defect-capacity fusion

- **ID:** ULF-DSA-002
- **Stage:** 3-formalized
- **Status:** escape-capacity fusion and formation-relative completion law Lean-proved;
  relative-index selection remains open
- **Lean:** `RHTower.DirectSubunitEscapeCapacityFusion`

## Big picture

Direct subunit selection does not need a new integral lattice or a winding.  The corpus already
contains the integer: a nonzero horizontal formation grade tropicalizes to one unsigned harmonic
escape unit.  It also contains a coercive real lift of that unit and a literal source capacity
strictly below one unit.

The resulting law is

```text
continuous nonneutral grade
  -> integer escape support I = 1
  -> cubic completed energy E >= (115/108) I
  while literal Euler source capacity B < 115/108.
```

This is the Ferrero--Washington shape: a discrete obstruction and a direct strict subunit budget,
with no tensor power, repeated scale, or density amplification.

## Corpus audit

1. `HedenmalmThetaKakutaniBalancedIndexNoGo` defines
   `thetaKakutaniEscapeMultiplicity : XiZeroCopy -> Nat`.  It is zero on neutral copies and one on
   nonneutral copies.  Reflection preserves it; signed Fredholm index cancels, unsigned defect does
   not.
2. `XiFormationEscapePrincipalClassLaw` reconstructs the same 0/1 class from Gamma-six boundary
   jets, Mobius prime-normal energy, resolved Green codiagonal, and Kakutani polarization.
3. `XiWardCubicReflectionLoewnerCodiagonalIncidence` proves that each strict-right divisor support
   has integrated cubic landing at least `115/108`, multiplicity included.
4. `RoutePPrimitiveCollisionSubquantum` proves the complete primitive Euler collision budget is
   strictly below `115/108`.
5. `RoutePPrimitiveCollisionCapacityTerminal` proves that asserting target trace capacity directly
   is RH-equivalent.  The missing edge must therefore arise from a source-defined completion, not
   be assumed as a target inequality.

## Theorem

For every `q : XiRightZeroCopy`, put

```text
I(q) = thetaKakutaniEscapeMultiplicity(q) in Nat,
E(q) = integral of xiWardCubicReflectionLoewnerCodiagonalLanding(q).
```

Then unconditionally

```text
I(q) = 1,
B_Euler < (115/108) I(q) <= E(q).
```

### Proof

Strict-rightness says `Re(rho)-1/2 > 0`, hence centered modular rate is nonzero.  The exact
flux/rate zero-locus theorem makes theta boundary flux nonzero, so quantized escape multiplicity is
one.  Substitute this equality into the proved Euler subquantum bound.  The cubic Loewner quantum
theorem gives the second inequality.  No new assumption enters.

`[LEAN-PROVED: RHTower.xiRight_tropicalizedDefectCapacityFusion]`

## Exact formation-relative completion law

W-H197/W-H198 already construct the unique rate-changing boundary transmuter and its exact
`SU(1,1)` companion. W-H205 proves that assembling those companions independently over primes has
divergent trace. That divergence is exactly synchronized squarefree formation curvature.

For a strict-right copy `q`, write

```text
a = Re(xiRightCenteredZero(q)) > 0,
lambda_p = log p,
w_p = (115/864)/(p lambda_p^2),
kappa_p = w_p (lambda_p^4/a^4 - 1),
C_p = gammaSewnSynchronizedRecoveryQuadraticCost({p}) = (3/8) lambda_p^2.
```

Then, for every prime `p`,

```text
kappa_p + w_p = (115/(324 a^4)) (C_p/p),
```

equivalently

```text
(115/(324 a^4)) (C_p/p) - kappa_p = w_p.
```

### Proof

W-H205 gives `w_p=(115/864)/(p lambda_p^2)` and resonant transfer power
`lambda_p^4/a^4`. W-H198 gives companion square equal to transfer power minus one. The
synchronized-recovery curvature on a singleton is

```text
(1/3) lambda_p^2 + (1/24) lambda_p^2 = (3/8) lambda_p^2.
```

Substitution gives the identity.
`[LEAN-PROVED: RHTower.xiRight_tropicalizedDefectCapacityFormationRelativeCompletion]`

Formation curvature and completion companion are individually non-trace-class, while their
difference is the literal summable primitive source weight. These are formalized respectively by
`not_summable_xiWardCubicFormationMetricAnomalyTraceWeight`,
`not_summable_xiWardCubicPhaseMatchedKreinCompanionTraceWeight_prime_zero`, and
`summable_xiWardCubicFormationRelativeRemainder`. This is universal metric-anomaly subtraction
derived from squarefree formation. It preserves the unsquared Euler coefficient because that
coefficient is exactly the relative remainder.

The proposed clause “residual completion boundary vanishes” is false for this canonical
subtraction: residual is `w_p`, not zero. Correct conservation law is

```text
formation metric anomaly = completion companion + primitive source charge.
```

Vanishing would erase source provenance.

## Lean formalization audit

The exact Stage-2 theorem surface is closed in
`formal/GaloisForLFunctions/RHTower/DirectSubunitEscapeCapacityFusion.lean`:

1. `xiRight_thetaKakutaniEscapeMultiplicity_eq_one` proves `I(q)=1`.
2. `xiRight_directSubunitEscapeCapacityGap` proves
   `B_Euler < (115/108) I(q) <= E(q)`.
3. `xiRight_tropicalizedDefectCapacityFusion` packages the complete first theorem without an
   added premise.
4. `gammaSewnSynchronizedRecoveryQuadraticCost_singleton` proves
   `C_p=(3/8)(log p)^2`.
5. `xiWardCubicPhaseMatchedKreinCompanionTraceWeight_prime_zero_eq` proves the exact
   `kappa_p=w_p((log p)^4/a^4-1)` law.
6. `xiWardCubicFormationMetricAnomalyTraceWeight_eq_companion_add_source` and
   `xiWardCubicFormationMetricAnomalyTraceWeight_sub_companion_eq_source` prove both displayed
   forms of the formation-relative completion identity.
7. `not_summable_xiWardCubicPhaseMatchedKreinCompanionTraceWeight_prime_zero` and
   `not_summable_xiWardCubicFormationMetricAnomalyTraceWeight` prove both non-trace-class claims.
8. `summable_xiGammaEulerPrimitiveCubicLogMomentWeight_prime_zero` and
   `summable_xiWardCubicFormationRelativeRemainder` prove literal source-remainder summability.
9. `xiRight_tropicalizedDefectCapacityFormationRelativeCompletion` packages the complete second
   theorem without an added premise.

Verification on 2026-09-02:

- `lake env lean GaloisForLFunctions/RHTower/DirectSubunitEscapeCapacityFusion.lean`: pass.
- `lake build GaloisForLFunctions.RHTower.DirectSubunitEscapeCapacityFusion`: pass
  (`13190/13190`; targeted leaf only).
- `#print axioms` on every newly created declaration: only `propext`, `Classical.choice`, and
  `Quot.sound`.
- `scripts/formal_tools.py lint`: no issue for this module or its umbrella import; global exit 1 is
  caused by unrelated pre-existing unreachable modules listed by the lint report.
- `GaloisForLFunctions.RHTower.lean` imports the finished module; no umbrella build was run.

## Exact RH closure still missing

Transport itself is proved: literal unsquared Euler Krein coefficients land in the completed Xi
resolvent; source positive-shift covariance equals the reflection-Loewner kernel; opposite-radial
iterated residues recover the cubic residue Gram. Pointwise contractive landing is no longer the
right missing theorem. Exact transmuter and local Krein dilation exist, but W-H205 forbids their
independent-cell trace assembly. Positive trace-class majorization and positive
coefficient-recovering regularization are also critical-line receivers. Surviving theorem must be
relative and nonlocal:

> Construct before divisor specialization the pair of prime-mixed formation and completion
> polarizations whose non-trace-class metric parts cancel by the law above; prove their relative
> spectral index equals unsigned escape multiplicity and its normalized relative source trace is
> strictly below one.

Its trace consequence would be `E(q) <= B_Euler`.  Combined with the proved fusion,

```text
B_Euler < (115/108) I(q) <= E(q) <= B_Euler,
```

so no `XiRightZeroCopy` exists; functional equation gives RH.

P-G206/P-G207 already prove that rank-one source/environment shorting survives Gamma/polar descent,
but this is nonselective: a block `[[|c|^2,c],[conj(c),1]]` has zero short for arbitrarily large
`c`. The new theorem must define relative polarization before a divisor is supplied. No
`XiRightZeroCopy`, `analyticOrderAt xi`, or RH-equivalent target-capacity premise may enter its
construction.

## No-gos fixed by the fusion

- Signed index is wrong: functional-equation reflection cancels it.  Integer is unsigned escape
  multiplicity.
- Dyadic ghost integrality and integral frames are unnecessary and RH-equivalent as premises.
- Completed-SEM winding is unnecessary; its global vanishing is already an RH receiver and no
  same-boundary subunit estimate exists.
- Finite normalized Kakutani energies below one do not help: they converge to one off line.  The
  direct strict gap comes from the independent cubic Euler capacity.
- Literal Laurent coefficient integrality does not make physical evaluation integer-valued.
- Stating `E <= B_Euler` on divisor packets is forbidden: P-G176 proves that statement is already
  RH-equivalent.  It must be a consequence of pre-divisor completion properness.
- Independent-cell `SU(1,1)` completion is impossible: mandatory companion trace contains a
  prime-harmonic lower bound.
- Positive trace-class domination or positive cofinal regularization of trace-one incidence is
  possible exactly on critical line. Relative subtraction must occur before positivity or norms.
- Universal metric anomaly cannot be subtracted and discarded. Exact subtraction leaves unsquared
  primitive source charge.

## Interpretation

The higher mechanism is **tropicalized defect capacity**: completion turns every nonzero continuous
grade into one indivisible support unit; a coercive energy represents that unit; arithmetic
formation has less than one unit of total capacity.  RH becomes the assertion that literal Euler
formation owns its completed boundary energy after universal anomaly subtraction.
