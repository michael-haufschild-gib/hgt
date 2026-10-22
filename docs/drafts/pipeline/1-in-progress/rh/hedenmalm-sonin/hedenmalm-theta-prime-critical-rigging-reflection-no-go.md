# Hedenmalm theta prime critical-rigging reflection no-go

- **ID:** `hedenmalm-theta-prime-critical-rigging-reflection-no-go`
- **Stage:** 1-in-progress
- **Label:** `P-G109`
- **Type:** `[THEOREM (LEAN)] [ROUTE-P NO-GO] [POSITIVE SURVIVOR]`
- **Parents:** `P-G108`, `HedenmalmThetaCompactDivisorEigenmode.lean`,
  `FrankensteinThetaPrimeTranslationCommonForcing.lean`

## Frozen conjecture

Let `H_crit=L2(R,exp(|x|)dx)` be P-G108's uniquely forced radial rigging. For any `L>0`, prove a
sharp reflection-pair lower bound

```text
||f(.+L)||_crit^2 + ||f(.-L)||_crit^2
  >= 2 cosh(L) ||f||_crit^2.
```

Then prove each canonical theta Xi response `f_q` belongs to `H_crit`, has positive energy, and
the functional-equation partner is conjugate reflection:

```text
f_lineConj(q)(x) = conjugate(f_q(-x)).
```

Consequently forward centered translation cannot be contractive on both response orientations.

## Complete paper proof `[PROVED HERE]`

The pointwise critical-weight identity satisfies

```text
exp(|x-L|)+exp(|x+L|) >= 2 cosh(L) exp(|x|).
```

For `|x|>=L` this is equality. For `|x|<=L`, after replacing `x` by `|x|`, the difference is

```text
exp(L-|x|)-exp(-L+|x|) >= 0.
```

Multiplication by `|f(x)|^2` and integration gives the displayed hyperbolic lower bound after
translation invariance of Lebesgue measure. Since `cosh(L)>1`, positive energy excludes both
shifted energies being at most the original energy.

At every Xi divisor, existing theta-tail estimates prove `|f_q|^2/thetaSource.k` integrable.
The global source bound

```text
exp(|x|) thetaSource.k(x) <= thetaBound
```

therefore embeds `f_q` into `H_crit`. Its energy is positive because its integral is the nonzero
theta source mass. Source reflection and conjugation identities, together with
`xiSpectralPoint(lineConj(q))=conjugate(xiSpectralPoint(q))`, give the exact conjugate-reflection
law. Forward translation of the reflected response has the backward energy of the original, so
the generic no-go applies.

## No-go closure

- **Exact killing theorem/mechanism:** P-G108's critical rigging cannot realize Route P's two
  half-density inequalities as ordinary positive-norm contractivity on the two canonical source
  responses. Their energy sum is not merely sometimes expansive: it is bounded below by the
  strict factor `2 cosh(L)>2` for every nonzero response and every genuine prime aperture.
- **Strongest positive survivor:** exact hyperbolic reflection-pair energy law, critical-rigging
  admission and positive energy of every canonical Xi response, and exact source-mode
  conjugate-reflection identification.
- **New insight:** the missing half-density Ward gain cannot be diagonal in any ordinary positive
  critical-fibre norm that retains physical source reflection. It must subtract a cross-channel
  term before scalarization: a non-diagonal quotient, source-correlated Feshbach complement,
  indefinite boundary pairing followed by positive reduction, or equivalent renormalized Ward
  cancellation.
- **Status:** complete paper proof and direct Lean check; exact build, lint, axiom, and umbrella
  audits pending.

## Falsifiers

- A nonzero finite-energy vector with both centered translations contractive at `L>0` contradicts
  the hyperbolic theorem.
- Failure of canonical Xi response admission or positive energy invalidates the Route-P
  specialization.
- Failure of conjugate reflection invalidates the forward/backward identification.

## Gates

- [x] critical-rigging and canonical-response corpus audited
- [x] conjecture frozen and proved on paper
- [x] sharp pointwise and integrated hyperbolic bounds formalized
- [x] canonical Xi response admission and positive energy formalized
- [x] exact lineConj conjugate-reflection law formalized
- [x] two-response contractivity no-go formalized
- [ ] exact build, lint, axiom, and umbrella audits pass

## Lean status

Umbrella-wired module
`formal/GaloisForLFunctions/RHTower/HedenmalmThetaPrimeCriticalRiggingReflectionNoGo.lean`
contains the complete result. Direct `lake env lean` passes.

## Log

- 2026-08-13 — P-G109 conjectured after P-G108 normalization failure, paper-proved, and
  formalized.
