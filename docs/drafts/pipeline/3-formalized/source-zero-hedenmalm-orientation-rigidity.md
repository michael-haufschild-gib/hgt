# Source-zero Hedenmalm orientation rigidity

- **ID:** SOURCE-ZERO-HEDENMALM-ORIENTATION-RIGIDITY
- **Stage:** 3-formalized
- **Type:** THEOREM (paper + Lean 4)
- **Source:** `SOURCE-ZERO-TO-HORIZONTAL-CARRIER`, Hedenmalm two-ended Volterra source,
  multiplicity-exact Xi divisor
- **Statement:** Equality of the two actual Hedenmalm causal flows indexed by a Xi-divisor copy
  and its critical-line reflection forces both retained source orientations to be fixed, hence
  annihilates the complete-resolution carrier and every prime-labelled Bockstein before bounded
  scalarization.

## Goal

Construct an actual source relation, rather than a positivity or integrality certificate, which
forces the two retained cofinal orientations to annihilate while retaining each ordinary-prime
label and each analytic-multiplicity copy.

## Gates

- [x] 0 → 1: both compared objects are actual theta-source Volterra flows at actual Xi-divisor
  copies; no line placement, positivity certificate, or scalar quotient is inserted
- [x] 1 → 2: dependency-closed proof below
- [x] 2 → 3: unconditional Lean formalization; direct file check, targeted leaf build, and axiom
  audit passed
- [ ] 3 → 4: external novelty audit and standalone exposition pending

## Heavy conjecture loop

1. **Conjecture: polarize the two reflection-odd cofinal orientations. Failed.** Both tail log
   and prime Bockstein reverse sign. Their product is reflection-even and strictly positive off
   line, so reflection pairing doubles the obstruction instead of killing it.
2. **Pivot: land the corrected Kummer cap in an integer Fredholm index. Failed producer audit.**
   Existing cap lands in complex Hochschild/Stokes homology. Calling its normalized real
   coefficient an index would assume a new integer-valued comparison whose existence is already
   critical-line strength.
3. **Pivot: use two-sided Hedenmalm integrability plus a first-order energy identity. Failed.**
   Off-real parameters lie in the resolvent set of the self-adjoint first-order operator, where a
   two-sided decaying inhomogeneous solution is expected. Integrability alone cannot force reality.
4. **Pivot: compare the two actual source-pointed flows before any quadratic pairing. Proved.**
   The source ODE makes the causal-flow family injective in its spectral parameter. Critical-line
   reflection is conjugation of that parameter, so equality of the reflected flows forces a real
   centered parameter and annihilates the full horizontal carrier.

## Construction

For a multiplicity copy `q` of an Xi zero, put

```text
alpha(q) = xiSpectralPoint(q),
Jq       = xiZeroCopyLineConjEquiv(q),
u_q(x)   = hedenmalmCausalVolterra(alpha(q), x).
```

The divisor source supplies, unconditionally,

```text
XiC(alpha(q)) = 0,
alpha(Jq) = conj(alpha(q)),
|Im alpha(q)| < 1/2.
```

The proposed source law at `q` is the literal, unscalarized identity

```text
forall x, u_q(x) = u_Jq(x).
```

It retains the analytic multiplicity copy because its domain is `XiZeroCopy`. It makes no prime
sum: after source rigidity is applied, each prime-labelled carrier is killed separately.

## General source rigidity theorem

Let `alpha,beta` lie in `|Im z|<1`. Both causal flows solve

```text
-i u_alpha'(x) + alpha u_alpha(x) = -k(x),
-i u_beta'(x)  + beta  u_beta(x)  = -k(x),
```

where `k = thetaCuspFullSource` is strictly positive everywhere. Suppose
`u_alpha = u_beta` pointwise. Equality of functions gives equality of derivatives. Subtracting
the two ODEs gives

```text
(alpha - beta) u_alpha(x) = 0                         (1)
```

for every real `x`. If `alpha != beta`, (1) forces `u_alpha` to be identically zero. Its derivative
is then identically zero, and the first ODE forces `k(x)=0` for every `x`, contradicting
`k(0)>0`. Hence `alpha=beta`.

This proves injectivity of the actual causal-flow family on the full analytic strip. It uses the
linear source equation and source nonvanishing, not a norm, bounded observer, or postulated
spectral theorem.

## Xi orientation theorem

Apply source rigidity with

```text
alpha = alpha(q),
beta  = alpha(Jq) = conj(alpha(q)).
```

Then the source law is equivalent to `alpha(q)=conj(alpha(q))`, hence to
`Im alpha(q)=0`. Since

```text
Im alpha(q) = 1/2 - Re(q),
```

this is equivalent to `Re(q)=1/2`.

Conversely, on the critical line `alpha(q)` is real, so the two parameters and therefore the two
causal flows are literally equal. Thus the source law has no slack:

```text
reflected Hedenmalm flow equality at q
  <-> Im alpha(q)=0
  <-> Re(q)=1/2
  <-> sourceZeroHorizontalCarrierAt(K,q)=0.
```

The last equivalence is the existing source-zero carrier theorem. Consequently the law forces,
for every shell start `K` and every ordinary prime `p`,

```text
sourceZeroHorizontalResolutionCarrier(K,q) = 0,
sourceZeroHorizontalTailLog(q) = 0,
sourceZeroHorizontalPrimeCarrier(q,p) = 0,
sourceZeroHorizontalCarrierAt(K,q) = 0.
```

Both functional-equation orientations are killed individually, not merely after orbit summation.
The Rees-corona comparison then kills every physical prime-labelled landing without summing prime
labels or divisor copies.

## Exact strength and remaining producer

Global reflected-flow equality for every `XiZeroCopy` is equivalent to RH. This card does not prove
that global equality and does not claim RH. It replaces several abstract same-fibre receivers with
one concrete source equation:

> Prove that the canonical two-ended theta-source solution is independent of which member of a
> critical-line-reflection orbit supplies its centered spectral parameter.

The hostile audit matters: equivariance only proves that source involution transports the flow at
`alpha` to the flow at `conj(alpha)`; it does not prove those flows equal. Any next producer must
force fixedness of this actual flow, not merely transport it or pair it quadratically.

## Lean formalization

`formal/GaloisForLFunctions/RHTower/SourceZeroHedenmalmOrientationRigidity.lean`

Formal declarations:

- `hedenmalmCausalVolterra_injective_on_strip`
- `SourceZeroHedenmalmOrientationLaw`
- `sourceZeroHedenmalmOrientationLaw_iff_re_eq_half`
- `sourceZeroHedenmalmOrientationLaw_iff_carrierAt_eq_zero`
- `sourceZeroHedenmalmOrientationLaw_annihilates_both_orientations`
- `SourceZeroHedenmalmOrientationsAnnihilate`
- `sourceZeroHedenmalmOrientationsAnnihilate_iff_riemannHypothesis`

Targeted verification on 2026-08-09:

```text
lake env lean GaloisForLFunctions/RHTower/SourceZeroHedenmalmOrientationRigidity.lean
lake build GaloisForLFunctions.RHTower.SourceZeroHedenmalmOrientationRigidity
```

Both passed. `#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound` for the
source injectivity theorem, local orientation equivalence, annihilation theorem, and global RH
equivalence. Repository-wide lint is presently blocked by three unrelated, concurrently added
`HTGeometry.ConstraintFrameRelativity` modules missing from the `HTGeometry` umbrella; the new
RHTower file contains none of `sorry`, `admit`, `axiom`, `opaque`, or `unsafe`.

## Log

- 2026-08-09 — three candidate mechanisms killed; actual-flow injectivity and reflected-source
  annihilation law proved on paper.
- 2026-08-09 — theorem formalized unconditionally in Lean; targeted leaf build and axiom audit
  passed; RHTower umbrella import wired without running an umbrella build.
