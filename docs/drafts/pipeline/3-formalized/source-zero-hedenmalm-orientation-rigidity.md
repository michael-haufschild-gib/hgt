# Source-zero Hedenmalm orientation rigidity

- **ID:** SOURCE-ZERO-HEDENMALM-ORIENTATION-RIGIDITY
- **Stage:** 3-formalized
- **Type:** THEOREM / EXACT CLASSIFIER, NOT AN RH PRODUCER (paper + Lean 4)
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
5. **Conjecture: source involution itself identifies the two flows. Refined, then proved exactly.**
   It sends the causal flow at `alpha` to the anti-causal flow at `conj(alpha)`. At an Xi zero,
   two-ended matching turns this into causal orbit transport. It proves equivariance, not fixedness.
6. **Pivot: combine orbit transport with Burnol two-head energy. Failed producer audit.** Reflected
   channel exchange changes the fixed co-Poisson source normalization because its two heads are
   `1` and `log 2`. Same-source energy equality would force the line, but source symmetry supplies
   reflected-source equality instead. Assuming the former renames RH.
7. **Pivot: find an even coefficient-faithful landing of the odd carrier. Failed.** Every current
   even Green landing acquires a second reflection-odd Hodge/grade normalizer. Double oddness is
   consistent off line; removing that factor is exactly the missing incidence theorem.
8. **Pivot: homogenize the ODE into a parameter-independent symmetric block operator. Failed.**
   Corpus closed this mechanism: the required nondegenerate positive source metric/self-adjoint
   domain is the Hedenmalm--Weil positivity wall and has RH strength.
9. **Pivot: use the Route-L/Suzuki/Mass odd-current weld. Failed Xi handoff.** The weld reconstructs
   every prime coefficient, but pairing its odd distribution with an involution-even test kills it
   tautologically and loses the horizontal class. No coefficient-faithful Xi-fibre comparison is
   present.
10. **Pivot: use prime-2/prime-3 translation generation. Failed bounded-source audit.** Their entire
    windows generate the Xi ideal, but every Bezout synthesis is unbounded on the real axis.
    Pointwise conormal generation preserves conjugate nonreal zero pairs and supplies no fixedness.

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
that global equality and does not claim RH. Therefore the global law fails the corpus fatal
falsifier for a producer: stated globally, it is RH by another name. Its value is as an exact
receiver and as a test which any genuine source producer must pass.

## Unconditional source involution law

The source itself supplies a stronger unconditional relation than bare orbit transport. Let

```text
(Sf)(x) = conj(f(-x)).
```

Evenness and reality of `k = thetaCuspFullSource`, conjugation of Bochner integration, and the
measure-preserving substitution `t = -u` give, for every complex `alpha`,

```text
S(u_causal(alpha)) = u_anti(conj(alpha)).                 (2)
```

Indeed, at `x` the left side is

```text
conj(-i ∫_{t <= -x} k(t) exp(-i alpha (-x-t)) dt)
  = i ∫_{u >= x} k(u) exp(-i conj(alpha) (x-u)) du.
```

If `XiC(alpha)=0`, Schwarz reality gives `XiC(conj(alpha))=0`; exact two-ended boundary matching at
that conjugate zero turns the right side of (2) into `u_causal(conj(alpha))`. Hence at every
`XiZeroCopy q`,

```text
S(u_q) = u_Jq.                                            (3)
```

Combining (3) with causal-flow injectivity proves the sharp fixed-point classification

```text
S(u_q) = u_q
  <-> u_Jq = u_q
  <-> Re(q)=1/2
  <-> sourceZeroHorizontalCarrierAt(K,q)=0.
```

Thus actual source law preserves divisor multiplicity and both orientations exactly, but does not
choose fixed points: its unconditional content is equivariance (3). Any argument deriving global
fixedness from source involutivity, symmetry, or transform sharpness alone is circular.

The remaining producer obligation is now narrower:

> Prove that the canonical two-ended theta-source solution is independent of which member of a
> critical-line-reflection orbit supplies its centered spectral parameter.

The hostile audit matters: equivariance only proves that source involution transports the flow at
`alpha` to the flow at `conj(alpha)`; it does not prove those flows equal. Any next producer must
force fixedness of this actual flow, not merely transport it or pair it quadratically.

## Lean formalization

`formal/GaloisForLFunctions/RHTower/SourceZeroHedenmalmOrientationRigidity.lean`

Formal declarations:

- `sourceInvolution_hedenmalmCausalVolterra`
- `sourceInvolution_hedenmalmCausalVolterra_of_XiC_eq_zero`
- `hedenmalmCausalVolterra_injective_on_strip`
- `SourceZeroHedenmalmOrientationLaw`
- `sourceInvolution_xiZeroCausalFlow`
- `SourceZeroHedenmalmInvolutionFixed`
- `sourceZeroHedenmalmOrientationLaw_iff_re_eq_half`
- `sourceZeroHedenmalmInvolutionFixed_iff_orientationLaw`
- `sourceZeroHedenmalmInvolutionFixed_iff_re_eq_half`
- `sourceZeroHedenmalmOrientationLaw_iff_carrierAt_eq_zero`
- `sourceZeroHedenmalmInvolutionFixed_iff_carrierAt_eq_zero`
- `sourceZeroHedenmalmOrientationLaw_annihilates_both_orientations`
- `sourceZeroHedenmalmInvolutionFixed_annihilates_both_orientations`
- `SourceZeroHedenmalmOrientationsAnnihilate`
- `sourceZeroHedenmalmOrientationsAnnihilate_iff_riemannHypothesis`
- `sourceZeroHedenmalmInvolutionFixed_globally_iff_riemannHypothesis`

Targeted verification on 2026-08-09:

```text
lake env lean GaloisForLFunctions/RHTower/SourceZeroHedenmalmOrientationRigidity.lean
lake build GaloisForLFunctions.RHTower.SourceZeroHedenmalmOrientationRigidity
```

Both passed after the involution extension; the targeted build completed `11379/11379`.
`#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound` for source
equivariance, Xi-orbit transport, source injectivity, both local classifiers, both annihilation
theorems, and both global RH equivalences. The new RHTower file contains none of `sorry`, `admit`,
`axiom`, `opaque`, or `unsafe`. No umbrella build was run.

## Log

- 2026-08-09 — three candidate mechanisms killed; actual-flow injectivity and reflected-source
  annihilation law proved on paper.
- 2026-08-09 — theorem formalized unconditionally in Lean; targeted leaf build and axiom audit
  passed; RHTower umbrella import wired without running an umbrella build.
- 2026-08-09 — proved unconditional source-involution equivariance and Xi-zero orbit transport;
  proved involution fixedness is exactly carrier annihilation locally and RH globally; five further
  producer pivots failed exact corpus audits rather than being promoted as assumptions.

## Further producer pivots: exact failures

### 11. Minimal source-dagger cyclic boundary

Conjecture: ordinary-prime cyclic transport plus the source-dagger boundary residue forces the two
reflection orientations to share the same minimal stable boundary, hence annihilate.

Result: failed as a producer. Existing corpus theorems already give the exact classification. On
the critical line the minimal boundary is bottom and its source residue vanishes; off the line the
minimal stable boundary is the whole target. Global residue annihilation is equivalent to RH. The
ordinary-prime cycles preserve labels, ordering, and multiplicity jets, but they do not select the
bottom boundary. No source law independent of RH was found that performs that selection.

### 12. Reflected Borel common-domain transfer

Conjecture: source involution transports boundedness of one cofinal Borel orientation to the other
on one canonical source-cyclic Hilbert module, forcing both orientations bounded and therefore
forcing zero horizontal drift.

Result: failed in its unconditional form. Source involution identifies the two
orientation-dependent carriers; it does not identify their actions on one fixed carrier. Moreover,
each reflected holonomy vector already lies in the source-weighted `L2` space throughout the strip,
so individual domain membership contains no RH information. The existing sharp theorem says that
both characters are bounded on one fixed carrier exactly when the horizontal parameter vanishes.
Thus common fixed-carrier boundedness is the missing producer, not a consequence of equivariance.

These failures close the pure-symmetry family. A surviving producer must add a genuinely
coefficient-faithful, non-equivariant source anchor: a theorem that canonically identifies the two
reflection transports on the same source carrier before scalarization. Pairing, orbit closure,
ordinary `L2` membership, or passage to an orientation-dependent norm cannot supply it.
