# Gamma--Julia endpoint-correction Hilbert--Schmidt dressing

- **ID:** `gamma-julia-endpoint-correction-hilbert-schmidt-dressing`
- **Stage:** 1-in-progress
- **Type:** SOURCE REPRESENTATION / COMPACT HT CARRIER / RH FRONTIER BRIDGE
- **Status:** `[PAPER-PROVED CORE] [LEAN-PROVED CORE] [NOVELTY UNVERIFIED] [NOT RH]`
- **Parents:**
  - `../4-publication-ready/arithmetic-julia-normal-cone/main.tex`
  - `../2-fully-proven/needs-audit/xi-physical-endpoint-valuation-correction-odd-shuttle.md`
  - `../2-fully-proven/new_scientific_knowledge/suzuki-wall-field-antidiagonal-gram-lift.md`
- **RH used:** no
- **Computation used:** no

## Problem exposed by the corpus

The critical arithmetic Julia normal coordinate has boundary wall mass

```text
b_(p,e)^2 = Lambda(p^(e+1))/sqrt(p^(e+1))
          = log(p) p^(-(e+1)/2).                              (JEC1)
```

The physical endpoint correction has clocked coefficient

```text
log(p) eta_(p,e),

eta_(p,0)=2p^-2,
eta_(p,e)=-p^(-(e+1))+2p^(-2(e+1))  for e>0.                 (JEC2)
```

Earlier source audit proves no bounded depthwise multiplier converts the positive true-aperture
innovation feature into the fine-minus-coarse response.  That no-go uses the wrong Hilbert
weight for `(JEC2)`.  The Julia wall half-weight `(JEC1)` exposes a different exact operator.

## Exact diagonal dressing

Put `r=e+1` and define

```text
chi_(p,0) = 2p^(-3/2),
chi_(p,e) = p^(-r/2)(2p^-r-1)  for e>0.                      (JEC3)
```

Then coefficientwise

```text
log(p) eta_(p,e) = b_(p,e)^2 chi_(p,e).                      (JEC4)
```

This is not a fitted factorization: divide `(JEC2)` by the source-forced nonzero wall mass
`(JEC1)`.

Let `D` be the real diagonal operator on `ell^2(Primes x Nat)` with diagonal `chi_(p,e)`.
Then:

```text
chi_(p,0)>0,
chi_(p,e)<0 for e>0,
|chi_(p,e)|>0 for every (p,e),                               (JEC5)

||D|| = chi_(2,0) = 1/sqrt(2),                               (JEC6)

sum_(p,e) |chi_(p,e)|^2 < infinity,                          (JEC7)

sum_(p,e) |chi_(p,e)| = infinity.                            (JEC8)
```

Therefore `D` is a sharp strict contraction, injective Hilbert--Schmidt compact operator with
dense nonclosed range, but is not trace class.  Proof:

- depth zero is bounded by `2*2^(-3/2)=1/sqrt(2)`, with equality at `p=2`;
- at positive depth, `p^r>=4`, so
  `|chi|=p^(-r/2)(1-2p^-r)<=p^(-r/2)<=1/2`;
- squares are dominated by `4p^-3` at depth zero and by `p^-r` for `r>=2`; summing first over
  `r` gives a constant multiple of `p^-2`, hence `(JEC7)`;
- the `r=2` slice satisfies
  `|chi_(p,1)|=p^-1(1-2p^-2)>=p^-1/2`; Euler's divergence of the reciprocal-prime sum gives
  `(JEC8)`;
- nonzero diagonal entries give injectivity and dense range; their decay gives compactness and
  failure of bounded invertibility/closed range.

## The singular wall becomes an honest correction Hilbert channel

Let

```text
omega_(p,e)(t)
 = b_(p,e) exp(i t log(p^(e+1))/2)
```

be the FE-reflected critical wall field.  Although `omega(t)` is not in the raw cofinal Hilbert
space, its half-dressing is:

```text
v_(p,e)(t)=sqrt(|chi_(p,e)|) omega_(p,e)(t),

sum_(p,e) |v_(p,e)(t)|^2
 =sum_(p,e) log(p)|eta_(p,e)| < infinity.                    (JEC9)
```

Let `J` be the diagonal sign involution of `chi`.  The complete physical endpoint correction
kernel is the literal Krein matrix coefficient

```text
E(t)=sum_(p,e) log(p)eta_(p,e)exp(-i(e+1)log(p)t)
    =<v(t), J v(-t)>.                                        (JEC10)
```

Thus arithmetic Julia normal geometry supplies an infinite, compact, phase-faithful response
channel exactly where the raw critical wall has no standalone Hilbert realization.  The channel
has one positive valuation layer (`e=0`) and a negative higher-valuation tail; it is not a
positive Gram and does not have finite negative index.

## Hypertranscendental consequence

Every diagonal multiplier is nonzero, so the dressing loses no finite prime-power clock
coordinate algebraically.  Yet `chi_(p,e)->0`, so recovery is necessarily unbounded.  This gives
an explicit source-specific mechanism by which a complete hypertranscendental clock survives
inside an honest Hilbert response while no bounded local inverse can reconstruct the singular
wall.  It matches the arithmetic-Julia paper's conclusion that exact phase requires an
infinite/nonlocal state, now with the exact compact operator and singular values fixed.

## Anti-theatre boundary

`(JEC1)`--`(JEC10)` do **not** prove RH and do not control a Xi zero.  They close only the endpoint
correction representation gap.  The fine-minus-coarse Poisson layer and Gamma/polar completion
must still be assembled with this dressed Julia channel, and the resulting connected tangent
kernel must control the completed three-node response.

There is now an exact countermodel to every sign argument using only positive Euler source,
functional-equation reflection, entire symmetric completion, or hypertranscendence.
`PositivePrimeDensityMobiusInversion.lean` constructs an explicit off-line complex quartet with a
measurable nonnegative generalized-prime density, exact prime-power inversion, Riemann reflection,
entire hypertranscendental completion, `8*pi` Ward charge, and strictly positive unsquared Cauchy
orientation at every regular first-quadrant probe.  Therefore unsquared Julia/Cauchy orientation
is not merely insufficient: the proposed favorable sign is positively realized by an off-line
Euler system.  No proof may infer the opposite sign from those properties, separately or jointly.

The next RH-bearing theorem is not `D`'s contractivity.  It is:

```text
JULIA-DRESSED-ENDPOINT-EXTERIOR-INTERTWINER

the canonical causal/Poisson source plus the fixed Krein coefficient (JEC10),
after Gamma--polar completion and before projective division,
maps the source Xi-shift exterior cube to the completed physical endpoint
three-node response with a source-side Loewner/Green lower bound.              (JEC11)
```

One negative smallest-packet principal minor after exact completion falsifies `(JEC11)`.
Contractivity of `D`, positivity of the Julia defect, or exterior-cube positivity alone cannot
imply `(JEC11)`.  Any valid proof of `(JEC11)` must use ordinary-prime-specific global coupling
not shared by the positive off-line quartet model; restating positive Euler source, reflection,
entire completion, hypertranscendence, or unsquared orientation is a falsified route.

## Novelty audit

- Diagonal compact-operator criteria are standard and not claimed as new.
- Suzuki screw/Weil papers supply RH-equivalent completed response positivity, not `(JEC3)` or
  the arithmetic Julia dressing.
- Internal exact-form and concept searches found the Julia wall theorem and endpoint correction
  separately, but no identification `(JEC4)`--`(JEC10)`.
- External exact-form and concept searches on arXiv and the wider indexed literature found
  unrelated Hilbert--Schmidt RH operators, but no collision with the prime-power Julia-wall
  factorization, its sharp multiplier boundary, or the endpoint phase identity.
- Candidate novelty is the source-specific sharp Hilbert--Schmidt dressing and its phase-faithful
  Hilbert/Krein realization.  Search noncollision is not a priority claim.

## Lean audit

File:

```text
formal/GaloisForLFunctions/RHTower/
  GammaJuliaEndpointCorrectionHilbertSchmidtDressing.lean
```

Unconditionally formalized:

- `(JEC4)` coefficient factorization;
- `(JEC5)` sign and nonvanishing;
- the sharp squared bound `chi^2 <= 1/2` and equality at `(p,e)=(2,0)`;
- `(JEC7)` square summability and `(JEC8)` failure of absolute summability;
- `(JEC9)` square summability of the half-dressed amplitude;
- the phase-faithful coefficient identity underlying `(JEC10)`.

Direct `lake env lean` and final module-only `lake build` pass.  Printed axiom surfaces are exactly
`propext`, `Classical.choice`, and `Quot.sound`.  No project axiom, `sorry`, computation, or RH
assumption occurs.  Compactness, operator norm equality, dense nonclosed range, and the global
Krein-series packaging remain paper corollaries rather than Lean declarations.

## Gates

- [x] exact source and response coefficients fixed
- [x] dependency-closed paper proof of factorization, signs, sharp norm, Hilbert--Schmidt and
  non-trace-class boundary
- [x] explicit RH/non-RH separation and smallest-packet falsifier
- [x] preliminary internal and external noncollision audit
- [x] unconditional Lean formalization of the exact coefficient/operator-class core
- [ ] Lean packaging of compactness, norm equality, dense nonclosed range, and global Krein series
- [ ] exact Julia-dressed endpoint exterior intertwiner `(JEC11)`
- [ ] completed source lower bound
- [ ] RH
