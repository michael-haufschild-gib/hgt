# Stokes-conditioned source information coenergy

- **ID:** source-horizontal-stokes-conditioned-information-coenergy
- **Stage:** 3-formalized bridge survivor
- **Type:** THEOREM / BRIDGE SURVIVOR
- **Source:** `rh-current-frontier-map.md`; P-G55--P-G58 information virial; P-G69--P-G70 reflected Stokes carrier; `source-horizontal-gamma-six-abelian-strip-slack.md`
- **Statement:** Pairing every prime-power information virial at horizontal depth `(1-s)/2` with its own P-G70 reflected Stokes weight produces a strictly positive, absolutely summable source action with a universal quadratic prime envelope for every `0<s<1`.

## Public sentence

One source subtraction is not merely convergence repair: it supplies exactly the two reciprocal
prime clocks needed to turn divergent off-wall information into finite coefficient-faithful
coenergy without erasing its sign.

## Frozen claim

For `0<s<1`, `pk=(p,e)`, and `t=(1-s)/2`, define

```text
J_s(pk) = sourceHorizontalPrimeGeometricKLScaleTerm(p,e,t)
          * gammaSewnMobiusApertureStokesReflectedWeight(s,pk).
```

Then every `J_s(pk)>0`, the complete prime-power family is summable, and with
`r_s(p)=p^(-s)` and `k=e+1`,

```text
0 < J_s(p,e) <= 4(1-s) p^(-2) r_s(p)^(2e) / k^2.
```

In particular the unstable horizontal exponent cancels exactly and the outer prime envelope is
`p^(-2)`, independent of `s`.

## Why this is a genuine Frankenstein claim

Neither parent organ has this property.  P-G58 proves the unweighted information virial is
nonsummable for every positive horizontal depth.  P-G70 proves the reflected Stokes weights are
summable but does not test them against the unbounded information observable.  The pairing uses the
functional-equation complementary coordinate `s=1-2t`; arbitrary damping would not force the
quadratic cancellation.  The resulting object preserves prime-power labels and both constructions'
literal coefficients.

## Universal-shadow map

| Corpus shadow | Proposed common law |
|---|---|
| P-G58 all-prime information divergence | unconditioned source work omits reciprocal coenergy |
| P-G69 one-subtracted anti-Herglotz response | inverse-gap susceptibility supplies two reciprocal clocks |
| P-G70 compact reflected carrier | `b/g` is positive coenergy mass, not normalized probability |
| Gamma-six abelian strip-slack no-go | missing forward payment is exactly two prime-clock units |
| reciprocal-fusion leg separation | work is quadratic in semantic/lineage separation |

## Hostile conjecture loop

### C0 — fixed-matrix reciprocal properness closes Route U

**Verdict: CIRCULAR / WRONG TYPE.** Complete powers of fixed matrices are external amplification;
Route U changes degree and admission.  No source theorem bounds those artificial powers.

### C1 — P passive prime form plus Suzuki semibounded archimedean form is positive

**Verdict: FALSE AS STATED.** Suzuki repair gives an explicit lower bound, not nonnegativity, and
no exact common test-function comparison identifies its counterterm with P-G70.  Adding the two
forms would assume the missing completion comparison.

### C2 — one-subtracted Stokes weight is coenergy for information virial

**Verdict: PROVED ON PAPER.** Exact source formulas give the displayed `p^(-2)` bound, strict
positivity, and complete prime-power summability.  It does not by itself annihilate the action or
prove RH.  Next obligation is exact Lean formalization before any completed-seam identification.

## Dependency-closed proof

Write `L=log p`, `q=p^(-1)`, `r=p^(-s)`, `k=e+1`,
`c=gammaSewnMobiusValuationContractionMultiplier(s,p)`, and `A=q/(1+q)`.  Source definitions give

```text
KL_s(p,e) = 4 exp(-Lk) V((1-s)kL) / k,
V(u)       = u cosh(u) - sinh(u),
w_s(p,e)   = c^2 A^2 (1-r)^2 r^e / (k^2 L r).
```

For `u>=0`, `0<V(u)<=u exp(u)`: strict positivity is the existing holonomy-virial theorem, while
the upper bound follows from `sinh(u)>=0` and `cosh(u)<=exp(u)`.  Moreover
`0<c<1`, `0<A<=q`, and `0<1-r<1`, so

```text
w_s(p,e) <= q^2 r^e / (k^2 L r).
```

At complementary coordinate `t=(1-s)/2`, therefore,

```text
J_s(p,e)
 <= 4(1-s)L exp(-sLk) * q^2 r^e/(k^2 Lr)
  = 4(1-s) q^2 r^(e+1) r^e/(k^2 r)
  = 4(1-s) p^(-2) r^(2e)/k^2.
```

The cancellation retains exact valuation label `e`; no tensor, averaging, or relabeling occurs.
Since `r<=R=2^(-s)<1`, the right side is bounded by the product of the prime-summable family
`p^(-2)` and geometric family `(R^2)^e`.  Hence `(J_s(p,e))_(p,e)` is summable.  Every factor in
`J_s` is strictly positive, so its total sum is strictly positive.

## External frontier

Classical Herglotz--Nevanlinna theory inserts a subtraction to represent passive functions with
non-finite raw spectral mass; operator-valued realizations and regularized Cauchy transforms are
established parent theories.  No audited source identifies the arithmetic P-G55 hyperbolic virial
with the P-G70 prime-power reciprocal-gap weights or proves the complementary-exponent quadratic
envelope.  Priority therefore remains `[NOVELTY UNVERIFIED]`.

Primary parents checked:

- Figotin--Schenker, *Spectral Theory of Time Dispersive and Dissipative Systems*, J. Stat. Phys. 118 (2005), operator Herglotz--Nevanlinna realization.
- Agler--McCarthy--Young, *Operator monotone functions and Löwner functions of several variables*, Ann. Math. 176 (2012), Pick/Nevanlinna resolvent representation.
- Langer--Woracek, *Karamata's theorem for regularized Cauchy transforms*, Proc. RSE A 155 (2025), regularized Cauchy transforms for polynomially growing measures.

## Gates

- [x] 0 → 1: exact source-pure claim, complementary parameter, falsifiers, and parent theories frozen
- [x] 1 → 2: dependency-closed paper proof and hostile audit
- [x] 2 → 3: exact unconditional Lean theorem, leaf build, axiom audit, umbrella wiring
- [ ] 3 → 4: independent priority audit and completed-seam consequence

## Open core

`[OPEN CORE]` Identify this finite positive coenergy with a completed prime--Gamma seam quantity
having a source-forced zero or opposite sign.  Summability alone is not an RH contradiction.

## Log

- 2026-08-12 — C0 and C1 killed; C2 frozen after cross-corpus/external audit.
- 2026-08-12 — C2 paper proof closed: exact two-clock cancellation leaves
  `4(1-s)p^(-2)r^(2e)/(e+1)^2`; product summability and strict positive total follow.
- 2026-08-12 — Formalized unconditionally in
  `RHTower/SourceHorizontalStokesConditionedInformationCoenergy.lean`; direct Lean check and exact
  leaf build pass, umbrella import wired, and public theorem audit reports only `propext`,
  `Classical.choice`, and `Quot.sound`.
