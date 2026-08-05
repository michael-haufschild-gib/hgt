# Mass--Xi zero-free profiled prime envelope

- **ID:** `mass-xi-zero-free-profiled-prime-envelope`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Date:** 2026-08-05
- **Parent:** `docs/reports/mass-shifted-spectral-trace-route.md`, §9.3
- **Scientific status:** `[PROVED HERE ON PAPER] [INTERNAL COLLISION AUDIT PASSED] [EXTERNAL NOVELTY UNVERIFIED]`

## Exact claim

Let `C = xiWardZeroFreeMarginC`.  For `a >= 1/2`, `sigma > 0`, and real `u`, put

```text
U_sigma(u) = exp(|u|/2 - min(C,sigma/2) |u| / log(|u|+9)^9).
```

Then the mass-shifted Xi trace satisfies

```text
||(xiMassFamily a).traceC(sigma+i u)||
  <= ((xiMassFamily a).traceReal(sigma)
      + (xiMassFamily a).traceReal(sigma/2)) * U_sigma(u).
```

If `1/2 < c < a`, its literal von-Mangoldt bottom integral satisfies

```text
||P_(a,c)(sigma+i u)||
  <= (||pi i|| * (traceReal(sigma)+traceReal(sigma/2)) + B_(a,sigma)) * U_sigma(u),
```

where `B_(a,sigma)` is the already-formalized uniform Archimedean bound.

## Goal

Extract the strongest unconditional source-side growth law currently forced by the corpus's
zero-free margin.  This claim is source-pure after the established Euler-contour identity: it uses
only the unconditional zero-free region, divisor symmetries, mass contraction, real-time trace
summability, and the uniform Gamma bound.  It does **not** establish the bounded (`lambda=0`)
endpoint and therefore makes no RH claim.

## Gates

- [x] 0 → 1 in-progress: well-posed, source-pure, exact split proof, Door passport
- [x] 1 → 2 fully-proven: dependency-closed paper proof audited line by line
- [x] 2 → 3 formalized: Lean theorem, targeted build green, axiom audit
- [ ] 3 → 4 publication-ready: standalone theorem/proof/Lean certificate

## Proof architecture

Write `R(q) = Re xiPoissonPoint(q)`, `M(q) = Re massPoint(q)`, and
`J(q) = Im massPoint(q)`.  Functional-equation reflection leaves the Poisson point fixed.  Applying
the formalized strict-right zero-free margin to a right copy, its reflection when left, and the
trivial `J=0` estimate on the critical line gives, for every divisor copy,

```text
|Im xiSpectralPoint(q)| <= 1/2 - C/log(R(q)+9)^9.
```

The mass contraction theorem and height increase then give

```text
|J(q)| <= 1/2 - C/log(R(q)+9)^9,       R(q) < M(q).
```

Fix `u`, set `U=|u|`, `L=log(U+9)`, and `G=U/L^9`.  Split each summand by `R(q) <= G`.

1. Low-height case.  Since `L>1`, `G<=U`, hence `R(q)<=U`.  Antitonicity of the zero-free margin
   yields `|J(q)| <= 1/2-C/L^9`.  Therefore

   ```text
   exp(-sigma M(q) + u J(q))
     <= U_sigma(u) exp(-sigma M(q)).
   ```

2. High-height case.  Here `M(q)>R(q)>G`.  Discarding the margin but retaining `|J(q)|<=1/2`
   gives

   ```text
   -sigma M(q)+uJ(q)
     <= -(sigma/2)M(q)+U/2-(sigma/2)G
     <= -(sigma/2)M(q)+U/2-min(C,sigma/2)U/L^9.
   ```

Thus every term is bounded by `U_sigma(u)` times the sum of its real-time weights at `sigma` and
`sigma/2`.  Summability at both positive times and the triangle inequality prove the trace claim.

Finally `U_sigma(u)>=1`: `C<=1/2`, `log(U+9)^9>=1`, and
`min(C,sigma/2)<=C`.  The exact source identity

```text
P_(a,c) = i * (pi i * trace) + arch
```

together with the uniform Archimedean bound therefore proves the prime claim with the displayed
constant.

## Hostile audit

- **Cancellation hidden?** No.  Proof is absolute-value domination; result is unconditional but
  remains exponentially large.
- **RH smuggled through a spectral hypothesis?** No.  Only the formalized unconditional zero-free
  margin is consumed.
- **Classical-route drift?** No contour/PNT remainder is imported.  Corpus divisor geometry is
  transported through the exact mass source identity.
- **Could constant exponential type already imply it?** No.  `exp(U/2-DU/log^9 U)` is
  `o(exp(U/2))`; no fixed multiplicative constant recovers this deficit.
- **Does it close §9.3?** No.  It sharpens the source acquisition frontier but leaves a gap of order
  `exp(U/2-o(U))` to boundedness.
- **Internal collision audit:** searches over `formal/`, formalized/fully-proven/failed cards, and
  the route report found zero-free margins and constant-type laws separately, but no theorem
  transporting a height-dependent margin to a profiled mass trace or literal prime-source envelope.

## Higher principle exposed

The repeated failure of constant-exponent routes is the shadow of a two-resource localization law:
transverse zero-free margin controls low spectral heights, while semigroup decay controls high
spectral heights.  The optimal split converts any decreasing margin profile `m(R)` into a vertical
growth deficit determined by balancing `U*m(G)` against `sigma*G`.  Here choosing
`G=U/log(U+9)^9` already gives the explicit deficit `U/log(U+9)^9`; sharper optimization or stronger
corpus margins can be inserted without changing the route.

## Lean certificate

Module:
`formal/GaloisForLFunctions/RHTower/XiMassZeroFreeProfiledPrimeEnvelope.lean`.

Key declarations:

- `abs_xiSpectralPoint_im_le_half_sub_zeroFreeMargin`;
- `xiMassZeroFreeProfileEnvelope`;
- `one_le_xiMassZeroFreeProfileEnvelope`;
- `abs_im_xiMassFamily_le_half_sub_zeroFreeMargin`;
- `norm_xiMassFamily_term_le_zeroFreeProfile`;
- `norm_xiMassFamily_traceC_le_zeroFreeProfile`;
- `norm_xiMassBottomPrimeIntegral_le_zeroFreeProfile`.

The module is wired into `GaloisForLFunctions.RHTower`.  Direct `lake env lean` and targeted
`lake build GaloisForLFunctions.RHTower.XiMassZeroFreeProfiledPrimeEnvelope` succeed.  Axiom audit
on the all-copy margin, summed trace profile, and prime-source profile reports only `propext`,
`Classical.choice`, and `Quot.sound`.

## Log

- 2026-08-05 — conjectured after the exact graded prime-source law exposed constant type as too
  coarse; strict-right margin transported on paper to every multiplicity copy; low/high split and
  prime-source transfer completed; Lean formalization pending.
- 2026-08-05 — all symmetry cases, term split, summation, and literal prime-source transfer proved
  unconditionally in Lean; targeted build and axiom audit pass.
