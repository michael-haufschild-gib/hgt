# TG complete mixed reflected cubic first-order coefficient

- **ID:** TG-C7-FIRST-COEFFICIENT
- **Stage:** 3-formalized
- **Route:** TG
- **Module:** `RHTower.PrimeBurnolMixedCubicLaurent`
- **Parent:** `../1-in-progress/tg-mixed-reflection-first-order-counterterm.md`

## Exact source theorem

For every finite injective prime-depth packet and every real theta grade, let tau(k) be the
actual reflected source cubic from `PrimeBurnolMixedCubicPrincipal`, with its already checked
second-order coefficient L2. The new theorem proves the two-sided punctured limit

```
k (tau(k)-L2/k²) -> L1.
```

L1 is an explicit finite matrix expression, not an existential coefficient. Put
`E=diag(I,0)`, `F+=diag(0,iI)`, `F-=diag(0,-iI)`, `J0=2[[G,M1],[M1,M2]]`, and `A=J0^-1`.
With the actual parity projections p,q, define

```
c = E J0 E,       d = F+ J0 E + E J0 F-,
r = F+ A F-,      s = E A F- + F+ A E,
L1 = Tr(d p r q c(p-q) + c p s q c(p-q) + c p r q d(p-q)).
```

The code uses the definitionally equivalent actual `c(0)` and regularized inverse at zero.
Every mixed-prime entry and the entire confluent inverse are retained. No invertibility,
convergence, derivative, projection, or arithmetic premise is assumed in the endpoint.

## Dependency-closed proof

1. The exact rational source matrix J(k) factors through k squared. Constructing its
   square-parameter expression proves differentiability at zero and `J'(0)=0`.
2. The finite determinant/adjugate formula proves entrywise differentiability of the inverse
   at its checked invertible value. The same square-parameter factorization gives `(J^-1)'(0)=0`.
3. Entrywise product rules give `c'(0)=d` and the derivative s of
   `R(k)=diag(k,iI) J(k)^-1 diag(k,-iI)`. Explicit block inverses prove
   `R(k)=k² c(k)^-1` away from zero.
4. The actual single-inverse cubic identity extends `k² tau(k)` differentiably to zero.
   Its derivative is exactly L1; the remaining polynomial term has derivative zero after
   multiplication by k squared. Its value at zero is L2 by uniqueness of the previously
   checked principal limit.
5. The derivative's slope limit, followed by exact source/parity conjugation, proves the
   stated endpoint for the original literal reflected L2 source.

This uses symbolic matrix identities and Lean proofs, with no numerical experiment.

## Frontier contribution and limits

The missing mixed first-order Laurent coefficient is now determined from the actual source.
Together with L2 it gives the full two-term asymptotic required for local Gamma comparison.
The remainder after both pole subtractions is only shown to be `o(1/k)` here; a bounded finite
part is not asserted. Single-prime Schur simplification, its sign and cofinal behavior, actual
Gamma matching, Hardy-index transfer, and the final sub-unit estimate remain open.

The preceding C6 theorem already excludes bounding the uncompensated canonical counterterm.
A successful TG producer must compare the joint prime–Gamma operator before completion.
RH remains unproved and unfalsified.

## Audit

- Production `lake --old env lean -o ... PrimeBurnolMixedCubicLaurent.lean`: exit 0,
  no warnings, default heartbeats.
- Leaf wired into RHTower umbrella; no full or umbrella build.
- Separate `lake --old env lean /tmp/...` import audit of all six public theorem axiom sets:
  exit 0; only `propext`, `Classical.choice`, and `Quot.sound`.
- Corpus index refreshed. Final lint exits 1 on twelve unrelated unwired RHTower leaves:
  CCMApertureChainProfile, CCMApertureTranslationChains, CCMExponentialRampPrimeMoment,
  CCMExponentialRampSourceDissipation, CCMExponentialRampTerminalEntropy,
  CCMRetainedChainKernelLower, MobiusDivisorCriticalPrimeNegativeEscape,
  MoebiusMollifiedCriticalMoment, MoebiusMollifiedErrorThreeLines,
  ThetaCuspCurvatureDefectKernel, ThetaMovingShellFirstOrderPhase, ZetaZeroDensityPowerSaving.
  Neither new TG leaf is reported. Scoped tracked-file whitespace check passes.
- Owned scratch, search and diagnostic files cleaned after recording outcomes; matching production
  `.olean` files retained. No owned process remains. No commit or push.
