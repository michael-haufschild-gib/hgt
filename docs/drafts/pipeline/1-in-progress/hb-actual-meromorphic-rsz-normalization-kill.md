# Actual completed-Eisenstein RSZ normalization kill

- **ID:** C-A.9x
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** `rh-current-frontier-map.md` HB survivor after C-A.9w
- **Statement:** The genuine parameter-family regularized triple moment of the actual completed Poincare legs is the classical four-`Lambda` family, not the corpus four-`XiC` canonical vertex; their forced nonconstant pole-fill ratio kills the surviving HB scalar-landing chain for the unmodified actual source.

## Goal

Close the surviving C-A.9w burden without replacing family regularization by a pointwise reporter.
Construct the literal meromorphic regularized scalar family from the actual completed Poincare
series, evaluate it, and compare its normalization with the canonical scalar vertex.

Exact RH chain tested:

`actual meromorphic scalar triple regularization -> claimed canonical four-Xi scalar landing ->
C-A.9u balanced source -> negative BM leg -> conserved left-QNM projection -> HC94 cocycle ->
Re(s)=1/2 on every Xi fibre -> RH`.

Hostile kill criterion: if the literal family equals the classical four-`Lambda` product, then the
already-proved nonzero factor-ten mismatch at `s=t=2` makes canonical scalar landing false and
retires this HB source normalization before any QNM work. A survivor must rescale the actual
Eisenstein source by the four elementary pole-fill factors before integration; post-specialization
finite-part modification is forbidden by C-A.9w.

## Gates

- [x] 0 → 1 in-progress: well-posed, source-pure, exact chain and kill witness fixed
- [ ] 1 → 2 fully-proven: literal family construction, complete paper proof, normalization comparison
- [ ] 2 → 3 formalized: unconditional Lean theorem, direct Lean, targeted module build, axiom/lint audit
- [ ] 3 → 4 publication-ready: standalone theorem, proof, Lean certificate, literature comparison

## Approach

1. Prove the full complex two-shift Ramanujan identity
   `sum sigma_a(n) sigma_b(n) n^(-w)` as the four-zeta quotient. This is the arithmetic collapse
   forced by the two nonzero Fourier modes after unfolding one actual Poincare leg.
2. Prove the Mellin integral of the product of two corpus `modifiedBesselKOrder` functions as the
   four-Gamma quotient on its exact absolute-convergence chamber.
3. Define family regularization before specialization: subtract the full actual constant-term
   family, unfold one primitive-pair Poincare sum, apply Fourier orthogonality/Fubini, then use 1–2.
4. Continue the resulting meromorphic family by the corpus several-variable germ identity theorem.
5. Compare with `d4BMActualCanonicalScalarTripleVertex`. At `s=t=2`, use the existing theorem
   `canonical = 10 * classical` and nonvanishing to derive an unconditional contradiction to the
   claimed actual/canonical landing.

Conjecture loop:

- C-A.9x-a: full two-shift Ramanujan divisor-product identity.
- C-A.9x-b: exact two-`K` Mellin product identity.
- C-A.9x-c: literal unfolded regularized family equals the classical four-`Lambda` product.
- C-A.9x-d: actual four-`Lambda` family cannot equal the canonical four-`XiC` family.

Failure of any identity triggers correction of its exact normalization or chamber; it does not
authorize replacing the literal source, regularization, or integral by a prescribed scalar.

## Novelty and source audit

Zagier's regularized Rankin--Selberg method and the triple-Eisenstein formula quoted in
Djankovic--Khan give the classical four-completed-zeta family; Wu treats singular cases by
deformation. Corpus search finds the actual completed Poincare series, its exact Fourier
coefficients, the one-kernel Gamma--Bessel transform, and the one-Ramanujan-sum Dirichlet series,
but no two-shift divisor-product identity, two-`K` Mellin identity, literal family regularization,
or source-normalized comparison theorem. Novelty claim is the exact HB source-normalization kill
and its forced pre-integration pole-fill survivor, not the classical scalar formula by itself.

## No-go closure

- **Exact killing theorem/mechanism:** pending C-A.9x-c/d.
- **Strongest positive survivor:** pending audit; expected pre-integration pole-filled source family.
- **New insight:** pointwise regularization is already impossible by C-A.9w; only source-level
  pole filling can change the classical family into the canonical one.
- **Status:** active.

## Log

- 2026-08-29 — created in 1-in-progress after corpus and primary-source audit.
