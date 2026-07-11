# Locally uniform real-zero transfer to RH

- **ID:** locally-uniform-real-zero-transfer
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** Route B finite-Weil characteristic-determinant lane
- **Statement:** A nonzero entire locally uniform limit inherits every closed constraint on the zeros of its approximants; in particular, locally uniform convergence of entire real-zero approximants to `XiC` implies RH.

## Goal

Formalize the analytic transfer step in the chain

```text
self-adjoint finite models
  -> real-zero characteristic determinants
  -> locally uniform convergence to XiC
  -> all XiC zeros are real
  -> RH.
```

The theorem is a transfer mechanism, not an independent source of convergence and not a new
formulation of RH. Its hypotheses mention only entire approximation and the closed zero locus of
the approximants. The open Route-B content remains the source-selected determinant construction and
the quantitative convergence estimate.

The finite spectral input is also discharged in Lean: Hermitian matrices have real-rooted
characteristic polynomials, and nowhere-zero entire normalizations preserve the zero locus.

## Gates

- [x] 0 → 1 in-progress: well-posed, source-pure transfer statement and proof mechanism isolated
- [x] 1 → 2 fully-proven: complete proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3 formalized: Lean theorems `riemannHypothesis_of_XiC_locally_uniform_real_zero_approximants` and `riemannHypothesis_of_normalizedHermitianCharpoly_tendstoLocallyUniformly`, target builds green, axioms/lint pass
- [ ] 3 → 4 publication-ready: not intended; this is standard Hurwitz/Rouché transfer infrastructure

## Approach

Use compactness of an isolating sphere to obtain a positive lower bound for the nonzero limit
function. Local uniform convergence makes the approximation error less than one third of that
bound. The existing sphere-domination theorem then plants an approximant zero in every sufficiently
small closed ball. Closedness of the prescribed zero locus forces the limit zero into that locus.

For `XiC`, take the prescribed locus to be the real axis. A right-half `xi` zero produces a nonreal
zero of `XiC`, contradicting the transfer theorem.

For the Route-B spectral specialization, use the exact normalized family

```text
F_n(z) = u_n(z) charpoly(A_n)(z),
```

where every `A_n` is Hermitian and every `u_n` is entire and nowhere zero. Matrix spectral theory
forces every zero of `F_n` to be real, so locally uniform convergence `F_n -> XiC` feeds the generic
transfer theorem directly.

## Scientific status

`[BRIDGE] [SEARCH] [NOT NEW SCIENTIFIC KNOWLEDGE]`. The mathematical mechanism is a Hurwitz/Rouché
closure theorem. Its value is that the Lean tree previously cited this analytic gate without
formalizing it. It does not prove locally uniform convergence of the CCM determinants.

## Log

- 2026-07-11 — created in `1-in-progress`; scratch proof compiled for the local persistence,
  general closed-locus transfer, and `XiC -> RH` specialization.
- 2026-07-11 — added and scratch-verified the complete Hermitian characteristic-polynomial chain;
  locally uniform convergence is now the sole hypothesis not discharged by generic formal theory.
- 2026-07-11 — both producing modules built, declarations use only `propext`, `Classical.choice`,
  and `Quot.sound`, generated API files were refreshed, and the formal lint gate passed.
