# Möbius--Laplace/Hedenmalm simplicity universality law

- **ID:** mobius-laplace-hedenmalm-simplicity-universality-law
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper-proved; core Lean transport checked; thin consumer awaits final cache refresh)
- **Source:** Fresh terminal `MobiusLaplaceBoundaryMultiplicity` plus Law 19
- **Statement:** Exact half-power decay of the discrete Möbius--Laplace transform forces RH and
  global centered-Xi simplicity, hence discharges every chart of the Hedenmalm
  RH-and-simplicity universal certificate.

## Gates

- [x] Fresh terminal source read completely
- [x] Internal noncollision audit
- [x] Complete paper proof
- [x] Core Möbius-boundary-to-Xi Lean transport direct check
- [ ] Thin Law-19 consumer direct check (missing new parent `.olean`s; final audit)
- [x] Hostile literature noncollision audit
- [ ] Final module build, lint, and axiom audit

## Internal noncollision audit

Searches for Möbius--Laplace half-decay/boundary simplicity, zeta analytic order versus
`XiZerosSimple`, and Möbius/Hedenmalm certificates found no existing transport theorem. Corpus had
the boundary zeta result and the Hedenmalm universal certificate separately.

## Paper proof

Half-decay supplies RH and a nonzero zeta derivative at every critical-line zeta zero. Given a
centered Xi zero `alpha`, RH forces `alpha.im = 0`, so `rho = 1/2 + alpha*I` lies on the critical
line. The open-strip identity `xi = archFactor * zeta` and nonvanishing of `archFactor` give
`xi'(rho) = archFactor(rho) * zeta'(rho) != 0`. The affine centered coordinate has derivative
`I != 0`, hence `XiC'(alpha) != 0`. Thus all centered Xi zeros are simple. Law 19 then transports
`RH ∧ XiZerosSimple` into all Hedenmalm continuation, Hilbert, Jordan, Bezoutian, theta-source,
operator, Hermitian, and conservative-metric charts. `[PROVED HERE]`

## Lean formalization

- Core bridge appended to
  `formal/GaloisForLFunctions/RHTower/MobiusLaplaceBoundaryMultiplicity.lean`:
  `mobiusDiscreteLaplaceHalfDecay_implies_riemannHypothesis_and_xiZerosSimple`
- Thin consumer module:
  `formal/GaloisForLFunctions/RHTower/MobiusLaplaceHedenmalmSimplicityUniversalityLaw.lean`

Core source exact check passed:

```text
lake env lean GaloisForLFunctions/RHTower/MobiusLaplaceBoundaryMultiplicity.lean
```

Thin consumer intentionally awaits final build because both newly created parent modules lack
`.olean`s; no mid-discovery dependency build was run.

## Hostile literature noncollision audit

Closest source is Liflandsky's 2026 discrete Möbius--Laplace criterion (`arXiv:2607.09797`), which
states the half-power bound implies RH but assumes simple zeros for its explicit formula. Inoue
(`arXiv:1705.00853`) derives simplicity from a different summatory/Riesz-mean condition.
Hedenmalm's spectral paper (`arXiv:2606.17494`) supplies a theta/operator spectral route but not
this Möbius decay transport. No source states the decay-to-full-Hedenmalm certificate law.
Verdict: `NO COLLISION FOUND`; no priority claim.

## Log

- 2026-07-21 — Fresh post-ledger terminal read; derived and Lean-checked boundary-zeta to
  global-centered-Xi derivative transport.
- 2026-07-21 — Added thin Law-19 certificate consumer; final cache refresh pending. Targeted
  post-proof literature audit passed. Exhaustion restarted.
