# Gamma--digamma--zeta--Xi arbitrary-window escape universality law

## Status

Lean source complete. Exact law check deferred because
`FiniteFamilySynchronizedJetEscapeLaw.olean` is absent; its source passes exact
`lake env lean GaloisForLFunctions/HTGeometry/FiniteFamilySynchronizedJetEscapeLaw.lean`.
Dependency and law are reserved for final module audit.

## Lean-generated inputs

- `FiniteFamilySynchronizedJetEscapeLaw.lean`: arbitrary finite-order-window escape for any finite
  family of constant-coefficient differentially transcendental sources.
- `GammaDigammaZetaXiSynchronizedJetEscapeLaw.lean` and its imported freeness modules: Gamma,
  digamma, zeta, and completed Xi each have the required transcendence property; existing
  specialization only treats the initial derivative segment.

## Survivor

Every finite order window with cardinality greater than four times a finite dictionary's dimension
contains one derivative order simultaneously missed by Gamma, digamma, zeta, and Xi. Window
location is irrelevant; capacity depends only on cardinality.

## Formal target

`GaloisForLFunctions.RHTower.GammaDigammaZetaXiArbitraryWindowEscapeUniversalityLaw`

## Novelty audit

Pending post-formalization literature search.
