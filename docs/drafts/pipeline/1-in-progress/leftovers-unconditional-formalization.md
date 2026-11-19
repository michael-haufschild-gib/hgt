# Unconditional formalization of every leftover paper card

- **ID:** leftovers-unconditional-formalization
- **Stage:** 1-in-progress
- **Type:** FORMALIZATION PROGRAMME
- **Scope:** every proven theorem on the cards in `docs/drafts/pipeline/2-fully-proven/leftovers/`.
- **Rules:** exact statements and constants; no hypotheses, axioms, sorry, computations or raised
  limits; corpus search before new code; one `lake --old env lean` check per finished module;
  new modules wired into their umbrella; a card moves to `3-formalized/leftovers/` only when every
  theorem on it is in Lean.

## Promoted cards

`3-formalized/leftovers/`: Nyquist critical finite part, compact physical box producers,
PM long-modulus quadrature, finite closed-cycle recovery, dyadic joint coercivity,
perturbed incidence.

## Remaining cards and their open Lean obligations

| Card | Already in Lean | Open |
|---|---|---|
| `weil-cone-pole-duality-anatomy` | (A), (B), σ-picture (`RHTower/WeilConeDefectSignRigidity`) | (C): Weil's theorem for every curve over F_q; sub-programme [leftovers-weil-theorem-for-curves](leftovers-weil-theorem-for-curves.md) |
| `route-tt-structural-theorems-2026-10-14` | T1, T3–T7, L1–L3, L5, L6, L10, L12–L14; T2 parametric and its critical-line correction (`RHTower/PrimeGapDirichletCriticalLittleO`) | L7 (Davenport–Heilbronn for Epstein zeta, class number > 1); T2 at Heath-Brown's θ₂ = 5/18 + ε |
| `twisted-minimum-principle` | main TMP (dual route), Step 1, Step 5 positivity, mixed minimum principle | primal construction: (C1) corrected, (C2), (C3), Green/jet identity of Step 4, stream-function regularity; corner-flux counterexample done (`RHTower/WhittakerCornerFlux`) |
| `nonvacuous-independence-and-polarization-import-law` | spectral-parameter core; clauses 1–2 (`RHTower/NonvacuousSmallEigenvalue`) | clause 3: Selberg zeta of the noncongruence Γ_N, continuation, zero at s_j |
| `smooth-stein-order-two-autonomous-ade-frequency-rank` | nothing | entire geometric theorem and corollary; route on `leftovers-stein-contact-geometry.md` |
| `route-e-cofactor-amplified-e3-token-supply` | elementary layer (4), (5), (6a), (7), (9) | (6): Matomäki–Teräväinen all-interval E₃ theorem; gate is Lemma 3.5(ii) (Deshouillers–Iwaniec cancellation) |
| `route-e-forbidden-support-e3-stability` | elementary layer | same analytic input as above |
| `verified-height-one-zero-turing-extension` | generic one-zero amplification | Platt–Trudgian prefix and Arb count are numerical certificates; conflicts with the no-computation rule |
