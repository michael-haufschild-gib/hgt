# Audit: does the two-prime card resolve Markus's conjecture?

**Priority:** high. Every card consuming `archimedean-relative-prime-cocycle-curvature` inherits this
risk, and if the card is correct the project holds a proof of a named open conjecture.

## The literature position

Wang–Liu–Li, arXiv:2005.02707 (2020), introduction:

- **Markus's conjecture, stated there as OPEN:** `zeta` satisfies no nontrivial algebraic differential
  equation whose coefficients are polynomials in `Gamma` and its derivatives. Equivalently
  **`zeta` is differentially transcendental over `C(s)<Gamma>_D`.**
- Markus proved the weaker statement for `zeta(sin 2 pi z)`.
- Wang–Liu–Li prove the case where the coefficients use only the three jets `Gamma, Gamma^{(n)},
  Gamma^{(l)}` — Markus's conjecture restricted, not resolved.
- Ancestry cited: Hilbert Problem 18 for `zeta`, solved by Ostrowski; Bank–Kaufman; Liao–Yang; Li–Ye.

## The implication

The card asserts `dtrdeg_K K<zeta>_D = 1` for `K = C(s)<Gamma(s+lambda) : lambda in Z log p + Z log q>_D`.
Since `0 ∈ Lambda`, `K ⊇ C(s)<Gamma>_D`, and differential transcendence over a larger field is the
stronger statement. **The card implies Markus's conjecture.**

## Audit of the card's proof

The proof runs:

1. On `Re s > 1`, `zeta` is holomorphic and vertically uniformly almost periodic. **Verified** —
   the Dirichlet series converges absolutely and uniformly on `Re s ≥ 1+delta`, and each `n^{-s}` is
   almost periodic in `t`; uniform limits of trigonometric polynomials are uniformly almost periodic.
2. Its Bohr spectrum contains `{log p : p prime}`, which is `Q`-linearly independent by unique
   factorization, so `zeta` has **infinite** rational Bohr rank. **Verified.**
3. **Projective-boundary law:** every holomorphic vertically uniformly almost-periodic function that
   is DA over `K_E` (finitely many `Gamma`-translates, pairwise incongruent mod `Z`) has **finite**
   rational Bohr rank. **NOT verified here — this is where the entire weight sits.**
4. Hence `zeta` is not DA over any `K_E`; finite support of relations extends this to
   `K_(Gamma,Lambda)`. **Verified**, given 3.

So the chain is valid and the load is isolated to step 3.

### Why step 3 is plausible

`Gamma` decays vertically like `e^{-pi|t|/2}`, so `Gamma`-translates share a one-point upper vertical
projective boundary and cannot inject frequency richness; anything almost-periodic in their
DA-closure should draw its frequencies from a finite-rank source. That is exactly the card
`finite-real-shift-gamma-projective-boundary-law`, whose core is:

> almost-periodic + differentially algebraic  ⟹  finite rational Bohr-frequency rank.

### Literature status of that core

Classical Bohr theory covers **algebraic** equations with almost-periodic coefficients (a continuous
solution of `Σ a_k(z) w^k = 0` with holomorphic almost-periodic `a_k` is itself holomorphic almost
periodic) and Bohr's spectrum/half-plane theorems. Searches did not surface the **differential**-algebraic
statement — that a DA almost-periodic function has finite rational frequency rank. It is plausible
(an order-`n` ADE bounds the phase space, so the frequency module should have bounded rank) but was
not found as a classical result.

## Recommended actions

1. Audit `finite-real-shift-gamma-projective-boundary-law` line by line, and separately the
   `almost-periodic-autonomous-ade-finite-frequency-law` card that supplies its core.
2. Determine whether "almost-periodic + DA ⟹ finite rational Bohr rank" is classical. If it is not,
   it is itself a significant result and should carry its own novelty claim.
3. If both survive: write the two-prime card up **explicitly against Markus's conjecture and
   Wang–Liu–Li**, since in that form it resolves a named open problem and its current
   `[NOVELTY UNVERIFIED]` label understates it substantially.
4. Until then, treat every downstream card — including
   `relative-postnikov-over-gamma-translation-field` — as carrying inherited risk.
