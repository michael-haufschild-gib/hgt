# SC holomorphic unitization cubic-parity no-go

- **ID:** SC-HUCPN
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** read-only `rh-current-frontier-map.md` · route SC `LAND COMP`; corpus theorems `preDivisorRiggedPrimeHolomorphicReservoirMatrix_det`, `hasDerivAt_primeGammaCofinalBocksteinCoefficient_zero`, and compact-open holomorphic jet transport
- **Statement:** Canonical additive unitization of the coefficient-faithful holomorphic SC reservoir has a sign-definite nonvanishing central cubic exterior compound, so its determinants cannot converge compact-open to normalized centered Xi.

## Goal

Attack the first genuine additive escape left by the scalar-factor and matrix-equivalence no-goes.
The identity counterterm is canonical because it is full-rank at the wall and normalizes every
finite determinant to one at the origin.  Decide whether this central unitization can be the missing
SC Xi determinant.

## Gates

- [x] 0 → 1  in-progress: source-pure conjecture, hostile escape audit, corpus and literature search
- [ ] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3  formalized: Lean theorem `<name>`, exact leaf build green, scoped axiom audit PASS
- [ ] 3 → 4  publication-ready: standalone paper and independent novelty review

## Corpus baseline

For packet dimension `n=m+2`, the exact complex SC reservoir is

`M_m(z) = (I - 11ᵀ) diag(B_0(z),…,B_{n-1}(z))`,

where each `B_j` is entire, odd, vanishes at the wall, and has strictly negative first central jet
`-2 a_p log p`.  The new candidate is the literal unitized determinant

`U_m(z)=det(I+M_m(z))`.

Unlike every previously excluded multiplicative correction, `U_m(0)=1`; moving prime-log zeros of
`det M_m` are no longer automatically zeros of `U_m`.  This is therefore a genuinely new additive
branch, not another reformulation of scalar normalization.

## Conjecture loop

1. **C1 — central normalization.** `U_m(0)=1` for every packet.
2. **C2 — cubic exterior compound.** The third central derivative of `U_m` is
   `-12` times the sum over all three-prime subsets of the product of their signed neutral jets.
   Since every jet is strictly negative, every summand contributes strictly positively.
3. **C3 — cofinal obstruction.** Every packet of dimension at least three retains the fixed first
   three-prime contribution, so the cubic jets stay uniformly separated from zero.  Compact-open
   convergence of entire functions transports third derivatives, but normalized centered Xi is
   even and has zero third central derivative.  Therefore `U_m` cannot converge compact-open to Xi.

## Hostile audit

- A scalar or left/right matrix factor cannot help: already excluded by the moving-divisor theorem.
- Identity unitization does remove the old divisor argument; the new obstruction is independent and
  occurs in the third exterior compound.
- Symmetrizing `U_m(z)U_m(-z)` cancels the odd jet and is not covered.  More general additive
  counterterms can also cancel it.  Therefore the conclusion must not claim all additive coupling
  fails.
- Exact survivor: viable additive SC landing must cancel the source-derived third exterior compound
  cofinally while preserving the center unit, then satisfy every higher odd-compound cancellation.

## Attack

Use the principal-minor expansion of `det(I+X M)`.  A three-coordinate principal restriction of the
reservoir has determinant `(1-3)` times the product of the three diagonal jets.  One-coordinate
minors vanish and two-coordinate terms have even central parity, so the cubic jet of the nonlinear
entire Bockstein matrix equals the cubic coefficient of its linearization.  Apply compact-open
holomorphic jet transport at order three and Xi evenness.

## Literature audit (as of 2026-08-28)

- Principal-minor expansions, Fredholm finite-section determinants, and perturbation determinant
  trace formulas are classical; no novelty is claimed for those general identities.
- Bornemann, *On the Numerical Evaluation of Fredholm Determinants* (2008), treats convergence of
  finite determinant approximations for suitable kernels.
- Gesztesy--Zinchenko, *Symmetrized Perturbation Determinants and Applications to Boundary Data Maps
  and Krein-Type Resolvent Formulas* (2010), treats symmetrized perturbation determinants and trace
  formulas.
- No located source states the SC reservoir cubic-parity obstruction or its cofinal additive
  cancellation consequence. **Novelty status:** `[NOVELTY UNVERIFIED]`.

## Door passport

- **Unconditional source:** ordinary-prime enumeration, exact activation-Fisher density, exact
  holomorphic Gamma-Bocksteins, universal shared reservoir.
- **No RH leakage:** target uses only unconditional Xi evenness and `XiC(0) ≠ 0`.
- **Hard burden removed if proved:** canonical full-rank identity unitization, the first genuine
  additive determinant surviving earlier no-goes.
- **Positive survivor:** a landing must introduce coefficient-faithful odd-compound counterterms,
  beginning at exterior order three; central normalization alone is insufficient.

## Log

- 2026-08-28 — created after mandatory corpus search, hostile audit, and current primary-literature
  search. Frontier map left read-only.
