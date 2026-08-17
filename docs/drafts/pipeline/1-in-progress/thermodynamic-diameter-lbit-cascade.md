# Thermodynamic diameter-scaled l-bit cascade

- **ID:** `thermodynamic-diameter-lbit-cascade`
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Date:** 2026-08-17
- **Statement:** One absolutely summable quasi-local interaction field on the half-chain, scaled by (g^{\operatorname{diam}S}), has compatible finite-volume Hamiltonians and realizes every positive temporal birth order as an exact finite-time wall crossing of a finite-support observer.

## Goal

Upgrade the abstract countable spectral cascade to one thermodynamic-limit local many-body model.

## Exact target

Let (J_S) be the corpus's rationally independent quasi-local coefficient field and set

\[
J_S(g)=g^{\operatorname{diam}S}J_S,
\qquad
E_g(\sigma)=\sum_{S\subset_{\mathrm{fin}}\mathbb N}J_S(g)\chi_S(\sigma).
\]

For (0\le g\le1):

1. (sum_S|J_S(g)|\le\sum_S|J_S|<\infty), with the inherited exponential locality envelope.
2. First-(n)-site restrictions form a nested compatible family and converge uniformly to (E_g).
3. In every finite window, the diameter-scaled spectral jet decomposes exactly by birth layer; its
   resolved temporal dimension is the number of nonempty supports below resolution because the
   coefficients within every layer are rationally independent.
4. For every (b\ge1), support (S_b=\{0,b\}) has nonzero coefficient and exact birth order (b);
   its finite-time reporter obeys the exact sinc law and the three quantitative regimes.

## Gates

- [x] 0 → 1: corpus-led construction and hostile test
- [ ] 1 → 2: complete paper proof
- [ ] 2 → 3: Lean theorem `thermodynamicDiameterLBitCascadeLaw`
- [ ] 3 → 4: publication integration

## Approach

Absolute summability is preserved because (0\le g^{\operatorname{diam}S}\le1). Canonical
inclusions preserve lattice distance and diameter. Rational independence of all nonempty (J_S)
implies nonvanishing and every layerwise independence premise. Existing exact Walsh extraction and
sinc-response theorems then apply support by support.

## Log

- 2026-08-17 — `[PIVOT]` survivor of failed rank-implies-birth conjecture.

