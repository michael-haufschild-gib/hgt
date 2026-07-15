# All-order even finite-tail residue of the Gamma factorial microscope

- **ID:** `gamma-factorial-all-order-even-finite-tail`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Scientific status:** `[PROVEN IN LEAN] [CANDIDATE NEW SCIENTIFIC KNOWLEDGE]`
- **Statement:** At every positive even polygamma order `m`, after the reciprocal principal jet and
  bounded zeta layer cancel, multiplication by `(n+1)^m` exposes the universal nonzero residue
  `-(m-1)!`.

## Goal

Resolve the coordinates missed by the all-order zeta-parity law.  The theorem completes the first
two subordinate levels of the pole-germ microscope: even zeta values detect odd polygamma orders,
and rational finite Euler-product tails detect positive even orders.

## Theorem

Let `m=2r+2`, let `sₙ=(-1)^(n+1)/n!`, and fix `x≠0`.  Lean proves

\[
 (n+1)^m
 \frac{s_n^{m+1}\psi^{(m)}(-n+s_nx)+m!/x^{m+1}}
      {s_n^{m+1}}
 \longrightarrow -(m-1)!.
\]

The limit is nonzero and independent of `x`.  Equivalently, after the local odd-zeta value cancels
the limiting generalized harmonic sum, the remainder is exactly governed by

\[
 (n+1)^m\sum_{j>n}j^{-(m+1)}\longrightarrow\frac1m.
\]

## Meaning

The cancellation at even order is not loss of information.  It routes those jet coordinates to a
strictly finer arithmetic scale.  Every positive polygamma coordinate is therefore detected by a
uniform parity-tail ladder:

- odd `m`: factorial-scale residue `2m!ζ(m+1)≠0`;
- positive even `m`: finer factorial-polynomial residue `-(m-1)!≠0`.

The displacement `sₙx` contributes only factorially small errors against the polynomial tail
normalization, so the second residue is universal across the punctured microscope.

## Lean certificate

Module: `formal/GaloisForLFunctions/HTGeometry/GammaFactorialAllOrderFiniteTail.lean`.

Headline declarations:

- `hzeta_natSucc_eq_riemannZeta_sub_shiftedHarmonicPowerSum_zero`
- `tendsto_scaled_riemannZeta_sub_shiftedHarmonicPowerSum_zero`
- `tendsto_natSuccPow_mul_localPolygamma_sub`
- `tendsto_natSuccPow_mul_shiftedHarmonicPowerSum_sub_zero`
- `tendsto_gammaFactorialEvenPolygamma_regular_finiteTail`
- `tendsto_gammaFactorialScaledPolygamma_even_finiteTail`

Direct compilation and the individual Lake target pass.  Axiom audits use only `propext`,
`Classical.choice`, and `Quot.sound`.  Formal lint passes.  No full build and no numerical
computation were used.

## Gates

- [x] 0 → 1 in-progress: finite-tail normalization and predicted coefficient isolated
- [x] 1 → 2 fully-proven: Hurwitz tail, local error, and shifted-sum error combined exactly
- [x] 2 → 3 formalized: uniform Lean theorem, targeted build, axiom audit, and lint pass
- [ ] 3 → 4 publication-ready: integrate into the pole-germ residue paper and priority audit

## Approach

Identify the zeta-minus-partial-sum remainder with a positive-shift Hurwitz tail.  Apply the exact
continuum limit at exponent `m+1`.  Differentiability at the local point `1` makes the local
polygamma displacement `O(sₙ)`, and the shifted-harmonic comparison is `O(sₙHₙ)`; factorial decay
annihilates both after multiplication by `(n+1)^m`.  The identity `m!/m=(m-1)!` gives the residue.

## Log

- 2026-07-15 — proved and formalized uniformly for every positive even polygamma order.
