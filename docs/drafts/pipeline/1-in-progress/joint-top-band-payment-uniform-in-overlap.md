# Joint top-band payment uniform in overlap

- **ID:** SSH-UNIFORM-JOINT-TOP-BAND
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Parent:** [O1](weil-positivity-five-structural-mechanisms.md)
- **Target:** For every supported `C²` profile `φ` of positive square mass, a constant `Kφ` independent of overlap satisfies `|κ_N(c)| ≤ Kφ G(c + 1 + log N)` whenever `c ≥ 1`, `N ≥ 8`, and `4c ≤ N`. Here `κ_N` is `jointWitnessCoefficient` and `G = (c/N)∫φ²`.

## Proof mechanism

The existing row comparison and exact pole cancellation give

`|κ_N(c)| ≤ 17cG + 2G log N + (18c + 24)(G + A₁)(2 + log N)/N`,

where `A₁` bounds the derivative of the fixed profile autocorrelation. Retain the factor `1/N`: since `GN = cM`,

`(18c + 24)(G + A₁)/N = (18 + 24/c)(c/N + A₁/M)G ≤ 42(1/4 + A₁/M)G`.

This removes the growing overlap constant in the existing final estimate. On `c ≤ log N`, the joint coefficient is `Oφ(G log N)`, uniformly in `c`.

## Scope and status

- This controls the full joint coefficient on the top-band witness, not arbitrary coefficient vectors.
- O1 still requires the signed joint payment off this family and the complete sum-of-squares identity.
- [ ] Export the finite-horizon row remainder without weakening `G/N` to `G`.
- [ ] Formalize the uniform overlap bound and audit its axioms.
