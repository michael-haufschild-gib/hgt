# HC Gauss–Hodge bounded-diagonal route kill

- **ID:** HC-UB
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Route:** HC
- **Statement:** `[LEAN-PROVED]` For `m ≥ 1`, every off-line Xi copy has `gaussHodgeMassCurrent m q` tending to `+∞` along ordered primes; consequently a finite-window HC current is bounded above iff its horizontal-collision charge is zero, and boundedness for every window is equivalent to RH.

## RH proof chain

`bounded HC current in every window → zero charge in every window → RH`.
This kills every bounded diagonal HC receiver, not only the filtered Gamma-six envelope. Surviving HC comparison must be signed/off-diagonal and genuinely unbounded or singular.

## Frontier

- `[CORPUS]` `gaussChannelResidueCurrent_mul_log` gives exact residue growth.
- `[CORPUS]` `primeActivationOccupancyFisherDensity_bounds` gives the uniform `1/(4p)` lower bound.
- `[CORPUS]` `gaussHodgeMassCurrent_virial_lower` transfers those factors to positive Hodge mass.
- `[CORPUS]` `summable_xiHorizontalCollisionGaussHodgePrimeCurrent_iff_charge_eq_zero` identifies zero charge, but no corpus theorem classifies boundedness or prime-end escape.
- `[LITERATURE]` Deninger’s cohomological/Hodge programme and Connes–Consani trace positivity provide parent frameworks, but neither defines this multiplicity-faithful prime current nor a bounded-diagonal classification: https://arxiv.org/abs/math/0204194, https://arxiv.org/abs/2006.13771, https://arxiv.org/abs/math/0703392.

## Hostile attack

- Weak-`ℓ¹`/Dixmier-residue version is `[FALSIFIED]`: exact Gauss residue contains `(p^m-1)^2`, so an off-line current is far larger than harmonic scale.
- Reflection cannot cancel: current is nonnegative and reflection-even.
- Quantitative target: prove a positive constant `C(m,q)` with `C(m,q)·p ≤ gaussHodgeMassCurrent m q p` for every prime.
- **Verdict:** `SURVIVES HOSTILE AUDIT`.

## Paper proof

Put `P=p`, `t=2 Re(q)-1`. The corpus virial inequality gives
`H_m(q,p) ≥ log(2)·R_m(p)·F(p)·log(P)·t²`. The exact residue identity, local-factor lower bound, and Fisher lower bound give
`R_m(p)F(p)log(P) ≥ (2/m²)·2^(-2m)·(P^m-1)²/(4P)`.
Since `P≥2`, `m≥1`, we have `P^m-1 ≥ P-1 ≥ P/2`; hence
`H_m(q,p) ≥ C(m,q)P`, where `C(m,q)=log(2)t²2^(-2m)/(8m²)>0` off line. Ordered primes tend to infinity, so `H_m(q,p_n)→+∞`.

Every finite-window current is a finite sum of nonnegative copy currents. Nonzero collision charge is equivalent to existence of an off-line retained support point; its first multiplicity copy supplies the escaping lower summand. Thus the window current is unbounded. Zero charge puts every retained support point on line, so every summand is zero. Therefore boundedness is equivalent to zero charge. Applying this to every window and the corpus collision-charge endpoint proves the global equivalence with RH. No conjectural input remains.

## Gates

- [x] 0 → 1 in-progress: exact route class, corpus and primary-literature audits, falsity attack
- [x] 1 → 2 fully-proven: dependency-closed paper proof
- [x] 2 → 3 formalized: `RHTower/HCGaussHodgeBoundedDiagonalNoGo.lean`; hypothesis-free grade-one RH endpoint; source check and targeted module build pass; axioms are only `propext`, `Classical.choice`, `Quot.sound`
