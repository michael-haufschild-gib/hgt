# Multiplicative independence of shifted values {n+α} for transcendental α

- **ID:** shifted-mult-independence
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) — `[PROVED HERE]`, axiom-clean
- **Source:** composes LogIndependence.log_shifts_independent + ValueOrbit.log_relation_of_mul_relation + orbit_on_relation_subtorus
- **Statement:** `shifted_values_mult_independent` — for transcendental α>0, `∏_{n∈s}(n+α)^{k_n}=1 ⟹ k_n=0 ∀n` (the shifted values are multiplicatively independent). `shifted_value_orbit_relation_trivial` — consequently the value orbit `t↦((n+α)^{−it})_n` satisfies a character relation only trivially (rationally independent joint phase, on no proper subtorus).
- **Lean:** `RHTower.shifted_values_mult_independent`, `RHTower.shifted_value_orbit_relation_trivial` in `formal/GaloisForLFunctions/RHTower/ShiftedMultIndependence.lean`. Axiom-clean. `lake build` green.

## What this is
The transcendence backbone of the Hurwitz value-independence pillar (HT mission pillar ii). LogIndependence proves the log-independence and ValueOrbit the relation→subtorus map, but neither composes them into the multiplicative-independence statement for the actual shifted values. This makes explicit: the shifted Dirichlet monomials' frequencies are rationally independent for transcendental shift — the reason ζ(s,α) has no spurious multiplicative structure.

## Log
- 2026-07-07 — created directly in 3-formalized.

## Update: Weyl equidistribution
`shifted_character_time_average_vanishes`: composes the shifted independence with Weyl (char_time_average_tendsto) — for transcendental α and any nontrivial exponent vector, the character frequency ∑k_n log(n+α) ≠ 0, so its Cesàro time average vanishes. The shifted Dirichlet monomials (n+α)^{−it} equidistribute (no nontrivial character has nonzero mean). The almost-periodicity backbone of ζ(s,α), unconditional for transcendental shift. Axiom-clean.

## Update: Hurwitz Parseval (mean value) + concrete Liouville instance
- `shifted_dirichlet_meanValue`: the Cesàro time average of |∑_{n∈s} c_n(n+α)^{−it}|² converges to ∑_{n∈s}|c_n|² (only the diagonal survives — shifted frequencies log(n+α) are distinct). Parseval for the shifted/Hurwitz monomials, needs only α>0.
- `shifted_values_mult_independent_liouville`: fully unconditional instance at the concrete Liouville constant (via NamedTranscendental).
Axiom-clean.
