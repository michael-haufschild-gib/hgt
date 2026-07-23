# Shift-stable superlacunary domination universality law

- **ID:** shift-stable-superlacunary-domination-universality
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean)
- **Source:** theorem-first closure of constant-shift ratio stability and
  polynomial-versus-superlacunary exponential domination
- **Statement:** Eventual positivity and divergent successive ratio already force divergence to
  infinity; every fixed nonnegative shift then preserves positivity and ratio divergence and,
  through its exponential, eventually dominates every fixed positive polynomial scale.

## Gates

- [x] 0 → 1 in-progress: generated from verified Lean endpoints
- [x] 1 → 2 fully-proven: dependency-closed paper proof, `[PROVED HERE]`
- [ ] 2 → 3 formalized: exact-file Lean passed; final axiom audit pending
- [ ] 3 → 4 publication-ready: post-proof literature audit complete; final audit pending

## Corpus inputs

- `ratio_sub_nonneg_const_tendsto_atTop`
- `tendsto_div_natCast_atTop_of_ratio_tendsto_atTop`
- `exists_const_mul_pow_lt_exp_div_of_ratio`

## Proof

`[PROVED HERE]` Suppose `b_n>0` eventually and `b_{n+1}/b_n→+∞`.  Corpus
superexponential growth gives `b_n/n→+∞`; since eventually `n≥1` and `b_n>0`, this forces
`b_n→+∞`.  Fix `c≥0`.  Eventual inequality `b_n>c` gives `b_n-c>0`.  The corpus
constant-shift theorem gives

`(b_{n+1}-c)/(b_n-c) → +∞`.

Apply the corpus polynomial-versus-exponential domination theorem to the shifted sequence
`n ↦ b_n-c`.  For every `A>0`, `C>0`, and natural `E,R`, some `M₀` satisfies, for all
`m≥M₀`,

`A(C(m+1))^E < exp((b_m-c)/(R+1))`.

Taking `c=j∈ℕ` is the support shift induced by any fixed formal derivative order.  No computation
is used.

## Lean certificate

- Module:
  `GaloisForLFunctions.HTGeometry.ShiftStableSuperlacunaryDominationUniversalityLaw`
- Main theorem:
  `GaloisForLFunctions.eventuallyPositiveShiftStableSuperlacunaryDominationUniversality`
- Exact source check:
  `lake env lean GaloisForLFunctions/HTGeometry/ShiftStableSuperlacunaryDominationUniversalityLaw.lean`
  passed warning-free on 2026-07-23.
- Imported by `GaloisForLFunctions/HTGeometry.lean`.

## Novelty protocol

No literature search before exact Lean proof.

## Post-proof literature audit

Performed only after exact Lean source check passed.

- Aistleitner--Berkes--Tichy,
  *Lacunary sequences in analysis, probability and number theory*
  ([arXiv:2301.05561](https://arxiv.org/abs/2301.05561)), surveys Hadamard-gap and lacunary
  sequence theory, not preservation of a ratio tending to infinity under every constant support
  shift together with the displayed all-polynomial exponential domination conclusion.
- Aistleitner--Kabluchko--Prochno,
  *Arithmetic sensitivity of cumulant growth in lacunary sums*
  ([arXiv:2512.15501](https://arxiv.org/abs/2512.15501)), studies finite ratio limits and cumulant
  asymptotics rather than the divergent-ratio, derivative-shift domination law.
- Targeted searches of classical lacunary power-series and gap-series sources found derivative and
  Hadamard-gap results, but no theorem matching the simultaneous eventual positivity, shifted
  divergent ratio, and universal polynomial exponential bound.

No exact literature match was found.  Door 2 remains open rather than claimed closed.

## Log

- 2026-07-23 — Whole-corpus terminal review found that shift stability and exponential domination
  were proved independently, while no consumer connected them.
- 2026-07-23 — Main theorem exact-checked warning-free, wired into HTGeometry umbrella, and
  post-proof collision audit found no exact match.
