# Finite-difference superlacunary domination universality law

- **ID:** finite-difference-superlacunary-domination-universality
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean)
- **Source:** induction closure exposed by increment explosion and shift-stable superlacunary
  domination
- **Statement:** Every finite forward-difference layer of an eventually positive divergent-ratio
  sequence remains eventually positive and divergent-ratio; after every fixed nonnegative residual
  shift, its exponential eventually dominates every fixed positive polynomial scale.

## Gates

- [x] 0 → 1 in-progress: generated from verified Lean endpoints
- [x] 1 → 2 fully-proven: dependency-closed paper proof, `[PROVED HERE]`
- [ ] 2 → 3 formalized: exact-file Lean passed; final axiom audit pending
- [ ] 3 → 4 publication-ready: post-proof literature audit complete; final audit pending

## Corpus inputs

- `increments_ratio_tendsto_atTop`
- `tendsto_div_natCast_atTop_of_ratio_tendsto_atTop`
- `ratio_sub_nonneg_const_tendsto_atTop`
- `exists_const_mul_pow_lt_exp_div_of_ratio`
- `eventuallyPositiveShiftStableSuperlacunaryDominationUniversality`
- `exists_superlacunary_sequence`

## Proof

`[PROVED HERE]` Define `Δ⁰b=b` and
`Δ^(k+1)b(n)=Δ^k b(n+1)-Δ^k b(n)`.  Induct on `k`.  At depth zero, eventual positivity and
divergent successive ratio are hypotheses.  If they hold for `Δ^k b`, corpus increment explosion
applied to that sequence gives them for `Δ^(k+1)b`.

For each `k`, the corpus superexponential theorem gives
`Δ^k b(n)/n→+∞`, hence `Δ^k b(n)→+∞`.  The constant-shift theorem then shows that every
`Δ^k b-c`, `c≥0`, stays eventually positive and divergent-ratio.  Applying polynomial
exponential domination to this shifted layer proves, for every `A>0`, `C>0`, and natural `E,R`,

`A(C(m+1))^E < exp((Δ^k b(m)-c)/(R+1))`

eventually.  No computation is used.

The corpus factorial witness `b_n=(n+1)!`, cast to `ℝ`, is strictly increasing and positive and
starts the induction, proving that one sequence satisfies the hierarchy simultaneously at every
finite depth.

## Lean certificate

- Module:
  `GaloisForLFunctions.HTGeometry.FiniteDifferenceSuperlacunaryDominationUniversalityLaw`
- Main theorem:
  `GaloisForLFunctions.finiteDifferenceSuperlacunaryDominationUniversality`
- Exact source check:
  `lake env lean GaloisForLFunctions/HTGeometry/FiniteDifferenceSuperlacunaryDominationUniversalityLaw.lean`
  passed warning-free on 2026-07-23.
- Imported by `GaloisForLFunctions/HTGeometry.lean`.

## Novelty protocol

No literature search before exact Lean proof.

## Post-proof literature audit

Performed only after exact Lean source check passed.

- Aistleitner--Berkes--Tichy,
  *Lacunary sequences in analysis, probability and number theory*
  ([arXiv:2301.05561](https://arxiv.org/abs/2301.05561)), surveys Hadamard and superlacunary
  sequences but does not state closure of every finite forward-difference layer together with
  arbitrary residual shifts and all-polynomial exponential domination.
- Pushnitski--Yafaev, *Sharp estimates for singular values of Hankel operators*
  ([arXiv:1412.0551](https://arxiv.org/abs/1412.0551)), explicitly uses iterated differences of
  sequences, but in a polynomial-decay Hankel-operator criterion unrelated to divergent-ratio
  preservation.
- Classical lacunary power-series searches found gap and block theorems but no matching all-depth
  finite-difference law.

No exact literature match was found.  Door 2 remains open rather than claimed closed.

## Log

- 2026-07-23 — Iterating corpus increment explosion exposed an all-depth hierarchy subsuming the
  single-increment closure rather than stopping at the first new law.
- 2026-07-23 — Main theorem exact-checked warning-free, wired into HTGeometry umbrella, and
  post-proof collision audit found no exact match.
