# Unitary rank-one superzeta/dual-Satake Torelli universality law

- **ID:** unitary-rank-one-superzeta-dual-satake-torelli-universality
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean)
- **Source:** theorem-generated closure of `finiteSuperzetaResolventTrace_eq_iff`,
  `unitaryRankOneDualSpectrum_closed_iff_firstMoments_real`, and
  `unitaryRankOneDualSpectrum_allMoments_real_and_localFactor_eq`
- **Statement:** For an `n`-point unitary rank-one spectrum, equality of its complete superzeta
  resolvent trace with the dual trace is equivalent to reality of only the first `n` secular
  moments. Either condition forces reality of every moment and dual invariance of every local
  Euler factor.

## Goal

Connect additive superzeta trace tomography to multiplicative rank-one duality and Satake reality
through the shared finite spectral multiset.

## Gates

- [x] 0 → 1 in-progress: source-pure theorem-generated connector
- [x] 1 → 2 fully-proven: dependency-closed paper proof, `[PROVED HERE]`
- [x] 2 → 3 formalized: exact-file Lean check passed; final global axiom audit pending
- [x] 3 → 4 publication-ready: post-proof collision audit found no exact literature match

## Corpus inputs

- `finiteSuperzetaResolventTrace_eq_iff`
- `unitaryRankOneDualSpectrum_closed_iff_firstMoments_real`
- `unitaryRankOneDualSpectrum_allMoments_real_and_localFactor_eq`
- `unitaryRankOneSpectrum`
- `unitaryRankOneDualSpectrum`
- `rankOneDualMultiplier`

## Proof

**[PROVED HERE]** Let `f : Fin n → Circle`. Form the complete additive superzeta trace by summing
the local power-series resolvents of the complex multipliers `f(i)`. Form its dual trace by
replacing every multiplier with its abstract rank-one dual.

Finite superzeta Torelli says these two complete traces are equal exactly when their underlying
complex spectral multisets agree. By definition those multisets are the unitary spectrum and its
rank-one dual spectrum, so trace equality is exactly dual closure.

On the unit circle, rank-one inversion equals complex conjugation. The finite dual-Satake Torelli
theorem therefore identifies dual closure exactly with reality of the secular power sums of orders
`k≤n`. This gives the sharp finite trace test.

Under either equivalent condition, dual closure holds. The terminal unitary duality theorem then
forces every secular moment, with no order cutoff, to be real and makes the local Euler polynomial
unchanged when all multipliers are inverted. Thus a complete additive-resolvent symmetry is
detected by finitely many real moments and propagates to all additive moments and every
multiplicative local factor. No computation is used. ∎

## Strict gain over corpus endpoints

Finite superzeta Torelli detects multiset equality but has no unitary duality, real-moment
criterion, or Euler-factor consequence. Unitary dual-Satake Torelli detects dual closure from
moments but does not identify it with equality of complete superzeta traces. Their closure gives
one additive-to-multiplicative spectral law with a sharp finite test and all-order consequences.

## Lean certificate

- Module:
  `GaloisForLFunctions.RHTower.UnitaryRankOneSuperzetaDualSatakeTorelliUniversalityLaw`
- Main theorem:
  `unitaryRankOne_superzetaDualSatakeTorelliUniversality`
- Exact-file command:
  `lake env lean GaloisForLFunctions/RHTower/UnitaryRankOneSuperzetaDualSatakeTorelliUniversalityLaw.lean`
  passed warning-free on 2026-07-23.
- Umbrella:
  imported by `formal/GaloisForLFunctions/RHTower.lean`.

## Novelty audit

No literature search occurred before dependency-closed paper and Lean proofs. Post-proof searches
for superzeta resolvent traces, finite power-sum reconstruction, unitary Satake duality, and local
Euler factors found no exact additive-trace/finite-reality/multiplicative-factor equivalence.
Closest primary sources:

- J. S. Friedman, J. Jorgenson, and L. Smajlovic, *Superzeta functions, regularized products, and
  the Selberg zeta function on hyperbolic manifolds with cusps*,
  <https://arxiv.org/abs/1701.06869>, develops superzeta continuation and regularized products,
  not finite multiset tomography tied to Satake duality.
- G. Grubb, *A resolvent approach to traces and zeta Laurent expansions*,
  <https://arxiv.org/abs/math/0311081>, connects resolvent trace asymptotics to zeta
  coefficients, without finite dual-spectrum recovery or Euler-factor invariance.
- S. Bera and S. K. Mukherjee, *Generalized power sum and Newton-Girard identities*,
  <https://arxiv.org/abs/2004.14590>, extends the algebraic power-sum identities underlying
  finite Torelli, but has no unitary dual/Satake or superzeta trace phase.
- Y. Mieda, *Parity of the Langlands parameters of conjugate self-dual representations of GL(n)
  and the local Jacquet-Langlands correspondence*, <https://arxiv.org/abs/1603.04691>, studies
  conjugate self-dual local parameters, not the sharp first-`n` secular-moment test or complete
  resolvent-trace equality.

## Log

- 2026-07-23 — whole-corpus terminal scan matched finite superzeta Torelli with unitary
  rank-one dual-Satake Torelli through the same spectral multiset.
- 2026-07-23 — dependency-closed paper proof completed before literature search or Lean source.
- 2026-07-23 — exact Lean proof passed warning-free and module was wired into RHTower umbrella.
- 2026-07-23 — post-proof collision audit found no exact literature match.
