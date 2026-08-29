# JAS Half-Density Dixmier-Trace Blindness

- **ID:** JAS-W2-DIXMIER-NOGO
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) · FALSIFIED ROUTE
- **Source:** `HedenmalmThetaMobiusPrimeNormalHalfDensityWeakSchattenBoundary.lean` · `PrimeDiagonalSingularValues.lean` · `WeakSchattenResidue.lean`
- **Statement:** Every literal Möbius prime-normal half-density diagonal has zero ordinary logarithmic Schatten-2 residue, even on nonneutral Xi copies.

## Goal

Kill the bounded diagonal singular-trace version of the proposed compensated codiagonal before
building it. The attempted chain was

`physical half-density T_q ∈ weak-S₂`
→ `quadratic weak-S₁ signal T_q* T_q`
→ `positive ordinary Dixmier trace detects boundary flux`
→ `codiagonal vanishing / source-linear prime-Poisson sewing`
→ `XiPrimePoissonReflectionSewing ρ`
→ critical line
→ RH.

The zero-residue theorem kills the third arrow. The surviving chain must instead use genuinely
unbounded, non-diagonal Gamma--theta support/grade transport before forming the codiagonal; bounded
diagonal ideal calculus loses the divisor signal.

## Gates

- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3  formalized: Lean theorem, leaf build green, axiom audit PASS
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Corpus derivation

The weak boundary theorem bounds `|a_p(q)|²` by `1/p`. Corpus theorem
`tendsto_natCast_div_nthPrime` gives little-o decay at the weak endpoint, while
`tendsto_primeDiagonalSum_div_log` proves that reciprocal-prime prefixes vanish under ordinary
Dixmier normalization. `WeakSchattenResidue.lean` supplies the exact residue notion. Corpus search
found no residue theorem for this literal physical half-density diagonal.

## Result

Module:
`GaloisForLFunctions.RHTower.HedenmalmThetaMobiusPrimeNormalHalfDensityDixmierTraceNoGo`

Main declarations:

- `approxNumber_thetaMobiusPrimeNormalHalfDensityDiagonal_sq_le_primeReciprocal`
- `schattenPowerPartialSum_two_thetaMobiusPrimeNormalHalfDensityDiagonal_le_primeDiagonalSum`
- `thetaMobiusPrimeNormalHalfDensityDiagonal_hasSchattenLogResidue_two_zero`

Paper proof: ordered-prime truncation bounds the omitted operator tail by the universal amplitude
at `p_n`, hence `a_n(T_q)² ≤ 1/p_n`. Every Schatten-2 prefix is bounded by the corresponding
reciprocal-prime prefix. Corpus Mertens/PNT asymptotics give
`primeDiagonalSum N / log N → 0`; positivity and squeezing give zero logarithmic residue for every
Xi copy. `[PROVED HERE]`

## No-go closure

- **Exact killing theorem/mechanism:** `thetaMobiusPrimeNormalHalfDensityDiagonal_hasSchattenLogResidue_two_zero`; prime sparsity makes every ordinary logarithmic Schatten-2 residue zero.
- **Strongest positive survivor:** exact little weak-`S₂` approximation bound `a_n(T_q)² ≤ 1/p_n`; a double-logarithmic or unbounded non-diagonal invariant may still retain flux.
- **New insight:** weak-ideal admission is legal but ordinary Dixmier trace is blind; Gamma--theta compensation must occur before bounded diagonal trace formation.
- **Status:** dependency-closed paper proof and Lean theorem; bounded diagonal/Dixmier compensation retired.

## Novelty audit

Search through 2026-08-29 found general Dixmier-trace/Lorentz-ideal theory such as
[Carey--Rennie--Sedaev--Sukochev](https://arxiv.org/abs/math/0611629) and
[Gayral--Sukochev](https://arxiv.org/abs/1302.1367), but no treatment of the prime-indexed Gamma
channel-gap diagonal or this all-divisor trace-blindness statement. Status: `[NOVELTY UNVERIFIED]`
pending expert review.

## Verification

- direct `lake env lean` — PASS
- leaf `lake build GaloisForLFunctions.RHTower.HedenmalmThetaMobiusPrimeNormalHalfDensityDixmierTraceNoGo` — PASS (`12794/12794`)
- `#print axioms` on three capstones — only `propext`, `Classical.choice`, `Quot.sound`
- umbrella import added to `GaloisForLFunctions/RHTower.lean`

## Log

- 2026-08-29 — created directly in 1-in-progress from corpus weak-boundary and prime-diagonal asymptotics.
- 2026-08-29 — conjecture proved; route retired with positive survivor; promoted to 3-formalized.
