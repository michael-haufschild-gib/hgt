# Route E four-card formalization — brick 135 (2026-09-02)

Added `formal/GaloisForLFunctions/RHTower/Sieve/KloostermanProductFrequencyGcdBound.lean` and wired it into `formal/GaloisForLFunctions/RHTower.lean` without building umbrella.

## Exact theorem chain

For positive q,r, equality of
`q*val(y)-r*val(x) mod q*r`
forces x representatives to be congruent modulo `q / gcd(q,r)`.
The quotient label `val(x)/(q/gcd(q,r))` lies in `Fin (gcd q r)`, and cross frequency is injective at fixed label. Hence:
- `card_kloostermanProductCrossPhaseFrequencyFibre_le_gcd`
- every full two-coordinate frequency fibre has cardinality at most gcd(q,r).

Fibrewise summation over nonzero frequencies plus existing injective harmonic theorem yields:
- `sum_kloostermanCrossPhaseRatio_reciprocalChord_le_productHarmonic_gcd`
- bound = gcd(q,r) * q*r * (1+log(q*r)).

Propagated unconditionally through:
- terminal and stored correlation bounds,
- shifted shared-gcd pair/modulus budgets,
- terminal/stored distinct-modulus Gram entries,
- full source Gram quadratic,
- erased off-diagonal Gram quadratic.

Principal no-premise aggregate theorems:
- `norm_kloostermanDistinctModulusTerminalGram_le_productHarmonic_gcd`
- `norm_kloostermanDistinctModulusTerminalGramQuadratic_le_productHarmonic_gcd`
- `norm_kloostermanDistinctModulusTerminalGramOffDiagonal_le_productHarmonic_gcd`.

## Verification

- Direct: `lake env lean GaloisForLFunctions/RHTower/Sieve/KloostermanProductFrequencyGcdBound.lean` passes.
- Targeted leaf: `lake build GaloisForLFunctions.RHTower.Sieve.KloostermanProductFrequencyGcdBound` passes, 13494/13494.
- Focused axiom audit of 8 principal new theorems: only `[propext, Classical.choice, Quot.sound]`.
- Scoped `git diff --check` passes.
- `scripts/formal_tools.py lint` still reports unrelated pre-existing unreachable modules; new module is not among them and is umbrella-wired.
- Scratch files removed. No task-owned Lean processes remain. Other process `/tmp/hgt_trace_retract.lean` was already running and was not touched.

## Documentation

Appended brick 135 to:
- cofactor amplified card,
- forbidden-support card,
- Matomäki–Teräväinen E3 Lean programme.

Cards remain Stage 2. This closes named noncoprime frequency-multiplicity arithmetic debt, but it still takes absolute values frequency by frequency. Remaining cofactor/forbidden core is genuine collective signed spectral/Kuznetsov saving at paper ranges, then Lemma 3.5(ii), amplification, and Theorem 1.2/all-interval supply. Growing-marker and coprime-sqrt cards remain blocked on the uniform quantitative Menon–Halász mean-square input with required sharp rate.

Related memories: `mem:cards/route-e-four-card-formalization-2026-09-02-brick-134`, `mem:cards/route-e-four-card-formalization-2026-09-02-bricks-124-130`.