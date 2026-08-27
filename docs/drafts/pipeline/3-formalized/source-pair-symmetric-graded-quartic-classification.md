# Source-pair symmetric graded quartic classification

- **ID:** `source-pair-symmetric-graded-quartic-classification`
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Route:** GTA (`ORIENT` local classification)
- **Status:** `[LEAN-PROVED] [NOVELTY UNVERIFIED]`
- **Statement:** Symmetric two-even/four-odd real graded lifts preserve source-pair traces one and two exactly on the negative Pell conic, with sharp quartic positivity and faithfulness boundaries at squared even scale `3`.

## Goal

Classify complete scaled family containing corpus canonical lift and positive `(7,5)` lift. Determine whether positive quartic orientation is exceptional or occupies exact open chamber.

## Gates

- [x] 0 → 1 in-progress: family, invariants, falsifiers, and parent corpus fixed
- [x] 1 → 2 fully-proven: dependency-closed algebraic classification
- [x] 2 → 3 formalized: exact Lean theorem and audit

## Internal frontier

- `[CORPUS]` Canonical nodes `a±b` and odd nodes `b,b,-b,-b` preserve traces one/two but have sign-changing quartic anomaly `4b²(6a²-b²)`.
- `[CORPUS]` Pell nodes `a±7b` and `5b,5b,-5b,-5b` preserve traces one/two and have positive faithful quartic anomaly `100b²(6a²+23b²)`.
- `[LOCAL-RESEARCH]` Entrywise aggregation is formally excluded; classification concerns local spectral-pair reporter only.

## Theorem

For real scales `k,l`, take even nodes `a+kb,a-kb` and odd nodes
`lb,lb,-lb,-lb`. Write `A_n` for real-even moment minus real-odd moment minus
the conjugate-pair moment. Then:

1. `A₁=0` for every `k,l,a,b`.
2. `A₂=0` for every `a,b` iff `k²-2l²=-1`.
3. On that conic,
   `A₄=(k²+1)b²(12a²+(k²-3)b²)`.
4. Among trace-two-preserving lifts, `A₄≥0` for every `a,b` iff `k²≥3`.
5. Among trace-two-preserving lifts, `A₄=0 ↔ b=0` for every `a,b` iff `k²>3`.

## Dependency-closed proof

Let

`E_n=(a+kb)^n+(a-kb)^n`,

`O_n=2(lb)^n+2(-lb)^n`, and

`S_n=(a+ib)^n+(a-ib)^n`.

Direct expansion gives `A₁=E₁-O₁-S₁=0` and

`A₂=2(k²-2l²+1)b²`.

Hence the conic implies universal quadratic exactness. Conversely, universal exactness at
`(a,b)=(0,1)` forces `k²-2l²=-1`.

In degree four, expansion gives

`A₄=12(k²+1)a²b²+(2k⁴-4l⁴-2)b⁴`.

On the conic, `2l²=k²+1`, so `4l⁴=(k²+1)²` and

`2k⁴-4l⁴-2=(k²+1)(k²-3)`.

This proves the displayed factorization. Since `k²+1>0`, nonnegativity for `k²≥3`
is immediate. If `k²<3`, `(a,b)=(0,1)` makes the charge strictly negative, proving
the sharp positivity converse.

If `k²>3` and `b≠0`, all outer factors are positive and
`12a²+(k²-3)b²>0`; hence the anomaly cannot vanish. Conversely suppose `k²≤3`.
Set

`b=1`, `a=sqrt((3-k²)/12)`.

The radicand is nonnegative and `12a²+k²-3=0`, so `A₄=0` although `b≠0`.
This includes the boundary `k²=3` and proves the strict faithfulness threshold.

## Hostile attacks resolved

- `a=0`, `b=0`, and `k²=3` checked explicitly.
- Odd multiplicity four yields coefficient `4lⁿ` in even degrees and exactly the stated conic.
- Subcritical faithful failure has an explicit witness, not only a sign argument.
- Result is source-coordinate algebra only; no Xi divisor, fitted spectrum, or RH premise enters.
- Exact corpus and web searches found no prior graded-moment classification with these sharp thresholds; priority remains unverified pending expert review.

## Positive survivor and route meaning

Positive quartic orientation is not an isolated `(7,5)` trick. It is the full chamber
`k²>3` on the negative Pell conic. The canonical `(1,1)` lift lies in the sign-changing
region; `(7,5)` lies deep in the faithful region. Global GTA assembly must therefore choose
a conjugation-invariant lift from this chamber, rather than aggregate coefficientwise charges.

## Open core

`[OPEN CORE]` Construct a conjugation-invariant, stage-degree-aware global source reporter or
prove a class-complete obstruction.

## Log

- 2026-08-27 — frozen from canonical sign-changing and `(7,5)` positive Lean theorems.
- 2026-08-27 — full algebraic iff classification proved; subcritical square-root falsifier closes sharp converse.
- 2026-08-27 — formalized in `SourcePairSymmetricGradedQuarticClassification.lean`; direct Lean,
  targeted module build, formal lint, and axiom audit passed. Axiom footprint is only
  `propext`, `Classical.choice`, and `Quot.sound`.
