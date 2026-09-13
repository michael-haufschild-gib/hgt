# Two-clock Laplace local-boundedness no-go

- **ID:** squarefree-half-laplace-two-clock-no-go
- **Stage:** 5-failed
- **Type:** FALSIFIED
- **Source:** squarefree-convolution-half-laplace-scheduled-frontier positive survivor
- **Statement:** Decoupling pole degree `κ_N` from heat time `τ_N` cannot restore local boundedness
  when `κ_N` is eventually at least `24`, `τ_N>0`, `τ_N→0`, and the heat clock is eventually
  `16/11`-dense.

## Goal

Connect the abstract weighted mesh escape law to the actual pole-cleared two-clock analytic family.
This tests the only schedule-based survivor of the diagonal Laplace no-go without assuming RH or a
Selberg--Delange asymptotic.

## Gates

- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3  formalized: Lean theorem
  `not_poleClearedFirstTraceLaplaceTwoClockLocallyBounded_of_weightedDense`, targeted build green,
  explicit axiom audit passed
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Frozen conjecture

Define the literal two-clock heat sum

`L_N(s)=sum_n a_n n^(-s) exp(-n τ_N)`

and normalized approximation

`P_N(s) L_N(s) / squarefreeCarlemanHalfDet(s)`,

where `P_N` is `poleFactorSqrtApprox (κ_N)`.  If:

1. `κ_N≥24` eventually;
2. `τ_N>0` and `τ_N→0`;
3. `|τ_N-τ_(N+1)|≤C τ_(N+1)^(16/11)` eventually;

then the normalized family is not locally bounded on `rightHalf`.

## Approach

Local boundedness at `boundaryExteriorPoint=6/11` and the certified pole-factor lower bound force
uniform boundedness of the exact heat samples `F(τ_N)`.  Conditions 2--3 then contradict
`not_exists_bounded_samples_and_weighted_dense_gaps_of_tendsto_zero`.  Pole-clock growth rate is
otherwise irrelevant.

## Surviving RH-chain edge

Exact half-divisor scalar construction remains open. The
[complete source-mass audit](dyadic-root-laplace-source-mass.md) strengthens this result: every
positive heat clock tending to zero fails with every cofinal pole-degree clock, without a gap
condition. Sparse sampling is no longer a surviving candidate for this unchanged source.

## No-go closure (mandatory when falsified)

- **Exact killing theorem/mechanism:** `[PROVED HERE]` Local boundedness at `6/11` and the explicit
  pole-factor lower bound turn every post-degree-24 two-clock value into a uniformly bounded sample
  of the canonical boundary heat profile.  Positive convergence and weighted dense gaps then
  violate the scheduled mesh escape theorem.
- **Strongest positive survivor:** Two-clock separation law: pole-degree rate is irrelevant once it
  reaches `24`. This theorem left unbounded normalized `16/11` gaps unexcluded; the later
  all-clock obstruction closes that gap and retains a quantitative positive source-mass reserve.
- **New insight:** Slowing or accelerating pole degree cannot compensate for dense heat geometry.
  The later source-mass theorem also excludes sparse heat time: a replacement must change or
  compensate the divergent profile while preserving the actual Euler germ.
- **Status:** dependency-closed paper proof; Lean module
  `GaloisForLFunctions.RHTower.SquarefreeConvolutionHalfLaplaceTwoClockNoGo`; direct check and
  targeted build `13036/13036` passed; three public theorems axiom-audited with only `propext`,
  `Classical.choice`, and `Quot.sound`; umbrella-wired; no forbidden declarations.

## Log

- 2026-09-04 — frozen after arithmetic-weighted scheduled no-go; proved, formalized, audited, and
  retired to Stage 5 without computation or RH assumption.
