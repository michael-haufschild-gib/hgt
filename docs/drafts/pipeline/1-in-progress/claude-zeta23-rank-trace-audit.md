# Claude Zeta-23 finite Weil compression and rank--trace audit

- **ID:** `claude-zeta23-rank-trace-audit`
- **Stage:** 1-in-progress
- **Type:** PRIMARY-LITERATURE / EXTERNAL LEAN ARTIFACT AUDIT
- **Source:** [paper](https://www-cdn.anthropic.com/564f962e60643842f5fcb4a17c9dbc8f608f1c37.pdf) · [Lean artifact](https://github.com/anthropics/zeta-23-lean)
- **Statement:** Finite critical-density Gabor compressions of Weil's Hermitian form, combined with unconditional prime-side first and second moments and a multiplicity-aware rank--trace inequality, prove lower proportions `2/3` for distinct and simple critical-line zeta zeros and `5/6` for distinct zeta zeros; the mechanism cannot exclude a finite or density-zero off-line set.

## Goal

Determine which parts of the 10 August 2026 paper and its Lean artifact add mathematical content to
the RH corpus, which duplicate existing formal structure, and whether the finite-compression
mechanism supplies or changes any first unresolved RH producer.

## Gates

- [x] 0 -> 1 in-progress: paper, source repository, theorem statements, proof architecture, and
  corpus overlap audited.
- [ ] 1 -> 2 fully-proven: independent analytic peer audit or independent replay of the pinned Lean
  comparator at tag `v1.0`.
- [ ] 2 -> 3 formalized locally: only if a non-duplicative theorem is ported against the corpus's
  pinned Mathlib and connected to a literal corpus object.
- [ ] 3 -> 4 publication-ready: not applicable to an external paper without an independent audit.

## External theorem and verification status

The paper claims, unconditionally,

```text
liminf N0*(T)/N(T) >= 2/3,
liminf N0simple(T)/N(T) >= 2/3,
liminf Ndistinct(T)/N(T) >= 5/6,
```

with optimized constants approximately `0.6725`, `0.6725`, and `0.83625`, plus primitive
Dirichlet-L analogues. Its finite matrix is a critical-density Gabor compression of Weil's
Hermitian form. An on-line zero gives a positive-semidefinite rank-one contribution. A reflected
off-line pair gives one hyperbolic block of signature `(1,1)`. The prime side computes the trace and
Frobenius-square asymptotics, while a rank--trace inequality replaces the termwise positivity used
in the RH-conditional Montgomery argument.

Repository audit at public tag `v1.0`, dereferencing to commit
`3635e74826a4c1fcece7d1cd2b6fa75e43a00510`:

- theorem statements use Mathlib's `riemannZeta` and `analyticOrderAt` directly;
- source scan finds no `sorry`, `admit`, `axiom`, `opaque`, or `unsafe` declaration under
  `Zeta23/`; deliberate `sorry`s occur only in comparator challenge statement files;
- repository audit records only `propext`, `Classical.choice`, and `Quot.sound` for headline
  theorem dependencies and a successful independent comparator replay;
- artifact uses Lean `v4.33.0-rc2` / Mathlib `51e6992...`; this corpus uses Lean/Mathlib `v4.32.2`;
- the artifact contains about 102,265 lines of Lean. This audit inspected source and recorded build
  evidence but did not rerun its 9,000-job build or comparator locally.

The mathematical claim is therefore a serious, unusually strong external result with a complete
formal artifact, but remains classified as externally verified rather than independently replayed
inside this corpus.

## Corpus delta

### Already present

- `XiWeilGramStructure`: every critical-line divisor copy contributes a squared norm.
- `WeilIndexBudgetBridge` and `WeilIndexConservation`: reflected off-line orbits contribute exact
  hyperbolic inertia, with multiplicity bookkeeping.
- `MeasuredIndexBlindness`: finite and density-zero off-line sets disappear under normalized
  counting/trace limits.
- source-horizontal carrier files: prime labels, divisor multiplicity, and both reflection
  orientations are retained before bounded scalarization.

### Genuinely new to this corpus

1. The finite critical-density Gabor realization joining Weil's form to unconditional prime-side
   trace and Frobenius-square asymptotics.
2. The Hermitian rank--trace inequality using matrix positive index and von Neumann's trace
   inequality.
3. Its multiplicity-aware strengthening via the convex scalar function `g_c`, Schur--Jensen, and
   equality of the nonzero spectra of `W W*` and `W* W`.
4. The unconditional zeta and primitive Dirichlet-L density theorems themselves.
5. A sharp bandwidth-one ceiling: the scalar configuration-by-configuration method cannot approach
   density one; the artifact's explicit ceiling is approximately `0.68185`.

The reusable isolated Lean core is `Zeta23/LinAlg/` (seven files, 1,385 lines) plus
`Zeta23/ZeroSide/RankTraceMult.lean` (442 lines), Apache-2.0 licensed. A local port is justified only
with a concrete corpus consumer; copying the full artifact or proving a scalar corollary would add
duplication, not RH progress.

## RH impact and exact no-go

This paper does **not** construct the missing coefficient-faithful source theorem forcing the two
retained cofinal orientations to agree or annihilate. It first compresses to a finite scalar Weil
matrix and then reads normalized trace moments. Prime labels and the two source orientations have
already been codiagonalized. Consequently the proof bounds how many off-line signature blocks can
occur but cannot rule out one block, finitely many blocks, or density-zero dust. This is exactly the
formal blindness in `MeasuredIndexBlindness`, not a route around it.

It therefore neither proves `U_t = U_{-t}` for an individual retained Xi divisor class nor changes
the first unresolved R/L/CCM source producer. It is a major density theorem and a new receiver,
not an RH proof chain.

## Hostile follow-up: moment-neutral amplification exists but cannot close rank--trace

The initially proposed Frankenstein handoff was false. The source carrier itself already supplies
the requested raw amplification. For every off-line Xi multiplicity copy, every prime-labelled
coefficient is nonzero and those coefficients tend to zero cofinally. Hence one can choose
arbitrarily many distinct prime labels whose hyperbolic blocks have zero trace and arbitrarily small
average Frobenius-square cost, while retaining the multiplicity copy and both reflected
orientations.

The inference to contradiction has the wrong sign. In the paper's rank--trace inequality the
off-line positive-index bound occurs as `-c^2 b` in the lower-bound form, equivalently `+c^2 b` in
the certificate upper-bound form. Every independent nonzero hyperbolic block adds one positive-index
unit, irrespective of its amplitude. Amplifying one source class to `k` blocks therefore forces
`b >= k`; it does not retain the original one-pair price. The artifact's equality examples show
that this per-index allowance is sharp.

There is also an exact spectral-scale wall. If every amplified block has eigenvalue magnitude at
least `delta>0`, its Frobenius square is at least `2 delta^2`, so `k` uniformly visible blocks cost
at least `2 delta^2 k`. Sublinear second-moment growth is possible only when the amplified spectrum
collapses to zero. Bounded coefficient-faithful functional calculus preserves that collapse;
fixed-size projection/sign quantization requires unbounded normalization. The corpus already proves
that simultaneous forward/reflected admissibility of that singular normalization occurs exactly at
neutral grade, so assuming it is RH-equivalent.

The full conjecture/failure chain and positive survivor are recorded in
`source-horizontal-moment-neutral-amplification-no-go.md`. The new local Lean module
`SourceHorizontalMomentNeutralAmplification.lean` constructs the arbitrary finite packets, proves
their moment bound and reflection invariance, and proves the uniform-threshold linear-cost theorem.

## Lean disposition

1. Do not vendor the 102k-line repository or run an umbrella build in this corpus.
2. Do not locally re-formalize the headline density theorem unless toolchains are aligned; the
   external theorem already has a stronger dedicated artifact.
3. Port the 1,827-line rank--trace core only when a literal source-labelled compression consumer is
   defined. Preserve Apache attribution and audit against Lean `v4.32.2` with targeted
   `lake env lean <file>` checks.
4. The source-horizontal hyperbolic packet and its non-proportional moment budget are now formalized
   locally. They do not consume rank--trace: the paper's index term prices every replicated block.
   Do not port the rank--trace core unless a new source theorem controls that index price or prevents
   spectral collapse without assuming two-sided normalization.

## Log

- 2026-08-10 -- paper and companion repository audited; corpus overlap, exact limitation, selective
  Lean reuse boundary, and source-faithful index-amplification conjecture recorded.
- 2026-08-10 -- hostile follow-up proved the requested moment-neutral source amplification already
  exists, falsified its claimed rank--trace contradiction, and formalized the packet/threshold wall.
