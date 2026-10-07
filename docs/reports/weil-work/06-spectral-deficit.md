# WP06 — Produce zero lower spectral-deficit density

Status: open detection route. Mode: paper research, then Lean. Read [shared contract](/Users/michael/Documents/code/hgt/docs/reports/weil-work/README.md).

## Single objective

For `hW : WeilPositiveFull λ`, prove the exact hypothesis of `RHTower.WeilSpectral.eq_vonMangoldt_of_deficitCount`:

```lean
∀ η > 0, ∃ᶠ (T : ℝ) in Filter.atTop,
  RHTower.WeilSpectral.deficitCount hW T / T ≤ η
```

Equivalently, the nonnegative deficit has zero lower density on the **linear** scale. A subsequence suffices; proving a full `o(T)` limit is stronger than the receiver requires.

For each actual ξ-zero copy, deficit is `1` off the critical line and `(1 − atomShare)⁺` on it. The share is the canonical spectral atom at that ordinate divided by ξ-zero multiplicity. `D(T)` sums those deficits over positive ordinates up to `T`.

## Starting evidence

- [Exact deficit definition and receiver](/Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/WeilConeSingularDeficitCounting.lean:207), [rigidity theorem](/Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/WeilConeSingularDeficitCounting.lean:445).
- [Atom-share and per-copy deficit definitions](/Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/WeilConeSingularDeficitEnvelope.lean:209). Retain multiplicities and distinguish off-line copies from critical atoms.
- [Smoothed spectral count](/Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/WeilConeSpectralCounting.lean:317) supplies global information but does not match individual zeta-zero atoms.
- [Deviation residue law](/Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/WeilFullConeDeviationResidue.lean:41) identifies the arithmetic/spectral discrepancy to exploit.

## First research milestone

Derive one new comparison inequality for the **actual shared mass** between `μλ` and the ξ-zero divisor. Write an exact decomposition into a controllable term and a remainder; specify the estimate on the remainder sufficient for `D(T_j)/T_j → 0` along an unbounded sequence.

A useful intermediate theorem can give a quantitative coefficient bound from a nonzero deficit bound, but first check the existing quantitative statements in `WeilConeSingularDeficitCounting`. The advance must improve the arithmetic input or error scale, not merely restate that receiver.

If using shrinking windows to compare atoms, prove the window-to-atom passage and all required uniform estimates. A smoothed window cannot be silently replaced by an atom at the exact zero ordinate.

## Exclusions and traps

- Matching total spectral counts or their leading `T log T` term does not supply overlap with actual zeta zeros.
- `D(T) = o(T log T)` is insufficient. The required scale is `T`.
- Ordinary statements that almost all zeros lie close to the critical line do not give this deficit bound: off-line copies each cost `1`, and critical copies still need enough canonical atom mass.
- Do not assume critical support, RH, or exact zeta mass when defining the comparison.
- Positivity allows spectral mass elsewhere; that extra mass does not automatically cancel the nonnegative deficit.
- The existing rigidity theorem already implies a distinct producer cannot satisfy the target. A new result must derive the small deficit, not use that implication as evidence it is small.

## Search entry points

```sh
scripts/formal_tools.py research 'deficitCount' --mode lexical --exact --per-module 0
scripts/formal_tools.py research 'spectral atom share zero divisor deficit sublinear comparison' --mode deep --module Weil --budget-seconds 300
scripts/formal_tools.py research 'spectral counting Poisson' --module Weil
```

## Completion and handoff

`CLOSED` requires the target for arbitrary `hW`, with a compiled application giving `λ = Λ` and hence RH for any supplied producer. An estimate needing an additional correlation or overlap hypothesis is `CONDITIONAL ADVANCE`; state that missing premise quantitatively. Send a proved such property for a special producer to WP01, or a proved new obstruction with its positive survivor to the coordinator.

This package owns deficit comparison, not half-integer quantization, atomic-phase settlement or bounded-quotient arguments. It may consume their results without duplicating their work.

Owned result directory: `/Users/michael/Documents/code/hgt/docs/reports/weil-work/results/06-deficit/`.

Owned initial card: `/Users/michael/Documents/code/hgt/docs/drafts/pipeline/1-in-progress/weil-work-06-deficit.md`.

Reserved new Lean scope: `/Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/WeilWorkDeficit*.lean`. Existing modules are read-only. Output `RESULT.md`, `PROOF.md`, `EVIDENCE.md`.
