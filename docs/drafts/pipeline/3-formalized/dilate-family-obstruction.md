# The dilate family is obstructed too — the interface works

Status: formalized (Lean, unconditional)
Date: 2026-08-09

## What this tests

`no-finite-muentz-system-inverts-zeta.md` ends with `exists_detector_floor_of_linearIndependent_pairings`:
for *any* finite family in the Nyman–Beurling carrier whose Mellin-detector pairings are given by linearly
independent functions on the strip, a detector `w` annihilating the family and pairing with the target at `1`
certifies the floor `1/‖w‖`, so the target is at positive distance from the family's span. A claim like that is only
worth what a second instance shows, so this card supplies one.

## What is proved

`RHTower/DilateFamilyObstruction.lean`, for the unbalanced dilates `fractDilate θ : u ↦ {θu}/u` whose pairings
`FractDilateBalance.inner_bdDetector_fractDilate` computes as `θ^s·(−ζ(s)/s) − θ/(1−s)`:

* `dilateRowFun`, with its `castSucc`/`last` equations — those pairings bordered by the target pairing `1/s`;
* **`linearIndependent_dilateRowFun`** — they are linearly independent for distinct dilations in `(0,1)`;
* **`infDist_pos_fractDilate`** — hence `1/u` is at positive distance from the span of any finite family of
  distinct dilates in `(0,1)`, unconditionally.

The instantiation itself is four lines: supply the two pairing identities and the independence proof. Both
declarations are `#print axioms`-clean.

## The one structural difference

Clearing the relation by `s(1−s)` gives a function analytic on the convex half-plane `Re s < 1`, exactly as
for the Báez-Duarte generators. But the extra term `θ/(1−s)` contributes a second unknown — the dilate mass
`K = ∑ᵢ cᵢθᵢ` — alongside the constant `c_N`, and one trivial zero cannot separate them. Evaluating at **two**
trivial zeros, `ζ(−2) = ζ(−4) = 0`, leaves

`2K + 3c_N = 0`,  `4K + 5c_N = 0`,

whose only solution is `K = c_N = 0`. After that the argument is the same: `ζ(3/4) ≠ 0` kills the exponential
sum near `3/4` and hence everywhere, and `eq_zero_of_forall_sum_cpow_eq` kills the coefficients.

That two-zero step is the precise formal cost of dropping Báez-Duarte's normalisation. It is worth recording
because `FractDilateBalance` already showed the *balance* condition `∑ᵢ cᵢθᵢ = 0` is what a single zeta zero
forces on a dilate combination: the same quantity `K` reappears here, and two trivial zeros pin it
unconditionally where one nontrivial zero pinned it before.

## Why it matters

Two things.

**The interface is real.** The obstruction law is stated and used for a family other than the one it was built
from, with no re-derivation of the sampling, determinant, or duality steps. A further family — Beurling
dilations, Möbius-weighted generators, Balazard–Saias — needs only its pairing functions and one independence
proof.

**The obstruction is not about Báez-Duarte's normalisation.** One might have hoped the finite-section
positivity was an artefact of the `{θu} − θ{u}` combination. It is not: the raw dilates, which span a strictly
larger space (`bdGen θ = fractDilate θ − θ·fractDilate 1`), are obstructed for the same reason. So enlarging
the family within this class does not approach the target, which sharpens the no-go already recorded in
`FractDilateBalance`.
