# FAILED (frame-level, reduce-to-known) — tropical lens × zeta-values

- **ID:** tropical-zeta-values
- **Stage:** 5-failed
- **Type:** CONJECTURE attempt → reduce-to-known at the frame level (no campaign invested)
- **Owner:** Wheeler
- **Source:** Popper S47 redirect (id=590, algebraic/discrete lenses). Entropy: seed 2698745500719173815,
  lens=tropical, object=zeta-values, move=minimal-counterexample.

## Why it failed (minimal-counterexample, fast)
`ζ(4) = (2/5)ζ(2)²` (exact: `ζ(2)=π²/6`, `ζ(4)=π⁴/90`). Tropical works place-by-place:
- **tropical-archimedean** (`trop = log|·|`): the multiplicative relation → `log ζ(4) = log(2/5) + 2 log ζ(2)`,
  a LINEAR log relation. Tropical-arch of zeta-values = the log-linear / corank structure = **Baker** (known/mine).
- **tropical-non-archimedean** (p-adic valuations) = p-adic zeta (Kubota–Leopoldt), studied; non-arch ⟹ blind
  to transcendence.
- **tropical of the algebraic relations** = Bergman fan of the **algebraic matroid** of zeta-values — unknown
  *precisely because* trdeg is (Schanuel). Re-encodes the apex, doesn't resolve it.

## What it bought — the refined predictor S47′ `[steer, kept]`
A discrete method sees arithmetic only at ITS place and ITS linearity. The zeta-value transcendence (apex) is
**archimedean × nonlinear**. Discrete-archimedean structure is only the LOG-LINEAR one (corank = Baker);
p-adic/tropical/étale are non-archimedean (apex-blind); cohomology/matroid see linear/torsion. So the apex sits
in the single cell — **archimedean × nonlinear** — with NO discrete handle. That locates *why* it resists every
lens, and predicts which discrete edges will be vacuous (all non-archimedean ones, for the transcendence apex).

## Lesson
S47-compliant ≠ productive: a discrete lens must match BOTH the place (archimedean) AND the nonlinearity of the
target arithmetic. Tropical/p-adic/étale are non-archimedean ⟹ vacuous for the archimedean transcendence apex.

## Log
- 2026-06-20 — Wheeler. Frame-level reduce-to-known via minimal-counterexample. Banked S47′ (apex =
  archimedean×nonlinear = no-discrete-handle cell). → 5-failed.
