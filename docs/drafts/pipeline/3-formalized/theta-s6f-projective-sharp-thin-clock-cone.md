# Theta S6F sharp thin clock cone

- **ID:** S6F-PD-SHARP-THIN-CONE
- **Stage:** 3-formalized
- **Label:** `[LEAN-PROVED] [NOVELTY UNVERIFIED]`
- **Parent:** `../1-in-progress/theta-rank-three-projective-drift.md`

## Claim

Let

```text
z(x) = -(thetaCuspModularODEState Z x).re,
v(x) = thetaCuspModularNormalizedQuasimodularDrift x.
```

For every `0 < x < 137/2000`,

```text
(13/32) z(x) < v(x) < (7/16) z(x).
```

## Paper proof

Write `R>0`, `X=R²`, `A=X(1-z²)`, and `S=R(v-z)`. Existing source theorems give

```text
A < X(0) < (600/137)² < 96/5,
X > 191/10,
0 < z < 3/10.
```

The normalized clock ODE gives

```text
v' = (3 + A/4 + S²/3)/R,
z' = A/R.
```

Hence

```text
(v-(13/32)z)' = (3-(5/32)A+S²/3)/R > 0.
```

Both clocks vanish at `x=0`, so `(13/32)z<v` for `x>0`.

This lower wall and `S=R(v-z)` imply

```text
S² < X (19z/32)².
```

For the upper gap,

```text
((7/16)z-v)'
  = (X*(3/16)*(1-z²) - 3 - S²/3)/R
  > (X*(3/16-(937/3072)z²)-3)/R.
```

The bracket is positive because

```text
0 < 3/16-(937/3072)*(3/10)²
```

and direct rational arithmetic gives

```text
3 < (191/10)*(3/16-(937/3072)*(3/10)²).
```

Thus the upper gap also has positive derivative and vanishes at `0`, proving
`v<(7/16)z`.

## Hostile audit

- No computed coefficient, enclosure, or numerical approximation occurs in proof.
- Strict inequalities are preserved at every multiplication by `R`, `X`, and positive brackets.
- The lower wall is needed before upper-wall control; replacing it by `v>0` loses required margin.
- Claim is source-orbit localization only. It does not prove projective-drift positivity.

## Research consequence

Previous formal cone `2/5<y<1/2` is not sharp enough for efficient drift analysis. New rational cone
has width `1/32`, retains simple exact constants, and strengthens the diagnostic domain for the
remaining S6F polynomial sign. The intrinsic ratio-only generalization remains false; physical
amplitude bounds are essential.

## Lean

- Module: `GaloisForLFunctions.RHTower.ThetaCuspFullReflectionEighthProjectiveSharpThinClockCone`
- Main theorem: `thetaCuspModularProjectiveClocks_mem_sharpThinCone`
- Umbrella: `GaloisForLFunctions.RHTower`
- Direct `lake env lean` and exact-module `lake build` pass.
- Axiom audit: only `propext`, `Classical.choice`, and `Quot.sound`.
- No computational result, coefficient table, external premise, hypothesis, or added axiom enters proof.
