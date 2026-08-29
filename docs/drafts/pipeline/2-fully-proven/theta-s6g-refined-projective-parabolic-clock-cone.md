# Refined projective parabolic clock cone

- **ID:** S6G-PPC
- **Stage:** 3-formalized (paper proof retained here)
- **Type:** THEOREM (Lean)
- **Source:** `../1-in-progress/theta-rank-three-projective-drift.md` · S6F-PD direct-determinant survivor
- **Statement:** On `0 < x < 137/2000`, the physical theta clocks satisfy the old parabolic lower wall together with the sharper upper wall `v < (33/80+z²/16)z` and sharper scale floor `191/10+(37/5)z² < X`.

## Goal

Shrink the computation-free physical cone selected by the exact modular ODE. This is a source
theorem, independent of D1 positivity and of every RunPod result. It strengthens the domain on
which the surviving direct rank-three determinant inequality must be proved.

## Gates

- [x] 0 → 1 in-progress: exact source-pure ODE barrier selected by hostile direct-D1 diagnostics
- [x] 1 → 2 fully-proven: complete paper proof below; `[PAPER-PROVED]`
- [x] 2 → 3 formalized: exact theorem, targeted build, and axiom audit pass
- [ ] 3 → 4 publication-ready: integrate only after S6F-PD finite gate closes

## Exact claim

For `0 < x < 137/2000`, put

```text
R = Re(theta modular scale),    X = R²,
z = positive modular-lambda clock,
v = normalized quasimodular drift.
```

Then

```text
(13/32 + z²/32) z < v,
v < (33/80 + z²/16) z,
191/10 + (37/5) z² < X.
```

## Complete proof

Existing unconditional source laws give `R>0`, `0<z<3/10`,

```text
(13/32 + z²/32)z < v,
191/10 + (147/20)z² < X,
S = R(v-z),
z' = R(1-z²),
v' = (3 + X(1-z²)/4 + S²/3)/R.
```

The first displayed conclusion is therefore already proved. It remains to improve the upper and
scale walls.

Define

```text
G(x) = (33/80)z + z³/16 - v.
```

At the modular seam, `G(0)=0`. Direct differentiation by the displayed ODE gives

```text
R G' = X(13/80 + 3z²/16)(1-z²) - 3 - S²/3.       (1)
```

The old lower wall implies `0<z-v<(19/32)z`, hence

```text
S² < X(19z/32)².                                  (2)
```

Write `t=z²`, `T=9/100`, `X₀=191/10`, and `k=147/20`. The bracket produced by
(1)--(2) is

```text
H(t) = (13/80+3t/16)(1-t) - (19/32)²t/3
     = 13/80 - (1421/15360)t - (3/16)t².
```

It is positive on `0≤t<T`: indeed `H(t)>H(T)>0` by the exact factorization

```text
H(t)-H(T) = (T-t)(1421/15360 + (3/16)(T+t)).
```

Moreover, with

```text
c₁ = X₀(1421/15360)-k(13/80) > 0,
c₂ = X₀(3/16)+k(1421/15360) > 0,
c₃ = k(3/16) > 0,
```

one has

```text
(X₀+kt)H(t) = X₀(13/80) - c₁t - c₂t² - c₃t³.
```

Thus this product strictly decreases on `[0,T]`. Exact rational arithmetic gives

```text
3 < (X₀+kT)H(T).
```

Since `X>X₀+kt` and `H(t)>0`, equations (1)--(2) imply `RG'>0`, hence `G'>0`.
Therefore `G(x)>G(0)=0`, proving

```text
v < (33/80+z²/16)z.                                (3)
```

Because `z²<T`, (3) also gives the uniform ratio bound

```text
v < (669/1600)z,
z-v > (931/1600)z.                                 (4)
```

Now define the refined scale gap

```text
K(x)=X-191/10-(37/5)z².
```

The seam value is strictly positive by the established self-dual scale bound. Differentiating and
using `S=R(v-z)` gives

```text
K' = R[(4/3)X(z-v) - (74/5)z(1-z²)].               (5)
```

Exact rational arithmetic gives

```text
74/5 < (4/3)(191/10)(931/1600).
```

Together with `X>191/10`, (4), `z>0`, and `1-z²<1`, equation (5) yields `K'>0`.
Hence `K(x)>K(0)>0`, proving the refined scale floor and the theorem. No numerical enclosure,
computed coefficient, or D1 sign enters the proof.

## Audit

- `[LOCAL-RESEARCH]` The old parabolic lower/upper/scale cone is Lean-proved in
  `ThetaCuspFullReflectionEighthProjectiveParabolicClockCone.lean`.
- `[LITERATURE]` Planat--Solé's rank-two autonomous theta phase-space argument uses a related
  polynomial-shear barrier, but does not state either refined rank-three clock wall.
- `[BRIDGE]` This theorem is a sharper source localization theorem, not RH and not the remaining
  direct D1 sign.
- `[OPEN CORE]` Give a computation-free proof that native D1 is positive on this refined cone.
- `[LEAN-PROVED]` `thetaCuspModularProjectiveClocks_mem_refinedParabolicThinCone` in
  `ThetaCuspFullReflectionEighthProjectiveRefinedParabolicClockCone.lean` proves the exact claim.

## Log

- 2026-08-29 — `[PAPER-PROVED]` Exact ODE barrier proof closed after direct-D1 hostile diagnostics
  identified upper clock ratio and scale as the dangerous directions.
- 2026-08-29 — `[LEAN-PROVED]` Exact-module build (`9079/9079`) and axiom audit pass; no computed
  result enters the module.
