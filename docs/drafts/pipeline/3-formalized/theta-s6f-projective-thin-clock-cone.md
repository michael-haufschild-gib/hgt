# Theta S6F projective thin clock cone

- **ID:** S6F-PD-THIN-CONE
- **Stage:** 3-formalized
- **Type:** UNCONDITIONAL SOURCE-ORBIT RIGIDITY
- **Parent:** `../1-in-progress/theta-rank-three-projective-drift.md`

## Theorem

Let

```text
z(x) = -(thetaCuspModularODEState Z x).re
v(x) = thetaCuspModularNormalizedQuasimodularDrift x.
```

For actual theta modular trajectory and every `0 < x < 137/2000`,

```text
(2/5) * z(x) < v(x) < (1/2) * z(x).
```

Proof is computation-free. Lower gap `v-(2/5)z` has strictly positive derivative because modular
discriminant gap stays below `20`. Modular scale is strictly increasing on positive half-line,
hence its square stays above `191/10`. Combined with existing `z<3/10` and strict clock simplex,
this makes upper gap `z/2-v` strictly increasing on missing compact interval. Both gaps vanish at
self-dual seam, so both are strict afterward.

## Lean

- Module:
  `GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspFullReflectionEighthProjectiveThinClockCone`
- Main theorem: `thetaCuspModularProjectiveClocks_mem_thinCone`
- Supporting theorems:
  - `thetaCuspModularLowerProjectiveClockGap_pos`
  - `thetaCuspModularUpperProjectiveClockGap_pos`
  - `strictMonoOn_thetaCuspModularODEState_R_re_nonneg`
  - `nineteen_point_one_lt_thetaCuspModularScale_sq_of_pos`
  - `thetaCuspModularDrift_re_eq_scale_mul_clock_sub_lambda`
- Umbrella: `GaloisForLFunctions.RHTower`

Direct `lake env lean`, exact module `lake build`, and `#print axioms` pass. Dependencies are only
`propext`, `Classical.choice`, and `Quot.sound`.

## Research consequence

Actual S6F orbit occupies only thin slice `2/5<y=v/z<1/2`, not whole simplex `0<y<1`.
RunPod diagnostics independently indicate normalized projective drift is positive on stronger
half-cone `X>=191/10`, `0<=z<=3/10`, `2/5<=y<=1/2`; no computed coefficient enters Lean.
Remaining paper/Lean core is independent conceptual proof of that polynomial half-cone sign.
Previous upper scale localization `X<=20` is no longer needed if half-cone positivity is proved.
