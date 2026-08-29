# Theta S6G refined projective parabolic clock cone

- **ID:** S6G-PPC
- **Stage:** 3-formalized
- **Status:** `[LEAN-PROVED] [NOVELTY UNVERIFIED]`
- **Paper proof:** `../2-fully-proven/theta-s6g-refined-projective-parabolic-clock-cone.md`
- **Lean module:**
  `GaloisForLFunctions.RHTower.ThetaCuspFullReflectionEighthProjectiveRefinedParabolicClockCone`

## Exact theorem

For every `0 < x < 137/2000`, with physical modular clocks `R,z,v`, Lean proves unconditionally

```text
(13/32 + z²/32)z < v,
v < (33/80 + z²/16)z,
191/10 + (37/5)z² < R².
```

Main declaration:

```text
thetaCuspModularProjectiveClocks_mem_refinedParabolicThinCone
```

Supporting declarations prove the refined upper gap and refined scale gap have strictly positive
physical derivatives. The module also proves `v < (669/1600)z` on the missing interval.

## Verification

- scratch: `lake env lean /tmp/s6g_refined.lean` — pass;
- tree source:
  `lake env lean GaloisForLFunctions/RHTower/ThetaCuspFullReflectionEighthProjectiveRefinedParabolicClockCone.lean`
  — pass;
- final exact-module audit:
  `lake build GaloisForLFunctions.RHTower.ThetaCuspFullReflectionEighthProjectiveRefinedParabolicClockCone`
  — pass (`9079/9079`);
- `#print axioms` for refined upper gap, refined scale gap, and main cone theorem — only
  `propext`, `Classical.choice`, `Quot.sound`;
- no `sorry`, `admit`, `axiom`, `opaque`, or `unsafe` declaration;
- wired into `GaloisForLFunctions.RHTower`; no full umbrella build run.

## Research consequence

This strictly improves both dangerous faces of the old parabolic cone. It does not use or prove a
computed D1 certificate. RunPod diagnostics independently indicate direct D1 positivity on the
larger old cone; the remaining mathematical core is a computation-free determinant second-variation
proof, not further trajectory localization.
