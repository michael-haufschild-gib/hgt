# Theta S6F projective parabolic clock cone

- **ID:** S6F-PD-PARABOLIC-CONE
- **Stage:** 3-formalized
- **Status:** `[LEAN-PROVED] [NOVELTY UNVERIFIED]`
- **Paper proof:** `../2-fully-proven/theta-s6f-projective-parabolic-clock-cone.md`
- **Lean module:**
  `GaloisForLFunctions.RHTower.ThetaCuspFullReflectionEighthProjectiveParabolicClockCone`

## Exact theorem

For every `0 < x < 137/2000`, with physical modular clocks `R,z,v`, Lean proves unconditionally

```text
(13/32 + z^2/32) z < v,
v < (33/80 + z^2/12) z,
191/10 + (147/20) z^2 < R^2.
```

Main declaration:

```text
thetaCuspModularProjectiveClocks_mem_parabolicThinCone
```

Supporting declarations prove both curved gaps and parabolic scale gap have strictly positive
physical derivatives and are anchored at the modular seam. The module also proves the convenient
upper consequence `v < (21/50)z`.

## Verification

- scratch: `lake env lean /tmp/s6f_parabolic.lean` — pass;
- tree source: `lake env lean GaloisForLFunctions/RHTower/ThetaCuspFullReflectionEighthProjectiveParabolicClockCone.lean` — pass;
- final exact-module audit:
  `lake build GaloisForLFunctions.RHTower.ThetaCuspFullReflectionEighthProjectiveParabolicClockCone`
  — pass (`9078/9078`);
- `#print axioms` for upper gap, lower gap, scale gap, and main cone theorem — only
  `propext`, `Classical.choice`, `Quot.sound`;
- no `sorry`, `admit`, `axiom`, `opaque`, or `unsafe` declaration;
- wired into `GaloisForLFunctions.RHTower` umbrella; no full umbrella build run.

Repository-wide `scripts/formal_tools.py lint` still exits nonzero only for pre-existing unrelated
unreachable modules; it does not report this module as unreachable or report a banned declaration
here.

## Research consequence

This replaces independent rectangular bounds by a curved, trajectory-coupled region. It excludes
the old artificial worst corner but does not prove projective-drift positivity. RunPod hostile tests
are documented separately and are not dependencies of this theorem.
