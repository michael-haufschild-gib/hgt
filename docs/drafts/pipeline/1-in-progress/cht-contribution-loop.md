# CHT contribution loop

- **ID:** cht-loop
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean), programme loop
- **Source:** goal of 2026-11-07; formal/GaloisForLFunctions/CriticalHardyTheoryOfTheWindowCone/README.md §10
- **Statement:** successive unconditional theorems about the window cone, its data, edge and canonical system.

## Goal
Answer the open topics of README §10 (margin law, uniformity in n, singular part, bridge, edge coefficients,
formats on the cone, transport, data beyond ζ). Working log: logs/cht-250-contributions-2026-11-07.md.

## Gates
- [x] 0 → 1  in-progress
- [ ] 1 → 2  per contribution
- [ ] 2 → 3  per contribution

## State
- Proved (Lean): local density law; residue read from above at rate `1/c`; datum region left of `β = 1` for every
  conductor; short-interval law and no gaps `≫ √X log X`; second moment and positive support density `X/(log X)²`.
- Open queue: odd-multiplier blind family (doubly exponential upper residue reading?); upper bound on support
  (`≲ X/log X`?); local law near the top of the box; bands at the top; transport across prime steps; no-pole critical
  conductor below Beckner's constant.

## Log
- 2026-11-07 — created; contributions 1–5 formalized.
