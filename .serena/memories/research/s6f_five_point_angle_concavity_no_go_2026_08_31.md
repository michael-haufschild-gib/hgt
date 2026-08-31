# S6F five-point angle-concavity no-go — 2026-08-31

## Result

Killed the proof arrow

```text
theta reflected correlation-angle concavity
→ five-point reflection-even Toeplitz PSD
→ confluent native rank-three D1 nonnegativity.
```

The closed Lean capstone `exists_strictMono_concave_angle_with_nonPSD_toeplitzFiveEvenBlock`
constructs a normalized, globally concave, strictly increasing angle mapping `[0,4]` into
`[0,π/2]` whose cosine five-point reflection-even block is not PSD.

## Exact mechanism and survivor

For the even block

```text
[[1, 2c₁, 2c₂],
 [2c₁, 2(1+c₂), 2(c₁+c₃)],
 [2c₂, 2(c₁+c₃), 2(1+c₄)]],
```

the saturated head relation `c₂ = 2c₁² - 1` gives

```text
det = -4(c₁+c₃-2c₁c₂)².
```

Thus PSD forces exact null coupling `c₁+c₃=2c₁c₂`; formal theorem
`toeplitzFiveEvenBlock_boundary_coupling_eq_zero_of_posSemidef`. This is strongest positive
survivor. Future finite-section work must derive this three-lag coupling, or a strict-interior
replacement, from theta source dynamics. Stronger scalar concavity alone is not viable.

## Files

- Lean: `formal/GaloisForLFunctions/RHTower/ThetaCuspReflectedFivePointEvenAngleConcavityNoGo.lean`
- Umbrella: `formal/GaloisForLFunctions/RHTower.lean`
- Failed-route card: `docs/drafts/pipeline/5-failed/s6f-five-point-even-angle-concavity.md`
- Frontier map was not edited.

## Verification

- `lake env lean GaloisForLFunctions/RHTower/ThetaCuspReflectedFivePointEvenAngleConcavityNoGo.lean` — PASS
- `lake env lean /tmp/S6FFivePointAngleAxioms.lean` — only `propext`, `Classical.choice`, `Quot.sound`
- `lake build GaloisForLFunctions.RHTower.ThetaCuspReflectedFivePointEvenAngleConcavityNoGo` — PASS
- Global `scripts/formal_tools.py lint` — module clean/reachable; gate remains red only for unrelated pre-existing unreachable modules.

## Novelty audit

Corpus search found no predecessor before this module. Literature search through 2026-08-31 found
general Toeplitz/PSD completion and singular-face theory, but no statement of this specific
correlation-angle implication or counterexample. Planat--Solé arXiv:2608.19160 proves second-level
theta-kernel concavity and stops at necessary Laguerre--Turán consequences. Priority is provisional:
the source-specific no-go appears new, while the negative-square mechanism belongs to standard PSD
facial rigidity.
