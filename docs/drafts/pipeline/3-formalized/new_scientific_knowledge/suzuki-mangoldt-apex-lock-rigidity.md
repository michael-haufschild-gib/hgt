# Suzuki Mangoldt apex-lock rigidity — Lean formalization

- **Stage:** 3 — formalized in Lean 4
- **Module:** `GaloisForLFunctions.RHTower.SuzukiMangoldtApexLock`
- **Imported by:** `GaloisForLFunctions.RHTower.RiemannHypothesisSOTA2026`
- **Status:** `[LEAN-PROVED] [AXIOM-CLEAN] [NOVELTY UNVERIFIED]`
- **Paper proof:**
  `../../2-fully-proven/new_scientific_knowledge/suzuki-mangoldt-apex-lock-rigidity.md`

## Formal theorem surface

Channel geometry:

- `suzukiRectangularFixedArchChannel`
- `suzukiRectangularMovingArchChannel`
- `suzukiRectangularMovingApex`
- `suzukiRectangularPositiveArchSampleChannel_eq_fixed_add_moving`
- `suzukiRectangularFixedArchChannel_lt_zeroLag`
- `suzukiRectangularMovingArchChannel_at_apex`
- `suzukiRectangularMovingArchChannel_lt_apex`
- `suzukiRectangularPositiveArchSampleChannel_at_movingApex`
- `suzukiRectangularPositiveArchSampleChannel_lt_movingApex`
- `suzukiRectangularPositiveArchSampleChannel_apex_le_iff`

Source lock and no-go:

- `suzukiMangoldtApexAperture`
- `suzukiMangoldtApex_node_eq_apex`
- `suzukiMangoldtApex_unique_positiveLag_maximizer`
- `volume_suzukiMangoldtApex_pointwiseDominatingSet_eq_zero`
- `mangoldtLogHaarAtomMass_pos_of_vonMangoldt_pos`
- `no_suzukiMangoldtApex_positiveVolume_pointwiseDominatingCell`
- `no_suzukiMangoldtApex_cell_at_two_pow`

## Exact formal boundary

The module proves unconditional impossibility only for per-atom pointwise-dominating cells.  It
does not rule out aggregate block transport: low-valued flank atoms can in principle provide
surplus for one apex atom before capacity is enforced.

The unique-max theorem is a positive source rigidity law.  At width `log 2` and aperture
`log(2n)/2`, every node `2log n`, `n>=4`, is locked to the unique positive-lag Suzuki apex.  At
prime powers this null superlevel carries positive Mangoldt mass.

## Verification

- Direct source check:
  `lake env lean GaloisForLFunctions/RHTower/SuzukiMangoldtApexLock.lean` — passed.
- Final umbrella audit:
  `lake build GaloisForLFunctions.RHTower.RiemannHypothesisSOTA2026` — passed `9514/9514`.
- Nine capstone axiom surfaces contain only `propext`, `Classical.choice`, and `Quot.sound`.
- Forbidden declaration scan is clean.
- Repository lint reaches this module; its remaining 23 failures are unrelated shared-tree
  unreachable modules.
