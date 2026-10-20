# SRT explicit-lag loop (goal: 100 significant contributions toward `P_v ≥ 0` for `v ≥ V`)

- **ID:** srt-explicit-lag-1020
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean) per contribution; CONJECTURE for open items
- **Source:** formal/GaloisForLFunctions/SquareRootThreshold/README.md (research topics 1, 2, 4)
- **Statement:** For `ζ` and one generic width, prove `P_v ≥ 0` for all `v ≥ V` with explicit `V`,
  knowing that every crystal and every finite off-line set has a first negative lag.

## Goal
100 contributions, each meeting one of: (1) explicit unconditional `V`; (2) visibility at
`ζ`-density for a non-attained top with controlled lag; (3) off-diagonal prime pairs at `λ > 1`
with the consequence for `P_v`; (4) exact aperture/height/length tradeoff with the strongest
unconditional estimate; (5) the proof says what replaces the attainment premise of grids.
Not counted: nonselective positivity apertures, invisibility without witness, pair-correlation
restatements.

## Coordination
Other agents work in `SquareRootThreshold/` (window prime polynomial, Stieltjes, zero-count
remainder, ground-energy bridges). Check `ls SquareRootThreshold/` before naming a module. My lane:
effective (finite-window) visibility of the lag family, records, non-attained tops, grids.

## Conjecture queue
1. Finite Laplace windows: `P_v ≥ 0` on `[0, V]` bounds the Laplace pole of every off-line zero
   by the potential of the others (effective Landau inequality; record-potential law).
2. Non-attained tops (chains) seen by the continuum lag family at an explicit lag.
3. `ζ`: companion law at the Legendre record from finite lag positivity, with the corpus
   zero-free region, local count and 6/5 density.
4. Grids: z-transform (Pringsheim) version; the attainment premise replaced by a non-aliasing
   condition at the record.
5. Clusters: Toeplitz/positive-definite version of the Laplace window in the height variable.

## Contribution ledger (append-only)
