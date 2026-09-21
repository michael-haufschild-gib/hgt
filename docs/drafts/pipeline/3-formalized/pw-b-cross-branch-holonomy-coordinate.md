# PW-B complementary Peierls / Borel-holonomy coordinate

- **ID:** pw-b-cross-branch-holonomy-coordinate
- **Stage:** 3-formalized
- **Type:** SIGNIFICANT PREMISE DISCHARGED
- **Source:** `docs/drafts/pipeline/1-in-progress/rh-current-frontier-map.md` · PW-B complementary cyclic-Peierls source

## Result

For `P=parameter₊+parameter₋=8q²−8q+6` and PW closed recoil holonomy `Hₖ`, Lean proves

`64Hₖ=P²−(16(2k+1)²+12)P+64(2k+1)⁴+32(2k+1)²+36`.

## Consequence for the whole route

The literal complementary source carries the complete reflection-even PW closed-history coordinate at every grade. Together with the full-circle CTP reflection-odd numerator, both required source/PW parity coordinates are fixed. Remaining hard premise: derive the cap/lift-defect transport which identifies its normalized odd magnitude with fixed-grade PW real imbalance.

## Formal evidence

- [ThetaCuspHawkingParikhWilczekCrossBranchHolonomyBridge.lean](/Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingParikhWilczekCrossBranchHolonomyBridge.lean) directly passes `lake env lean`.
- Scratch axiom audit reports only `propext`, `Classical.choice`, `Quot.sound`.
- Module is wired into `GaloisForLFunctions/RHTower.lean`; no umbrella build was run.
