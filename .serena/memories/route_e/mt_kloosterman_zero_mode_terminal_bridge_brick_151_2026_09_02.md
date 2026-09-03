# Route E MT E3 Brick 151 — zero-mode-exact terminal bridge

- Modified `formal/GaloisForLFunctions/RHTower/Sieve/KloostermanGlobalFrequencyParseval.lean`.
- Added exact zero orbit and erased Parseval identity: for `P = kloostermanGlobalPeriod Q`, `r = M % P`, `sum_(z != 0) normSq(GlobalTerminalOrbit z) = P*r - r^2`.
- Added `norm_kloostermanDistinctModulusTerminalGramQuadratic_sq_le_globalFrequencyCollisionEnergy_erase_zero`, retaining signed global collision cancellation and deleting the zero orbit charge exactly.
- Extended `formal/GaloisForLFunctions/RHTower/Sieve/KloostermanGlobalCollisionCentered.lean` with general and literal-Icc terminal Gram capstones composed with Brick 150's sharp `#Q + 1` centered collision receiver.
- Direct `lake env lean` checks passed for both changed files.
- Targeted leaf builds passed for `GaloisForLFunctions.RHTower.Sieve.KloostermanGlobalFrequencyParseval` and `GaloisForLFunctions.RHTower.Sieve.KloostermanGlobalCollisionCentered`; no umbrella build.
- Five new declarations audit with `[propext, Classical.choice, Quot.sound]` only.
- Programme doc updated with Brick 151.
- Remaining hard input: nonzero-frequency cross-modulus Kuznetsov/DI saving strong enough for Lemma 3.5(ii), then amplification and Theorem 1.2. No Stage-2 card moved.