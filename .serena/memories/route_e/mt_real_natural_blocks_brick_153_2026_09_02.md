# Brick 153 — lossless real-to-natural Type-I blocks

Added `formal/GaloisForLFunctions/RHTower/Sieve/MatomakiTeravainenRealNaturalBlocks.lean`.

New exact infrastructure:
- `coeff_eq_two_natural_dyadic_blocks`: any sequence supported on real `(M,2M]`, `M≥1`, splits coefficientwise into the natural `(floor M,2 floor M]` block plus the rounding tail `(2 floor M,4 floor M]`.
- `perronPoly_mtRealDyadicSource_eq_two_wattBlocks`: exact Perron-line identity for the Proposition-2.2 real dyadic coefficient factor as two literal `mtWattCoefficientBlock`s.
- `mtRealUnitIntervalAF_eq_floor` and `perronPoly_mtRealUnitInterval_eq_mtWattUnitBlock`: real unit interval `(L,U]` equals natural `(floor L,floor U]`, including exact Perron polynomial.
- `mtRealUnitFloor_window`: `1 ≤ delta*M ≤ floor M` implies `floor M < floor((1+delta)M) ≤ 2 floor M`, exactly the admission condition of the natural unit-block moments.

Direct source check and targeted build `lake build GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenRealNaturalBlocks` passed (`11124/11124`). Five theorems audit with `[propext, Classical.choice, Quot.sound]`. Leaf imported by `formal/GaloisForLFunctions/RHTower.lean`; umbrella not built. Remaining source task: derive scalar window conditions from actual geometric schedule and apply Type-I/II receivers to every Proposition-2.2 piece.