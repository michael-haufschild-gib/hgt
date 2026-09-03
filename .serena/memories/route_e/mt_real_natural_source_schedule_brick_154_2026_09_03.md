# MT actual-source real-to-natural Watt windows — Brick 154 (2026-09-03)

- Added `formal/GaloisForLFunctions/RHTower/Sieve/MatomakiTeravainenRealNaturalSourceSchedule.lean`.
- `mtGeometricLevel_unitFloor_conditions` derives `1 <= delta*M <= floor M` on every rooted
  geometric level from positive half-width and the literal lower-cutoff progress inequality.
- `eventually_mtPaperWidth_succ_geometricLevel_unitFloor_window` discharges those inputs from
  `mtPaperWidth (A+1) X` for every `A`, uniformly in all levels.
- `eventually_mtPaperWidth_succ_geometricUnit_eq_wattBlock` gives the exact real-unit Perron /
  natural-Watt identity and `floor M < floor((1+delta)M) <= 2 floor M` on the source schedule.
- Direct check and targeted leaf build passed (`11149/11149`); umbrella import added without
  building umbrella.
- Focused axiom audit: all three declarations use only `propext`, `Classical.choice`, `Quot.sound`.
- Remaining MT frontier: route complete Proposition-2.2 pieces through Type-I/Type-II receivers;
  residual Lemma 3.5(ii) still needs collective signed cross-modulus strength, then Perron and
  all-interval Theorem 1.2 assembly.
