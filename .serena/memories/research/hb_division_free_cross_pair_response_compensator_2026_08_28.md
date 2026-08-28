# HB division-free cross-pair response compensator (HC19)

Formalized 2026-08-28 in `formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMCrossPairResponseCompensator.lean`, wired into `formal/GaloisForLFunctions/RHTower.lean`.

Let `F_n(q)` be literal unit unsquared BM source amplitude times complementary exponent and define `K_n(q)=(2q-1)F_n(reflect q)`. Corrected charge factors as `H_n(q)=(2q-1)F_n(q)F_n(reflect q)`. FE involution makes `H_n` reflection-odd without division, so corrected reflection current vanishes for every Xi copy unconditionally. `K_n` and `H_n` vanish exactly on critical wall. At every tilted Xi copy, `H_n` is nonzero while corrected current is zero and HC18 canonical optical power is strictly positive.

This kills response regularity/division-freeness alone as HB closure. Remaining gate must enforce/derive source independence, reflection locality, or literal left-QNM/action incidence. Next conjecture: exact fixed source-independent scalar response classification—zero correction is blind; every nonzero fixed correction should make universal stationarity equivalent RH.

Audit: direct Lean passed; target `lake build GaloisForLFunctions.RHTower.ThetaCuspHawkingBMCrossPairResponseCompensator` passed (11913 jobs); seven endpoints use only `[propext, Classical.choice, Quot.sound]`; forbidden/diff clean; global lint only unrelated reachability failures. Cards: `docs/drafts/pipeline/3-formalized/hb-division-free-cross-pair-response-compensator.md`, `docs/drafts/pipeline/5-failed/hb-response-regularity-alone-no-go.md`.