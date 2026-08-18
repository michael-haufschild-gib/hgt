# Prime-arch directed passive parity no-go (2026-08-18)

New Lean module: `formal/GaloisForLFunctions/RHTower/PrimeArchDirectedPassiveParityNoGo.lean`.

At `z = I/4`, completed prime–Gamma response has real part zero by centered negative-conjugation symmetry. Canonical directed prime-log finite KMS responses converge to a limit with strictly negative real part. Canonical one-sided Gamma-sewn Stokes truncations are passive at every finite stage but converge to a response with strictly positive real part. Thus neither directed family can converge to completed source.

Formal positive survivor:
- canonical reflected Gamma-sewn finite responses;
- finite passivity at every upper-half-plane point;
- exact oddness at every finite stage;
- cofinal finite-sum pointwise convergence throughout upper half-plane to countable reflected Stokes response.

Missing open core: identify reflected Stokes response/compact Markov germ with continued completed prime–Gamma one-Cauchy response. Existing `GammaSewnMobiusApertureStokesReflectedCompactCarrier.lean` explicitly names this missing germ/moment equality.

Targeted `lake env lean` and `lake build GaloisForLFunctions.RHTower.PrimeArchDirectedPassiveParityNoGo` pass. Axiom audit for eight public capstones: only `propext`, `Classical.choice`, `Quot.sound`. Global lint failed because of unrelated concurrent proof debt in `HTGeometry/MilnorFiltrationReduction.lean` and unrelated unreachable modules. Module is wired into `RHTower.lean`.
