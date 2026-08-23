# Theta-cusp Hawking–Krein flux endpoint (2026-08-23)

## Goal
Develop Hawking radiation as actual mathematical backbone for theta-cusp RH route, not metaphor.

## New formal endpoint
Extended `formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBogoliubovBornEndpoint.lean`.

New exact chain:
1. Nonkinematic dark frequency `z` of actual moving-mirror Born amplitude `B_theta(z) = -i z XiC(z)/(4π)` gives `XiC z = 0`.
2. It produces a nonzero trapped theta source mode `thetaCuspHawkingKreinMode d` of fixed compact source inverse with eigenvalue `-z⁻¹`.
3. Universal singular-metric Green/Krein law:
   `⟨C g,g⟩ = 2 Im(mu) ⟨G g,g⟩`
   for every `thetaKernelOperator` eigenmode `B g = mu g`.
4. Direct physical-frequency evaluation:
   `thetaCuspHawkingKreinFlux d = 2 * thetaSource.mass * Im(z) * thetaCuspHawkingKreinEnergy d`.
5. Energy is strictly positive, hence flux neutrality iff `Im z = 0`.
6. Closed endpoint:
   `riemannHypothesis_iff_thetaCuspHawkingKreinStable`.

This uses actual Hawking structures: unsquared Bogoliubov pair-production amplitude, complex-frequency trapped mode, positive/negative-norm/Krein mode mechanics, oriented horizon flux. Primary physics comparison: Corley–Jacobson black-hole laser (arXiv:hep-th/9806203); Coutant–Parentani mode analysis (arXiv:0912.2755); Finazzi–Parentani BdG treatment (arXiv:1005.4024).

## Hostile audit
- Local/reflection-symmetric flux sums cancel unconditionally; cannot prove RH.
- Particle-number/intensity or squaring loses phase/orientation.
- Passivity/minimum-phase inference is invalid generally.
- New endpoint is exact and route-specific but still RH-equivalent, not a proof.
- Missing producer isolated: unconditional same-mode oriented horizon neutrality/no-lasing before reflection pairing or positive squaring. Likely requires source-nonlocal causal law or quantitative no-escape theorem for singular metric.

## Verification
- `lake env lean GaloisForLFunctions/RHTower/ThetaCuspHawkingBogoliubovBornEndpoint.lean` passed cleanly.
- Scratch `#print axioms` for universal balance, explicit flux, capstone: only `propext`, `Classical.choice`, `Quot.sound`.
- `git diff --check` passed.
- No `sorry`, `admit`, `axiom`, `opaque`, `unsafe` in module.
- Global `scripts/formal_tools.py lint` failed only on unrelated dirty umbrella reachability: `GaloisForLFunctions.RHTower.Sieve.ScaledTwoRangeWindow`.

## Next high-value research
Attack producer, not endpoint: prove source-derived absence of oriented gain/loss for each trapped mode. Candidate higher principle: finite/coercive causal approximants plus quantitative no-escape through singular metric; must avoid reflection pairing and divisor-indexed assumptions.
