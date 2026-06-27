# Formal/Bottcher

- Aggregator: `formal/GaloisForLFunctions/Bottcher.lean` imports the Böttcher modules.
- Status log: `formal/GaloisForLFunctions/Bottcher/STATUS.md`; use it to locate declared gaps, but verify current Lean state directly.
- Brolin/Riesz stack: public aggregator `Bottcher/Brolin.lean`; implementation chapters live in `Bottcher/Brolin/*.lean`. Add new Brolin work as a chapter module, not by rebuilding a monolith.
- Potential theory starts in `Bottcher/LogPotential.lean`, `Bottcher/Capacity.lean`, `Bottcher/EnergyVariation.lean`; many analytic facts are represented as explicit predicates/hypotheses because mathlib lacks logarithmic capacity/equilibrium/Riesz measure APIs.
- Dynamical Green function infrastructure is in `Bottcher/GreenFunction.lean`, `Bottcher/BottcherCoord.lean`, `Bottcher/GreenContinuity.lean`, `Bottcher/GreenUnique.lean`, and `Bottcher/GreenLogDeriv.lean`.
- Period and monodromy measure-adjacent files: `Bottcher/Period.lean`, `Bottcher/MonodromyMultiplier.lean`, `Bottcher/Winding.lean`.
