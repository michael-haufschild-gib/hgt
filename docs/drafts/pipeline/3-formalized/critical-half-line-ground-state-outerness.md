# Causal translations of the critical half-line state are dense

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Target:** B104; causal cyclicity of the actual critical state.
- **Statement:** RH holds, or an actual critical half-line ground state, reflected to the positive ray, generates all complex half-line L² by causal translations.

## Proof

The actual state's bounded Cayley Laplace multiplier is [outer](critical-half-line-laplace-outerness.md). Let `U` be the unitary from disk Hardy space to half-line L² obtained by matching normalized Laplace features with Szegő kernels. Laplace uniqueness proves totality, and its exact evaluation formula is

`hardyFun(U⁻¹f)(cayleyRight w) = (w+1) ℒf(w)/√2`.

Causal translations `T_h` form a strongly continuous isometric semigroup. Their exponential average `Vf=∫₀∞ exp(-t)T_t f dt` has Laplace multiplier `(1+w)⁻¹` and preserves every closed translation-invariant subspace. Consequently, for the disk shift `S`,

`U⁻¹f-SU⁻¹f = 2 U⁻¹Vf = √2 hardyOf(ℒf∘diskToRight)`.

If a closed causal-invariant subspace contains `f`, its inverse image under `U` is shift-invariant and contains the Hardy vector of the literal Laplace multiplier. Outerness makes this inverse image the whole Hardy space. Apply this to the closed span of causal translates of the actual reflected critical state; its L² representative has the same literal Laplace transform.

## Lean audit

Application: `ArithmeticHodgeTheoryOfDegenerations/CausalReflection/TheCriticalHalfLineStateIsCyclic.lean`.

- `criticalHalfLineGroundState_causalCyclicSubspace_eq_top`
- `riemannHypothesis_or_exists_causalCyclic_criticalHalfLineGroundState`

Reusable transport: `HTGeometry/HardyBoundary/DiskHalfLineCayley.lean`, `HalfLineShiftLaplace.lean`, `HalfLineIntegratedShift.lean`, and `HalfLineCausalCyclicity.lean`; main theorem `causalCyclicSubspace_eq_top_of_outerLaplace`.

Plain `lake --old env lean` source audits passed. The unconditional theorem's transitive axioms are exactly `propext`, `Classical.choice`, and `Quot.sound`. All modules are wired into programme umbrellas.

Cyclicity concerns unweighted L². The polar source is verified only in the dual of the exponential norm; this result does not decide polar pairing. B4's positive finite-window margins also remain unproved.
