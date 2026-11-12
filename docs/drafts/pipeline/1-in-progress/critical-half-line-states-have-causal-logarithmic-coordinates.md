# Critical half-line states have causal logarithmic coordinates

- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Target:** B104; establish the form domain of the actual critical state.
- **Statement:** Every `IsCriticalHalfLineGroundState W₀ F` has absolutely
  integrable full Gamma energy. The L² class of `t ↦ F(-t)` belongs to
  `HasLogarithmicEnergy`, hence to the range of `logarithmicCausalOperator`.
- **Status:** Full Gamma, logarithmic energy and causal-coordinate proofs written in Lean; checking after coercion fixes. No polar-charge or weak Euler equation claimed.

The ground-state definition bounds `lowGammaForm F T` uniformly for all
large cutoffs. Put `C=10+log 4`. The proved global inequality
`log(2+|r|)≤gammaBracket(r)+C` makes
`|paperFT(F)(r)|² (gammaBracket(r)+C)` nonnegative and continuous.
`RHTower.KernelStrip.integrable_norm_sq_paperFT` applies to the state's
actual L¹ and L² data; its full Fourier mass bounds the added constant
term on every cutoff. Thus the original signed bound gives uniformly
bounded positive window integrals. Apply
`HTGeometry.integrable_of_bounded_windows`, then subtract the integrable
constant term to obtain full Gamma integrability. No smoothness or compact
support of F is required.

The exact reference symbol is `Ψ(r)=1+(1/2)log(1+r²)`, bounded by
`1+log(2+|r|)≤1+gammaBracket(r)+C`. Thus Gamma integrability and Plancherel
should pay its full graph norm. For `g(t)=F(-t)`, the Fourier convention is
`𝓕g(ξ)=paperFT(F)(2πξ)`; the existing classical/L² Fourier bridge transfers
this identity to the actual L² class. Reflection gives positive-half-line
support. `hasLogarithmicEnergy_iff_mem_range` then supplies causal coordinates.

Corpus inputs:
- `ArithmeticHodgeTheoryOfDegenerations/HalfLinePolarThresholdAndGroundStateOrthogonality`:
  actual ground-state definition and unconditional existence dichotomy.
- `CriticalArithmeticCorrelationTheory/BoundedWeilEnergyUpgradesL1LimitsToStrongLimits`:
  `lowGammaForm` and continuity of the L¹ Fourier transform.
- `RHTower/WeilPaperSpectralCoercivity`: the logarithmic Gamma lower bound.
- `CanonicalSystemOfTheWindowTower/TheHalfLineLogarithmicFormHasItsActualInverse`:
  actual finite-energy domain and its causal range characterization.

The remaining B104 obstacle is the full variational equation and its
relation to `exp(-u/2) terminalPolarKernel u`. Causal coordinates alone
give no sign for the state or its polar pairing.

Lean candidate: `ArithmeticHodgeTheoryOfDegenerations/TheCriticalHalfLineStateHasCausalCoordinates.lean`,
with `integrable_gamma_of_criticalHalfLineGroundState`,
`integrable_logarithmic_energy_of_criticalHalfLineGroundState`, and
`exists_causal_coordinates_of_criticalHalfLineGroundState`.
The existing ground-state dependency now has its required olean.

Variational continuation: under the remaining B104 equality,
`polarPaymentCriticalThreshold_eq_iInf_windowThreshold_iff_halfLinePolarPositive`
gives positivity of the charged truncated form for every smaller ratio.
`archForm` is already the literal full Gamma integral. The tail is nonnegative
above `exp factorialSpanGammaOffset`, by `gammaBracket_ge_log_of_le_abs`.
Thus each truncation is bounded by the full form for every integrable state.
`TheCriticalHalfLineStateHasZeroFullEnergy.lean` writes this continuation:
monotone exhaustion gives the full Gamma limit; nonnegative tails compare
truncations with the full form; positivity below W₀ and continuity in the
ratio give nonnegative endpoint energy; the state's upper bound forces equality.
These follow-on theorems are unchecked. This does not yet prove the weak equation or polar charge.

For admissible variations, `summable_primePairTerm` supplies the full mixed
prime series. `ThePrimeFormIsQuadraticOnTheWeightedDomain.lean` writes its
bilinearity and exact quadratic expansion on measurable weighted profiles.
This support module is unchecked; the full Gamma polarization and weak equation remain open.
