# Critical half-line states have causal logarithmic coordinates

- **Stage:** 0-backlog
- **Type:** CONJECTURE
- **Target:** B104; establish the form domain of the actual critical state.
- **Statement:** Every `IsCriticalHalfLineGroundState W₀ F` has absolutely
  integrable full Gamma energy. The L² class of `t ↦ F(-t)` belongs to
  `HasLogarithmicEnergy`, hence to the range of `logarithmicCausalOperator`.
- **Status:** Unproved. No polar-charge or weak Euler equation claimed.

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

The lower bound `log(2+|r|)≤gammaBracket(r)+10+log 4`, together with
Plancherel, should then pay the actual logarithmic graph norm.
Reflection matches the positive-half-line support and the Fourier sign.
`hasLogarithmicEnergy_iff_mem_range` supplies the causal coordinates once
that norm is finite.

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
