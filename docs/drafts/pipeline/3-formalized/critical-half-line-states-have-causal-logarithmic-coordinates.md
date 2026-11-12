# Critical half-line states: actual domain and weak equation

- **Stage:** 3-formalized
- **Target:** B104; actual ground-state variational law.
- **Statement:** At the finite global window threshold W, every actual critical half-line state F has absolutely integrable full Gamma energy, actual causal logarithmic coordinates, `Q_W(F)=0`, and `B_W(F,G)=0` for every finite-energy half-line test G. Polar-threshold equality is unnecessary.
- **Status:** Proved in Lean. The unconditional dichotomy supplies RH or an actual weak zero mode.
- **Open:** Nonvanishing of the arithmetic polar pairing. This domain/variation result is not counted separately toward the connection goal.

## Domain and positivity

The global Gamma bound makes `|F̂(r)|²(Γ(r)+10+log 4)` nonnegative.
The state's bounded Gamma truncations and actual L¹/L² Plancherel bound
its integrals on all bounded frequency windows. Full Gamma integrability
follows. The exact logarithmic symbol satisfies
`Ψ(r)=1+(1/2)log(1+r²)≤Γ(r)+11+log 4`, giving finite logarithmic energy.
The classical/L² Fourier bridge and the causal convolution range theorem
then produce actual causal coordinates for the reflected state.

Gamma cutoffs exhaust the full integral; beyond `exp G₀` the omitted tail
is nonnegative. The defining state inequalities give `Q_W(F)≤0`.

One-sided window approximation supplies smooth compact profiles H_k with
weighted convergence, `arch(H_k)≤arch(F)+C/(k+1)`, and
`I₈(H_k)≤exp(8/(k+1))I₈(F)`. Below the global window threshold their
pencils are nonnegative. Prime and pole convergence passes this inequality
to the full form. Scalar normalization removes the norm restriction;
continuity in the ratio gives endpoint nonnegativity on the whole domain.
Consequently every actual critical state has zero full energy.

## Genuine variations

Mixed prime correlations are absolutely summable in `WeightedTwo`.
Mixed Gamma energy is integrable by `2|Re(z conj w)|≤|z|²+|w|²`.
Pole moments and exponential mixed products are integrable. Thus the actual
domain is closed under real variations and
`Q_W(F+cG)=Q_W(F)+2cB_W(F,G)+c²Q_W(G)`.
Nonnegativity for every real c and `Q_W(F)=0` force `B_W(F,G)=0`.
No smoothness, compact support or sign condition is imposed on F.

## Lean

All modules verified and imported by their umbrellas:

- AHT/`TheCriticalHalfLineStateHasCausalCoordinates`.
- AHT/`TheCriticalHalfLineStateHasZeroFullEnergy`.
- CACT/`ThePrimeFormIsQuadraticOnTheWeightedDomain`.
- CACT/`TheFullGammaFormIsQuadraticOnItsIntegrableDomain`.
- AHT/`TheCriticalHalfLineFormHasItsActualDomain`.
- AHT/`TheWindowThresholdControlsTheFullHalfLineForm`.
- AHT/`TheCriticalHalfLineStateSatisfiesTheWeakEquation`.

Principal declarations: `criticalHalfLineFullEnergy_nonneg_at_windowThreshold`,
`criticalHalfLineFullEnergy_groundState_eq_zero`,
`criticalHalfLineMixedEnergy_groundState_eq_zero`, and
`riemannHypothesis_or_exists_weak_criticalHalfLineGroundState`.
The final weak-equation module passed `lake --old env lean`.

The arithmetic polar source is `exp(-u/2) terminalPolarKernel u` on the
negative half-line. The weak equation does not identify it with a boundary
trace or prove its pairing nonzero. The positive-ground-state/Markov
obstruction remains in force.
