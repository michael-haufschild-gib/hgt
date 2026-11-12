# Critical half-line states: causal coordinates and the weak equation

- **Stage:** 1-in-progress
- **Target:** B104, actual ground-state variational law.
- **Verified:** Every `IsCriticalHalfLineGroundState W₀ F` has absolutely integrable full Gamma energy. Its reflected L² class has finite logarithmic energy and lies in the range of the actual causal convolution.
- **Candidate:** In the remaining finite threshold-equality case, the actual state has zero full energy and annihilates the full mixed form against every finite-energy half-line test.
- **Open:** Identification with the polar source; exclusion or construction of a polar-orthogonal critical state. No additional contribution counted.

## Domain argument

Put `C=10+log 4`. The global Gamma bound makes
`|F̂(r)|²(Γ(r)+C)` nonnegative. Its integral over every bounded frequency
window is bounded by the state's signed truncation bound plus `C‖F̂‖₂²`.
The latter is finite by the actual L¹/L² Plancherel theorem.
`integrable_of_bounded_windows` gives full integrability; subtract the
constant term to obtain absolute Gamma integrability.

The exact positive symbol satisfies
`Ψ(r)=1+(1/2)log(1+r²)≤Γ(r)+11+log 4`.
Thus the actual state has finite logarithmic energy. For `g(t)=F(-t)`,
`𝓕g(ξ)=F̂(2πξ)`. The classical/L² Fourier bridge and
`hasLogarithmicEnergy_iff_mem_range` give causal coordinates.

## Variational argument

Gamma cutoffs exhaust the full integral. Beyond `exp G₀`, the omitted
Gamma tail is nonnegative. The defining state inequalities therefore give
nonpositive full energy.

Threshold equality gives polar positivity at every smaller positive ratio.
For any normalized admissible profile, apply it with a nonzero auxiliary
charge, then let that charge tend to zero. This yields nonnegative full
energy even for a zero-norm profile. Continuity in the ratio gives endpoint
nonnegativity; scalar normalization extends it to the whole domain.
The critical state's full energy is therefore zero. This normalized positivity
and zero-energy passage is verified in Lean; unrestricted normalization and
quadratic variation remain under verification.

Mixed prime correlations are absolutely summable in `WeightedTwo`.
Mixed Gamma energy is integrable because
`2|Re(z conj w)|≤|z|²+|w|²`. The pole and exponential terms have integrable
mixed products. These facts give domain closure and the exact identity
`Q(F+cG)=Q(F)+2cB(F,G)+c²Q(G)`.
Endpoint nonnegativity and `Q(F)=0` force `B(F,G)=0` for every domain test.
No smoothness or compact-support assumption is imposed on the actual state.

## Lean status

| Module | Status |
| --- | --- |
| AHT/`TheCriticalHalfLineStateHasCausalCoordinates` | Verified; imported by umbrella |
| AHT/`TheCriticalHalfLineStateHasZeroFullEnergy` | Verified; imported by umbrella |
| CACT/`ThePrimeFormIsQuadraticOnTheWeightedDomain` | Verified; imported by umbrella |
| CACT/`TheFullGammaFormIsQuadraticOnItsIntegrableDomain` | Checking |
| AHT/`TheCriticalHalfLineFormHasItsActualDomain` | Written, unchecked |
| AHT/`TheCriticalHalfLineStateSatisfiesTheWeakEquation` | Written, unchecked |

The polar source is `exp(-u/2) terminalPolarKernel u` on the negative
half-line. The weak equation does not yet identify this functional with
a boundary trace or prove that it is nonzero. Positivity of the state is
unavailable: the existing sign/Markov obstruction remains in force.
