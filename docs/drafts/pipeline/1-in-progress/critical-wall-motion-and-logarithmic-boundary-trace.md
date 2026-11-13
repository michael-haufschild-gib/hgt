# Critical wall motion and the logarithmic boundary trace

- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Target:** B104; identify a nonzero boundary readout of the actual critical state.
- **Status:** No proof or contribution claimed. Polar identification open.

## Corpus connection

The exact arithmetic translation law gives `E(T_hF-F)=a(exp(8h)-1)W(F,F)`, hence a strictly positive right derivative `8aW(F,F)` at zero. The weak equation removes the cross term.

`exists_causal_coordinates_of_criticalHalfLineGroundState` places the reflected actual state in the range of the logarithmic causal convolution. `logarithmicHalfLineGreenOperator_normalized_boundary_limit` gives a normalized trace `sqrt(log(1/x))·u(x)` for actual Green solutions with locally bounded L² forcing. These statements concern compatible logarithmic form geometry, but do not yet identify the critical state's forcing.

The exact decomposition `gammaHardyPhaseRate_eq_log_reference` isolates the logarithmic symbol from an integrable bounded convolution remainder. `SignedWindowCriticality.eq_zero_of_isWindowSolution` already excludes smooth compact-window extremals with exponential-polynomial forcing; it does not give this half-line state's trace or its magnitude.

## Question

Does a canonical Green representative have a normalized logarithmic boundary trace
`c=lim_{x↓0}sqrt(log(1/x))F(-x)` satisfying `c²=8a(R)W(F)` at every
confining minimum? The literal density `archLevyDensity(t)=exp(-t/2)/(1-exp(-2t))`
has leading term `1/(2t)`, consistent with this constant. The identity is a
conjecture; a positive answer would replace endpoint support by a nonzero
quantitative boundary invariant.

The statement must use a canonical representative or an essential trace. `IsCriticalHalfLineGroundState` assumes measurability and integral conditions, so null-set changes on the negative half-line can destroy a literal pointwise limit.

## Missing mathematical inputs

1. Express the actual critical weak equation as the logarithmic Green equation, with its literal arithmetic forcing.
2. Prove the required forcing regularity from the actual state; do not add it as a premise.
3. Relate normalized boundary trace to the first translation-energy increment, controlling all lower-order arithmetic and weighted terms.
4. Determine whether this readout is the polar source pairing or a distinct boundary channel. Existing L² cyclicity alone does not identify it.

Sources: `ArithmeticHodgeTheoryOfDegenerations/TheCriticalHalfLineStateHasCausalCoordinates.lean`, `CanonicalSystemOfTheWindowTower/TheHalfLineLogarithmicFormHasItsActualInverse.lean`, `CanonicalSystemOfTheWindowTower/TheHalfLineLogarithmicGreenSolutionsHaveBoundaryValues.lean`, and `CausalReflection/CriticalCausalEnergyTranslation.lean`.

## Intermediate regularity conjecture

The exact translation-energy law may give a quantitative Fourier tail:
`∫_{|ξ|≥T}|Fourier(F)(ξ)|²dξ≤C/(T log T)` for large `T`.
This would imply every fractional Sobolev order below `1/2`, beyond the
existing logarithmic form-domain statement. No endpoint trace follows from
this bound alone.

Proposed bridge: retain both the logarithmic Fourier weight and half the
exponential potential in the arithmetic absorption estimate. Apply it to
`F(·+h)-F`, whose full energy is `O(h)`. A low/high frequency split should
absorb the negative ordinary-mass term and give
`‖F(·+h)-F‖₂²≤Ch/log(1/h)`. Averaging the Fourier translation multiplier
over `0<h<1/T` then detects the entire frequency tail. The estimate and its
Sobolev consequences remain unproved in Lean.

The arbitrary-ratio weak equation suggests the same bound for every
confining minimizer: for `Δ_hF=F(·+h)-F`, it should give
`E_R(Δ_hF)-λ(R)‖Δ_hF‖₂²=a(R)(exp(8h)-1)W(F)`.
The extra ordinary-mass term can enter the same absorption estimate.
Source: `CausalReflection/ConfiningHalfLineWeakEquation.lean`.

`CausalReflection/ConfiningHalfLineTranslationEnergy.lean` contains unchecked
proofs of the shifted translation identity and absorption retaining the
Gamma form. No regularity theorem is verified yet.

`CausalReflection/HalfLineGammaContractions.lean` contains an unchecked
converse Lévy-domain proof and closure under zero-preserving real
contractions. Weighted barrier truncations require the additional
admissibility argument below.

## Exponential-barrier route

[Exponential barriers](../2-fully-proven/exponential-barriers-for-confining-minimizers.md)
has a paper argument for `|F(u)|≤Cβ exp(βu)` whenever `1/2<β<15/2`,
and hence all exponential square moments of order below `15`. Lean
formalization is in progress; the argument is not counted as a proof until
that audit passes.

In particular, `|F(u)|≤C exp(u)` on the negative half-line would bound the complete prime
forcing near the terminal endpoint, since its backward translates then
carry the summable weight `Λ(n)/n^(3/2)`.

The corpus connection is `TheCompletedWeilRieszVectorsAreBounded.lean`:
positive-level tests in inverse-Doob coordinates combine divergent
archimedean row mass with bounded cutoff readouts. For the half-line, the
candidate barrier is `exp(u)`, with tests `(F-t exp(u))₊` and both signs of
`F`. The forward prime row grows at most like `exp(-3u/2)` and should be
absorbed by the actual potential `a exp(-8u)`. Admissibility of these tests
and the complete weighted row inequality are open; the finite-aperture
Riesz theorem does not supply them.

For the barrier, the normalized prime row is
`Σ_{n<exp(-u)}Λ(n)√n + Σ_n Λ(n)/n^(3/2)`; the first term is bounded by
`6 exp(-3u/2)` using the existing Chebyshev bound. The cutoff Gamma
readout is bounded by its kernel's L² norm times `‖F‖₂`. Choosing its row
mass large should leave a coefficient dominating `exp(-u)+exp(-3u/2)`
after the prime row and eigenvalue are subtracted from `a exp(-8u)`.
This is the proposed positive-level comparison, not a verified theorem.

Even this bound would not make `exp(-8u)F` globally L², so localization
remains necessary. `TheLogarithmicCutoffCommutatorHasABoundedKernel.lean`
already bounds the literal commutator kernel by
`(Lip(χ)/2)exp(-|x-y|)` and proves an L² operator preserving essential
boundedness. Thus this commutator estimate need not be reproved. The
remaining bridge identifies the terminally localized actual weak equation,
including its prime and confining terms, with the existing Green inverse.
The boundary coefficient's magnitude and polar identification would still
remain open.

The exact normalization is
`Gamma=A_log+(archLogScalar-1)I-archLogConvolution`, with
`A_log` having symbol `1+(1/2)log(1+r²)`. For the reflected profile
`u(x)=F(-x)`, the proposed localized forcing is

`χ[(λ-a exp(8x)-archLogScalar+1)u+Prime(u)-Pole(u)+archLogConvolution(u)]
 +[A_log,χ]u`.

Choose `χ=1` near zero, supported below `log 2`. The outward prime shifts
then vanish on its support, while the inward shifts are bounded by the
summable barrier row. The other localized terms and the existing cutoff
commutator would be both `L²` and bounded. This identifies the precise
candidate Green forcing; transfer of the actual weak identity to the
closed logarithmic form is still unproved.

## Candidate wall-flux argument

Assuming the preceding regularity steps have been proved, put
`B_h=F·1_{[-h,0]}`. The weak equation and the jump-kernel cross term suggest
`E(B_h)/h→c²` at the critical ratio: the kernel `1/(2|u-v|)` pairs the
terminal trace with the adjacent logarithmic tail. The prime and polar
cross terms would be `o(h)` under the exponential barrier bound.

For `Q=E-λ‖·‖₂²`, admissibility of the collar gives the exact reduction
`Q(B_h)=-Q(F-B_h,B_h)`. The two profiles on the right have disjoint support.
Thus this argument needs a cross-kernel asymptotic, rather than an estimate
of the possibly rough internal jump energy from the trace alone.

The sharp wall floor applied to `F-B_h` would then give `c²≥8aW(F)`.
The same cross-kernel asymptotic predicts
`E(T_hF,B_h)/h→-c²`. Cauchy–Schwarz for the nonnegative critical form,
together with `E(T_hF-F)/h→8aW(F)`, would give the reverse inequality.
At a general minimum the same argument uses `E-λ‖·‖₂²`.
Admissibility of the sharp collar and both cross-kernel asymptotics remain
to be proved; no flux identity or nonzero trace is claimed.
