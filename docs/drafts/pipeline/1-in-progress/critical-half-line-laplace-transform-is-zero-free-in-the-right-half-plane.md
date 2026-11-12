# The critical half-line Laplace transform is zero-free in the right half-plane

- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Target:** B104; complex factorization of the actual critical-state line.
- **Statement:** Every actual critical half-line state F at a finite global window threshold has `∫ F(u) exp(zu) du ≠ 0` whenever `Re z>0`.
- **Status:** Unproved. Positive-real-axis nonvanishing and uniqueness up to sign are verified. Complex-rate support, weighted energy and the resonance-inclusive complex resolvent moment law are verified. The paired state theorem remains unchecked.

## Proposed connection

Modulation conjugates the real causal resolvent into the resolvent of a
complex exponential. At a nonreal Laplace zero, reflect at that zero and
its conjugate. Both factors preserve negative-half-line support; their
composition should have a real representative, unchanged Fourier modulus
and unchanged opposite pole-moment product. Each factor has a positive
weighted norm defect because `Re z>0`.

Endpoint nonnegativity would force both resolvents to vanish, contradicting
the state's unit norm. This would exclude complex zeros without assuming
an outer factorization or regularity of the actual state.

## Corpus inputs and missing work

- `RHTower.fourier_exp_mul` in `SoninPacketFourierModulation`: literal modulation/translation identity.
- `ArithmeticHodgeTheoryOfDegenerations/CausalReflection/WeightedCausalExponentialReflection`: verified real-rate weighted norm defect.
- `ArithmeticHodgeTheoryOfDegenerations/CausalReflection/CausalExponentialLaplaceReflection`: verified two-sided kernel representation and resonance-inclusive moment laws.
- Verified real-state input: `TheCriticalHalfLineStateHasNoPositiveLaplaceZero`.

Verified:

- `ArithmeticHodgeTheoryOfDegenerations/CausalReflection/NegativeHalfLineLaplaceContinuity`: actual L¹ admission and continuity on the closed right half-plane.
- `ArithmeticHodgeTheoryOfDegenerations/CausalReflection/ModulatedCausalExponentialReflection`: literal measurability, modulation, L¹/L² closure and resolvent conjugacy.
- `ArithmeticHodgeTheoryOfDegenerations/CausalReflection/ModulatedCausalReflectionEnergy`: unweighted/weighted L² closure, exact norm defect, Fourier modulus preservation and resolvent injectivity.
- `ArithmeticHodgeTheoryOfDegenerations/CausalReflection/ModulatedCausalLaplaceReflection`: complex rate and support preservation at one complex Laplace zero.
- `ArithmeticHodgeTheoryOfDegenerations/CausalReflection/ComplexCausalLaplaceWeight`: complex kernel admission, exact kernel mass and stable-side moment law.
- `ArithmeticHodgeTheoryOfDegenerations/CausalReflection/ComplexCausalLaplaceDuality`: lower/upper Laplace tails and the anti-causal representation at a complex zero.
- `ArithmeticHodgeTheoryOfDegenerations/CausalReflection/ComplexCausalLaplaceMoments`: opposite-side complex resolvent moments.
- `ArithmeticHodgeTheoryOfDegenerations/CausalReflection/ComplexCausalLaplaceBoundary`: continuity across neutral decay and the unrestricted admitted moment law.
- `ArithmeticHodgeTheoryOfDegenerations/CausalReflection/ModulatedCausalReflectionCommutation`: Fourier multipliers and almost-everywhere commutation.
- `ArithmeticHodgeTheoryOfDegenerations/CausalReflection/PairedCausalReflectionIsReal`: conjugate kernels, commuting conjugate reflections and the actual real representative.
- `ArithmeticHodgeTheoryOfDegenerations/CausalReflection/ComplexHalfLinePoleDomain`: both half-pole moments from the actual weighted square domain.
- `ArithmeticHodgeTheoryOfDegenerations/CausalReflection/ModulatedCausalReflectionMoments`: linear reflection law, preservation of the conjugate zero and paired half-line support.
- `ArithmeticHodgeTheoryOfDegenerations/CausalReflection/PairedCausalReflectionPreservesPoleProduct`: the paired quadratic Laplace factor and reciprocal opposite real moments.
- `ArithmeticHodgeTheoryOfDegenerations/CausalReflection/ThePairedReflectionPreservesTheActualDomain`: all six actual-domain fields, including Gamma integrability.
- `ArithmeticHodgeTheoryOfDegenerations/CausalReflection/ThePairedReflectionPreservesArithmeticEnergy`: all translated correlations, the prime sum and the real pole term.
- `ArithmeticHodgeTheoryOfDegenerations/CausalReflection/ThePairedReflectionHasPositiveEnergyDefect`: the telescoped physical norm defect and exact full-form loss.

Written, unchecked:

- `ArithmeticHodgeTheoryOfDegenerations/CausalReflection/TheCriticalHalfLineStateHasNoRightHalfPlaneLaplaceZero`: zero-energy vanishing, actual-state nonvanishing and the unconditional RH dichotomy.

The remaining chain is written but unverified. No complex-state nonvanishing
claim is established until its final leaf passes Lean.

At `Re z=1/2` the pole-weighted kernel has no exponential decay. The real
resonance shortcut does not apply to a nonreal z; the pole law must pass
through this case by continuity of the actual weighted Laplace moments.
At the positive half-pole, negative-half-line support bounds the Laplace
weights by one; actual L¹ integrability supplies the required domination.

Zero-freeness alone is not an outer-factor theorem and does not establish
the arithmetic polar charge.
