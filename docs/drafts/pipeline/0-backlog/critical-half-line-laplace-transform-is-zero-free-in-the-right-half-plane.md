# The critical half-line Laplace transform is zero-free in the right half-plane

- **Stage:** 0-backlog
- **Type:** CONJECTURE
- **Target:** B104; complex factorization of the actual critical-state line.
- **Statement:** Every actual critical half-line state F at a finite global window threshold has `∫ F(u) exp(zu) du ≠ 0` whenever `Re z>0`.
- **Status:** Unproved. The positive-real-axis case and uniqueness are being formalized separately.

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
- `HTGeometry/WeightedCausalExponentialReflection`: verified real-rate weighted norm defect.
- `HTGeometry/CausalExponentialLaplaceReflection`: verified two-sided kernel representation and resonance-inclusive moment laws.
- Pending real-state input: `TheCriticalHalfLineStateHasNoPositiveLaplaceZero`.

Missing: modulated resolvent laws; preservation of the conjugate zero after
the first reflection; real representative of the composed reflection;
actual-domain closure and exact paired pole-product identity.

At `Re z=1/2` the pole-weighted kernel has no exponential decay. The real
resonance shortcut does not apply to a nonreal z; the pole law must pass
through this case by continuity of the actual weighted Laplace moments.

Zero-freeness alone is not an outer-factor theorem and does not establish
the arithmetic polar charge.
