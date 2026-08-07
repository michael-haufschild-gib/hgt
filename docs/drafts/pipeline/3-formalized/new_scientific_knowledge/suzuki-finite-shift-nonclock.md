# Suzuki finite-shift non-clock rigidity

- **ID:** `suzuki-finite-shift-nonclock`
- **Stage:** 3-formalized
- **Type:** THEOREM / ENDPOINT SINGULARITY / FOURIER-COMPLETE CARRIER RIGIDITY
- **Scientific status:** `[LEAN-PROVED] [UNCONDITIONAL] [NOVELTY UNVERIFIED] [NOT AN RH PROOF]`
- **Paper proof:**
  `../3-formalized/new_scientific_knowledge/suzuki/suzuki-boundary-log-nonclock-nonflat-tangent.md`
- **Lean module:**
  `formal/GaloisForLFunctions/RHTower/SuzukiFiniteShiftNonClock.lean`

## Formalized theorem chain

For every `a>0`, Suzuki's finite-part boundary term applied to the exponential source is

```text
-(1/2) exp(x) log(a^2-x^2).
```

Lean proves this term tends to `+infinity` at `a-`. Adding any residual with a finite left endpoint
limit preserves divergence, so the resulting kernel profile cannot equal `c exp(x)` throughout
`(-a,a)`.

The second chain formalizes all integer modes, not a finite truncation. For any complex Hilbert
basis indexed by `Z`, vanishing of every nonzero coordinate forces the vector to equal its zero
mode. Applied to the free-clock sampling points

```text
z_n=pi n/a+i,
```

Lean proves:

1. `z_n != i` for `n!=0`;
2. Suzuki's explicit free carrier vanishes at every `z_n`;
3. equality of a finite-shift Livsic carrier with the free carrier at `z_n`, with its
   Hermite--Biehler denominator nonzero, forces the source Fourier sample to vanish;
4. equality at all nonzero samples forces the weighted source to be a pure zero mode;
5. an identically vanishing reflected cross-tangent numerator likewise forces a pure zero mode;
6. a genuine nonzero source mode forces the cross-tangent numerator to be nonzero somewhere.

Principal declarations:

```text
tendsto_suzukiBoundaryDistanceSq_nhdsLT
suzukiBoundaryLogTerm_tendsto_atTop
suzukiBoundaryKernelProfile_tendsto_atTop
suzukiBoundaryKernelProfile_ne_exp_smul
suzukiFreeClockSample_ne_I
suzukiFreeLivsic_freeClockSample_eq_zero
eq_smul_hilbertBasis_zero_of_repr_eq_zero_off_zero
eq_smul_hilbertBasis_zero_of_suzukiReflectionTangentNumerator_eq_zero
exists_suzukiReflectionTangentNumerator_ne_zero
suzukiFourier_freeClockSample_eq_zero_of_livsic_eq_freeClock
eq_smul_hilbertBasis_zero_of_suzukiLivsic_eq_freeClock
```

## What is and is not closed

Formalized mechanisms close exact endpoint and Fourier-completeness steps without axioms. Combined
with Suzuki's paper construction and paper proof of source-domain membership, they prove no finite
admissible shift can equal the free clock and far-negative projective tangent is nonzero at every
fixed aperture.

Lean tree still lacks concrete unbounded operator `A_a`, its Friedrichs form domain, and
distribution convolution `-g''`. Therefore source instantiation of analytic endpoint decomposition
remains paper-level. No cofinal lower bound or Xi-divisor identification is claimed.
