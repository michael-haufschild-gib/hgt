# Xi antipodal-shift phase-splitting universality law

Status: **Stage 3 — formalized in Lean 4**

## Discovery

Whole-corpus theorem-posting closure joined:

- `seamFluxCochain_conj`, which makes the completed Xi logarithmic derivative
  Schwarz-equivariant;
- `xiPairwiseShiftRawLogDerivDifference_neg`, which makes every antipodal pairwise shift
  difference even in its observation coordinate; and
- `re_logDeriv_xi_criticalLine`, which annihilates the real part of the unshifted center channel.

The corpus contains each symmetry separately, but no theorem identifies their joint phase
decomposition on the imaginary observation axis.

## Universal law

Let `a,b ∈ ℝ` satisfy `a+b=1`, and put

`D_ab(t) = (xi'/xi)(a+it) - (xi'/xi)(b+it)`.

Then, for every real `t`:

1. `D_ab(-t)=D_ab(t)`;
2. `conj(D_ab(t))=D_ab(t)`, hence `Im D_ab(t)=0`; and
3. the center channel `(xi'/xi)(1/2+it)` has real part zero.

Thus antipodal differencing rotates the completed-Xi boundary response into a real-even channel,
whereas the unshifted critical-line response remains purely imaginary. This phase split is
unconditional and pointwise, including the totalized quotient values at zeros.

## Dependency-closed paper proof

1. Schwarz equivariance gives
   `conj((xi'/xi)(z)) = (xi'/xi)(conj z)`.
2. Since `a,b,t` are real,
   `conj(a+it)=a-it` and `conj(b+it)=b-it`. Therefore
   `conj(D_ab(t))=D_ab(-t)`.
3. The antipodal relation `a+b=1` invokes the existing pair-reflection theorem, whose fixed
   coordinate is the origin, and gives `D_ab(-t)=D_ab(t)`.
4. Combining steps 2 and 3 gives `conj(D_ab(t))=D_ab(t)`, equivalent over `ℂ` to
   `Im D_ab(t)=0`.
5. Existing edge blindness gives
   `Re((xi'/xi)(1/2+it))=0`.

No zero distribution, convergence, spectral sum, RH premise, or numerical computation enters.

## Formal targets

- `logDeriv_xi_conj_global`
- `star_xiPairwiseShiftRawLogDerivDifference_ofReal`
- `xiPairwiseShiftRawLogDerivDifference_antipodal_star`
- `xiPairwiseShiftRawLogDerivDifference_antipodal_im`
- `xi_antipodalShift_phaseSplittingUniversality`

## Novelty audit

Post-proof searches found work on the real part and positivity of the completed-Xi logarithmic
derivative near the critical line, and work on symmetric shifts of Xi values off the line. They did
not reveal the exact pointwise law that the logarithmic-derivative *difference* of every real
antipodal shift pair is simultaneously real and even while the center channel is purely imaginary.

The exact phase decomposition remains **[NOVELTY UNVERIFIED]**:

- https://arxiv.org/abs/2509.18963
- https://arxiv.org/abs/2201.08599
- https://arxiv.org/abs/0904.1051

## Lean formalization

Formalized in:

`formal/GaloisForLFunctions/RHTower/XiAntipodalShiftPhaseSplittingUniversalityLaw.lean`

with declarations:

- `logDeriv_xi_conj_global`
- `star_xiPairwiseShiftRawLogDerivDifference_ofReal`
- `xiPairwiseShiftRawLogDerivDifference_antipodal_star`
- `xiPairwiseShiftRawLogDerivDifference_antipodal_im`
- `xi_antipodalShift_phaseSplittingUniversality`

Exact-file verification passed:

`lake env lean GaloisForLFunctions/RHTower/XiAntipodalShiftPhaseSplittingUniversalityLaw.lean`

Wired into `GaloisForLFunctions/RHTower.lean` beside the Xi pair-reflection instance.
