# CCM Gauss moving-clock cubic rate

Status: formalized in Lean 4

## Frontier

Earlier Gauss hierarchy work proved only qualitative moving-translation
convergence.  Its paper audit explicitly identified missing quantitative
finite-shift control, while the later corrected audit isolated a relative
two-sided Fourier problem for higher Gauss depths.

Route map was used read-only.  This card records new work without changing
frontier-map history.

## New result

For every Gauss component and prime lattice:

1. Exact logarithmic derivative differs from universal moving clock by
   `O(t⁻¹)`.
2. Forward transport over shift `h` has envelope `(C h + h²) / t`;
   backward transport has `(C h + 2h²) / (t-h)`.
3. On integer lattice, both shift signs satisfy a uniform parabolic law
   `‖defect(j,I)‖ ≤ D (|j|+|j|²)/I` when `2|j|² ≤ I`.
4. For full quadratic Fourier defect `E_I²`,
   `I^(1/3) E_I² → 0`.
5. Consequently, at every depth `m ≥ 3`,
   `I^(1/m) E_I² → 0`.

Proof of summed rate is structural.  Central band cancels quadratic clock
curvature against Fourier weight and leaves summable exponent `4/3`.
Outside band, `I^(1/3) ≤ 2(1+|j|)^(2/3)`; existing power-weight translation
theorem at exponent `4/3` kills full outer sum.

## Scientific content

Old heuristic requested uniform `O(|j|/I)`. Exact Gamma transport shows
quadratic `j²/I` clock-curvature term is intrinsic when clock is frozen at
base height.  Despite that obstruction, infinite Fourier sum has cubic rate.
This removes critical relative translation-rate deficit for all depths
`m ≥ 3`, without assuming sharper false linear-in-shift law.

Depth `m = 2` is exposed as genuine endpoint: needed scale is `I^(1/2)`,
where outer Fourier exponent becomes `1`, exactly nonsummable. Remaining depth-two
problem must exploit cancellation, endpoint logarithmic gain, or fold
convolution structure; stronger positive-weight domination cannot suffice.

## Literature audit

Connes--Consani, *Quasi-inner functions and local factors* (2021),
https://arxiv.org/abs/2008.10974, proves Gauss factorization and sampled-value
decay `O(n^(-1/(2m)))`, and derives quasi-inner compactness/infinitesimal
order. It does not state a finite-shift moving-clock ratio rate, a two-sided
parabolic defect law, or an `I^(1/3)`-scaled infinite Fourier-defect limit.

Connes--Consani--Moscovici, *Zeta Spectral Triples* (2025),
https://arxiv.org/abs/2511.22755, pursues finite-aperture self-adjoint spectral
triples and identifies determinant/eigenvalue convergence as missing. Its
stated framework does not supply this Gauss moving-translation estimate.

Novelty claim is narrow: not Gauss factorization or quasi-inner compactness,
which are literature results, but quantitative transport and summed
critical-relative rate for corpus's Gauss Fourier model.

## Lean artifacts

- formal/GaloisForLFunctions/RHTower/GaussComponentQuantitativeRatio.lean
- formal/GaloisForLFunctions/RHTower/GaussSampleQuantitativeRatio.lean
- formal/GaloisForLFunctions/RHTower/GaussSampleTranslationCubicRate.lean
- umbrella: formal/GaloisForLFunctions/RHTower.lean

Capstones:

- exists_gaussComponentVerticalLogDerivError_inv_bound
- exists_gaussSampleRatioDefect_signed_central_bound
- tendsto_gaussTranslationL2CubicScaledDefectBound
- tendsto_gaussTranslationL2DefectBound_depth_scale

Exact leaf build:

    lake build GaloisForLFunctions.RHTower.GaussSampleTranslationCubicRate

Axiom audit: only propext, Classical.choice, Quot.sound.

## Open core

1. Depth-two endpoint `I^(1/2) E_I²`: positive absolute-value summation hits
   harmonic divergence.
2. Propagate depth-`m ≥ 3` rate through actual folded
   `B⁻²` convolution, not merely same-frequency ratio defect.
3. Determine whether phase-sensitive cancellation removes depth-two logarithm
   or whether separate unnormalized fold is necessary.
