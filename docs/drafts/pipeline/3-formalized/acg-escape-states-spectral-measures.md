# Escape states are spectral measures on the gauge torus

- **ID:** acg-escape-spectral-2026-10-26
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** ArithmeticCorrelationGeometry README §9 topic 6; ADR common cofactor limits
- **Statement:** Every symmetric PSD kernel `K` on `ℕ_{>0}` with `Q(p·) ≤ Q/p` (every ADR actual
  cofactor limit) has an asymptotic kernel `K̃_∞(j,k) = lim_d √(dj)√(dk)K(dj,dk)` (along any
  cofinal divisibility chain), PSD and dilation invariant, and a finite measure `ν` on the prime
  torus with `K̃_∞(j,k) = ∫ χ_x(j/k) dν`, mass `≤ K(1,1)`; `ν` is a multiple of Haar iff `K̃_∞` is
  diagonal; exactly covariant kernels equal their asymptotic kernel.

## Proof
Critical normalisation turns the packet contraction into monotonicity of `Q_d` along divisibility;
infimum = limit along `(n+1)!` and `p·(n+1)!`; polarization on `{j,k}`; dilation invariance by
uniqueness of limits. The ratio function `u ↦ K̃_∞(num u, den u)` is PD on `ℚ_{>0}` (common
denominators, real-kernel complexification); APD `exists_measure_ratChar`. Haar: Fourier
coefficients vs `integral_torusCharacter`, uniqueness `finiteMeasure_ext_of_ratChar`.

## Lean
`formal/GaloisForLFunctions/ArithmeticCorrelationGeometry/EscapeStatesAreSpectralMeasuresOnTheGaugeTorus.lean`:
`dilForm_mul_le`, `tendsto_dilForm`, `asymKernel_mul_mul`, `isPosDefOnGroup_ratioFunction`,
`exists_spectralMeasure`, `spectralMeasure_eq_haar_iff`, `asymKernel_eq_of_covariant`,
`exists_actualCofactorLimit_spectralMeasure`.

## Insight
An escape state is a measure on the gauge torus (the isometric part of its dilation action), not a
gauge point; it is gauge invariant only if dilated receivers become asymptotically orthogonal.
