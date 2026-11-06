# Six below-RH questions

- **Stage:** 1-in-progress
- **Source:** [Obstacles summary §2.5](../../../reports/review-0511/obstacles-summary.md#25-breakthrough-questions-below-rh-and-quasi-rh)

## Exact targets

| Target | Required conclusion | Status |
|---|---|---|
| B20 | `T⁻¹∫_T^{2T} log|ζ(1/2+it)| dt → 0`, equivalently clustering at every positive critical-spacing multiple | Open |
| B46 | `ζ(2s)≠0` on `Re(2s)=1` from the actual Mayer/Lewis–Hecke carrier without the Euler-product inequality | Formalized: exact boundary theorem and Mayer consequences; direct check and independence audits passed |
| B21 | At most `ε(A)V` unit windows contain zeros of depth at least `A/log V`, with `ε(A)→0` | Open |
| B7 | Eventual full-space tilted-spline positivity at `c=2K(log N)^(1/8)` for one `K` above the certified size-only optimum | Open |
| TH | Every signed section of `Θ₁+Θ₂` is positive definite for every `0<a<1/2`, with aperture weight retained | Formalized: all ranks, positive determinants and successor Schur coordinates; direct checks and standard-axiom audits passed |
| B73 | `localNewmanConstant X * log X → 0` on one measurable density-one set | Formalized: exact limit and all-future heat corollary; direct checks and standard-axiom audits passed |

Each answer requires its exact Lean theorem, consequences, direct module
check, transitive axiom audit, and umbrella import. Conditional receivers,
finite-rank cases, estimates and equivalences do not settle these targets.

## Proof routes

- [B73: local Newman density-one limit](../3-formalized/local-newman-density-one.md).
  Typical-height bounds give `ζ′/ζ=O_η(log log T)` right of `1/2+η`.
  The half-Gaussian saddle then controls every heat time above
  `16η/log((X−1)/(2π))`, uniformly throughout good unit windows.
  Every positive level set of `Λ_X log X` has density zero; measurable
  diagonal extraction gives the exact limit.
- [B46: Mayer boundary norm](../3-formalized/mayer-boundary-maass-selberg-norm.md).
  A boundary zeta zero annihilates both constant terms and hence the
  Maass–Selberg norm. The nonzero first Fourier coefficient contradicts
  vanishing of the actual lifted carrier.
- [TH: two-atom aperture comparison](../3-formalized/two-atom-aperture-convexity.md).
  The diagonal weights pay the damped midpoint cross term pointwise.
  The interval `0<s<log 2` supplies strict spectral positivity.
  Exact literal jets and Fourier inversion give all-rank positivity.

## Established boundaries

- B20's eight-way equivalence and long-mollifier receivers do not prove
  their moment-law premises.
- `GaussMayerBoundaryZeroFree` uses the von Mangoldt three-four-one
  inequality; `boundarySlope_zero_le` imports `xiZeroCopy_re_lt_one`.
  Neither supplies B46's required independent argument.
- B21 has a sharp sufficient detector and cluster-tail receivers, but
  no producer of the required log-free occupancy bound.
- B7's small critical-multiple theorem and enlarged window-pencil
  range do not prove full-space positivity above the size-only optimum.
  The report also leaves certification of that optimum open (A4).
  The growing low packet now has signed coercivity at every fixed
  critical ratio; the horizon complement and mixed collar cost remain.
- A signed unequal theta pair, or a failure after removing the aperture
  weight, does not decide the weighted two-atom sum.
- B73 concerns the all-future-time `localNewmanConstant`.
  `exists_localHeatThreshold_le_localNewmanConstant` bounds the slice
  threshold in the wrong direction to transfer its density theorem.
  No implication from the B73 limit to B20 is established.
