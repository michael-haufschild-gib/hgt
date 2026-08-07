# Constrained prolate stage-3 Lean closure

- **ID:** `constrained-prolate-stage3-lean-closure`
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean)
- **Source:** `../2-fully-proven/new_scientific_knowledge/constrained-prolate/`
- **Statement:** Formalize unconditionally every theorem in all six constrained-prolate stage-2
  cards, including actual classical PSWF identification, fixed-mode Fuchs/Hermite asymptotics,
  radial Dunster transfer, off-diagonal decay, weighted projective convergence, and every existing
  downstream capstone.

## Goal

Move all six source cards to stage 3 only after dependency-closed Lean proofs, umbrella wiring,
per-module checks, axiom audit, formal lint, and final module build.  No asymptotic hypothesis may
remain in any card capstone.

Target cards:

1. `constrained-prolate-two-mode-ground-state`
2. `constrained-prolate-fixed-mode-spectral-ladder`
3. `constrained-prolate-fourier-parity-floor-separation`
4. `constrained-prolate-radial-leakage-divisibility-spectrum`
5. `constrained-prolate-full-radial-prime-charge-law`
6. `constrained-prolate-arithmetic-dilation-operator-limit`

## Gates

- [x] 0 → 1 in-progress: well-posed, source-pure, dependency audit complete
- [ ] 1 → 2 fully-proven: not applicable; six source cards already carry complete paper proofs
- [ ] 2 → 3 formalized: concrete unconditional Lean capstones, `lake build` green, lint and axiom
  audits pass
- [ ] 3 → 4 publication-ready: outside current goal

## Approach

1. Identify actual finite-Fourier signed modes with simple regular even prolate ODE modes.
2. Construct honest classical even numbering and prove positive `4j` / negative `4j+2` sectors.
3. Prove true fixed-mode Fuchs leakage asymptotics and normalized prolate-to-Hermite coordinate
   limits; instantiate existing secular, ladder, parity, and distance machinery.
4. Prove uniform actual-radial-PSWF to Dunster-leading-model transfer, then weak convergence and
   fixed off-diagonal vanishing.
5. Sum off-diagonal sectors and discharge actual weighted projective convergence; instantiate
   arithmetic trace-class and determinant capstones.

Existing closed infrastructure includes concrete time-band/leakage operators, signed spectrum,
canonical pointwise representatives, exact Slepian kernel scaling, exact joint band/prolate
eigenfunction existence, secular roots/tails/eigenvectors, Fuchs-rate algebra, Hermite contrast
algebra, leading Dunster-model tightness/weak convergence, radial mass transfer, arithmetic
projective/trace-class/determinant consequences.

## No-go closure

- **Exact killing theorem/mechanism:** none; task active.
- **Strongest positive survivor:** not applicable.
- **New insight:** six cards share one upstream analytic bottleneck rather than six independent
  formalization gaps.
- **Status:** active.

## Log

- 2026-08-07 — created directly in stage 1 for explicit user-requested long-running formalization.
- 2026-08-07 — added exact scaled Fourier/Fubini composition and true-mode joint smooth even
  Slepian/prolate eigenfunction existence in
  `formal/GaloisForLFunctions/RHTower/SlepianKernelScaledFubini.lean`.
- 2026-08-07 — proved compact-interior prolate ODE uniqueness, center nonvanishing, and
  one-dimensionality of each regular even separation eigenspace on `[-1,1]` in the same module.
- 2026-08-07 — ruled out equating signed greedy index `n` with classical `4n`: signed greedy order
  is by absolute eigenvalue and interleaves positive `4j` with negative `4j+2` sectors.
- 2026-08-07 — ruled out a global solved-form ODE Lipschitz constant on `(-1,1)`; coefficient
  `1/(1-x^2)` is unbounded at singular endpoints.  Compact subinterval uniqueness is exact.
- 2026-08-07 — constructed the complementary negative Hermite sector `h_(4j+2)` in
  `HermiteEvenCarrier.lean`: exact Fourier eigenvalue `-1`, unit normalization, internal and
  positive/negative cross orthogonality, truncation convergence, and uniform finite-span
  compressed-operator estimates.  Positive `h_(4j)` and negative `h_(4j+2)` trial spaces both
  have exact dimension `n+1`.
- 2026-08-07 — added `ProlateFourierSignSectors.lean`.  C-star spectral order plus the compact
  Fredholm alternative now turns a strict quadratic sign witness into an actual signed-greedy
  eigenvalue of that sign.  At every fixed depth the true compressed Fourier form is eventually
  positive definite on the `h_(4j)` trial space and negative definite on the `h_(4j+2)` trial
  space; hence the concrete signed spectrum eventually contains both signs.  Remaining numbering
  gate is multiplicity-sensitive Sturm/min-max identification, not existence of either sector.
- 2026-08-07 — closed the multiplicity-sensitive sign half of the gate.  A new compact
  self-adjoint min–max induction proves that every `m`-dimensional strictly negative (respectively
  positive) quadratic trial space forces `m` orthonormal genuine eigenvectors of the corresponding
  sign.  Applied to the exact Hermite trial spaces, the true even prolate block eventually has
  `n+1` orthonormal positive eigenvectors and `n+1` orthonormal negative eigenvectors at every fixed
  depth.  `lake env lean GaloisForLFunctions/RHTower/ProlateFourierSignSectors.lean` passes.  The
  remaining numbering gate is conversion of these eigenvalue counts into signed-greedy indices,
  followed by Sturm separation for classical `4j` / `4j+2` labels.
- 2026-08-07 — closed signed-greedy multiplicity conversion.  Spectral exhaustion now returns an
  index with nonzero eigenvector coefficient, permitting induction in the orthogonal complement of
  already selected greedy vectors.  Each fixed Hermite depth eventually supplies injective maps
  `Fin (n+1) → ℕ` to distinct positive and distinct negative `evenProlateSignedValue` entries.
  Remaining numbering gate is solely classical Sturm separation and degree identification.
- 2026-08-07 — lifted compact-interior ODE uniqueness into the live even band eigenspaces.
  `bandEigenvalue_eq_of_same_even_prolate_eigen` proves that one regular even separation value
  cannot belong to two distinct nonzero band eigenvalues.  New module
  `ProlateSeparationSimplicity.lean` proves proportionality of same-separation eigenvectors and
  `finrank ≤ 1` for every separation eigenspace inside a fixed live band eigenspace.  Both modules
  pass `lake env lean`.  Remaining classical-label gate is Sturm eigenvalue existence/order and
  degree/zero-count identification.
- 2026-08-07 — closed the angular-to-exterior equation bridge.  Slepian commutation now propagates
  a joint mode's prolate equation from `[-1,1]` to the whole real line after cancellation of its
  nonzero band eigenvalue.  `exists_joint_prolate_band_eigen` and both signed-mode wrappers return
  global ODE solutions.  New `ProlateRadialODEBridge.lean` converts the sign convention exactly to
  the radial equation with `s = -chi/c²`, so every live signed mode is now an admissible exact input
  to the existing Dunster/Volterra comparison.  Per-file `lake env lean` checks pass.
- 2026-08-07 — proved exact separation-energy sign.  New
  `ProlateSeparationEnergy.lean` derives the boundary-term-free identity
  `∫Phi·P_c Phi = -∫(1-x²)|Phi'|² - ∫c²x²|Phi|²`, proves the quadratic form is
  nonpositive, and proves every nonzero global joint mode has `chi ≤ 0`.  Consequently the radial
  ratio `s = -chi/c²` returned by `ProlateRadialODEBridge.lean` is unconditionally nonnegative.
  Both modules pass `lake env lean`.  Remaining Dunster input includes the eventual upper bound
  `s ≤ 1/2`, which belongs to fixed-label Hermite/Sturm control.
- 2026-08-07 — strengthened separation simplicity to the exterior ray.
  `eq_const_mul_of_same_even_joint_prolate_eigen` proves that two live smooth even joint modes with
  the same separation value have the same band eigenvalue and are scalar multiples on the entire
  real line.  Thus regular angular label fixes radial continuation uniquely; no independent
  exterior branch choice remains.  `lake env lean ProlateSeparationSimplicity.lean` passes.
