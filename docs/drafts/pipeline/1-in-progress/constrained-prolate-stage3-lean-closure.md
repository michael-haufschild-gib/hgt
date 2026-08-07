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
- 2026-08-07 — added exact radial endpoint and Hermite-scale equations.  The radial bridge now
  proves `2 Phi'(1) = (s c²-c²) Phi(1)` for every live mode.  Separation energy also gives the
  Rayleigh identity for `s = -chi/c²`.  New `ProlateHermiteRescale.lean` constructs the genuine
  central profile `u(xi)=Phi(xi/√c)` and proves
  `H u + c s u = (xi² u'' + 2 xi u')/c` pointwise, with global smoothness, evenness, and
  `s ≥ 0`, for every live signed mode.  This is the exact true-operator input to the future
  Hermite compactness/label proof; no model family is substituted.  Per-file checks pass.
### 2026-08-07: regular-singular endpoint nonvanishing

- Added `ProlateEndpointNonvanishing.lean`.
- Proved interior uniqueness based at any point of `(-1,1)`.
- Proved a smooth prolate solution with `Phi(1)=0` vanishes on the aperture, using the exact
  Sturm--Liouville flux identity and a strict compact-maximum contraction near `1`.
- Proved every nonzero global joint band/prolate mode has `Phi(1) != 0`.
- Strengthened the signed-mode radial witness with exact endpoint nonvanishing, without analytic,
  asymptotic, or spectral-identification premises.
- Verified with `lake env lean GaloisForLFunctions/RHTower/ProlateEndpointNonvanishing.lean`.

### 2026-08-07: canonical radial normalization and exact Dunster endpoint bridge

- Added `ProlateRadialNormalization.lean`.  Every live signed mode now supplies a smooth even
  exterior radial solution normalized by its proved-nonzero endpoint value, with `R(1)=1`, exact
  endpoint slope `2 R'(1)=c²(s-1)`, exact global prolate equation, and exact exterior radial ODE.
- Added `ProlateDunsterComparisonBridge.lean`.  Proved the exact amplitude identity
  `nfWeight(x) * xiAmplitude(s,x) = lgAmplitude(s,x)`, hence the existing comparison solution is
  literally `R(x)/xiAmplitude(s,x)`.
- Proved a quantitative two-sided endpoint squeeze for `xiAmplitude^4`, then the unconditional
  right-endpoint limit `xiAmplitude(s,x) -> 1` for `0 ≤ s ≤ 1/2`.
- Consequently every continuous endpoint-normalized radial profile satisfies
  `comparisonSol(prolateNormalFormSol R,s,x) -> 1` as `x -> 1+`.  This fixes the regular Dunster
  branch normalization and is the required input for eliminating the logarithmic second branch.
- Verified both new modules with foreground `lake env lean <file>` checks.

### 2026-08-07: exact regular Dunster branch and Green constant

- Added `ProlateDunsterRegularBranch.lean`.
- Proved the constructed second Bessel solution satisfies `besselK(u) -> -infinity` as `u -> 0+`.
- Evaluated the positive Bessel weighted Wronskian exactly as `pi/4` on the whole positive ray.
- Proved the Liouville phase tends to zero at `x -> 1+`, the regular model tends to one, and the
  independent model tends to negative infinity.
- Proved exact homogeneous branch rigidity: any fixed linear combination of the two model branches
  with finite endpoint-normalized limit one has coefficients `(1,0)`.
- Verified with `lake env lean GaloisForLFunctions/RHTower/ProlateDunsterRegularBranch.lean`.

### 2026-08-07: endpoint Dunster Wronskian data

- Strengthened `ProlateDunsterComparisonBridge.lean` with an unconditional eventual bound for the
  derivative of every transformed endpoint-normalized radial profile.
- Added `ProlateDunsterEndpointWronskian.lean`.  Proved `lgWeight -> 0`, the exact logarithmic phase
  identity, and `(x^2-1)|log(c xi_s(x))| -> 0` at the singular endpoint.
- Used those limits to prove `lgWeight * K(c xi_s) -> 0` despite the logarithmic singularity, and
  evaluated the two actual-profile weighted Wronskians at the endpoint as `0` and `pi/4`.
- Specialized both results to the exact comparison transform `R/xiAmplitude` of every smooth
  endpoint-normalized radial prolate profile.  No boundary-value premise for the transformed
  solution remains.
- Verified `ProlateDunsterComparisonBridge.lean`, `ProlateDunsterRegularBranch.lean`, and
  `ProlateDunsterEndpointWronskian.lean` with foreground `lake env lean <file>` checks.

### 2026-08-07: endpoint-anchored Volterra equation

- Added `ProlateDunsterEndpointVolterra.lean`.
- Passed both finite-interval Wronskian transport laws to `x=1+` as improper interval-integral
  limits, using endpoint constants `0` and `pi/4`; no endpoint integrability assumption is needed.
- Specialized both improper transport laws to exact smooth endpoint-normalized radial prolate
  solutions and the concrete `lgNormalFormDefect`.
- Proved exact endpoint-anchored reconstruction: transformed radial solution equals regular Bessel
  model plus two correction terms whose coefficients are precisely transported defect integrals.
- Verified with `lake env lean GaloisForLFunctions/RHTower/ProlateDunsterEndpointVolterra.lean`.

### 2026-08-07: explicit zero-free matching collar and coefficient bounds

- Added `ProlateRadialEndpointFlux.lean`: exact exterior flux identity, positivity-implies-
  monotonicity, a uniform derivative lower bound, and a strict zero-free collar under
  `3 c^2 (B-1) < 5`.
- Added `ProlateDunsterEndpointCrossing.lean`: deterministic matching point
  `B(c)=1+9/(8c^2)`; for `c>=5`, proved `1<B<=11/10`, collar inclusion, and
  `1<=c xi_s(B)` for every `0<=s<=1/2`.
- Added `ProlateRadialEndpointBounds.lean`: proved `0<R<=1`, Dunster amplitude `A_s>=1/2`, exact
  transform bound `|U|<=2`, `c xi_s(B)<=2`, and an integrable logarithmic Bessel envelope.
- Added `ProlateDunsterEndpointCoefficientBounds.lean`: transported endpoint limits through the
  explicit collar and proved, for the genuine endpoint-normalized radial profile,
  `|F_regular(B)|<=18/c` and `|F_log(B)-pi/4|<=141/c`.
- Strengthened `CCMRadialProlateDefect.lean` to expose the exact Gronwall constant used by its
  interior approximation theorem.  This removes the last hidden existential coefficient before
  the uniform actual-profile-to-leading-Bessel transfer.

### 2026-08-07: unconditional uniform actual-to-Dunster transfer

- Added a fixed, globally chosen common Bessel-envelope constant in
  `CCMFirstRowDunsterModel.lean`; interior estimates no longer return a parameter-dependent hidden
  envelope witness.
- Strengthened `CCMRadialProlateDefect.lean` so its approximation theorem exposes both that fixed
  constant and the exact Volterra--Gronwall constant.
- Added `ProlateDunsterUniformTransfer.lean`.  Proved the matching-point datum is at most `33`, the
  exact Gronwall constant is uniformly bounded, and the genuine endpoint-normalized radial
  comparison profile satisfies a fixed `O(1/c)` error bound against the regular Bessel model on
  every interval beyond `B(c)`.
- This is the previously missing actual-PSWF-to-leading-Dunster-model theorem required by the
  radial leakage, weak-measure, off-diagonal, and arithmetic projective-limit cards.

### 2026-08-07: exact radial density transfer and global weak tail law

- Added `ProlateDunsterDensityTransfer.lean`.  Squared the exact uniform profile estimate without
  losing tail integrability, proved fixed profile-weight envelopes for exact and Bessel densities,
  and closed the global `L1` exact-to-Bessel error bound `O(1/c)` on every tail beyond `B(c)`.
- Added `ProlateDunsterWeakLimit.lean`.  Proved fixed-radius phase divergence, compact-interval
  Bessel-density averaging, uniform tail gluing, and global tail-mass convergence to
  `profileDensity` for the literal Bessel density.
- Composed the global `L1` transfer with compact-tail averaging.  Every smooth even
  endpoint-normalized radial prolate solution with `c -> infinity` and `s -> 0` now has exact tail
  masses converging to the universal profile-density tail.  The proof is direct weak convergence;
  it does not assert the false pointwise convergence of oscillatory squared densities.
- Both new modules pass foreground `lake env lean <file>` checks; dependency `.olean` artifacts
  were regenerated for continued module work.
### 2026-08-07: full exterior off-diagonal cancellation

- Extended `formal/GaloisForLFunctions/RHTower/ProlateDunsterBesselOffDiagonal.lean` from compact-interval cancellation to the full radial ray.
- Proved exact endpoint-density identities, endpoint collar mass control, product tail integrability, full-tail bounds, and the compact/edge/vanishing-budget decomposition.
- Closed `tendsto_integral_Ioi_firstRowRadialProduct`: every fixed off-diagonal row product tends to zero for exact endpoint-normalized radial prolate solutions whenever `c → ∞` and `s → 0`.
- Verified in foreground with `lake env lean GaloisForLFunctions/RHTower/ProlateDunsterBesselOffDiagonal.lean` (exit 0).
