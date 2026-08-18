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
- [x] 2 → 3 formalized: concrete unconditional Lean capstones, `lake build` green, lint and axiom
  audits pass — ALL SIX target cards are now in
  `3-formalized/new_scientific_knowledge/constrained-prolate/` (see the closing log entry)
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

### 2026-08-07: canonical signed-mode radial family

- Added `ProlateCanonicalRadialFamily.lean`.  For every aperture and fixed signed-greedy index it
  chooses a concrete endpoint-normalized smooth even joint band/prolate mode, with a zero fallback
  outside the eventually live region.
- Proved eventual exactness: endpoint normalization, nonnegative radial separation, first and
  second derivatives, global angular equation, and global exterior radial equation all hold for
  the canonical family.
- Connected the canonical family to the full-ray weak arcsine-density and first-row off-diagonal
  theorems.  Both consequences now require only the single explicit fixed-index statement
  `Tendsto (fun a => (signedModeRadialData a n).s) atTop (nhds 0)`.
- Generalized the Dunster weak-limit and off-diagonal interfaces to eventual exact radial data, so
  zero fallback at finitely many apertures introduces no premise or choice artifact.
- Verified `ProlateCanonicalRadialFamily.lean`, `ProlateDunsterBesselOffDiagonal.lean`,
  `ProlateDunsterWeakLimit.lean`, and `ProlateCCMArcsineWeakLimit.lean` with foreground
  `lake env lean <file>` checks.

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

### 2026-08-07: finite-band joint prolate spectrum

- Added `ProlateBandJointSpectrum.lean`.  Every live even finite-band eigenspace now has a canonical
  finite orthonormal basis of simultaneous finite-band and prolate differential eigenvectors.
- Proved the basis separation values are injective and strictly decreasing in basis order, using the
  previously formalized one-dimensionality of every regular-even separation eigenspace.
- Extracted globally smooth, nonzero, even joint profiles satisfying both exact differential
  equations on the whole real line, and proved every joint separation value is nonpositive.
- This resolves internal multiplicity without assuming finite-band eigenvalue simplicity.  Remaining
  fixed-index gate is asymptotic mode selection: identify which ordered separation line is selected
  by each signed greedy band mode and prove its normalized separation tends to zero.
- Verified with foreground `lake env lean GaloisForLFunctions/RHTower/ProlateBandJointSpectrum.lean`
  (exit 0), then wired module into `GaloisForLFunctions.RHTower` umbrella.

### 2026-08-07: sharp Gaussian and Hermite polynomial tails

- Added `GaussianMonomialTailAsymptotic.lean`.  Proved integrability and the moving-tail derivative,
  then used the at-infinity L'Hôpital theorem to obtain the exact leading constant `1/(2b)` for
  every monomial Gaussian tail of degree at least two, together with the separate degree-zero law.
- Added `GaussianPolynomialTailAsymptotic.lean`.  Lifted the scalar result to every nonzero real
  polynomial of degree at least two: after division by `a^(d-1) exp(-b a^2)`, the tail converges
  exactly to `leadingCoeff/(2b)`.
- Specialized the polynomial theorem to products and squares of the self-dual Hermite polynomials,
  proving exact one-sided tail constants `2^(m+n)/(4*pi)` and `2^(2n)/(4*pi)`.  These are the
  leading entries required for the finite Hermite leakage Gram asymptotics behind fixed-index Fuchs
  mode selection.
- Verified both modules with foreground `lake env lean <file>` checks, cached their `.olean`
  artifacts, and wired them into the `GaloisForLFunctions.RHTower` umbrella.

### 2026-08-07: exact normalized Hermite truncation tails

- Added `HermiteTruncationTailAsymptotic.lean`.  Converted the polynomial Gaussian laws into exact
  two-sided truncation asymptotics for the actual normalized step-four Hermite trial vectors.
- For every positive Hermite index `j`, proved that the squared cutoff defect divided by
  `a^(8*j - 1) exp(-2*pi*a^2)` converges to
  `2^(8*j)/(2*pi*‖hermiteEven j‖^2)`; proved the degree-zero law separately with scale
  `a⁻¹ exp(-2*pi*a^2)` and constant `1/(2*pi*‖hermiteEven 0‖^2)`.
- This removes the earlier exponent loss in the finite Hermite trial envelope: individual trial
  leakage now has its correct `exp(-2*pi*a^2)` asymptotic.  It remains weaker than the true Fuchs
  leakage exponent `exp(-4*pi*a^2)`, so fixed-index separation decay still requires a sharper
  fixed-depth trial family or the global endpoint-response/WKB bridge.
- Verified and cached the module with foreground `lake env lean <file>` and wired it into the
  `GaloisForLFunctions.RHTower` umbrella.

### 2026-08-07: sharp finite-depth signed trial envelope

- Extended `HermiteTruncationTailAsymptotic.lean` with a unified ground/positive-index sharp scale,
  proved its monotonicity in Hermite index for aperture at least one, and aggregated all
  `(n+1)` normalized tails without losing the exponent.
- Added `ConstrainedProlateSignedSharpTrial.lean`.  The true unsigned leakage and the true signed
  leakage `1 - evenProlateSignedValue(a,n)^2` are now eventually bounded unconditionally by an
  explicit positive finite-depth constant times the top Hermite scale.
- For `n>0` the exposed rate is `a^(8*n-1) exp(-2*pi*a^2)`; for `n=0` it is
  `a⁻¹ exp(-2*pi*a^2)`.  This replaces the old lossy `exp(-pi*a^2)/a` estimate throughout the
  signed trial route while recording explicitly that the Fuchs exponent remains stronger.
- Verified and cached both modules with foreground `lake env lean <file>` checks and wired the new
  signed module into the `GaloisForLFunctions.RHTower` umbrella.

### 2026-08-07: fixed-depth Kaiser packet tail infrastructure

- Added `BandKaiserModulatedTrial.lean`.  Defined cosine-modulated Kaiser--Bessel packets, proved
  their exact Fourier transform is the average of two translated base transforms, and bounded the
  packet spectral density by the arithmetic mean of the translated base densities.
- Proved an aperture-independent inner-edge transform bound directly from the exact odd-factorial
  Kaiser series.  This controls the thin portion shifted back inside the band without discarding
  the oscillatory cancellation responsible for the Fuchs clock.
- Added `BandKaiserShiftedTail.lean`.  For every shift of size at most `1/(2*pi*c)`, decomposed the
  shifted tail pointwise into the translated global Cauchy envelope plus a measurable edge term,
  integrated it, and obtained an explicit polynomial tail bound.  The same bound now holds for
  every small cosine-modulated Kaiser packet.
- This is the first correct-exponent fixed-depth trial infrastructure: finite combinations retain
  polynomial tail mass against exponentially large in-band energy, hence can deliver
  `exp(-2*c+o(c))` concentration once their finite Gram conditioning is closed.
- Verified and cached both modules with foreground `lake env lean <file>` checks and wired them into
  the `GaloisForLFunctions.RHTower` umbrella.
- Audited the aggregate Hermite envelope, true signed leakage envelope, modulated transform, shifted
  tail, and modulated packet-tail capstones with `#print axioms`; each reports only `propext`,
  `Classical.choice`, and `Quot.sound`.

### 2026-08-07: finite Kaiser spans inherit the packet tail

- Added `BandKaiserFinitePacket.lean`.  Defined arbitrary finite real combinations of
  cosine-modulated Kaiser packets and proved continuity and evenness of every combination.
- Proved a pointwise spectral Cauchy--Schwarz estimate for the actual Fourier transforms: combination
  density is at most coefficient energy times the sum of individual packet densities.
- Integrated that estimate over the exact complement of the prolate band.  Whenever every packet
  shift lies in the established allowed window, the full span has tail bounded by coefficient
  energy times packet count times the common explicit polynomial envelope.
- Verified in foreground with
  `lake env lean GaloisForLFunctions/RHTower/BandKaiserFinitePacket.lean` (exit 0) and wired the
  module into the `GaloisForLFunctions.RHTower` umbrella.  Remaining trial-space gate is a
  quantitative Gram lower bound; fixed-index Fuchs constants still require true operator/ODE
  identification and endpoint matching.

### 2026-08-07: general sub-band Kaiser translations

- Added `BandKaiserGeneralShiftTail.lean`.  Replaced the thin `O(c^-1)` translation restriction by
  the full exact range `|2*pi*w| <= c`.
- Proved that a translated exterior frequency which crosses back into the band has squared depth at
  most `2*c*|2*pi*w|`, and bounded its transform by the corresponding exact positive
  odd-factorial series.
- Integrated the pointwise decomposition to obtain explicit shifted and cosine-packet tail bounds.
  Also proved the depth series is bounded by `2*exp(1+sqrt D)`, exposing the
  `exp(O(sqrt(c|q|)))` edge cost for angular shift `q`.
- Refactored `BandKaiserFinitePacket.lean` around an envelope-independent integrated
  Cauchy--Schwarz theorem, then added the general-shift finite-span bound retaining every packet's
  exact depth envelope.  This permits `o(c)` packet separation, removing the artificial
  near-coincidence forced by the old shift window and materially improves the Gram-conditioning
  route.
- Both modules pass foreground `lake env lean <file>` checks and are wired into the RHTower umbrella.

### 2026-08-07: conditioned Kaiser packet energy and Rayleigh clock

- Added `BandKaiserTransformSeparation.lean`.  Proved the sharp central lower scale
  `exp(c)/(2*c) <= T_c(0)` and the middle-band separation estimate
  `T_c(q) <= 8*exp(-q^2/(2*c))*T_c(0)`.
- Added `BandKaiserPacketConditioning.lean` on the explicit angular grid
  `q_j=(j+1)*sqrt(c*sqrt(c))`.  Proved exact product-to-sum readings, diagonal lower bound, and
  off-diagonal suppression by `8*exp(-sqrt(c)/2)` relative to central scale.
- Added `BandKaiserPacketEnergy.lean`.  A maximal-coefficient diagonal-dominance argument and
  integral Cauchy--Schwarz give the uniform whole-span bound
  `(sum b_j^2)*exp(c)^2 <= 128*m*c^2*physicalEnergy`.
- Added `BandKaiserPacketRayleigh.lean`.  Specialized the exact general shifted-tail envelope to
  the conditioned grid and proved
  `exp(c)^2*spectralTail <= 128*m*c^2*edgeEnvelope*physicalEnergy` for every coefficient vector.
- All four modules pass foreground `lake env lean <file>` checks.  Remaining Kaiser gate is to prove
  the explicit edge envelope is subexponential, which turns this quantitative inequality into the
  logarithmic leakage rate `-2`.

### 2026-08-07: unconditional fixed-depth Kaiser exponent

- Added `BandKaiserPacketEnvelope.lean`.  Proved the exact grid identities
  `q_step=c^(3/4)` and `sqrt(2*m*c*q_step)=sqrt(2*m)*c^(7/8)`.
- Bounded the complete finite edge envelope by an explicit polynomial times
  `exp(2+2*sqrt(2*m)*c^(7/8))`, then proved every full Rayleigh prefactor is eventually bounded by
  `exp(epsilon*c)` for arbitrary positive `epsilon`.
- Combined this with the quantitative Rayleigh theorem: for every fixed positive packet count and
  every `epsilon>0`, eventually every vector in the full packet span satisfies
  `exp((2-epsilon)*c)*spectralTail <= physicalEnergy`.
- This closes the true `-2` leakage exponent for explicit fixed-depth trial spaces.  Transfer to the
  ordered true prolate leakage values still needs the finite-dimensional trial-subspace bridge;
  exact Fuchs polynomial constants still require fixed-index ODE/endpoint identification.

### 2026-08-07: Kaiser trial spaces reach the true prolate spectrum

- Added `BandKaiserL2Trial.lean`.  Constructed the exact even `L²` Kaiser combination, proved its
  support, norm, Fourier representative, retained energy, spectral-tail identity, physical
  dilation conjugation, and uniform real time-band defect estimate.
- Added `BandKaiserComplexTrial.lean`.  Proved real and Fourier-truncated pairings have zero
  imaginary part, complexified every coefficient vector without loss, built the complex-linear
  physical synthesis, and proved it injective from the explicit packet energy lower bound.
- Added `BandKaiserTrialSpace.lean`.  Proved eventual injectivity and exact dimension of every
  fixed-depth packet range, then applied the true Courant--Fischer form interface.
- New closed capstones prove, for every fixed index `n`, both the true concentration leakage and
  actual signed greedy leakage are eventually at most `exp(-2*pi*a^2)`.  The more precise theorem
  retains the full arbitrary `exp(-(2-epsilon)*2*pi*a^2)` clock.
- Fixed the namespace reference in `ConstrainedProlateSpectralIdentification.lean`; its existing
  signed/concentration spectrum identification now compiles against the present tree.
- All new modules pass foreground `lake env lean <file>` checks.  This closes the previously open
  finite-dimensional trial-subspace bridge.  Exact Fuchs polynomial constants and classical mode
  identification remain open.

### 2026-08-08: logarithmically refined true ground leakage

- Added `BandEvenTrialCarrier.lean`, a reusable exact bridge from any continuous normalized even
  interval trial to the physical even `L²` carrier, including support, norm, Fourier energy,
  dilation conjugation, and exact time-band defect identities.
- Added `BandKaiserCentralEnergy.lean`.  Integrated a central angular-frequency window of width
  `sqrt(c)` and proved the physical Kaiser energy lower bound of order `exp(2*c)/c^(3/2)`.
- Added `BandKaiserGroundTrueLeakage.lean`.  Transported this lower bound through the actual
  time-band Fourier operator and Courant--Fischer interface, proving an unconditional true signed
  ground leakage bound of order `c^(3/2)*exp(-2*c)`.
- Added `BandKaiserLogTail.lean`.  Split the exact exterior sine-quotient transform into an edge
  strip, logarithmic middle region, and inverse-square far region.  Proved the full physical tail
  bound `(8 + 4*log(c))/(pi*c)` for every `c >= 2`.
- Added `BandKaiserGroundLogLeakage.lean`.  Combined sharp tail, central energy, exact physical
  carrier, and true spectral min--max bridge to prove
  `1 - evenProlateSignedValue(a,0)^2 <=
  16*c*(2+log(c))/sqrt(c)*exp(-2*(c-1))`, where `c=2*pi*a^2`.
- Every module passes foreground `lake env lean <file>`.  `#print axioms` for the physical tail,
  true ground leakage, signed ground leakage, and eventual capstone reports only `propext`,
  `Classical.choice`, and `Quot.sound`.  This closes the actual ground-spectrum upper bound to
  within one logarithm of Fuchs's sharp prefactor; matching lower bound, logarithm removal, and
  fixed higher-mode identification remain open.

## CLOSED — all six target cards are at stage 3

The last three of the six, `constrained-prolate-two-mode-ground-state`,
`constrained-prolate-fixed-mode-spectral-ladder` and
`constrained-prolate-fourier-parity-floor-separation`, are now in
`docs/drafts/pipeline/3-formalized/new_scientific_knowledge/constrained-prolate/`.  The other three
were promoted earlier.

### What the last step actually was

Not the analytic bottleneck this card predicted.  By the time the three spectral cards were audited
again, the two "true-operator inputs" they were gated on had already been discharged
unconditionally, for the actual `P_a F P_a` block:

```text
tendsto_norm_evenProlateConstraintCoord_atTop            ell_j(lambda) -> |h_{4j}(0)|
tendsto_norm_evenProlateConstraintCoord_negative_atTop   ell_j(lambda) -> |h_{4j+2}(0)|
ladderEnvelope_evenProlateSignedLeakage                  the Fourier-even leakage ladder
ladderEnvelope_evenProlateSignedLeakage_negative         the Fourier-odd leakage ladder
exists_bound_signedLeakage_ratio_power                   d_m <= C c^{-2(n-m)} d_n, the sharp power
```

The Fuchs identification was not formalized and is not needed: the ladder interface consumes only
nonnegativity, monotonicity, a strict step, a vanishing consecutive ratio and a vanishing
aperture-weighted tail — no sharp constant `A_n` and no matching two-sided power.

What was genuinely missing was the **operator bridge**: every law was a theorem about the secular
formulation, and none of it had been instantiated at the compression of `B_lambda = I − T_lambda²`
to the zero-integral hyperplane.  The closing session built it.

### New modules

```text
RHTower/ProlateSectorGroundLaws.lean          uniqueness of the constrained ground value; the
                                              two-mode and parity floor laws in operator form
RHTower/ProlateSectorDepthSpectrum.lean       the depth-k bridge: coordinate extraction from a
                                              constrained sector eigenvector, the depth-k converse,
                                              the depth-k eigenvector, existence and uniqueness of
                                              the constrained eigenvalue in every gap
RHTower/ProlateSectorSpectralGap.lean         Rayleigh value = eigenvalue; ground floor over the
                                              whole constrained spectrum; the dichotomy
                                              "ground value or at least d_1"; the quantified gaps
RHTower/ProlateNegativeTrueFamilyDistanceRate.lean
                                              the odd-sector O(lambda^{-7}) eigenvector rate, in
                                              coordinates and at the operator
RHTower/ProlateConstrainedOperatorLaws.lean   mu_+, mu_-, mu_k named as operator quantities, and
                                              every card law restated with no hypotheses
```

All wired into `GaloisForLFunctions.RHTower`, warning-free, axioms
`[propext, Classical.choice, Quot.sound]`.

### Two corrections worth keeping

1. **The recorded operator gap statements were vacuous.**
   `eventually_sectorConstrainedEigen_gap_positive` / `_negative` quantify over competing
   constrained eigenvalues *inside the first spectral gap*, where the secular root is unique — so
   their hypotheses are contradictory.  The cards' `(6)`--`(7)` and `(10)` are about the *next*
   constrained eigenvalue, which sits in the next gap.  The repair is the dichotomy
   `eventually_sectorConstrainedEigen_dichotomy_positive`: every constrained sector eigenvalue is
   either the ground value or at least `d_1`.  It needs no new analysis — testing the weak
   compressed equation against the eigenvector itself makes its Rayleigh value its own eigenvalue.
2. **The parity card's eigenvector rate was mis-attributed** to the parent card's `(4)`, which is
   the *even* sector.  The odd-sector rate is now proved in its own right, and the same sharp
   leakage ratio at `n − m = 2` (corpus signed indices `3` and `5`) supplies the same
   `lambda^{-7}`.
