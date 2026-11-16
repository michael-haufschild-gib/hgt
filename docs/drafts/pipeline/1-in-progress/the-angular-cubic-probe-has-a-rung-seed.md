# An angular cubic probe for a Grössencharacter rung seed

- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Obstacle:** O3; no contribution counted.
- **Target:** An unconditional zero-free half-plane `Re w>b`, `b<1`, for actual
  `grossenLFunction` with positive infinity type.
- **Verified:** Thirty-one helper modules passed final plain Lean checks and are umbrella-wired.
- **Missing:** Angular source moment induction and both common-signal estimates.

## Receiver

`grossenHalfPlane_step` fixes weight `k` and takes the zero supremum over all finite ray
characters at that weight. Constants and height orders may depend on `k`. The correction
identifies the next level `6k+1`; the receiver itself supplies no detector estimate.

Finite-order estimates use periodic `HeckeFamily.Character` coefficients. Multiplication by
`idealPsiSix^k` preserves multiplicativity and unit bounds, but does not preserve finite
periodicity. Neither periodic completion nor moment cancellation transfers from norm bounds alone.

## Verified connections

| Modules | Mathematical content |
|---|---|
| `AngularHarmonicGaussian`, `AngularFourierProfiles` | Exact harmonic-Gaussian Fourier transform, angular covariance, scaling, periodic Poisson reflection and annular-source seminorm decay. |
| `AngularMellinTransform`, `AngularMellinBounds` | `M H_(2n)(z)=C^(1−2z)Γ(z+n)/Γ(1−z+n) M W(1−z)`, `C=2π/√3`; positive value at `1/6` for nonzero nonnegative annular sources; right-half-plane continuation, vertical decay and inversion. |
| `AngularPhysicalPoisson`, `AngularSixthPowerFactor` | Exact physical compensation phase; the sixth-power decomposition moves infinity type `k` to ideal weight `6k`. |
| `AngularPeriodicSums`, `AngularPlainIdealSums` | Positive angular weight removes the zero lattice mode; six-unit summation gives ideal cancellation uniform in finite character, with polynomial Mellin-height cost. |
| `AngularPlainRowBounds`, `AngularPlainEnergy` | Actual completed-row character with explicit conductor bound; normalized two-slot product and radial energy bounds, including finite-principal rows. |
| `AngularPlainReflection`, `AngularFourierRegularity` | Primitive reflection in both infinity-type orientations preserves absolute normalized sums. Both transformed radial profiles have rapid Euler-derivative decay. |
| `AngularPrimitiveCoefficients` | The primitive finite character has ideal coefficients exactly `primitiveIdealValue`, hence those of actual `grossenLFunction`. |
| `AngularLFunctionBounds` | `|L(ψ,k,w)|≤C_k N(f)^(3/5)(3+|Im w|)^d` on `−1/10≤Re w≤11/10`; degree independent of finite character and positive infinity type. |
| `AngularRayFamily` | Every finite row character is an actual ray class character with the same zero-extended ideal coefficients. Primitive continuation times finite Euler deletions gives the original-modulus continuation, with identical positive-half-plane zeros. |
| `AngularEulerLog` | Primitive and original-modulus continuations equal their multiplicative angular ideal series on `Re w>1`; their analytic Euler logarithms have one uniform bound on disks of radius `49/100` centered at `2+it`. |

## Plain-slot estimates

For every bounded periodic coefficient `P mod c` and positive angular weight,
`|Σ_z P(z mod c) θ(z)^k W(Nz/X)| ≤ C·B·Nc·(1+X/Nc)^(-A)` when `|P|≤B`.
The constant uses finitely many seminorms of annular `W`.

The actual row character has modulus norm at most `Q = rowConductorBound η m f z`.
Its angular plain sum is bounded by `C(1+|t|)^J Q(1+X/Q)^(-A)`. For two slots
with scales at least `L`, the normalized product is bounded by
`C(1+|t|)^J Q²/[sqrt(X₁X₂)(1+L/Q)^(2A)]`.
Radial energy is at most radial lattice mass times the square of this bound.
Compact radial support `Nz≤bK` gives common conductor bound
`Q = rowConductorBound η m f a · bK` for physical rows `az`.

## Primitive reflection

For primitive unit-trivial finite `χ mod c`, let `S⁺` use `conj(idealPsiSix)^k`
and `S⁻` use `idealPsiSix^k`. Angular Poisson and the finite Gauss transform give
`S⁺_χ(W,X) = X·gχ/|c| · conj(ψ₆(c))^k · S⁻_(χ⁻¹)(H_(6k)W,Nc/X)`.
After square-root normalization all prefactors have modulus one. Conjugation
reflects the actual `idealPsiSix^k` source using `conj(H_(6k)(conj W))`.
The half-Euler operator on the underlying Schwartz ray map controls every fixed
number of logarithmic derivatives by finitely many source seminorms.

## Failed compensation subroute

Compensating the column character by an angular physical test transfers it to
frequency and replaces the free sixth-power zeta pole by a nonzero-infinity-type
Grössencharacter factor, regular and nonzero at `z=1/6`. Its residue is zero.
The positive archimedean Mellin value does not restore the pole.
[Exact obstruction and positive survivor](../5-failed/angular-compensation-preserves-the-sixth-power-pole.md).
This does not factorize the entire compensated principal series or exclude every angular probe.

## Direct angular source

Existing `ProbeRow.spectralSummand_mul_fixed_twist` factors any multiplicative
`φ` through `completedIndex I J`. Taking `φ=elemPsiSix^k` changes the completed
column coefficient while retaining the radial physical row. `spectralRow` and
`spectralRow_eq_gaussianCompleted` already accept arbitrary multiplicative
coefficients bounded by one. This is distinct from the failed angular-physical
compensation above. The actual direct probe, principal comparison and high-source
moment estimates still require their angular extensions. In particular,
`InverseReflectedPhase.low_original_completed_energy` and its sub-seven-eighths
variant require `CanonicalCoefficientClass.FactorsModulo Q Ψ`; the angular twist
fails this premise. Angular reflection must extend these low completed-sum
estimates as well as the high plain-slot moment induction.

## Verified reciprocal growth

For fixed positive `k`, define
`β_k = sup({1/2} ∪ {Re ρ : L(ψ,k,ρ)=0, Re ρ>0})` over all finite ray characters.
Absolute convergence gives `1/2≤β_k≤1`. The polynomial strip bound and
actual Euler logarithm give
`|L(ψ,k,w)^(-1)| ≤ C_(k,δ,ε) [2N(f)(3+|Im w|)²]^ε` for `Re w≥β_k+δ`.
`AngularReciprocalBounds.grossenLFunction_reciprocal_subpower` passed its final
plain Lean check and is umbrella-wired. The module also proves logarithmic-
derivative control on the corresponding disks. No zero-free premise is assumed;
no inequality `β_k<1` follows.

## Verified higher cusp geometry

`AntiholomorphicJets` combines `CompensatedSlices` with `ParametricSmoothness`:
all powers of `Dbar` commute with holomorphic multiplication; smooth multiples of `|z|²`
have zero pure antiholomorphic jets at zero. A smooth Hadamard remainder extends this
invariance to compositions. Conjugate-affine maps exchange `Dbar^r` and `Dz^r` with factor
`a^r`; equal germs have equal iterated derivatives.

`HigherCuspWirtingerJets.inverse_cusp_iterated_wirtinger_rule_of_contDiffOn` proves, for
`F` smooth near the inverse cusp center,
`Dbar^r(F∘T)(0) = (−1/(c²v²))^r Dz^r F(v₀,−d/c)`, where
`T(z)=(v/[|c|²(v²+|z|²)], −d/c−conj(z)/[c²(v²+|z|²)])` and `v₀=1/(|c|²v)`.
The explicit coordinate remainder is divisible by `|z|²`; local smooth extension supplies
the global Hadamard identity. 

The normalized order `r≥1` satisfies
`v^(r−1) Dbar^r(F∘T)(0) = (-conj(c)/c)^r/(|c|²v²) · v₀^(r−1) Dz^r F(v₀,−d/c)`.
The angular factor has modulus one, so the absolute reflection scale is independent of `r`.
This removes the apparent extra height powers; it does not establish reflected energy bounds.

## Source smoothness and missing kernel bridge

`BesselArgumentSmoothness` uses the adjacent-order argument derivative to give `K_ν(exp u)` infinite real smoothness for every complex `ν`; its
integral representation gives `|K_ν(x)|≤C_(ν,δ) exp(-x)` for every `x≥δ>0`.

`BesselFourierSmoothness` proves joint infinite smoothness of the actual residual cubic
source on positive cusp coordinates. Its generalized Fourier–Bessel sum is closed under
adjacent-order and linear-frequency differentiation; exponential majorants justify the
sum derivative, and induction gives every order. The positive-ray/cosh kernel identity
identifies the actual source, including its constant mode.

`HigherSourceCuspJets.SourceCuspDatum.reflection_higher` applies the all-order law to the
actual conjugate source and the same three cusp representatives. For every `n≥0`,
`higherBar(n,z,v) = multiplier(n)/v² · higherZ(n,j,z*,1/(heightScale·v))`,
with `|multiplier(n)|=1/heightScale`. Actual automorphy discharges the cusp decomposition;
Order one recovers the existing profiles and multiplier.

`PureJetAlgebra` proves conjugation and complex-affine transport of pure jets, together with
constant multiplication and recursion reassociation.

`BesselFourierJets` gives every pure horizontal derivative of the actual Fourier–Bessel sum
by the corresponding frequency power. The actual residual source loses its constant mode
after one derivative; conjugating source values gives the exact antiholomorphic expansion.
`HigherSourceFourier` identifies the actual three-cusp higher jets. At order `6k+1`,
the initial coefficient is twisted by `elemPsiSix^k`, the dual coefficient by its conjugate,
and both acquire radial factor `length^(3k)`. The frequency scale is purely imaginary;
its sixth-power normalization cancels the cusp-width power exactly.

At `r=6k+1`, the verified radial kernel is `v^(6k)` times the original kernel with
coefficient multiplied by `length^(3k)`. Low reflected energies, high moment induction
and both common-signal estimates remain open. No seed or new contribution is claimed.

`AngularSourceMellin` proves the exact shifted transform:
`M angularRadial(k,r,a,q)(2s) = besselMellinFactor(q,s+3k) Σ a_h r_h^(1/2−s)`.
For the actual angular source Dirichlet transform, cusp reflection has the original conductor
factor, multiplier `jetMultiplier(6k)`, and opposite angular dual coefficients. The extra
cusp-width powers cancel exactly. Its Gamma ratio is
`Γ(7/6+3k+w)Γ(5/6+3k+w) / [Γ(7/6+3k−w)Γ(5/6+3k−w)]`.
It is holomorphic on `Re w>−5/6−3k`, unitary on the imaginary axis, and bounded by
`C_(k,A)(1+|t|)^(4A+4)` on `−1/4≤Re w≤A`.
`AngularSourceEntire` proves exponential height decay for every higher jet, with rate
independent of jet order. Actual cusp reflection gives absolute Mellin convergence everywhere
and entire normalized angular Dirichlet continuation at every finite source cusp.
`AngularKernelData` proves smooth positive-axis reflected kernels and identifies all
logarithmic derivatives with Euler-weighted Mellin inversion. The imaginary-axis multiplier
is unitary, preserving every absolute Fourier moment; compact sources give rapid decay
of the Mellin data on common vertical strips. `AngularKernelBounds` proves arbitrary polynomial radial decay for every logarithmic
derivative, including uniform bounds on bounded logarithmic intervals. Source-uniform kernel bounds remain unverified.

`AngularSourceSmoothing` proves entire smoothing integrands, exponential strip bounds and
contour shifting between integrable vertical lines. Its exact initial/reflected line formulas
retain the original radial scale; the reflected multiplier has modulus `cuspWidth²`.

`AngularSmoothedReflection` proves absolute Mellin inversion for angular dual coefficients
and exact smoothed reflection at every source cusp, with the original conductor scale.
Finite periodic Fourier inversion and the reflected energy estimates still need their angular extensions.
