# Metaplectic Möbius descent

Finite character conversion supplies the algebraic part of a metaplectic approach to Möbius cancellation. Its normalized transform is

`T_j(x) = q⁻¹ G(χ^j,ψ(−·)) G(χ^(j+2),ψ(x·))`.

The factorization holds for every character power and every argument. For a primitive additive character, two nontrivial Gauss factors give a scalar of norm one. A sextic character becomes its quadratic third power. The exceptional fourth power is constant off zero and has a separate value at zero. For primitive `ψ`, cubing a cubic Gauss sum retains the Jacobi-sum phase: `G³ = qJ`.

`TheSexticCharacterBecomesQuadratic.lean` proves these statements. The Gauss norm theorem comes from `ArithmeticEffectivityTheory.TheTorsionCharacteristics`.

`ThePrimaryCubicGaussSumFixesTheSign.lean` constructs the actual cubic residue character and its canonical primary generator. It proves `J(χ_p,χ_p) = −p` and `γ_p³ = −p/|p|`, for every primitive additive character. Cubing erases invertible additive-shift phases.

`CubingTheCompositeGaussSumRecoversMobius.lean` proves
`γ(I,ψ)³ = μ(I) p/|p|` on quotients by finite products of distinct primes away
from three, for every primitive additive character. CRT factorization derives
local primitivity; a definite composite primitive character is constructed.

`MobiusBecomesACubicGaussCoefficient.lean` proves the exact conversion
`μ(I) conjugate(G₁) = c(I,ψ) G₂`, with explicit `|c(I,ψ)|=1`. The factor
contains primary generators, sextic values at four, and quadratic Gauss sums.

`CubicReciprocityFromFrobenius.lean` derives cubic reciprocity for canonical
primary generators of primes with distinct residue characteristics. Frobenius
in the second residue field is compared with the exact cubic Gauss identity.

`CubicReciprocityAtACommonCharacteristic.lean` closes the common-characteristic
case. The quadratic field degree bounds the prime fibre by two; primary
factorization of `−(p+q)` reduces the remaining relation to distinct residue
characteristics. Thus prime cubic reciprocity holds without that restriction.

`CubicJacobiSymbols.lean` constructs the ideal symbol with arbitrary prime
multiplicities. It proves composite primary reciprocity, numerator congruence,
multiplicativity in both arguments, and the cubic-root law for coprime arguments.

`TheCubicPhaseLivesModuloTwo.lean` identifies the product of sextic values at
four with a fixed cubic character of the primary product modulo two. It is
one on residue class one. The composite conversion factor is thereby reduced
to this fixed character, the primary product, and the quadratic Gauss sum.

`TheDifferentNormalizesTheTraceCharacter.lean` identifies the different with
`(1+2ω)` and constructs the primitive character
`ψ_c(x)=exp(2πi Tr(x/[c(1+2ω)]))` for every nonzero modulus. The exact composite
Möbius conversion therefore holds for the analytic trace normalization.

`EisensteinCoordinates.lean` proves the intrinsic trace formula
`Tr((a+bω)/(1+2ω))=b`, the norm form, and rational residue coordinates.

`BinaryGaussianPoisson.lean` proves the exact transform of the damped
quadratic trace form, including intermediate summability and the principal
square-root branch. Its dual separates the Gaussian scale from the phase.

`ShiftedEisensteinGaussianMass.lean` proves that every shifted lattice has
Gaussian Abel mass `2/√3`, or `2/(√3 q)` after rescaling by `q>0`.

`QuadraticTraceCoordinates.lean` gives the actual trace pairing and evaluates
the four-residue dual phase. Its identification with the normalized Gauss sum
requires the original and dual Abel limits.

`EisensteinResidueGaussianMass.lean` partitions the actual lattice modulo a
nonzero principal ideal and proves that its quadratic trace Gaussian has
Abel limit `2G(c)/(√3‖c‖²)`.

`TheDualGaussianPhaseFreezes.lean` proves that freezing the dual quadratic
phase changes its Gaussian sum by `o(η⁻¹)`. The proof bounds a quadratic
moment by a Gaussian at half the scale. The dual scale and Poisson prefactor
limits are explicit.

`TheQuadraticGaussPhaseLivesModuloFour.lean` proves the exact evaluation
`G(a+bω)/‖a+bω‖=(1+i^(−b)+i^a+i^(b−a))/2` for every nonzero modulus.
Thus the normalized trace Gauss sum depends only on the modulus modulo four
and equals one on the principal class.

`TheAnalyticConversionHasAFixedRayPhase.lean` identifies the actual quadratic
character sum with the trace square sum. It gives
`μ(I) conjugate(G₁) = R(p) (‖p‖/p) G₂`, where `R` depends only on `p mod 4`,
has unit modulus for these prime products, and equals one when `p≡1 mod 4`.

`TheRamifiedCubicSupplement.lean` evaluates the symbols of `ω` and `ω−1`
at primary primes `1+3A+3Bω` as `ω^(2A−B)` and `ω^A`.
The ramified comparison uses composite reciprocity and fixed primes of norms
four and seven.

`TheRamifiedCubicPhaseLivesModuloNine.lean` extends those laws to composite
primary denominators and evaluates the different's symbol as `ω^(−B)`.
The phases depend only on the denominator modulo nine. More generally,
`(x/a)₃=(x/b)₃` for primary `a,b` when both nine and `x` divide `a−b`.

`TheCubicKubotaMultiplier.lean` constructs `κ([a b;c d])=(c/a)₃` on the
principal level-three group and proves its product law. The explicit matrix
`[[1+3ω,−3ω²],[3,1−3ω]]` has multiplier `ω`. Hence the character is onto
the cubic roots, its kernel has index three in that group, and the corresponding subgroup
of `SL₂(O)` has finite index.

`TheCubicMultiplierExtendsOverRationalMatrices.lean` extends the character to
`Γ(3)·SL₂(ℤ)`, trivially on rational matrices. This larger group normalizes
the original metaplectic kernel, which remains a normal subgroup of finite index.

`HyperbolicThreeSpace.lean` identifies `SL₂(ℂ)/SU₂` homeomorphically with
upper half-space and proves the exact matrix height formula.
`EisensteinNearestPoint.lean` bounds nearest-point squared distance by `1/3`
in either embedding. `BianchiReductionAndCompactCore.lean` gives maximal
integral orbit height, Ford reduction with height floor `√(2/3)`, and a
compact core plus finitely many cusp tails for the actual cubic kernel.

`TheCubicEisensteinSeries.lean` constructs the actual cubic source series on
bottom-row classes. It proves absolute convergence and holomorphy for
`Re s>2`, character automorphy, and its expression as a sum of cusp-height powers.
Continuation to `s=4/3` and the nonzero residue are not yet established.

`TheCubicKernelHasAMeasurableFundamentalDomain.lean` proves freeness of the
level-three action and constructs a measurable orbit selector by Frobenius
energy and Gram coordinates. For every subgroup of level three, exactly one
group element moves each point into the selector. This applies to the actual
cubic kernel for every Borel measure.

`HyperbolicVolumeIsInvariant.lean` constructs `dx dy dv/v³` on hyperbolic
three-space and proves invariance under every complex special linear matrix.
The inversion Jacobian and height density cancel exactly.

`TheCubicQuotientHasFiniteVolume.lean` constructs the quotient measure,
proves independence from the fundamental selector, and proves its positive
finite total mass. The exact cusp-box integral supplies finiteness through
the Ford cover. The convergent Eisenstein series descends to this quotient.

`TheCubicQuotientHasLocalMeasureCharts.lean` proves proper discontinuity and
the covering property. Every injective measurable chart preserves the actual
restricted measure. Compactly supported continuous functions are dense in
the quotient `L²` space.

`SmoothCutoffsOnTheCubicQuotient.lean` constructs a smooth compact cutoff
around every quotient point, supported in an injective positive-height chart.
Its support carries the exact restricted quotient measure.
`TheCubicQuotientHasASmoothAtlas.lean` constructs a smooth manifold atlas
from actual covering lifts and proves the covering projection smooth.
Chart transitions are locally Möbius transformations.
`SmoothTestsOnTheCubicQuotient.lean` proves full support of invariant volume
and gives a faithful dense embedding of compactly supported smooth tests
in the actual complex quotient `L²` space.
`HyperbolicActionPreservesEnergy.lean` proves that every Möbius differential
scales Euclidean norm by the height ratio. Consequently, scalar gradient
energy weighted by squared height is invariant under pullback.
`TheCubicDirichletForm.lean` descends that energy to the actual quotient.
Its compactly supported density is integrable, and polarization gives a
nonnegative Hermitian form on smooth tests.
`TheCubicEnergyGraph.lean` completes the smooth mass-gradient pairs in their
Hilbert sum norm, with dense smooth core and dense quotient mass range.

`Sobolev/EuclideanEnergy.lean` constructs the complete `C¹` gradient graph.
`Sobolev/EuclideanTranslations.lean` constructs translation isometries on `L²`
and proves the pointwise segment-gradient bound.
`Sobolev/TranslationEnergyBound.lean` proves `‖τ_a u−u‖₂≤‖a‖‖∇u‖₂`,
including every element of the complete energy graph.

`Sobolev/LpZeroExtension.lean` and `ConvolutionSmoothing.lean` construct
isometric zero extension and smoothing with explicit support control.
`ContinuousKernelOperators.lean` applies the corpus compact-kernel theorem
to continuous kernels, including compact restrictions of the output measure.
`CompactConvolution.lean` identifies that operator with actual convolution
and proves that smoothing maps bounded balls to relatively compact families.
`ConvolutionApproximation.lean` bounds squared smoothing error by the average
squared translation error under the actual probability kernel measure.
`SmallProbabilityKernels.lean` constructs such kernels inside every positive
radius ball by normalizing a smooth bump.
`SmoothedTranslationBound.lean` and `SmoothingCompactnessCriterion.lean`
turn a uniform translation modulus into finite smoothing nets.
`EuclideanRellich.lean` discharges that modulus with the gradient bound:
restriction of the complete energy graph to a compact support has compact
mass projection. Common compact support and bounded mass and gradient norms
therefore give precompact `C¹` families in `L²`.
`ComplexWeakGradientGraph.lean` constructs the actual distributional gradient
space on `ℝ³`, with a closed gradient, injective dense mass embedding,
and Hilbert norm squared equal to mass squared plus gradient squared.
`CompactCutoffCharts.lean` gives a finite smooth cutoff cover of every compact
quotient set, with injective measure charts and compact Euclidean energy
projections. `LocalizingTheCubicEnergy.lean` bounds the Euclidean weak-gradient
norm of each localized smooth test by its quotient mass and Dirichlet energy.
`LocalizingTheCompletedCubicEnergy.lean` extends this map continuously to the
completed graph. Its mass depends only on quotient mass; zero quotient mass
therefore gives zero localized Euclidean weak gradient.
`TheCubicGradientIsClosable.lean` proves that these localizations detect
the whole gradient. The completed energy mass embedding is injective,
and the actual quotient weak-gradient operator is closed with dense domain.

`CompactCubicEnergyLocalizations.lean` applies Euclidean Rellich to real and
imaginary parts. Each injective cutoff therefore gives a compact mass map
from the completed quotient energy space into Euclidean `L²`.

`CompactRestrictionOfTheCubicEnergy.lean` combines finitely many such
localizations: mass restriction to every compact quotient set is compact
on the actual completed energy space.

`TheCubicVariationalLaplacian.lean` constructs the unique coercive weak
solution as the adjoint mass map. Its resolvent defines the actual closed,
densely defined, nonnegative self-adjoint quotient Laplacian.

`GreenIdentityOnTheCubicQuotient.lean` constructs finite smooth chart
partitions and proves weighted integration by parts with density `v⁻³`.
Exact chart transport identifies that expression with the quotient form.

`TheCubicLaplacianHasItsCoordinateExpression.lean` extends Green’s identity
by a finite chart partition, including equations valid only on test support.
Global square-integrable coordinate equations give the graph and action
of the actual variational Laplacian.

`HyperbolicAxisLaplacian.lean` identifies the positive Fréchet expression
with minus the iterated coordinate-axis Laplacian on positive half-space.

`HighCubicCuspsAreLocallyFinite.lean` bounds integral cusp-row coordinates
using a continuous triangular representative. Only finitely many rows can
have height at least one locally. The integral norm lower bound also gives
the height-product obstruction for distinct cusp directions.

`HyperbolicLogarithmicHeight.lean` identifies the actual transformed cusp
height and proves the eikonal and Laplace identities for its logarithm.

`HyperbolicHeightProfiles.lean` proves the profile formula
`Δ_axis F(h)=h²F″(h)−hF′(h)`, together with finite-sum and germ identities.

`TheCubicCuspBarrier.lean` constructs the invariant smooth barrier, equal
to height in every sufficiently high integral cusp. Its height-profile
defect is continuous and compactly supported on the actual quotient.

`TheCubicCuspProfileEquation.lean` proves the actual Laplace equation for
locally finite invariant sums of smooth height profiles.

`TheCubicBarrierPotential.lean` identifies the actual barrier equation
`Δφ=Vφ`, with continuous `V≥1−C1_K` for compact `K`. It also proves the
pointwise square-completion inequality for the ground-state transform.

`TheCubicExteriorCoercivity.lean` integrates the ground-state inequality
and extends by density: `‖Mu‖₂²≤‖Gu‖₂²+C‖1_KMu‖₂²` for every completed
energy vector, with compact `K` and compact restriction map.

`TheCubicSpectralPencilIsFredholm.lean` proves that
`T(λ)=Id−(λ+1)M*M` is Fredholm throughout `0≤λ<1`, in particular at
`λ=8/9`. The compact-error estimate feeds the corpus closed-range theorem;
self-adjointness identifies the finite-dimensional cokernel.

`TheCubicMeromorphicResolvent.lean` splits the pencil at `8/9` into its
finite nullspace and analytic regular inverse. It constructs the actual
meromorphic quotient resolvent and its inverse identities; composition
with `s(2−s)` is meromorphic at `4/3`.

`CharacterEquivariantCubicCuspProfiles.lean` proves that distinct principal
cusp cosets cannot both have height above one. High-cusp profile sums
therefore have finite support and transform by the actual cubic character.

`CubicIncomingHeightProfiles.lean` computes the exact cutoff-power
Laplacian defect. Its height support is compact, and each height value
is entire in the spectral parameter.

`SmoothCubicCuspSeeds.lean` constructs the actual smooth equivariant seed
and its exact Laplace defect. Both descend through the cubic character
kernel to the quotient and are entire pointwise in the spectral parameter.

`CubicCompactHeightProfiles.lean` constructs the bounded linear map from
compact-height profiles to quotient `L²`. The actual incoming defect is
its image of an entire Banach-algebra exponential family.

`CompactSmoothCubicDefects.lean` proves compact support and smoothness
of the actual quotient defect. Its compact smooth test has exactly the
entire `L²` forcing class constructed above.

`TheCubicIncomingResidue.lean` applies the actual resolvent to the entire
incoming forcing. Its residue at `4/3` is `(17/6)MPM*F(4/3)`, lies in
a finite-dimensional range, and satisfies the `8/9` eigenvalue equation.
Nonvanishing is a separate arithmetic input.

`LocalCubicCorrectedSeeds.lean` bounds every cusp height on compact quotient
sets. The restricted incoming seed is an entire `L²` family; adding the
resolvent correction gives a meromorphic family with the restricted residue.

`Sobolev/CompactSmoothParameterSums.lean` bounds all spatial derivatives
of jointly smooth families on compact parameter and support sets. Summable
scalar weights give a smooth sum, with every derivative computed termwise.

`SpatialSmoothnessOfTheCubicEisensteinSeries.lean` normalizes cusp rows onto
a compact unit-energy sphere. The convergent base-point series supplies
the scalar weights, proving spatial smoothness of the actual series for
`Re s>2` and termwise derivatives of its compact regularizations.

`CubicEisensteinDerivatives.lean` identifies each regularized family with
the actual series near a positive-height point. Every spatial derivative
therefore commutes with its row sum. The height-profile equation gives
the Laplace eigenvalue of each individual summand.

Theta identification and uniform contracting mean-square descent remain
unproved here. No global cancellation
estimate or zero-free half-plane is asserted by this module.

The arithmetic and quotient analysis draw on the [OpenAI metaplectic argument](https://github.com/openai/math/blob/main/preprints/The-Quasi-Riemann-Hypothesis-October-5-2026/paper2.pdf). Source attribution is in `NOTICE`; license is in `LICENSE`.

`TheCubicEisensteinEquation.lean` proves the actual Eisenstein series is smooth and satisfies its Laplace equation for Re s > 2. Termwise first and second axis derivatives follow from the summable multilinear jets.
