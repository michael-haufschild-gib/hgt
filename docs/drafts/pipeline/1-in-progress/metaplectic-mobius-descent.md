# Metaplectic conversion of Möbius coefficients

- **ID:** metaplectic-mobius-descent
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Statement:** Sextic Poisson transformation converts ideal Möbius coefficients over the Eisenstein integers into cubic theta coefficients; a second transformation may close a contracting mean-square descent.

## Target

Prove an unconditional source estimate beyond absolute convergence. The candidate external estimate is
`Σ_{0<N(u)≤D^(1+θ)} |Σ_n μ_K(n)(u/n)_6 W(N(n)/D)|² ≪ D^(2+θ+ε)`
for every fixed `θ, ε > 0` and smooth compactly supported `W`, with columns
indexed by primary generators outside a fixed finite set of exceptional
prime ideals. Sixth-power
rows retain `gcd(n,b)=1`; averaging over `b` produces the totient-weighted
coefficient `μ_K(n)φ(n)/N(n)` and the `11/12` exponent. The external final
bridge uses its corrected Euler product and Mellin continuation to exclude
zeta zeros. It does not identify ideal Möbius sums with rational-integer
Möbius sums. Neither the estimate nor this full bridge is established locally.

## Arithmetic mechanism to audit

1. Normalized cubic Gauss sums satisfy `γ₂(n)³ = μ_K(n) α(n)` on squarefree primary elements.
2. Hasse–Davenport converts `μ_K(n) γ₋₁(n)` to cubic theta coefficients, up to a fixed ray-class factor.
3. Theta completion adds cube indices. Möbius inversion removes them.
4. Two Poisson transformations, with a positive enlargement between them, produce a smaller row range. Regrouping divisor terms before absolute values forces `f′ | k′`.
5. Required transfer bounds must control transformed weights uniformly; scale contraction alone proves no estimate.

## Status and sources

The global mean-square estimate has no local dependency-closed proof. Corpus searches found no matching source estimate. External endpoints and their transitive analytic dependencies require audit before reuse.

The [frontier review](../../../reports/review-0711/route-obstacles.md)
separates classical cubic spectral theory (A33) from the cancellation
transfer (B94). The target here is the uniform mean-square estimate above;
continuation and coefficient identification are prerequisites. Generic
spectral positivity supplies neither the signed transfer nor its uniformity.

The following arithmetic statements are formalized in
`MetaplecticMobiusDescent/`, with direct Lean checks and standard-axiom audits.

| Module | Exact result |
|---|---|
| `TheSexticCharacterBecomesQuadratic` | Full Gauss-product conversion; quadratic output, unit norm, and exceptional zero frequency. |
| `ThePrimaryCubicGaussSumFixesTheSign` | Canonical primary generator; `J(χ_p,χ_p)=−p` and `γ_p³=−p/‖p‖`. |
| `CubingTheCompositeGaussSumRecoversMobius` | Actual CRT factorization; `γ(I,ψ)³=μ(I)p/‖p‖` for every primitive `ψ`. |
| `MobiusBecomesACubicGaussCoefficient` | `μ(I) conjugate(G₁)=c(I,ψ)G₂`, with explicit `‖c(I,ψ)‖=1`. |
| `CubicReciprocityFromFrobenius` | Cubic reciprocity for primary generators at distinct residue characteristics. |
| `TheCubicPhaseLivesModuloTwo` | Product of sextic values at four is the fixed cubic character `(p/(2))₃`. |
| `TheDifferentNormalizesTheTraceCharacter` | Different `(1+2ω)`; primitive analytic character `exp(2πi Tr(x/[p(1+2ω)]))`; exact Möbius conversion for this character. |

`EisensteinCoordinates` proves the intrinsic coordinate trace and norm form.
The Gaussian transform, residue-class Abel mass, and vanishing dual-phase
error prove the exact quadratic trace Gauss evaluation
`G(a+bω)/‖a+bω‖=(1+i^(−b)+i^a+i^(b−a))/2` for every nonzero modulus.
See [quadratic phase](../3-formalized/quadratic-trace-gauss-phase.md).

`TheAnalyticConversionHasAFixedRayPhase` identifies the composite quadratic
sum with the actual trace square sum and proves
`μ(I) conjugate(G₁)=R(p)(‖p‖/p)G₂`, with `R` fixed modulo four, of unit norm,
and one on the principal class. Six endpoint audits use only standard axioms.

`CubicReciprocityAtACommonCharacteristic` closes prime cubic reciprocity:
primary factorization of `−(p+q)` handles primes above the same rational prime.
The prime-cover bound follows from the quadratic extension degree.

`CubicJacobiSymbols` constructs the composite symbol and proves reciprocity
with arbitrary multiplicities, including common factors.

The ramified supplementary laws now give `(ω/p)₃=ω^(2A−B)`,
`(λ/p)₃=ω^A`, and `(1+2ω/p)₃=ω^(−B)` for every primary
`p=1+3A+3Bω`. Denominator congruence modulo both nine and the numerator is
also proved.

`TheCubicKubotaMultiplier` constructs the actual nontrivial cubic character
on `Γ(3)`. Its image is all cubic roots; its kernel has relative index three
and finite index in `SL₂(O)`.

`TheCubicMultiplierExtendsOverRationalMatrices` extends the character
trivially across rational matrices and proves that the larger group normalizes
the finite-index metaplectic kernel.

The actual hyperbolic quotient and Bianchi reduction are constructed.
The cubic kernel quotient has a compact core and finitely many cusp tails;
this topological cover alone supplies no Sobolev estimate.

The actual cubic Eisenstein series is absolutely convergent and holomorphic
for `Re s>2`, with character automorphy. The cubic quotient now has a
measurable fundamental selector and positive finite invariant volume.
Its completed energy space has a closed gradient, faithful mass embedding,
and [compact mass restriction](../3-formalized/cubic-kernel-local-sobolev-compactness.md)
to every compact quotient set. The [actual exterior coercivity estimate](../3-formalized/cubic-quotient-exterior-coercivity.md)
is formalized with compact error map.
The [meromorphic resolvent](../3-formalized/cubic-meromorphic-resolvent.md)
is constructed at spectral value `8/9`, hence at Eisenstein parameter
`4/3`. The [incoming spectral residue](../3-formalized/cubic-incoming-spectral-residue.md)
is identified as `(17/6)MPM*F(4/3)`, globally in `L²` and after compact
restriction of the corrected seed. [Initial source matching](../3-formalized/cubic-initial-resolvent-matching.md)
and [constant-term nonvanishing](../3-formalized/cubic-constant-term-nonvanishing.md)
prove that the actual residue is a nonzero `8/9` Laplace eigenvector.

`WeightedCubicResidualFourierTests` identifies every bounded height-weighted
residual Fourier test on every compact positive height interval, including
the arithmetic constant mode (`kernelCuspIntervalFourier_residue_full`).
The actual coefficients satisfy `|c_h| ≤ C_ε exp(ε|frequency(h)|)` for every
`ε>0` (`cubicResidualFourierCoefficient_subexponential`). Exponential Bessel
decay gives an absolutely convergent nonconstant Fourier series, continuous
at every positive height (`cubicResidualNonzeroSeries_continuousOn`).
Fourier completeness identifies this series with the actual residual vector
(`cubicEisensteinResidue_continuous_representative`), giving pointwise cubic
automorphy (`cubicResidualFunction_automorphy`).

Ramified support forces `uλ^n | 3h` and, for `h ≠ 0`, `3^n ≤ 9N(h)`
(`ramified_arithmetic_support`, `ramified_arithmetic_norm_bound`).
CRT and frequency twists factor the actual residue sum into its ramified
part and an unramified cubic Gauss sum
(`arithmeticResidueSum_coprime_product`). Character orthogonality evaluates
the ramified factor exactly (`ramified_arithmetic_character_test`). Absorbing
the CRT twist into frequency `9ah` gives a finite decomposition into
unramified Gauss series (`arithmeticDirichletSeries_finite_gauss`), absolutely
convergent for `Re s > 2`.

Finite rational averaging acts contractively on the actual quotient L² space
(`kernelRationalSourceProjection_norm_le`). Its continuous residual
representative has the extended cubic automorphy law
(`cubicSourceResidualFunction_represents_projection`,
`cubicSourceResidualFunction_automorphy`).

A nonzero Gauss sum modulo `p^(n+1)` forces `p^n | h`, for every nonzero `p`
(`cubicUnitGaussSum_power_support`). At a primary prime and a coprime
frequency, the geometric Gauss sum satisfies `G(h,p)^3 = −p N(p)`
(`cubicUnitGaussSum_prime_cube`). Conductor lifting evaluates all prime-power
Gauss sums through residue-field characters (`cubicUnitGaussSum_prime_power_lift`);
the two nontrivial prime factors multiply to `N(p)`
(`primeCubicGauss_one_mul_two`). Splitting ideals into a prime power and a
prime-deleted factor gives a finite local expansion and the exact recurrence
`D(s,hp³) = (1+N(p)³N(p)^(-3s))D(s,h) − N(p)^(-s)G(h,p)D(s,hp)`
for `p ∤ h` and `Re s > 2`
(`unramifiedCubicGaussSeries_prime_recurrence`). The conductor shift also gives
`D(s,hp⁶) = (1+N(p)³N(p)^(-3s))D(s,hp³) − N(p)³N(p)^(-3s)D(s,h)`
at every frequency (`unramifiedCubicGaussSeries_cube_recurrence`).

Opposite-cusp Fourier unfolding identifies this Gauss series with a bounded
test of the continued automorphic source (`oppositeEisenstein_fourier`,
`continuedUnramifiedGauss_residue_limit`). Analytic uniqueness transfers the
prime, cubic, and square-cubic recurrences to the actual Gauss residues
(`unramifiedGaussResidue_prime_recurrence`,
`unramifiedGaussResidue_cube_recurrence`,
`unramifiedGaussResidue_square_cube`). Finite ramified summation gives the
same recurrences for the original arithmetic Dirichlet series and its actual
scattering residues (`nonzeroScatteringResidue_prime_recurrence`,
`nonzeroScatteringResidue_cube_recurrence`,
`nonzeroScatteringResidue_square_cube`), with prime factor `G(9h,p)`.
All these statements passed a direct Lean check.

The modular generator relations reduce rational averaging to four cusp
translates (`rationalSourceProjection_four_cusps`). The actual residue inherits
the initial family's translation and central symmetries, giving the same
four-cusp formula pointwise (`cubicSourceResidualFunction_four_cusps`). These
identities passed Lean without enumerating the finite quotient.

The source's nonconstant Fourier factor is
`(A(s,h) + (1+e(h)+e(2h))D(s,9h))/4`, where
`e(h)=tracePhase(cuspFrequency h)` (`rationalSourceEisenstein_fourier`).
Primary multiplication preserves this phase, so the source factor inherits
all three prime recurrences. Opposite-cusp tests on every positive height
interval identify its actual Bessel coefficients and prove subexponential
growth (`rationalIntervalFourier_opposite_bessel`,
`oppositeResidualFourierCoefficient_subexponential`). Continuity upgrades the
interval identities to every positive height; the projected source has the
explicit Bessel coefficient `(c(h)+(1+e(h)+e(2h))c₀(h))/4`
(`cubicSourceResidualFunction_fourier_bessel`), also of subexponential growth.
These statements passed a direct Lean check.

The ramified constant factor is `2/(3^(3s−3)−1)`
(`arithmeticDirichletSeries_zero_unramified`). Its value at `s=4/3` is one,
so opposite and original cusp constant residues agree. The projected source
therefore has the same nonzero constant term
(`oppositeCuspResidue_zero`, `cubicSourceResidualFunction_fourier_zero`,
`cubicSourceResidualFunction_ne_zero`), checked in Lean.

Rational pullbacks extend isometrically to the completed energy graph and
commute with the variational resolvent. The nonzero projected source is an
actual `8/9` eigenvector
(`kernelRationalSourceProjection_cubicEisensteinResidue_eigenvector`).
Moving-cutoff residue pairings are independent of cutoff. The defect grows
as `A²`, so cubic cusp decay makes its pairing tend to zero. Thus a decaying
`8/9` eigenvector is orthogonal to the actual Eisenstein residue and, with
decay at every integral cusp, to the projected source
(`cubicEisensteinResidue_orthogonal_of_rapid_cusp_decay`,
`cubicSourceResidue_orthogonal_of_integral_cusp_decay`). These statements
passed Lean. Self-pairing reduces vanishing of a finite correspondence sum
to these orthogonality conditions (`commonCover_source_span_vanish`);
its common-cover and adjoint-trace hypotheses still need construction.

The actual projected source has an absolutely convergent Fourier expansion
at every positive height (`cubicSourceResidualFunction_fourier_expansion`).
The nonconstant part is uniformly `O(v⁻³)` for every fixed lower height
`v ≥ a > 0` (`cubicSourceResidualFunction_cusp_decay_from_height`): the
lattice frequency gap and exponential Bessel bound absorb the height
factor. Both statements passed Lean.
The source's actual arithmetic residues satisfy the prime, cube, and
square-cube recurrences (`rationalSourceScatteringResidue_prime_recurrence`,
`rationalSourceScatteringResidue_cube_recurrence`,
`rationalSourceScatteringResidue_square_cube`), also checked.

At the two ramified representatives, translation by `3(A+Bω)` has character
`ω^(A+B)` and `ω^(-A-B)`, respectively. Period nine is therefore untwisted,
and each ramified constant Fourier mode vanishes
(`ramifiedSourceFunction_omega_constant_zero`,
`ramifiedSourceFunction_omega_sq_constant_zero`), checked in Lean.
Finite integral covers have pushforward volume equal to covering degree
times base volume, and trace after pullback equals that degree times the
identity (`integralCoverMap_measure`, `integralCoverTrace_pullback`), also
checked.

The Hilbert trace is the finite sum over actual covering fibers
(`integralCoverTrace_representative`). Conjugate subgroup quotients are
isometric in `L²`; a correspondence leg's adjoint is inverse conjugation
followed by this trace (`kernelCoverLeg_adjoint`,
`kernelCoverLegAdjointFunction_represents`). Uniform inverse-cusp decay
passes to that adjoint with the covering degree as factor
(`kernelCoverLegAdjointFunction_cusp_decay`). These constructions passed
Lean.

Finite covering maps are proper. Their correspondences preserve smooth
compact support, satisfy the energy bound `E(Qf) ≤ deg(H) deg(J) E(f)`,
and have the reverse correspondence as Dirichlet-form adjoint
(`integralCoverMap_isProperMap`, `kernelCorrespondenceTest_energy_le`,
`kernelCorrespondenceForm_adjoint`), checked in Lean. The correspondence
extends to the completed energy graph, commutes with the variational
resolvent, and preserves eigenspaces
(`kernelCorrespondence_variationalResolvent`,
`kernelCorrespondence_eigenvector`). Common-cover adjoint sums therefore
preserve the source eigenvalue
(`kernelCoverLeg_adjoint_sum_eigenvector`), also checked.

An integral diagonal correspondence has finite-index projections because
each contains its principal congruence subgroup. Restricting both
projections to the multiplier kernel preserves finite index
(`integralDiagonalKernel_finite_covers`), checked in Lean. No separate
character-invariance identity is needed for these covers.
The translated cube-dilation branches now have a concrete common cover,
finite-index targets, intertwining subgroup isomorphisms, and bounded
`L²` legs (`cubeCommonCover_finiteIndex`, `cubeCommonTarget_finiteIndex`,
`cubeCommon_intertwines`, `cubeCommonLeg`), checked in Lean.

Zero cusp averages are a weaker sufficient input for residual
orthogonality: unfolding pairs each average with a height-only cutoff
defect, and `kernelEisensteinResidueVector_pairing` then gives zero.
Finite-trace unfolding proves orthogonality from zero cusp averages;
nonzero integral dilation preserves these averages by Haar uniqueness on
the cusp torus (`cubicSourceResidue_orthogonal_of_zero_enlarged_cusp_averages`,
`period_integral_eisenstein_affine`). Actual common-cover adjoint sums
therefore vanish once their enlarged cusp averages vanish
(`kernelCoverLeg_source_sum_vanish_of_zero_enlarged_averages`). These
statements passed Lean. Only matrices in `rationalExtension` enter the source
pairing. For primary `p`, the integral matrices representing either
direction of a cube branch are the identity modulo three. Dividing a
first column by its common factor `p^j` preserves that congruence;
`exists_congruent_cusp_completion` then preserves the rational cusp class.
This removes the need for all-cusp classification or ramified pointwise
decay in cube removal. Forward and inverse normalization are checked in
Lean (`primePowerCusp_reduction`, `primePowerCusp_inverse_reduction`), for
every prime-power exponent. At a primary upper-left entry the extended
character is the cubic symbol of the first column
(`extendedComplexCharacter_primary`), also checked. The two interior valuation
strata have zero cubic Gauss sum; the endpoint height weights are `N(p)⁻¹`
and `N(p)`, and the weighted phase sum is exactly `N(p)²`
(`actualCubeCuspPhaseSum_height`, checked). Every rational cusp becomes primary
under translation by one and a central sign (`rationalCusp_primary_normalization`,
checked). The cube difference therefore has zero mean on each `p^3` cusp cell.
For adjoint traces, scale `p^6` gives a common averaging cell: an inverse
branch has horizontal scale `p^(2j-3)`, so its image is a translate of the
`p^3` cell dilated by `p^(2j)`. Zero averages pass through each finite fiber
sum, forcing the actual common-cover difference to vanish. These steps and
the actual cube eigenrelation now pass Lean
(`cubeSourceDifference_inverse_rational_average_zero`,
`kernelCoverLegAdjointFunction_rational_average_zero`,
`cubicSourceResidualFunction_cube_eigenrelation`). Fourier transport sends
frequency `h` to `hp^3` and height `v` to `v/|p|^3`
(`cubicSourceResidualFunction_fourier_cube`, checked). Its exact height
weight cancels the eigenvalue, giving arithmetic cube removal
(`rationalSourceScatteringResidue_mul_prime_cube`, checked). The local
prime-power table is now exact: exponents zero modulo three retain the
base residue, exponents two vanish, and exponents one give
`N(p)^(-2/3) G₂(9h,p)` times the base residue
(`rationalSourceScatteringResidue_prime_power_table`, checked). Cube removal
also holds for every primary multiplier, without a coprimality restriction
(`rationalSourceScatteringResidue_mul_primary_cube`, checked).

The Fourier normalization converts the first-power factor to the conjugate
normalized cubic Gauss sum. Coprime products recover the composite Gauss
sum with its exact cubic twist. Every nonzero unramified coefficient has
squarefree-times-cube support; on this support its conjugate equals
`star(T(1)) |b| star((9/a)₃) G(a)/|a|` for the primary factorization
`h = ab³`, with squarefree `(a)`
(`rationalSourceResidualFourierCoefficient_squarefree_cube`,
`rationalSourceFourier_squarefree_cube_support`, checked). The normalization
is nonzero (`rationalSourceThetaScalar_ne_zero`, checked): otherwise Fourier
support would lie in `3O`, giving full Eisenstein translation symmetry,
which contradicts the lower cusp's cubic character. The phase `(9/a)₃`
equals the different symbol `((1+2ω)/a)₃`. The support is exact and the
coefficient magnitude is `|T(1)| |b|`
(`normalized_sourceFourier_squarefree_cube`,
`sourceFourier_squarefree_cube_support_iff`,
`sourceFourier_squarefree_cube_norm`, checked).

The Bessel Mellin identity is now formalized:
`∫₀∞ x^(s−1) K_(1/3)(x) dx = 2^(s−2) Γ((s−1/3)/2) Γ((s+1/3)/2)`
for `Re s > 1/3`. The Schläfli mixture is absolutely integrable: integrate
the positive Gaussian majorant first, leaving a Gamma density in the
mixture parameter. Fubini then gives the two Gamma factors
(`schlafliBesselK_cubic_mellin`, `source_cubic_bessel_mellin`, checked).
Prime valuations give unique squarefree-times-cube indexing of every
primary-supported Fourier sum. Multiplying by the different symbol cancels
the theta coefficient's phase, leaving the normalized cubic Gauss sum
(`fixedThetaTwist_source_tsum`, checked). For a character modulo `c`, this
twist is a concrete function modulo `9c` (`finiteThetaTwist_mk`, checked).
Finite Fourier inversion realizes it through rational translates of the
actual source (`finiteThetaTwist_source_bessel`, checked). Horizontal
differentiation multiplies each mode by its conjugate frequency;
exponential Bessel decay makes the first frequency moment summable
(`finiteThetaTwist_source_wirtingerBar`, checked). The Schläfli derivative
is dominated, uniformly for `x ≥ δ > 0`, by
`(4/δ) exp(−x/2) t^(−2/3) exp(−t/2)`. This proves joint differentiability
of the actual source and every fixed cusp translate. At a cusp `a/c`, inverse coordinates
have horizontal differential `h ↦ −conj(h)/(c²v²)` and zero vertical
differential. Consequently cusp inversion swaps the two Wirtinger
derivatives with factor `−1/(c²v²)`
(`cubicSourceResidualFunction_cusp_derivative`,
`conjugate_cubicSourceResidualFunction_cusp_derivative`, checked).

The complex embedding has unspecified orientation. Primitive trace characters
parametrize every additive character of `O/(3)`, so each ramified cusp row has
one intrinsic Fourier support class (`ramifiedScaledRow_fourier_support`, checked).
For `r=uλⁿ` and primary `a`, the additive phase in `(r/(a+3x))` determines
the support condition `3k=h₁+phase(r)a`; its contribution cancels modulo `a`,
leaving the Gauss frequency `3r²h₁`. Finite-index unfolding gives the exact
unit-cusp Fourier coefficient (`diagonal_unit_eisenstein_fourier`, checked).
Once-ramified rows split into three primary associates. Their indexing,
character-weighted cancellation, and scaled Fourier formulas are checked
(`onceRamifiedDataEquiv`, `scaled_unit_eisenstein_fourier`,
`scaled_once_eisenstein_fourier`).
Scaling cusp coordinates by three replaces the affine denominator `q` by
`3q` and contributes `3^s`. The period congruence then holds automatically;
finite-character cancellation selects `q ∣ h` and
`3 ∣ h/q + phase(r)`, without choosing an orientation of the complex embedding.
The projected source has six Gauss branches
(`ramifiedSourceEisenstein_scaled_fourier`, checked). Compact multiplicity bounds
give a bounded pullback for every cusp matrix (`arbitraryCuspPullback`, checked).
Native scalar continuation passes finite Gauss identities to residues
(`finite_unramified_residue`, checked). This identifies every Fourier coefficient
at the two primitive ramified cusps. Their constant modes vanish; the remaining
coefficients are subexponential. Fourier uniqueness gives a normally convergent
Bessel expansion and exponential height decay
(`ramifiedScaledRow_eq_bessel`, `ramifiedSource_bessel_normal`,
`ramifiedSource_exponential_decay`, checked).
Linear frequency weights preserve subexponential coefficient growth, so the
horizontal derivative also has a normally convergent Bessel expansion and
exponential decay. Cusp inversion reflects its Mellin parameter by `s ↦ 2−s`;
splitting at height one gives two exponentially decaying Mellin tails.

For a primitive column `a=A+Bω`, `c=C+Dω`, the determinant `AD−BC` modulo three
distinguishes the three cusp classes. Nonzero determinant gives the classes
of `(1,ω)` and `(1,ω²)` directly. At determinant zero, `(B,D)` is proportional
to the nonzero vector `(A+B,C+D)`; multiplication by a power of `ω` makes
the column rational modulo three. A signed lift of one nonzero first-column
entry, followed by one translation, lifts every matrix in `SL₂(F₃)` to
`SL₂(ℤ)`. Congruence-preserving completion then gives the integral three-cusp
decomposition (`three_cusp_decomposition`, checked).
Every Eisenstein rational cusp has an entire derivative Mellin transform, with
exact reflected cusp weight (`conjugateSource_rational_cusp_mellin_entire`,
`SourceCuspDatum.mellin_reflection`, checked).
Every nonzero source coefficient has unit–ramified–squarefree–cube support;
removing the squarefree part preserves its norm, while the cube contributes
its absolute value (`rationalSourceResidualFourierCoefficient_full_squarefree_cube_support`,
`rationalSourceResidualFourierCoefficient_full_squarefree_cube_norm`, checked).
Unramified Gauss residues depend on the ramified exponent modulo three, giving
a finite norm bound for each unit–ramified family. Transferring primary-cube
invariance from the projected source to these residues still requires inversion
of the finite ramified transform.

Cubic theta identification is formalized; uniform transfer estimates remain
open locally. The common-cover argument removes the decaying `N(p)⁻ⁿ`
component allowed by the prime recurrences alone.
The arithmetic conversion alone proves no mean-square cancellation estimate.

- [OpenAI, The Quasi-Riemann Hypothesis, §§4–7 and Appendix A](https://github.com/openai/math/blob/main/preprints/The-Quasi-Riemann-Hypothesis-October-5-2026/paper2.pdf).
- [Kontorovich development](https://github.com/AlexKontorovich/quasi-rh/tree/d26d846d6f3129017f06b6fd3f78dd72d361d60b): `ElevenTwelfths.Unconditional.riemannZeta_ne_zero_of_re_gt_elevenTwelfths` is an advertised unconditional endpoint; not locally checked.
- [Rubinstein's guide](https://www.math.uwaterloo.ca/~mrubinst/quasi_rh_notes/zeta_11_12_guide.pdf), §8, explicitly separates transfer estimates from the final induction.
