# Scalar modular bootstrap and arithmetic resonances

- **ID:** W11
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** [W11](../../../reports/review-0711/obstacles-summary.md#w11-ads₃-modular-bootstrap)
- **Statement:** Derive a scalar spectral remainder bound from actual torus partition functions, with a proved noncancellation mechanism for every arithmetic resonance.

## Mathematical boundary

The scalar projection kills cusp forms. It does not kill Eisenstein resonances automatically.
At radius-dependent central charge one, the completed Eisenstein factor cancels the zeta denominator: this family cannot detect RH. Central charge two instead has a product of completed Eisenstein functions divided by a completed zeta factor. Noncancellation must be proved, including multiple zeros.

The corpus's single-Eisenstein detection theorem now extends to the product:
[full pole multiplicity survives both pointwise detection and double horocycle averaging](../3-formalized/ads3-eisenstein-product-detection.md).

## Conjectures and obligations

1. **Product-kernel coverage — proved in Lean.** At every zero of `ξ(1+2u)`, the product kernel has a pole of the full multiplicity for some pair of moduli on each prescribed pair of horocycles. Its double horocycle numerator average is explicitly nonzero.
2. **Actual partition identity — formalized.** The convergent Narain sum, scalar projection, general two-modulus Dirichlet and Mellin formulas, and the scalar Mellin continuation into the pole-detecting kernel are proved in Lean. [Independent modularity and all three pairwise moduli exchanges](../3-formalized/ads3-narain-three-moduli-symmetry.md) are proved. The [regularized fundamental-domain overlap](../3-formalized/ads3-narain-regularized-overlap.md) equals this actual Mellin transform, with exact vacuum and scattering counterterms.
3. **Source estimate.** For every pair of central-charge-two target moduli, derive
   `yΣ_scalar exp(−2πΔy) − [y−(3/π)log y+B] = O_ε(y^(3/4−ε))`
   as `y→0+`, for every `ε>0`, with the vacuum included and `B` the exact
   [constant term](../3-formalized/ads3-narain-principal-part.md). The loss `ε` permits logarithmic factors from multiple zeros.
   The Mellin bridge from even one fixed target average to RH is now
   formalized. The bound itself remains open.
4. **[Pole-forced decay boundary — proved in Lean](../3-formalized/ads3-narain-pole-decay-boundary.md).** At each arithmetic zero `ρ`, some target
   pair on every prescribed pair of horocycles admits no scalar
   remainder bound `O(y^α)` with `α>1−Re ρ/2`, after subtraction of any
   constant and logarithmic main terms. Such a bound would make the
   remainder Mellin transform holomorphic across the detected pole;
   the main terms have poles only at `s=1`. The corpus's
   `BlackHoleRingdown/TheHorocycleReadsTheZeros.lean` supplies the
   decay-to-holomorphy and analytic-uniqueness mechanism. The Narain
   source's [local integrability and exponential large-height bound](../3-formalized/ads3-narain-heat-regularity.md),
   logarithmic Mellin subtraction and analytic uniqueness are all
   formalized. Any positive-power expansion also forces logarithmic
   coefficient `−3/π`. No small-height rate is supplied by this obstruction.

For the RH implication, one fixed
[double target-horocycle average](../3-formalized/ads3-narain-target-average.md)
at any prescribed positive heights suffices. Its actual Mellin transform
is the explicit mean, with target/height norm-Fubini fully proved.
The uniform square-target heat majorant uses
`K*=YZ(2Z²+3)Z⁻²(2+3Y⁻²)` and the mass bound
`M²≥(|n|²+|w|²)/K*`. It also proves continuity and exponential
large-height decay of the average. Every arithmetic pole survives.
The [fixed-source decay obstruction](../3-formalized/ads3-narain-average-pole-decay-boundary.md)
is formalized: rates `y^(1−σ₀/2−ε)` for every positive `ε` exclude xi
zeros with `Re s>σ₀`. At `σ₀=1/2`, this proves the rate-to-RH implication.
The [exact mean constant and weighted residue](../3-formalized/ads3-narain-average-principal-part.md)
are formalized, including rigidity of both main coefficients. The
[converse rate implication](../0-backlog/ads3-narain-average-sharp-rate.md) and
[universal-profile scaling identity](../0-backlog/ads3-narain-average-scaling.md)
remain targets.

The unconditional [half-power boundary rate](../3-formalized/ads3-narain-average-boundary-rate.md) is formalized: the actual remainder is `o(y^(1/2))`. The [quantitative saving](../3-formalized/ads3-narain-quantitative-boundary-saving.md) is also proved: with `L=−log y`, the remainder is bounded by `C√y exp(−cL/[(log L)^(2/3)(log log L)^(5/3)])`. The moving contour retains the full Vinogradov–Korobov width. The [universal-constant refinement](../3-formalized/ads3-narain-universal-saving-constant.md) fixes `c=1/(128·10^8)` independently of target heights. Consequently [every logarithmic saving](../3-formalized/ads3-narain-average-logarithmic-savings.md) holds: `R=o(√y/L^N)` for all `N≥0`.

[Schwartz regularity of the actual boundary and clock remainder](../3-formalized/ads3-narain-boundary-schwartz.md) is formalized. Both literal functions have all absolute polynomial moments, and the clock integral vanishes. Spectral moments, the two source tails, Landau interpolation and pointwise Fourier inversion prove these statements. The corresponding [pointwise saving at every target pair](../0-backlog/ads3-narain-pointwise-boundary-saving.md) should follow from the existing sharp Fourier-tail envelope and the full filled numerator.

The [common derivative bound](../3-formalized/ads3-narain-logarithmic-derivative-saving.md) is formalized: every order satisfies `|H^(n)(L)|≤C n! (16/π)^n exp(−Lw(L)/128)` with one threshold and prefactor independent of derivative order. A uniform complex disk estimate and Cauchy bounds prove the literal source statement.

The [central classification](../3-formalized/ads3-narain-central-order-classification.md) is formalized. With `Y*=exp(2−4 Re ξ′(1))`, the mean has order `1+2·1_{Y=Y*}+2·1_{Z=Y*}` at `u=0`. The exceptional target cubic jet is nonzero because `(logDeriv ξ)″(1)` is real and strictly negative. Every arithmetic pole still survives at every target height.

[Every physical Mellin boundary moment](../3-formalized/ads3-narain-central-moment-sum-rules.md) is formalized:
`∫₀∞ y^(−3/2+it)(log y)^n R(y)dy=M^(n)(it)`, absolutely convergently.
The first nonzero central moment has index one, three or five according
to the exceptional-height count. Its cubic and quintic coefficients are
explicit; the doubly exceptional fifth moment is strictly positive.
At fixed `P=YZ`, the first moment is exactly
`4√P[(c−(log P)/2)²−((log Y−log Z)/2)²]`.

## Product detector: formalized

Put `D(u)=ξ(1+2u)`, `N(u;x,Y)=D(u)E(1/2+u;x+iY)` and
`K(u;z,w)=N(u;z)N(u;w)/D(u)`. These use the corpus's actual Eisenstein function.
Its constant term is

`C_Y(u)=Y^(1/2+u)D(u) + ((1+2u)/(2u−1))ξ(2u)Y^(1/2−u)`.

At an actual resonance `p`, `−1/2<Re p<0`. Consequently `1+2p`, `2p−1`,
`ξ(2p)` and `Y^(1/2−p)` are all nonzero. Thus `C_Y(p)≠0` for every `Y>0`.
The iterated average of `K` on two horocycles equals `C_Y C_Z/D`.
The numerator is analytic and nonzero at `p`, so this average has exactly the
negative of the zero order of `D`. Separately, each nonzero constant term forces
a point with `N(p;x,Y)≠0`; choosing one on each horocycle gives the same full
pole order for the pointwise product. Multiple zeros require no extra assumption.

**[Normalization: formalized](../3-formalized/ads3-narain-mellin-continuation.md).** In the variable `s=1/2+u`,
`Λ(s)=π^(−s)Γ(s)ζ(2s)` and `ξ(2s)=s(2s−1)Λ(s)`.
The literature's Rankin–Selberg normalization is `2K/[u(1+2u)]`. This
elementary factor is nonzero at arithmetic resonances. The actual scalar
Mellin transform `2Λ(s)E_s(ρ)E_s(σ)` equals this quotient on `Re s>1`.
`NarainMellinContinuation.lean` proves global meromorphicity, the exact
partition-projection identity and full pole multiplicity for the actual
source continuations. At unit target heights the average is
`2L₊+4L₋+2L₋²/L₊`, where `L₊=Λ(s)`, `L₋=π^(1/2−s)Γ(s−1/2)ζ(2s−1)`.

## Lattice source

For the square two-torus, scalar charges are `n,w∈ℤ²` with `n·w=0`.
For `w≠0`, the unique parametrization is
`n=d(a,b)`, `w=c(−b,a)`, `c>0`, `gcd(a,b)=1`.
The energy factors as `(c²+d²)(a²+b²)`. The `w=0` contribution is separate.
The exact square-target Dirichlet identity is now formalized:

`Σ'_{n·w=0} (|n|²+|w|²)^(−s) = L(s)²/(2ζ(2s))`,

where `L(s)=Σ'_{(a,b)∈ℤ²}(a²+b²)^(−s)` and `Re s>1`.
The [orthogonal-charge bijection and energy factorization](../3-formalized/ads3-scalar-charge-coordinates.md)
are formalized in `ModularBootstrap/ScalarChargeCoordinates.lean`.
The [zero-winding split, absolute convergence and infinite-sum reindexing](../3-formalized/ads3-square-torus-dirichlet.md)
are formalized in `ModularBootstrap/SquareTorusDirichlet.lean`, including
the normalization `S(s)=2ζ(2s)E(i,s)²`.

For general moduli `σ=x+iy`, `ρ=B+iV`, set
`Qσ(v)=(yv₁)²+(v₂−xv₁)²` and `Jw=(w₂,−w₁)`. The source mass is
`M²=[Qσ(n+BJw)+V²Qσ(Jw)]/(Vy)`.
Primitive scalar coordinates give
`M²=Qσ(a,b)[(d+Bc)²+(Vc)²]/(Vy)`.
The [general-modulus Dirichlet identity](../3-formalized/ads3-narain-dirichlet-product.md)
is formalized in `EpsteinLatticeDecomposition.lean` and `NarainDirichlet.lean`:
`S_(ρ,σ)(s)=2ζ(2s)E_s(ρ)E_s(σ)` for `Re s>1`, with absolute convergence.
Positive-gcd decomposition and central reflection give the exact axis
cancellation; primitive reflection handles the target quadratic's sign convention.
The [general mass identities and bounds](../3-formalized/ads3-narain-mass-bounds.md)
are formalized in `NarainMass.lean`: chiral positivity `M²≥2|n·w|`,
the scalar factorization, and
`|n|²+|w|²≤KM²`, where
`D=(2y²+1+2x²)/y²`, `K=VyD[2+(2B²+1)/V²]>0`.
Every nonvacuum mass satisfies `M²≥1/K`.

**Selection boundary.** Corpus theorem
`LatticeSectionTheory.exists_epsteinLambda_eq_zero` gives real off-line zeros
for rectangular Epstein functions with aspect ratio greater than `e²`.
Positive lattice counting and Poisson duality therefore cannot justify
zero-freeness of a fixed-modulus numerator. Universal detection uses the
proved horocycle family, not such a zero-freeness claim.

[Absolute convergence, modular translation and exact scalar projection](../3-formalized/ads3-narain-partition-projection.md)
follow from Gaussian domination. [Full modular invariance and Poisson
triality](../3-formalized/ads3-narain-modular-inversion.md) are formalized:
momentum Poisson summation exchanges target area and worldsheet moduli;
the target charge permutation then gives worldsheet inversion, and the
standard generators give `SL₂(ℤ)` invariance. The [positive majorant, angular norm control and cusp bounds](../3-formalized/ads3-narain-partition-cusp-bounds.md)
are formalized. Angular norm integration reduces overlap convergence to
scalar Mellin convergence for `Re s>1`; linear cusp growth controls the
remaining Eisenstein tail. These estimates supply no small-height RH rate.

The [actual scalar Mellin identity](../3-formalized/ads3-narain-scalar-mellin.md)
is formalized in `NarainMellin.lean`:
`Mellin[y⁻¹∫₀¹ Z(x,y)dx−1](s)=2π^(−s)Γ(s)ζ(2s)E_s(ρ)E_s(σ)`
for `Re s>1`. Every Mellin interchange premise is discharged by the proved
mass positivity and absolute Dirichlet convergence.

For contour estimates, the corpus already proves sharp Gamma decay of the
Whittaker tails and `exists_eisenstein_strip_le` in
`BlackHoleRingdown/ThePolynomialGrowthOfTheEisensteinFunction.lean`.
Its `exists_exp_mul_norm_inv_xi_le` reduces the remaining strip weight to
polynomial growth of `1/ζ(1+2u)`. Thus the pointwise contour argument does
not need a new Bessel decay theorem. Mellin inversion and
the source rate still require formal proofs; the RH-strength zero-free
region cannot be assumed as an unconditional input.
The [exact principal part](../3-formalized/ads3-narain-principal-part.md) is formalized.
Its enlarged analytic domain uses the proved [removable central zero](../3-formalized/ads3-narain-central-zero.md).

## External audit

- [Benjamin–Collier–Fitzpatrick–Maloney–Perlmutter, 2021](https://arxiv.org/html/2107.10744): explicit central-charge-one and two spectral decompositions.
- [Benjamin–Chang, 2022](https://arxiv.org/html/2208.02259): scalar crossing and its RH remainder; Appendix C distinguishes central charges one and two.
- [Benjamin–Chang–Fitzpatrick–Ramella, 2025](https://arxiv.org/html/2505.18314): general CFT extension. Equation (3.24)→(3.26) assumes an integral interchange; the converse RH reading requires nonzero overlaps. These are obligations, not available Lean inputs.
- [Perlmutter, 2025](https://arxiv.org/html/2509.21672): §10.2 identifies the Narain core spectrum with primitive lattice dilations; at central charge two the core quotient is `2E_s(ρ)E_s(σ)`. Appendix D asks whether arithmetic poles must survive and gives a conditional argument for at least one. Its convergence and residual-spectrum assumptions do not supply universal pole coverage or a zero-location bound. The product detector addresses coverage for the explicit two-modulus kernel, without assuming simple zeros.

## Gates

- [x] 0 → 1: concrete source and noncancellation question.
- [ ] 1 → 2: dependency-closed paper proof of the partition identity and source estimate.
- [ ] 2 → 3: remainder bound and RH bridge formalized, with direct Lean checks, transitive axiom audits and umbrella imports.

No RH bound, unitarity-to-RH implication, or complete route is claimed.
