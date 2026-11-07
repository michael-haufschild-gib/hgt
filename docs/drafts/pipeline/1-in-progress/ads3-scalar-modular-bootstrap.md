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
2. **Actual partition identity — partly formalized.** The convergent Narain sum, scalar projection and general two-modulus Dirichlet and Mellin formulas are proved in Lean. Establish modular inversion, the regularized fundamental-domain overlap and normalization of its continuation into the pole-detecting kernel.
3. **Source estimate.** For every pair of central-charge-two target moduli, derive
   `yΣ_scalar exp(−2πΔy) − [y−(3/π)log y+B] = O_ε(y^(3/4−ε))`
   as `y→0+`, for every `ε>0`, with the vacuum included and `B` the exact
   constant term. The loss `ε` permits logarithmic factors from multiple zeros.
   Prove the Mellin bridge from this family of bounds to RH using full pole
   coverage. The bound itself is an open target, not an input.
4. **[Pole-forced decay boundary](ads3-narain-pole-decay-boundary.md).** At each arithmetic zero `ρ`, some target
   pair on every prescribed pair of horocycles should admit no scalar
   remainder bound `O(y^α)` with `α>1−Re ρ/2`, after subtraction of any
   constant and logarithmic main terms. Such a bound would make the
   remainder Mellin transform holomorphic across the detected pole;
   the main terms have poles only at `s=1`. The corpus's
   `BlackHoleRingdown/TheHorocycleReadsTheZeros.lean` supplies the
   decay-to-holomorphy and analytic-uniqueness mechanism. The Narain
   source still needs its local integrability, large-height bound and
   logarithmic Mellin subtraction proved.

For the RH implication, the proved mean-pole theorem exposes a weaker
sufficient target: the same remainder bound for one double target-horocycle
average at prescribed positive heights. No arithmetic pole cancels in that
average. Identifying its actual Mellin transform requires uniform Gaussian
and Dirichlet bounds on the compact target intervals; these remain obligations.
For fixed heights `Y,Z>0` and horizontal coordinates in `[0,1]`, the explicit
candidate majorant is `K*=YZ(2Z²+3)Z⁻²(2+3Y⁻²)`: mass coercivity gives
`M²≥(|n|²+|w|²)/K*`. The square-target scalar Dirichlet theorem would then
dominate all target Dirichlet norms by `K*^(Re s)` times one summable series.

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

**Normalization obligation.** In the literature's variable `s=1/2+u`,
`Λ(s)=π^(−s)Γ(s)ζ(2s)` and `ξ(2s)=s(2s−1)Λ(s)`.
The literature's Rankin–Selberg normalization is `2K/[u(1+2u)]`. This
elementary factor is nonzero at arithmetic resonances. The actual scalar
Mellin transform `2Λ(s)E_s(ρ)E_s(σ)` is now formalized; matching its continuation
to this quotient remains a Lean obligation.

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

For the partition-function bridge, the corpus supplies
`IntegerLatticePoisson.summable_norm_gaussian_affine_lattice` and
`gaussian_theta_characteristics` in `HTGeometry/GaussianThetaCharacteristics.lean`.
The coercive bound dominates the actual partition terms by four Gaussian
series. [Absolute convergence, modular translation and the exact scalar
projection](../3-formalized/ads3-narain-partition-projection.md) are formalized
in `NarainPartition.lean`, with all integration-interchange hypotheses
discharged by this Gaussian bound. Poisson summation in momentum gives the Lagrangian
expression, where modular inversion is an integer reindexing of the two
winding columns; that identification remains open.
The gap controls the large-worldsheet-height cusp. It does not supply the
small-height scalar remainder required for RH.

The explicit Poisson target is
`Z(x,t)=V Σ_(m,w) exp[−πV(Rσ(m−xw)+t²Rσ(w))/(tσ₂)+2πiB det(m,w)]`,
where `Rσ(v)=|v₁+σv₂|²`. Inversion sends
`(x,t)` to `(-x,t)/(x²+t²)` and `(m,w)` to `(-w,m)`; both the quadratic
exponent and determinant phase agree. The corpus's
`IntegerLatticePoisson.gaussian_theta_characteristics` supplies Poisson
summation with affine convergence already proved. Use
`Bσ(v₁,v₂)=(σ₂v₁,v₂−σ₁v₁)`, Gaussian parameter `t/(Vσ₂)`, spatial shift
`Bσ(BJw)` and modulation `x Bσ^(−T)w`. The shift-modulation cross phase
vanishes because `Jw·w=0`; the dual phase is `B det(m,w)`, the dual norm is
`Rσ(m−xw)/σ₂²`, and the prefactor is `V/t`. The explicit linear equivalence,
determinant and inverse-adjoint identities, followed by charge-sum
reindexing, remain to be formalized.
The dual quadratic is already a Narain mass:
`[Rσ(m−xw)+t²Rσ(w)]/(tσ₂)=M²_((x,t),σ)(Jm,−w)`.
Its spin is `det(m,w)`. Thus the dual convergence follows from the same
coercive bound, and the Poisson identity is equivalently the triality
`Z_(ρ,σ)(τ)=Z_(τ,σ)(ρ)`; this equality remains to be formalized.

The [actual scalar Mellin identity](../3-formalized/ads3-narain-scalar-mellin.md)
is formalized in `NarainMellin.lean`:
`Mellin[y⁻¹∫₀¹ Z(x,y)dx−1](s)=2π^(−s)Γ(s)ζ(2s)E_s(ρ)E_s(σ)`
for `Re s>1`. Every Mellin interchange premise is discharged by the proved
mass positivity and absolute Dirichlet convergence.

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
