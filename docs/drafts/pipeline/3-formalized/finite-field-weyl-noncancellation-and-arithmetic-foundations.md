# Finite-field Weyl-sum noncancellation and arithmetic foundations

- **ID:** `finite-field-weyl-noncancellation-and-arithmetic-foundations`
- **Stage:** 3-formalized
- **Type:** CLASSICAL BRIDGE / FORMALIZATION
- **Source:** [Finite-field zeta pole transfer](finite-field-zeta-pole-transfer.md).
- **Remaining target:** [Arithmetic Eisenstein unfolding](../1-in-progress/finite-field-eisenstein-unfolding.md).

## Exact completed result

The source is the actual genus-one curve `y²=x³−x` over `F₃`, with its actual
coordinate domain `A`, fraction field `K`, extension point counts and zeta numerator.
The complete infinite affine `A₁` Weyl expansion has a meromorphic continuation
on `−1<Re(s)<2` along `λ(s)=(4−s,s)`. For every sufficiently large integer `d`,
both indexed Frobenius poles survive simultaneously, each with its original
multiplicity, at degree parameter `R=d log 3`. The argument of `weylExponent`
is `r=log R`. This is an assertion about the entire Weyl sum, not termwise poles.

The separate arithmetic foundations below are also formalized. No theorem here
identifies the Weyl expansion with an independently defined Eisenstein constant
term. No meromorphic continuation of the full Eisenstein family is claimed.
No survival claim is made at every torus point or every smaller rotation.

## Literature and scope audit

The arithmetic constant-term formula is classical: Lee–Lombardo,
[Eisenstein series on affine Kac–Moody groups over function fields](https://arxiv.org/pdf/1208.4006),
§§2–7 and Appendix A. Verdict: **BRIDGE**, with no scientific-novelty claim.
The formalized noncancellation mechanism is normal convergence plus extraction
of a nonzero leading term under increasing degree rotation. The stronger claim
that every termwise coefficient pole must survive at every torus point is not used.

## Analytic proof and exact Lean realization

This section proves the analytic noncancellation statement for the actual affine
zeta-product expansion. It does not supply the separate arithmetic unfolding.

Put `t(s)=3^(−s)`,
`N(s)=(1−t(s)/3)P(t(s))`, and
`Q(s)=(1−3t(s))P(t(s)/3)`.
The reduced factor `N/Q` agrees with `c(s)` wherever `t(s)≠1`; at the exceptional
points it represents the same meromorphic germ. Both `N` and `Q` are entire.
For an arithmetic pole `s₀`, the prior root-order theorem gives `ord Q=m>0`, and
`N(s₀)≠0`: `P(t(s₀))≠0` by the two disjoint root circles, while `t(s₀)/3≠1`.

Use the connected strip `S={s:−1<Re s<2}` and `λ(s)=(4−s,s)`.
A positive root other than `α` has argument `4n+s` with `n≥1`, or `4n−s`
with `n≥1`; both have real part greater than two throughout `S`.
On `Re z≥2`, `|t(z)|≤1/9`. The reduced rational zeta quotient is analytic on
a neighborhood of that closed disk: its possible poles have moduli `1/3` and
`√3`. Compactness gives a constant `M≥1` bounding all these other root factors.
On `S`, `|t(s)|≤3`; compactness of the radius-three disk bounds `|N(s)|` and
`|Q(s)|` by one fixed `K≥1`.

Define a regular coefficient `A_w(s)` as follows. If `α∈I(w)`, replace its factor
`c(s)` by `N(s)` and retain all other factors. If `α∉I(w)`, multiply the coefficient
by `Q(s)`. These are holomorphic on `S` and satisfy
`|A_w(s)|≤K M^(#I(w))`. Their two index-zero values are `Q(s)` for the identity
and `N(s)` for the finite simple reflection. Whenever `Q(s)≠0` and `t(s)≠1`,
`A_w(s)=Q(s)c_w(λ(s))` term by term.

For both dihedral families indexed by `n∈Z`, the degree exponent at trivial finite
and central torus coordinates is `−R(4n²+ns)`. Since `|Re s|≤2` on `S` and
`|n|≤n²` for integral `n`, its real decay is at least `2Rn²`.
Also `#I(w)≤2|n|+1`. Thus, for every fixed `R>0`,

`|A_w(s) exp(−R(4n²+ns))| ≤ K M^(2|n|+1) exp(−2Rn²)`.

This bound is summable in `n`: writing `M^x=exp(x log M)`, complete the square
and dominate by a constant times `exp(−|n|)`. The Weierstrass theorem makes the
regularized sum `H_R(s)=Σ_w A_w(s)exp(−R(4n²+ns))` holomorphic on `S`.
Consequently `H_R/Q` is meromorphic there. On `1<Re s<2` every original term is
in the Godement chamber, and absolute convergence allows the factor `Q` to pass
through the sum. Hence this quotient is the meromorphic continuation of that full
Weyl expansion on the slice, rather than a newly chosen unrelated function.

For `R≥1`, the same majorant with `R=1` is independent of `R`. Every term with
`n≠0` tends to zero as `R→∞`; the two index-zero terms remain `Q(s)+N(s)`.
Dominated convergence for the counting measure therefore gives
`lim_(R→∞) H_R(s₀)=N(s₀)≠0`. Continuity of the norm gives an `R₀` such that
`H_R(s₀)≠0` for every `R≥R₀`. The local quotient order is then exactly `−m`.
In particular this holds along `R=d log 3` for all sufficiently large integers `d`.
There are exactly two Frobenius indices; taking the maximum of their two integer
thresholds gives one threshold above which both indexed poles survive simultaneously.
The actual degree-one infinity place is constructed separately. Identification of
these analytic parameters with an adelic loop-group action is not asserted here.

This proves survival for every actual arithmetic root copy, with multiplicity. It
makes no claim that no exceptional smaller rotations or torus values can cancel a
leading coefficient. All analytical inputs above are the already proved polynomial
root circle, finite inversion sets, elementary compactness, holomorphic uniform-limit
theory, and dominated convergence. No arithmetic unfolding theorem is used.

## Arithmetic foundation proofs and Lean declarations

### The actual global field and affine integers

The affine basis `(1,y)` remains a basis after localization over `F₃(x)`, so
`[K:F₃(x)]=2`. Trace of one is `2≠0`, proving separability. The integral closure
of `F₃[x]` in `K` is Dedekind. If `z=p+qy` is integral, quadratic conjugation
makes `2p` and `p²−(x³−x)q²` integral. Integral closedness of `F₃[x]` gives
polynomial `p`; coprime denominators in `q`, together with squarefreeness of
`x³−x`, force `q` polynomial too. Thus the integral closure is exactly `A`.
Finite prime residues are finite by Zariski's lemma.

Lean: `FiniteFieldEllipticGlobalField.lean`,
`FiniteFieldEllipticIntegralClosure.lean`; in particular
`isIntegral_iff_coordinateRing_image` and
`coordinateRingEquivRingOfIntegers`.

### Infinity valuation, pole semigroup and residues

Norm degree is additive on products and subadditive on sums, giving an actual
valuation on `A` and then `K`. The values of `x,y,x/y` are respectively
`exp 2`, `exp 3`, `exp (-1)`, so `x/y` is a uniformizer.
The linear encoding `p(x)+q(x)y ↦ p(T²)+T³q(T²)` has degree equal to pole
degree: its two summands have opposite parity. Polynomial leading-term
cancellation therefore represents every integral residue by a unique constant.
The infinity residue field is `F₃`.

The same parity calculation shows that pole degree at most one implies
constancy. Powers `x^k` and monomials `x^j y` realize all orders at least two.
Thus the affine pole semigroup has exactly one positive gap, at one.

Lean: `FiniteFieldEllipticInfinityValuation.lean`,
`FiniteFieldEllipticPoleReduction.lean`, `FiniteFieldEllipticInfinityResidue.lean`,
`FiniteFieldEllipticPoleSemigroup.lean`; in particular
`infinityParameter_isUniformizer`, `infinityResidueEquiv`,
`poleDegree_le_one_iff`, `exists_affine_infinity_valuation`.

### Actual completions and constant approximation

Density approximates a completed integer by an original-field integer with
error of value less than one. Hence completion preserves the residue field.
A complete discrete valuation field with finite residue field has compact
integer ring. This applies to every actual finite place and the infinity place.
Density followed by the preceding constant-residue reduction gives, for every
completed infinity integer `z`, a constant `c` with `v(z-c)<1`. Nonzero constants
have value one because their inverses are integral too.

Lean: `HTGeometry/DiscreteValuedCompletion.lean`,
`FiniteFieldEllipticLocalFields.lean`, `FiniteFieldEllipticInfinityApproximation.lean`;
in particular `finiteCompletionResidueEquiv`, `infinityCompletionResidue_card`,
`completedInfinity_sub_constant`, `completedInfinity_constant_valuation`.

### Ambient adelic Haar measure and finite-place approximation

The product of the local integer rings is compact and open. One nonzero affine
integer clears the finitely many nonintegral coordinates of each finite adele.
Countably many compact denominator dilates therefore cover the finite adeles;
including infinity preserves sigma-compactness. Additive Haar measure exists
and is normalized to give the full integral product mass one.

For finite-place approximation, clear denominators by `d`. At each prime dividing
`d`, density and localization approximation choose an affine integer approximating
the integral coordinate `d a_v` modulo `d`. Chinese remainders combine these choices
modulo the pairwise coprime powers `v^(ord_v d)`. At all remaining primes `d` is a
unit. Dividing the combined integer by `d` gives `z∈K` with `a-z` integral at
every finite place. This proves finite strong approximation; it does not assert
any global quotient covolume.

Lean: `FiniteFieldEllipticAdeleHaar.lean`,
`FiniteFieldEllipticFiniteApproximation.lean`; in particular
`finiteAdele_exists_integral_denominator`, `adeleHaar`,
`finiteAdele_exists_integral_difference`.

### Radial local Haar integral

For a completed local field, let `q` be the actual residue cardinality and
normalize `μ(O)=1`. Reduction has kernel `πO` of additive index `q`, hence
`μ(πO)=q⁻¹`. Haar scaling gives `μ(π⁻ⁿO)=qⁿ`. The disjoint valuation shells
have masses `1` at index zero and `qⁿ−qⁿ⁻¹` at positive index `n`.

Define the radial kernel on shell `n` to be `(z/q)ⁿ`, for `‖z‖<1`.
Its shellwise norm integrals are bounded by `‖z‖ⁿ`, so the kernel is integrable.
Interchanging the absolutely convergent sum and integral and summing the
geometric series yields

`∫ kernel_z dμ = 1+(1-q⁻¹)Σ_{n≥1}zⁿ = (1-z/q)/(1-z)`.

At a finite place, `q=|O/v|`, where `O≃A` is the proved integral closure; at infinity, `q=3`. This is an actual Haar integral.
Its identification with an Eisenstein Iwasawa character is not asserted.

Lean: `HTGeometry/DiscreteValuationHaar.lean`,
`HTGeometry/DiscreteValuationShells.lean`, `HTGeometry/LocalRankOneIntegral.lean`,
`FiniteFieldEllipticLocalIntegrals.lean`; in particular
`sphericalKernel_integrable`, `integral_sphericalKernel`,
`integral_finiteLocalKernel`, `integral_infinityLocalKernel`.

### Ideal cardinality norms in characteristic three

In an infinite Dedekind domain, Chinese remainders prove multiplicativity of
quotient cardinalities for coprime ideals. Prime-power successive quotients and
unique factorization extend this to all ideals. Infinitude makes the zero ideal
have norm zero. This requires no characteristic-zero assumption.

For the actual affine ring, Smith decomposition in the basis `(1,y)` shows that
every nonzero ideal quotient is finite-dimensional over `F₃`, hence finite.
For a nonzero principal generator `a`, its dimension is the degree of the
polynomial algebra norm. Thus

`|A/(a)| = 3^(natDegree Norm(a))`,

and that exponent is exactly the previously defined infinity pole degree.
A finite-place product formula is not asserted.

Lean: `HTGeometry/DedekindIdealNorm.lean`, `FiniteFieldEllipticIdealNorm.lean`;
in particular `ideal_cardinality_mul`, `affine_quotient_finite`,
`affineIdealNorm_principal`, `affine_principal_norm_exponent`.

## Validation and closure

Each retained source has a successful `lake --old env lean` check, or a successful
required dependency-olean compilation, from `formal/`. Files were compiled one
at a time; no `lake build` or umbrella compilation was used. Axiom audits of the
main analytic and arithmetic results contain only
`[propext, Classical.choice, Quot.sound]`. Source inspection found no proof
placeholders, trusted-computation shortcuts or raised proof limits.

All 21 completed modules are imported by their owning umbrellas. The five
arithmetic drafts closed in this batch are finite approximation, infinity
approximation, the pole semigroup, actual local integrals and principal ideal
norms. Their checked source is installed in the corpus. Owned scratch files
were removed after validation. The remaining unfolding target has been moved
to backlog; no unformalized paper proof is presented as a result.

The main analytic declaration is
`GaloisForLFunctions.HTGeometry.LoopEisenstein.AffineA1.finiteFieldWeylSum_simultaneous_integral_poles`.
All arithmetic filenames above are under
`formal/GaloisForLFunctions/ArithmeticEffectivityTheory/` unless explicitly prefixed
by `HTGeometry/`. Analytic Weyl modules are under `HTGeometry/LoopEisenstein/`:
`AffineDegreeGaussianSeries`, `AffineA1FiniteFieldRegularization`,
`AffineA1FiniteFieldWeylPoles`; the zeta bounds are in
`ArithmeticEffectivityTheory/FiniteFieldEllipticZetaBounds`.

The unformalized fundamental-domain, Bruhat-coordinate and global-product-formula
sketches from the former programme card are withdrawn as proof claims. The
unproved Eisenstein unfolding remains a backlog target. No new branch was started
when closing this batch at the user's request.
