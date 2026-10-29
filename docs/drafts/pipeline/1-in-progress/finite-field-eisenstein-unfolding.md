# Arithmetic affine Eisenstein unfolding and surviving zeta poles

- **ID:** `finite-field-eisenstein-unfolding`
- **Stage:** 1-in-progress
- **Type:** FORMALIZATION PROGRAMME / CLASSICAL BRIDGE
- **Source:** [finite-field-zeta-pole-transfer](../3-formalized/finite-field-zeta-pole-transfer.md).
- **Target:** Construct the arithmetic affine `SL₂` Eisenstein series over the actual genus-one
  function field of `y²=x³−x` over `F₃`, prove its constant-term unfolding, and prove that
  the arithmetic zeta poles survive the infinite Weyl sum at actual degree rotations.

## Exact scope

Use the existing actual function field, not a complex function field. Keep the infinite
untwisted affine `A₁` Weyl group and the centrally extended loop group. The arithmetic
series must be a sum over arithmetic Borel cosets, defined independently of its proposed
constant term. No interface may assume Iwasawa decomposition, local intertwining integrals,
Euler products, convergence, unfolding, or noncancellation.

With `λ=−(χ+ρ)`, the Godement chamber is `Re λ₀, Re λ₁>1`. The expected identity is

`∫_(U_A/(U_A∩Γ_F)) E_λ(h η u) du = Σ_w hη^(−wλ−ρ) ∏_(β∈I(w)) ζ_F(λ(β∨))/ζ_F(λ(β∨)+1)`.

The genus factor is one because the source curve has independently proved genus one.
The measure must be the actual invariant probability measure; the right side is not a
definition of the left side.

Here `Γ_F` is the intersection of the diagonal image of the completed rational loop
group with the restricted adelic group. Lee–Lombardo §3.5 explicitly shows that the
whole rational loop group need not embed in the restricted product. The intersection
cannot be replaced by the full rational group without proof.

Noncancellation is a generic or existence claim, not a claim at every torus point. Fix
an actual arithmetic pole `s₀` of `c(s)=ζ_F(s)/ζ_F(s+1)`, its order `−m`, and the
spectral slice `λ(s)=(4−s,s)`. All other positive-root arguments have real part greater
than one near `s₀`, since `Re s₀=−1/2`. At trivial finite/central torus coordinates,
translation index `n` has degree factor `exp(−R(4n²+ns))`. Only identity and finite
simple reflection have index zero. After multiplication by `(s−s₀)^m`, the identity
term vanishes at `s₀`, the simple reflection contributes a nonzero leading coefficient,
and the other terms tend to zero as `R→∞`. Prove uniform analytic convergence of the
regularized sum and this limit; conclude exact order `−m` for all sufficiently strong
actual degree rotations. Exchange the simple roots for the second direction.

A pole of the continued constant term is not by itself a construction of meromorphic
continuation of the full Eisenstein family. Track this distinction explicitly.

## Internal frontier

- The source function field, genus, all extension point counts, zeta series and rational
  continuation are formalized. Exact pole multiplicities and simple affine coefficient
  formulas are formalized and audited.
- The rational-field affine Weyl sum has absolute convergence via quadratic degree decay;
  this supplies reusable combinatorics, not the finite-field arithmetic unfolding.
- Existing loop-group sources construct the actual Laurent central extension, root
  splittings, degree rotation, simple coroots, positive-loop splitting, and field maps.
- The corpus now also supplies the actual affine Bruhat decomposition and uniqueness:
  `LoopSL2.exists_unique_bruhat` in `LoopBruhatDecomposition.lean`, obtained from the
  full Laurent-matrix Iwahori double-coset theorem. This supplies the Bruhat labels,
  but not yet the finite root-coordinate parametrization needed for integration.
- The arithmetic series, finite-field adelic quotient measure, Iwasawa/Bruhat integration,
  and full-sum noncancellation are not supplied by the preceding card.

## External audit and research gates

Primary source: Lee–Lombardo, *Eisenstein series on affine Kac–Moody groups over
function fields*, <https://arxiv.org/pdf/1208.4006>, especially §§2–7 and Appendix A.
Unfolding and meromorphic continuation of the constant term are classical. Verdict:
**BRIDGE**. This task requests proof and formalization of that theorem; a novelty claim
would be false. Audit descendants for precise continuation and pole-survival scope.

Competing assertions to attack: (1) every coefficient pole survives at every torus point;
(2) only generic survival holds; (3) degree rotation isolates a nonzero leading residue.
The third is the selected exact target. Do not infer noncancellation from termwise poles.

## Gates

- [x] Exact arithmetic source and intended group fixed.
- [ ] Complete internal and external dependency audit.
- [x] Dependency-closed paper proof of analytic noncancellation.
- [x] Lean proof of the exact full-sum pole theorem.
- [ ] Actual finite-field arithmetic series and convergence.
- [ ] Actual unipotent quotient measure and local/global intertwining integrals.
- [ ] Dependency-closed paper proof of arithmetic unfolding.
- [ ] Lean unfolding, final source checks, and transitive axiom audit.

## Open core

Construct and discharge the arithmetic definitions and integration theorems. Analytic
noncancellation of the complete infinite affine Weyl sum is now Lean-verified, including
uniform coefficient bounds, holomorphic regularization, and exact eventual pole orders.
The separate arithmetic unfolding theorem remains required.

## Dependency-closed analytic Weyl-sum proof `[PROVED HERE]`

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
The projective rational point at infinity supplies the degree-one place required to
realize those rotations; constructing that place in the adelic model remains part of
the separate arithmetic construction, not an input assumed by the analytic theorem.

This proves survival for every actual arithmetic root copy, with multiplicity. It
makes no claim that no exceptional smaller rotations or torus values can cancel a
leading coefficient. All analytical inputs above are the already proved polynomial
root circle, finite inversion sets, elementary compactness, holomorphic uniform-limit
theory, and dominated convergence. No arithmetic unfolding theorem is used.

## Working state

- Arithmetic drafts: `/tmp/hgt_ff_infinity_valuation.lean` constructs the actual
  valuation, DVR, parameter, and equality with `infinityRegular`. The complete source
  passed, exit 0 with no diagnostics, and is now
  `FiniteFieldEllipticInfinityValuation.lean`; its olean compilation also passed for
  the dependent residue-field module. Never rebuild that olean.
  `FiniteFieldEllipticPoleReduction.lean` proves leading-term cancellation
  through the linear polynomial encoding. Its scratch and dependent olean checks passed.
  `FiniteFieldEllipticInfinityResidue.lean` proves the infinity residue-field equivalence
  with `F₃` and exact cardinality three. Its scratch check and transitive axiom audit
  passed: only `[propext, Classical.choice, Quot.sound]` for the cardinality,
  uniformizer, valuation-ring identification, and pole-degree cancellation.
- The simultaneous two-index strengthening `finiteFieldWeylSum_simultaneous_integral_poles`
  is now in the production full-sum module. Its scratch source and transitive axiom audit
  passed with only `[propext, Classical.choice, Quot.sound]`. One threshold works for
  both Frobenius indices, with each root's exact multiplicity.

- The existing `AffineA1FiniteFieldCoefficients` olean was missing and has now been
  compiled for the new dependent modules. Compilation passed; do not rebuild it.
- `/tmp/hgt_ff_zeta_bounds.lean` passed its foreground check, exit 0, no diagnostics.
  It contains reduced numerator/denominator, compact-disk and right-half-plane bounds,
  entire additive factors, and exact denominator order. The identical production source
  is `ArithmeticEffectivityTheory/FiniteFieldEllipticZetaBounds.lean`; its olean is now
  compiled for the dependent affine coefficient module, exit 0 with no diagnostics.
  Never rebuild that olean.
- `HTGeometry/LoopEisenstein/AffineDegreeGaussianSeries.lean` proves uniform holomorphy
  and strong-rotation extraction for the level-four integer series. Both the scratch
  check and production olean compilation passed, exit 0 without diagnostics. Its olean
  is required by the cleared-coefficient module; never rebuild it.
- `HTGeometry/LoopEisenstein/AffineA1FiniteFieldRegularization.lean` contains the actual
  finite-field regularization, root-argument separation, uniform Weyl-length bounds,
  and exact clearing identity. Scratch check passed, exit 0 without diagnostics.
  Production olean compilation also passed, exit 0 without diagnostics. Never rebuild
  that olean. The dependent full-sum scratch check also passed.
- `HTGeometry/LoopEisenstein/AffineA1FiniteFieldWeylPoles.lean` contains the complete
  Weyl-sum definitions, normal convergence, original-series/continuation equality,
  punctured-germ equality, and exact eventual pole orders, including integral rotations.
  Its identical scratch source passed, exit 0 with no diagnostics. The final declaration
  is `finiteFieldWeylSum_integral_rotation_poles`. The transitive axiom audit passed for
  that theorem, `finiteFieldWeylSum_eventual_order`, chamber equality, holomorphy, and
  absolute convergence: only `[propext, Classical.choice, Quot.sound]`.
- `/tmp/hgt_ff_eisenstein_api.lean` is an owned API scratch file. Its check finished;
  expected unknown-name errors identified unavailable aliases. Valid APIs include
  `mul_div_mul_left`, `IsCompact.exists_bound_of_continuousOn`,
  `tendsto_tsum_of_dominated_convergence`, and `DifferentiableOn.analyticOnNhd`.
  Holomorphic sums use `Mathlib.Analysis.Complex.SummableUniformlyOn`, specifically
  `SummableLocallyUniformlyOn.differentiableOn`.
- Analytic modules are complete. Continue the actual arithmetic construction and
  unfolding; do not identify the independently defined Weyl sum with an Eisenstein
  constant term until that integration theorem is proved.
- Arithmetic dependency audit: no elliptic-coordinate Dedekind theorem surfaced yet.
  Corpus has actual general normal-local-ring DVR and finite-extension valuation
  machinery; inspect those and mathlib's adelic/function-field sources before building
  curve-specific places. Do not substitute number-field adeles without a proved transport.

## Arithmetic construction: rational subfield and finite adeles `[PAPER PROOF]`

Lean status: `FiniteFieldEllipticGlobalField.lean` passed its identical scratch check
and production olean compilation, exit 0 without diagnostics. The actual extension
degree, separability, finite residue fields, finite adeles, and injective diagonal map
are proved. Its olean is required by the integral-closure module; never rebuild it.
The transitive axiom audit passed with only `[propext, Classical.choice, Quot.sound]`.
`FiniteFieldEllipticIntegralClosure.lean` now proves
the identification with the affine ring as recorded below.

The actual affine coordinate ring `A` has the already proved free `F₃[X]` basis
`(1,y)`. Its polynomial algebra map is injective, and therefore extends uniquely
to `F₃(X) → K=Frac(A)`. This yields the same scalar tower as the existing curve
coordinates. The images of `(1,y)` remain linearly independent after localization.
They span `K`: an algebraic denominator can be rationalized into a nonzero element
of the base polynomial ring. Equivalently, for nonzero `b∈A`, its polynomial
equation with nonzero constant term supplies `b'∈A` and nonzero `p∈F₃[X]` with
`bb'=p`. Thus every `a/b` lies in the `F₃(X)`-span of the two basis elements.
Hence `[K:F₃(X)]=2`.

This extension is separable: the trace of one equals the extension degree, which
is `2≠0` in characteristic three; a finite inseparable extension has identically
zero trace. The integral closure `O` of `F₃[X]` in this proved finite separable
extension is therefore a Dedekind domain with fraction field `K`. Its finite
adele ring is the restricted product of the actual height-one-prime completions,
with the diagonal embedding supplied by finiteness of the denominator support.
No arbitrary family of local fields or assumed function-field structure is used.

Every finite residue field is finite: `O` is finite over `F₃[X]`, hence finitely
generated over `F₃`. Quotients by height-one primes are fields because `O` is
Dedekind. Zariski's lemma makes each a finite-dimensional `F₃`-vector space,
therefore a finite set. Nonemptiness of the finite-place set follows from
`O` not being a field; this also proves the diagonal finite-adele map injective.

Still required after this algebraic bridge: identify the omitted infinity place,
all residue cardinalities and the curve-point Euler product; construct normalized
global additive measure, the adelic completed loop group, Iwasawa coordinates,
and the actual arithmetic coset sum. The finite-adele ring alone is not unfolding.

## Arithmetic construction: the actual infinity valuation `[PAPER PROOF]`

The already proved norm degree `d:A→WithBot ℕ` is bottom exactly at zero,
additive on products, and subadditive on sums. Embed its finite values in `ℤ`
and reindex additively as the ordered multiplicative group `ℤ`. This is a
valuation `v_A:A→WithZero(Multiplicative ℤ)` with zero support. Its unique
extension to `K=Frac(A)` satisfies `v(a/b)=v_A(a)/v_A(b)`.
The existing calculations `d(x)=2` and `d(y)=3` therefore give
`v(x/y)=ofAdd(−1)`. Integer powers of `x/y` realize every nonzero value, so
this is an actual discrete nontrivial valuation of the curve field, with
uniformizer `x/y`. Its valuation subring consists exactly of the fractions
with numerator norm degree at most denominator norm degree, hence agrees
with the previously constructed infinity-regular subalgebra.

The remaining residue-field identification needs proof: equal-degree numerator
and denominator have a unique scalar leading-coefficient ratio, since the two
possible leading weights `2 deg p` and `2 deg q+3` have opposite parity. Subtracting
that scalar lowers degree. This will identify the residue field with `F₃`.

For the explicit cancellation lemma, linearly encode the unique affine coordinates
`p(x)+q(x)y` by the polynomial `p(T²)+T³q(T²)`. Its degree equals the norm pole
degree: the two nonzero summands have opposite parity of degree. This encoding
respects subtraction and scalar multiplication (it is not a ring homomorphism).
Thus equal non-bottom pole degrees reduce to ordinary polynomial leading-term
cancellation. For any nonzero denominator `b` and `d(a)≤d(b)`, choose `c=0` when
the inequality is strict; otherwise choose the ratio of these encoded leading
coefficients. Then `d(a−cb)<d(b)`, so `v(a/b−c)<1`. Every infinity residue is
therefore represented by a unique constant; nonzero constants have value one.

## Identifying finite places with the affine curve `[PAPER PROOF]`

The integral closure `O` above equals the actual affine coordinate ring `A`.
Write an integral element of `K` uniquely as `z=p+qy`, with `p,q∈F₃(x)`.
Quadratic conjugation sends `y` to `−y` and preserves integrality over `F₃[x]`.
Thus `2p=z+σz` and `p²−(x³−x)q²=zσz` are integral over `F₃[x]`.
The base polynomial ring is integrally closed and `2` is a unit, so `p∈F₃[x]`
and `(x³−x)q²∈F₃[x]`. Write `q=a/b` in coprime polynomial terms. Then
`b²|(x³−x)a²`, whence coprimality gives `b²|(x³−x)`. The proved squarefreeness
of `x³−x` forces `b` to be a unit. Hence `q∈F₃[x]` and `z∈A`.
Conversely `A` is finite over `F₃[x]`, so all its elements are integral.

This elementary trace/norm argument avoids assuming normality of the curve or
an unproved smooth-to-normal bridge. Its Lean proof now passes: the identical scratch
source for `FiniteFieldEllipticIntegralClosure.lean` checked with exit 0 and no diagnostics.
It proves `isIntegral_iff_coordinateRing_image`, the actual Dedekind instance, and
`coordinateRingEquivRingOfIntegers`, compatible with their maps into the function field.
The transitive axiom audit passed with only `[propext, Classical.choice, Quot.sound]`.
Euler product and quotient measure remain open.

## Completion preserves the local arithmetic `[PAPER PROOF]`

For an integer-valued nontrivial valuation, completion extends the valuation
without changing values on the original field. The induced map of valuation
rings is local, hence its map on residue fields is injective. It is surjective:
given a completed valuation integer, density supplies an original-field element
whose difference has value less than one; the ultrametric inequality makes that
element integral, and their residues agree. Thus completion preserves residue
cardinality. Its integer ring remains a DVR because the value group is discrete
and nontrivial. The complete DVR with finite residue field is locally compact:
each finite quotient by a power of a uniformizer is finite, and these quotients
give total boundedness of the integer ring. Completeness gives compactness.
This proves that the actual finite-place and infinity completions are local fields
once the already established finite residue results are applied. The generic valued-field
completion proof and explicit `WithVal` transport are now in
`HTGeometry/DiscreteValuedCompletion.lean`. Both scratch and production olean checks
passed. Its olean is required by the actual-place module; never rebuild it.
`FiniteFieldEllipticLocalFields.lean` applies it to the actual finite and infinity places,
identifies their completed residue fields, and constructs the full adele ring as the
product of finite adeles and the infinity completion. Its scratch source and transitive
axiom audit passed with only `[propext, Classical.choice, Quot.sound]`. Its production
olean compilation also passed; the adele-Haar draft imports it.

For full additive Haar measure, the integral product is compact by Tychonoff and open
by the restricted-product topology. Every finite adele has finitely many nonintegral
coordinates. At each such coordinate a nonzero affine integer clears its denominator;
their product clears them all. Thus finite adeles are covered by compact denominator
dilates indexed by the countable affine ring. They are sigma-compact, as is the full
adele ring after adjoining the infinity completion. Haar measure normalized to give
the integral product mass one is therefore sigma-finite. This is ambient Haar measure;
the rational quotient's covolume and the unipotent quotient measure still require proof.
`FiniteFieldEllipticAdeleHaar.lean` now passed its identical scratch check and
transitive axiom audit, with only `[propext, Classical.choice, Quot.sound]`.
It proves countability, denominator clearing, sigma-compactness, and normalized
ambient Haar measure on the actual adeles. Quotient volume remains open.

## Local rank-one integral `[PAPER PROOF]`

Let `k` be any of the actual completions, `O` its compact open valuation ring,
`π` a uniformizer, and `q=|O/πO|`. Normalize additive Haar measure by `μ(O)=1`.
The residue homomorphism is surjective with kernel `πO`; hence that kernel has
additive index `q`. Its cosets partition `O`, and translation invariance gives
`μ(πO)=q⁻¹`. Multiplication by `π` scales additive Haar measure by a constant
(uniqueness of Haar measure); evaluating on `O` identifies that constant as `q⁻¹`.
Consequently `μ(π⁻ⁿO)=qⁿ` for every integer `n`.

Normalize the absolute value by `|π|=q⁻¹`. The disjoint measurable partition
`k=O ⊔ ⋃_{n≥1}{x:|x|=qⁿ}` has shell measures `qⁿ−qⁿ⁻¹`. For `Re(s)>0`,
the spherical rank-one integrand `φ_s(x)=max(1,|x|)^(−s−1)` is constant one
on `O` and `q^(−n(s+1))` on the nth shell. Its absolute integral is bounded
by the convergent geometric series `1+(1−q⁻¹)Σ_{n≥1}q^(−n Re(s))`.
Countable additivity of the integral therefore gives

`∫_k φ_s(x) dμ(x) = 1+(1−q⁻¹)Σ_{n≥1}q^(−ns)`
`                       = (1−q^(−s−1))/(1−q^(−s))`.

This is the local intertwining factor, proved from the actual residue index and
Haar measure. Its identification with an Iwasawa character still requires the
rank-one matrix calculation. The product of these integrals is the required global
zeta quotient only after proving the closed-point Euler product and the global
measure normalization. None of those later identities is assumed here. Lean status:
the residue-index and uniformizer-scaling argument is now formalized in
`HTGeometry/DiscreteValuationHaar.lean`, with scratch and production olean checks
passing and an axiom audit containing only `[propext, Classical.choice, Quot.sound]`.
The shell partition and exact shell measures are now formalized in
`HTGeometry/DiscreteValuationShells.lean`. The two main axiom audits passed;
production olean compilation passed after a comment-placement fix.
The actual Haar integral is now proved in `HTGeometry/LocalRankOneIntegral.lean`:
`sphericalKernel_integrable` and `integral_sphericalKernel` passed their scratch
check and transitive axiom audits with only `[propext, Classical.choice, Quot.sound]`.
Using `z=Q⁻ˢ`, its exact value is `(1-z/Q)/(1-z)` for `‖z‖<1`.
The Iwasawa identification remains open. The corpus's `FieldOnePadicHaarScaling` supplies the same
residue-index argument for `Q_p`; generalize the proof rather than transport a
characteristic-zero field to the present completions.

## Ideal norms in positive characteristic `[PAPER PROOF]`

For any infinite Dedekind domain `A`, put `N(I)=|A/I|`, with value zero for an
infinite quotient. Chinese remainders give multiplicativity for coprime ideals.
For a nonzero prime `P`, each successive quotient `Pⁿ/Pⁿ⁺¹` is one-dimensional
over `A/P`; thus `N(Pⁿ)=N(P)ⁿ`. Unique ideal factorization gives full
multiplicativity. Infinitude gives `N(0)=0`, and `N(A)=1`. This proof works
in positive characteristic. Mathlib's bundled `Ideal.absNorm` unnecessarily
requires a free `Z`-module, so the argument must be exposed with the weaker
and applicable infinitude hypothesis.

For the actual elliptic coordinate ring, the proved basis `(1,y)` over `F₃[x]`
identifies `A/I` with the direct sum of polynomial quotients by the nonzero
Smith coefficients of any nonzero ideal `I`. Hence it is a finite-dimensional
`F₃`-vector space. For a nonzero principal ideal `(a)`, the determinant/Smith
identity gives `dim_F₃ A/(a)=deg Norm_F₃[x](a)`, already equal to its pole degree
at infinity. Therefore `N((a))=3^(poleDegree(a))`. Factoring `(a)` into prime
powers turns this into the finite-place part of the product formula; adjoining
the degree-one infinity valuation gives product one. The exact finite-support
valuation formulation still needs its factorization proof in Lean.
The characteristic-independent multiplicative norm is now checked in
`HTGeometry/DedekindIdealNorm.lean`. The actual affine principal-norm calculation
is drafted in `/tmp/hgt_ff_ideal_norm.lean`, awaiting its two dependency oleans.

## Finite coordinates on affine Bruhat cells `[PAPER PROOF]`

For the matrix Iwahori `B`, write a matrix as `[[a,b],[c,d]]`, with `a,d`
power-series units and `c` divisible by the loop variable `t`. Every inversion
set in affine `A₁` lies in one root string. Thus its root-coordinate group is
an additive space of upper or lower unipotent polynomials; its dimension is
the already proved inversion cardinality.

Use left Borel cosets `B\G`, represented by `w u(q)`. For translations
`w=diag(t⁻ᵐ,tᵐ)`, if `m≥0`, take the truncation of `b/a` in degrees
`0≤j<2m`; right multiplication by `u(−q)` makes the upper entry divisible
by `t^(2m)`. Conjugation by `w` then lies in `B`. If `m<0`, take the
truncation of `c/d` in degrees `1≤j≤−2m`; the remaining lower entry is
divisible by `t^(1−2m)`, again exactly the conjugated Iwahori condition.

For `w=s diag(t⁻ᵐ,tᵐ)`, the Weyl matrix exchanges upper and lower entries.
For `m≥0`, truncate `b/a` in degrees `0≤j≤2m`; for `m<0`, truncate `c/d`
in degrees `1≤j<−2m`. These are precisely the four interval formulas in
`AffineA1.inversions w`. The central extension introduces no new obstruction:
the positive Borel is the full inverse image of the matrix Iwahori, so its
central kernel absorbs all discrepancies between chosen lifts.

Bruhat existence supplies a representative of this form for every group element.
Bruhat uniqueness first forces equal Weyl labels. Within one label, equality
of the left Borel cosets forces the polynomial difference `q−q'` to satisfy
the complementary divisibility condition. Its degree bound forces it to vanish.
Hence `B\G` is bijective with the disjoint union of the finite inversion-root
coordinate spaces. This is the group-level parametrization needed for unfolding.
Arithmetic restriction and the integration argument are separate. Lean status:
the double-coset theorem is available; the truncation refinement remains to prove.

## Additive strong approximation at finite places `[PAPER PROOF]`

Given a finite adele `a`, choose a nonzero affine integer `d` such that every
`d a_v` is integral. Only finitely many primes divide `(d)`. At such a prime `v`,
density of the fraction field in its completion first approximates `d a_v` by an
integral fraction `y`. The localization at `v` is dense in the completed integer
ring: write `y=n/e` with `e` outside `v` and invert `e` modulo a sufficiently high
power of `v`. Thus choose `b_v` in the affine ring with
`v(d a_v-b_v) ≤ v(d)`.

The prime powers `v^(ord_v d)` for distinct divisors of `(d)` are pairwise
coprime. Chinese remainders supply `b` with `b-b_v` in each required prime power.
The valuation criterion for ideal-power membership gives
`v(d a_v-b) ≤ v(d)` at every divisor of `(d)`. At every other prime, both terms
are integral and `v(d)=1`, so the same inequality holds. Division by `d` proves
`a-b/d` integral at every finite place. Hence every finite-adele coset modulo the
actual diagonal field has an integral representative. This is the finite-place
input to the global additive fundamental domain; its Lean proof is still open.

## Genus-one additive fundamental domain `[PAPER PROOF; LEAN OPEN]`

Write `π=x/y` at infinity and let `m∞=π O∞`. The explicit pole semigroup of
the affine ring is `{0,2,3,4,...}`: even pole orders come from powers of `x`,
odd orders at least three from `x^j y`, and the two basis weights show that
order one is absent. The infinity residue field is exactly `F₃`.

For any completed infinity element, a finite inverse uniformizer power bounds
its pole. At every pole order `n≥2`, divide by an affine monomial of that pole
order, reduce in `F₃`, and subtract the corresponding scalar multiple of the
monomial. This strictly lowers the pole order. At order at most one, subtract
`c π⁻¹` to become integral, then subtract its constant residue to land in `m∞`.
Consequently every infinity element differs from an affine function by an
element of `T∞ = ⋃_{c∈F₃}(c π⁻¹ + m∞)`.

Strong approximation first makes all finite coordinates integral; the preceding
reduction, using affine functions, preserves finite integrality. Therefore
`F = (∏_{v finite} O_v) × T∞` meets every diagonal `K`-coset. It meets each
coset once: a diagonal difference integral at all finite places lies in the
affine ring (the Dedekind intersection-of-localizations theorem). Its infinity
pole order is at most one, so it is constant. A nonzero coefficient of `π⁻¹`
cannot be constant; once that coefficient vanishes, a constant in `m∞` is zero.

The subgroup `(∏ O_v) × m∞` has index three in the full integral product,
because reduction at infinity has residue field `F₃`. Its Haar volume is `1/3`.
The three displayed translates are disjoint, hence `F` is compact open and has
volume one. This gives an actual measurable fundamental domain and probability
measure on `Adeles/K`, with no assumed covolume. These statements still require
Lean formalization; the ambient Haar measure alone does not establish them.

## Conventions for the remaining Eisenstein identity

Use the `KHU` Iwasawa convention and the right arithmetic cosets
`Γ/(Γ∩B)`, with `χ=-λ-ρ`. The intended series is
`Eχ(g η)=Σ_{γ∈Γ/(Γ∩B)} Φχ(g η γ)`. Its constant term integrates
`Eχ(g η u)` over `U_A/(U_A∩Γ)`. The target torus factor is
`(h η)^(w(χ+ρ)-ρ)=(h η)^(-wλ-ρ)`, exactly `weylExponent`.
This matches Lee–Lombardo, §3.5 and Theorem 4.23.

In rank one, for `u(x)=[[1,x],[0,1]]` and
`w=[[0,-1],[1,0]]`, when `|x|>1` one has
`u(x)w = lower(x⁻¹) diag(x,x⁻¹) upper(-x⁻¹)`.
The first factor is integral, so `χ(h)=-s-1` gives `|x|^(-s-1)`;
for integral `x`, `u(x)w` itself is integral. This is the precise matrix
identity still to connect to `sphericalKernel`. The left-coset Bruhat
coordinates above transport to right cosets by inversion; the corresponding
Weyl labels must be inverted when making that comparison.
