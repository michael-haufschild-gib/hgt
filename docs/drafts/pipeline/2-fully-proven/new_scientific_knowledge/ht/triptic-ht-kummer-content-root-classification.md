# Triptic HT classes have an exact Kummer-content root classification

- **ID:** `triptic-ht-kummer-content-root-classification`
- **Stage:** 2-fully-proven / needs independent audit with parent
- **Type:** THEOREM (paper) / POSITIVE SOURCE-EFFECTIVITY MODEL
- **Scientific status:** `[PROVED HERE] [CANDIDATE NEW SCIENTIFIC KNOWLEDGE]`
  `[LEAN-FORMALIZED INTEGRAL CORE] [PARENT ATOMIC AUDIT PENDING] [NOT AN RH RESULT]`
- **Lean:** `formal/GaloisForLFunctions/HTGeometry/MinimalHTCompletionArchitecture.lean`
- **Parent:** `triptic-orbit-residue-reciprocity.md`
- **Statement:** In the multiplicative triptic HT class, existence and uniqueness of an `m`-th
  root modulo differentially algebraic factors are equivalent to coefficientwise divisibility by
  `m` of the common integral orbit divisor.  The maximum root order is the gcd of its coefficients.

## Multiplicative source class

Fix `tau,sigma` in the upper half-plane with `1,tau,sigma` rationally independent, and put

```text
H_3=Z+Z tau+Z sigma,              G=C/H_3.                 (1)
```

Let `M` be the multiplicative group of nonzero meromorphic functions `Y` such that

```text
Y(z+1)=Y(z)
```

and the mixed multiplicative coboundary

```text
C_Y(z)=Y(z+tau+sigma)Y(z)/(Y(z+tau)Y(z+sigma))             (2)
```

has constant logarithmic derivative.  Equivalently, `(2)` is an exponential character.

The triptic reciprocity theorem constructs two integral orbital divisors from the two elliptic
boundary quotients and proves that they agree:

```text
D_tau(Y)=D_sigma(Y)=D_Y in Z[G].                            (3)
```

It also proves

```text
Y is differentially algebraic  iff  D_Y=0.                 (4)
```

The divisor is additive under multiplication and changes sign under reciprocal.  Hence

```text
D:M -> Z[G]                                                 (5)
```

is a group homomorphism with kernel `M_DA`, the differentially algebraic members of `M`.

## Surjectivity and the effective quotient

The normalized elliptic-gamma source has divisor `[0]`.  Translation realizes `[g]` for every
`g in G`, products add divisors, and integer powers provide signed multiplicities.  Thus `(5)` is
surjective.  The first isomorphism theorem gives

```text
M/M_DA ~= Z[G].                                             (6)
```

Equation `(6)` is the first concrete source-effectivity fibre in the general program.  It does not
store a meromorphic germ.  It stores the finite integral boundary lift produced by the source, and
it reconstructs the source class exactly modulo DA ambiguity.  Its two noncommensurable elliptic
realizations are forced to be the same divisor by reciprocity.

## Exact root theorem

Fix `m>=1`.  Say that `Y` has an **`m`-th source root modulo DA** if there are `Z in M` and
`A in M_DA` with

```text
Y=A Z^m.                                                     (7)
```

> **[THEOREM -- TRIPTIC HT ROOT CLASSIFICATION]** For every `Y in M` and `m>=1`, the following
> are equivalent:
>
> 1. `Y` has an `m`-th source root modulo DA;
> 2. `D_Y=mE` for some finite integral divisor `E in Z[G]`;
> 3. every coefficient of `D_Y` is divisible by `m` in `Z`.

When these conditions hold, the root class `[Z] in M/M_DA` is unique.

### Proof

If `(7)` holds, additivity and `(4)` give

```text
D_Y=D_A+mD_Z=mD_Z,
```

so every coefficient is divisible by `m`.

Conversely, suppose `D_Y=mE`.  Surjectivity of `(5)` supplies `Z in M` with `D_Z=E`.  Then

```text
D_(Y/Z^m)=D_Y-mD_Z=0.
```

Equation `(4)` makes `A=Y/Z^m` differentially algebraic, proving `(7)`.  If `Z_1,Z_2` are two
roots, then `m(D_(Z_1)-D_(Z_2))=0`.  The free abelian group `Z[G]` is torsion-free, so their
divisors agree; `(4)` makes `Z_1/Z_2` DA. `QED`

## Kummer content

For nonzero `D_Y`, define

```text
kappa_K(Y)=gcd{|coefficient_g(D_Y)|:coefficient_g(D_Y)!=0}. (8)
```

The root theorem immediately yields

```text
Y has an m-th source root modulo DA  iff  m divides kappa_K(Y).   (9)
```

Thus every HT class in `M` has a finite maximum source-root order, namely `kappa_K(Y)`.  The
primitive classes are exactly those with `kappa_K(Y)=1`.  DA classes have `D_Y=0` and are the
separate infinitely divisible zero class of `(6)`.

This is a strong positive answer to the multiplicity/root/divisibility obstruction.  The source
does not merely carry a divisor: its integral content is the complete Kummer theory of the HT
class modulo DA factors.

## Why the integral channel is essential

After tensoring `(6)` with `C`, every divisor is divisible by every nonzero integer because
`C[G]` is a vector space.  The root spectrum `(9)` therefore disappears under complexification.
The real-conjugacy counterexample in
`../../3-formalized/source-producer-integral-realization-minimality.md` proves the same loss at the
operator level: even the complete real conjugacy class does not recover integral cokernel exponent.

> **[NO-GO]** No field theory retaining only complex analytic, spectral, polarized, or derived
> realizations can recover the source-root spectrum in general.
>
> **Positive theorem.** On the triptic multiplicative class, the common integral source divisor is
> a complete root classifier, and its coefficient gcd is the exact maximum root order.

## Unified-field interpretation

This theorem realizes three faces of the proposed source-producer fibre on a substantive HT class:

1. **source-purity:** `D_Y` is computed from either boundary quotient before any DA/HT verdict;
2. **comparison:** the two noncommensurable elliptic realizations agree by reciprocity;
3. **integral effectivity:** root existence is exactly divisibility of the common integral lift.

The theorem does not yet supply polarization or a critical all-scale analytic bornology.  It is a
height-one abelian model of the full six-channel theory, not the complete field theory.

## Novelty and anti-theatre gate

Divisor divisibility as a root obstruction, the first isomorphism theorem, gcd content, and
torsion-freeness of a free abelian group are classical.  They are not novelty claims.  The parent
threats are elliptic-gamma multiplication formulae, the gamma gerbe on the universal triptic curve,
one-curve orbital/panorbital residues, and parameterized difference Galois theory.

Primary searches checked:

- Felder--Henriques--Rossi--Zhu, *A gerbe for the elliptic gamma function*,
  https://arxiv.org/abs/math/0601337;
- Kato, *Differential Algebraicity of the Multiple Elliptic Gamma Function for a Rational Period*,
  https://doi.org/10.1619/fesi.64.225;
- the one-curve orbital and panorbital sources already audited in the parent card.

No located source classifies roots modulo DA factors for the entire exponential-character triptic
class by the coefficient content of a common cross-curve integral divisor.  Novelty is inherited
from, and cannot be stronger than, the parent reciprocity/completeness theorem until its specialist
audit is complete.

- `[ANTI-THEATRE -- PASS]` The theorem adds an exact analytic consequence—root existence and
  uniqueness—not new vocabulary for `(3)`.
- `[SIGNIFICANCE -- PASS]` It completely solves a natural Kummer problem on an infinite HT class
  and proves why integral realization is load-bearing.
- `[PAPER VERDICT]` This warrants a major theorem section in the triptic reciprocity paper.  It is
  not a separate Fields-scale paper by itself.
- `[RH BOUNDARY]` The theorem is general HT mathematics.  It does not construct roots, divisors,
  or multiplicity constraints for zeta or Xi.

## Lean certificate

The analytic meromorphic and DA objects are not present in the Lean tree.  Lean formalizes the
entire integral algebraic core for an arbitrary orbit type `G`:

```text
exists E:G ->_0 Z, m • E=D
  iff
every coefficient D(g) is divisible by m.                  (10)
```

For an arbitrary additive source group `M` and surjective divisor homomorphism
`D : M ->+ (G ->_0 Z)`, Lean now also formalizes the complete abstract Kummer step:

```text
Y has an m-th root modulo ker(D)
  iff
every coefficient of D(Y) is divisible by m,
```

and proves that, for `m != 0`, any two such roots differ by `ker(D)`.
Writing `content(D)` for the gcd of the absolute values of the finitely many nonzero coefficients,
Lean further proves the exact spectrum

```text
Y has an m-th root modulo ker(D)  iff  m divides content(D).
```

Declarations:

- `IntegralOrbitDivisorCoefficientwiseDivisible`;
- `integralOrbitDivisorQuotient`;
- `integralOrbitDivisor_has_nsmul_root_iff`;
- `integralOrbitDivisorContent`;
- `integralOrbitDivisor_coefficientwiseDivisible_iff_content_dvd`;
- `integralOrbitDivisor_has_nsmul_root_iff_content_dvd`;
- `HasSourceRootModuloKernel`;
- `hasSourceRootModuloKernel_iff`;
- `hasSourceRootModuloKernel_iff_content_dvd`;
- `sourceRoot_unique_mod_kernel`.

This proves the full group-theoretic implication from a surjective divisor map with specified
kernel, including uniqueness modulo that kernel.  Instantiating `M` by the meromorphic triptic
source class and identifying `ker(D)` with its DA subgroup still requires the elliptic
principal-part and atomic-difference theory excluded by the parent card's anti-theatre boundary.

## Gates

- [x] multiplicative triptic classes identified as a group
- [x] common integral divisor proved additive with DA kernel
- [x] every finite integral divisor realized by translated gamma products
- [x] quotient classification `M/M_DA ~= Z[G]` proved
- [x] root existence and uniqueness modulo DA proved
- [x] exact Kummer-content spectrum proved
- [x] coefficientwise divisibility core Lean-formalized
- [x] abstract root existence and uniqueness modulo a surjective divisor kernel Lean-formalized
- [x] exact abstract Kummer-content root spectrum Lean-formalized
- [x] every no-go paired with the complete positive root classifier
- [x] primary parent collision run provisionally
- [ ] independent audit of the parent atomic theorem
- [ ] independent specialist audit of the root-classification priority claim

## Correction — the elliptic-gamma atomic theorem is corpus-owned, not an external parent

Every boundary note on this card that defers to "the independently unaudited elliptic-gamma atomic
theorem" is stale.  The order-one atomic input is formalized in this tree:

    GaloisForLFunctions/HTGeometry/EllipticGammaAtomicOverDAExtension.lean
      ellipticGammaExternalDefectFamily_differentialIndependent_daExtension

Its hypotheses are the data of the class only — both periods in the upper half plane, `ℚ`-linear
independence of the source periods, and the theta-translation nonresonance and separation
conditions on the shift family.  There is no assumed theorem.  `#print axioms` reports
`[propext, Classical.choice, Quot.sound]`.

So the consequences on this card that were labelled conditional on that parent are conditional on
nothing external: what remains for them is Lean derivation work inside this corpus, not an
unformalized classical input.

## Lean progress — the integral channel of the common divisor

Added to `GaloisForLFunctions/HTGeometry/TripticSourceDivisor.lean` (wired, axiom-clean):

    intCast_finsum                                     casting an integer unrestricted sum
    triptic_multiplicative_divisor_reciprocity_int     **reciprocity in ℤ, not only after
                                                       complexification**
    laurentCoeff_shiftDiff_logDeriv                    the order-one coefficient is the shift order
    finite_support_shiftOrder                          the orbital divisor is finitely supported
    tripticOrbitCharge                                 the integral orbital charge `∑ᶠ` of a source
    tripticOrbitCharge_mul                             **additive under multiplication of sources**
    tripticOrbitCharge_shift                           invariant along the orbit direction

The integral channel is exactly what the Kummer-content card argues is load-bearing: after
tensoring with `ℂ` every divisor becomes infinitely divisible and the root spectrum disappears.
`tripticOrbitCharge_mul` is the homomorphism hypothesis of the abstract Kummer classification
(`hasSourceRootModuloKernel_iff_content_dvd`); what still separates the two is surjectivity of the
divisor map, i.e. realization of an arbitrary finite integral divisor by a translated gamma product.

## Lean progress — surjectivity reduced to single-class realization

`GaloisForLFunctions/HTGeometry/SourceDivisorSurjectivity.lean` (wired, axiom-clean):

    addMonoidHom_surjective_of_single
      a homomorphism into `ℤ[G] = G →₀ ℤ` whose image contains every generator `[g]` is surjective
    hasSourceRootModuloKernel_iff_content_dvd_of_single
      the Kummer root classification, with the surjectivity hypothesis replaced by single-class
      realization
    sourceQuotientEquiv
      the effective quotient `M/ker D ≃+ ℤ[G]` under the same hypothesis

This is exactly the card's surjectivity argument — "translation realizes `[g]` for every `g`,
products add divisors, integer powers provide signed multiplicities" — carried out once and for all
on the free abelian group, by induction on the `Finsupp` support.  The card's remaining Lean
obligation is therefore the single statement

    ∀ g : G, ∃ Y ∈ M, D_Y = [g].

### What that realization needs, precisely

The realizing source cannot be a theta function.  For a source whose zero divisor meets each
`σ`-orbit in finitely many points, the orbital sum

    ∑ᶠ m : ℤ, (ord(Y, p + mσ + σ) - ord(Y, p + mσ))

telescopes to zero.  A nonzero orbital charge requires the zero divisor to meet the orbit in a
*half-line*, i.e. the quadrant-shaped divisor of the elliptic gamma function
`Γ(z; τ, σ) = ∏_{j,k ≥ 0} (1 - e((j+1)τ + (k+1)σ - z)) / (1 - e(jτ + kσ + z))`, whose zeros lie at
`-jτ - kσ + ℤ` with `j, k ≥ 0`.  Along a `σ`-orbit that order is `1` for `m ≥ 0` and `0` for `m < 0`,
so the shift order is supported at one index and sums to `1`.

So the outstanding Lean input for this card is the convergence and zero set of that double product —
not any group theory, and not any unformalized classical theorem.

## Lean progress — the realizing source is built, with its exact divisor

The elliptic gamma function is now in the tree, constructed as a ratio of exponential cone products,
with its quadrant divisor computed exactly.

`GaloisForLFunctions/HTGeometry/ExpConeProduct.lean` (wired, axiom-clean):

    expChar, norm_expChar, expChar_eq_one_iff
    coneFactor, coneProduct                     `Φ(z) = ∏_{j,k ≥ 0}(1 - e(j a + k b + z))`
    summable_norm_coneFactor_sub_one            geometric domination `A^j B^k`, `A,B < 1`
    multipliable_coneFactor
    coneProduct_eq_zero_iff                     the product vanishes exactly where a factor does
    hasProdLocallyUniformlyOn_coneFactor
    differentiable_coneProduct                  **the cone product is entire**
    conePunctured, coneProduct_eq_factor_mul_punctured, conePunctured_ne_zero,
      differentiable_conePunctured
    hasDerivAt_coneFactor, analyticOrderAt_coneFactor_eq_one
    analyticOrderAt_coneProduct_eq_one          **simple zeros**, at a point with one vanishing
                                                factor

`GaloisForLFunctions/HTGeometry/EllipticGammaConeDivisor.lean` (wired, axiom-clean):

    IndepPeriods                                `ℤ`-independence of `1, a, b`
    coneFactor_index_unique                     under independence a zero comes from one index
    analyticOrderAt_coneProduct_of_zero         hence every zero of `Φ` is simple
    meromorphicOrderAt_coneProduct
    ellipticGammaCone                           `Γ(z) = Φ(a + b - z)/Φ(z)`
    coneProduct_orbit_eq_zero_iff               **the pole half line**: `Φ(m·b) = 0 ↔ m ≤ 0`
    coneProduct_num_orbit_ne_zero               the numerator misses that orbit entirely
    meromorphicOrderAt_ellipticGammaCone_orbit  `ord(Γ, m·b) = -1` for `m ≤ 0`, `0` otherwise
    shiftOrder_ellipticGammaCone_orbit          the shift order is `1` at `m = 0` and `0` elsewhere
    tripticOrbitCharge_ellipticGammaCone :      **`D_Γ = [0]`**
    ellipticGammaConeTranslate,
      tripticOrbitCharge_ellipticGammaConeTranslate :  **`D_{Γ(·-g)} = [g]`**
    PeriodGroupMem, tripticOrbitCharge_ellipticGammaCone_of_notMem :
      the charge vanishes on every orbit off the class

So the card's surjectivity input — "the normalized elliptic-gamma source has divisor `[0]`, and
translation realizes `[g]`" — is now a proved Lean statement, and it composes with
`addMonoidHom_surjective_of_single`.

What remains on this card is the identification of the kernel: statement `(4)`, `Y` is
differentially algebraic exactly when `D_Y = 0`.

## Lean progress — the realizing source belongs to the class

`GaloisForLFunctions/HTGeometry/EllipticGammaConeCocycle.lean` (wired, axiom-clean):

    expChar_add, expChar_one, expChar_add_one, expChar_neg_mul_self, one_sub_expChar_neg
    coneProduct_periodic            every factor is `1`-periodic, hence so is the product
    ellipticGammaCone_periodic      **`Γ(z+1) = Γ(z)`**
    coneProduct_cocycle_identity    the four-fold shift identity
                                      `(1 - e(z))·N = (1 - e(-z))·D`
    coneProduct_mixed_cocycle       `N = -e(-z)·D`
    ellipticGammaCone_mixed_cocycle **`C_Γ(z) = Γ(z+a+b)Γ(z)/(Γ(z+a)Γ(z+b)) = -e(-z)`**

Together with the two shift relations added to `ExpConeProduct.lean`,

    singleFactor, singleProduct     `P(w) = ∏_{k ≥ 0}(1 - e(k b + w))`
    singleProduct_shift             `P(w) = (1 - e(w))·P(w + b)`
    hasProd_singleProduct_shifted   Fubini for the double product
    coneProduct_shift               `Φ(w) = P(w)·Φ(w + a)`
    coneProduct_comm                `Φ` is symmetric in its two periods

this establishes both defining properties of the multiplicative triptic source class for `Γ`:
`1`-periodicity, and a mixed multiplicative coboundary that is an exponential character (so its
logarithmic derivative is the constant `-2πi`).  Combined with the divisor computation, the
realizing source is now a proved member of the class with proved divisor `[0]`, and its translates
realize every class `[g]`.

The cancellation is exact and needs no analysis beyond the shift relations: in

    N = Φ(-z)Φ(a+b-z)Φ(z+a)Φ(z+b),   D = Φ(z+a+b)Φ(z)Φ(b-z)Φ(a-z),

every cone product cancels against a partner, leaving `P(-z)P(z+b)` against `P(z)P(b-z)`, whose
ratio is `(1 - e(-z))/(1 - e(z)) = -e(-z)`.

## Lean progress — the orbital charge is a class function on `G`

`GaloisForLFunctions/HTGeometry/TripticChargeClassFunction.lean` (wired, axiom-clean):

    meromorphicOrderAt_of_period       a period of a function is a period of its order
    shiftOrder_of_period               hence of every shift order
    tripticOrbitCharge_of_period       **`1`-invariance**, from `1`-periodicity of the source
    tripticOrbitCharge_of_shiftOrder_invariant
                                       **`τ`-invariance**, from `τ`-invariance of the shift-quotient
                                       divisor — the exact content of the mixed-cocycle condition,
                                       since an exponential character has no zeros or poles
    eq_of_add_zsmul                    one period upgrades to all its integer multiples
    tripticOrbitCharge_of_periodGroup  **the charge is constant on classes of `H₃ = ℤ + ℤτ + ℤσ`**

This is the well-definedness of `D_Y` as an element of `ℤ[G]`, `G = ℂ/H₃`: the three directions have
three different reasons, and only the `τ` one uses the defining cocycle condition of the source
class.  Together with `tripticOrbitCharge_mul` (additivity) and the elliptic-gamma realization it
completes every input of the abstract Kummer classification except finiteness of the class support
and the identification of the kernel with the differentially algebraic members.

Added to the same module (wired, axiom-clean):

    meromorphicOrderAt_eq_zero_of_untop₀
    finite_setOf_meromorphicOrderAt_ne_zero  the divisor of a meromorphic function meets every
                                             compact set finitely
    finite_setOf_shiftOrder_ne_zero          hence so does the shift-order support: a base point
                                             carries charge only if the source has a zero or pole at
                                             it or at its `σ`-translate

With `H₃`-invariance and compact local finiteness together, the charge is a well-defined finitely
supported function on `G` once a bounded fundamental domain is chosen, which is the last structural
input of `D : M → ℤ[G]`.

## Lean progress — finite order everywhere, and the half-line law at every period point

`GaloisForLFunctions/HTGeometry/EllipticGammaConeOrder.lean` (wired, axiom-clean):

    exists_notMem_of_countable                    a countable set is not the plane
    analyticOrderAt_ne_top_of_countable_zeroSet   an entire function with countable zero set is
                                                  nowhere locally zero
    withTop_sub_ne_top                            a difference of finite orders is finite
    countable_coneProduct_zeroSet                 the zero set is indexed by `ℕ × ℕ × ℤ`
    countable_ellipticGammaConeNum_zeroSet
    meromorphicOn_ellipticGammaCone
    meromorphicOrderAt_ellipticGammaCone_ne_top   **the order of `Γ` is finite everywhere**

Finiteness of the order is precisely the hypothesis `tripticOrbitCharge_mul` needs, so the divisor
map is now known to be additive on the realizing sources.

Added to `EllipticGammaConeDivisor.lean` (wired, axiom-clean):

    coneProduct_periodPoint_orbit_eq_zero_iff      **the general pole half line**: along the
                                                   `b`-orbit of `c + d·a + e·b`, the denominator
                                                   vanishes exactly for `d ≤ 0` and `m ≤ -e`
    coneProduct_num_periodPoint_orbit_eq_zero_iff  and the numerator exactly for `1 ≤ d`,
                                                   `1 - e ≤ m`
    meromorphicOrderAt_ellipticGammaCone_periodPoint
                                                   the order along that orbit, as the difference of
                                                   the two indicator conditions

The two half lines are disjoint (`d ≥ 1` against `d ≤ 0`), and in both regimes the shift difference
is supported at the single index `m = -e`.  So the charge is `1` on the orbit of *every* period
point, not only the origin — which is the statement that `D_Γ` is the class `[0]` in `ℤ[G]` rather
than a base-point-dependent number.

## Lean progress — products of gamma translates add their divisors

Added to `EllipticGammaConeDivisor.lean` and `EllipticGammaConeOrder.lean` (wired, axiom-clean):

    untop₀_ite_sub_ite
    shiftOrder_ellipticGammaCone_periodPoint       **the shift order along the orbit of any period
                                                   point is supported at the single index `m = -e`**,
                                                   uniformly in the two regimes `1 ≤ d` and `d ≤ 0`
    tripticOrbitCharge_ellipticGammaCone_periodPoint
                                                   hence the charge is `1` at *every* period point
    finite_shiftOrder_support_ellipticGammaCone_periodPoint
    ellipticGammaConeTranslate_eq_comp
    meromorphicOn_ellipticGammaConeTranslate
    meromorphicOrderAt_ellipticGammaConeTranslate_ne_top
    finite_shiftOrder_support_ellipticGammaConeTranslate
                                                   the support is a single index inside the class and
                                                   empty outside it
    tripticOrbitCharge_ellipticGammaConeTranslate_mul
                                                   **`D_{Y₁Y₂} = D_{Y₁} + D_{Y₂}` for translates**

The uniformity is the point: in the zero regime the shift difference is
`[1-e ≤ m+1] - [1-e ≤ m]` and in the pole regime it is `[m ≤ -e] - [m+1 ≤ -e]`, and both equal
`[m = -e]`.  So the charge does not depend on which representative of the class is taken as base
point, which is what makes `D` a function on `ℤ[G]` rather than on `ℂ`.

With additivity now available *on the realizing sources* — the finiteness and finite-order
hypotheses of `tripticOrbitCharge_mul` are discharged, not assumed — the card's "products add
divisors, integer powers give signed multiplicities" is formal for the gamma translates.

## Lean progress — the elliptic gamma source as a convergent atom series

`GaloisForLFunctions/HTGeometry/EllipticGammaConeSource.lean` (wired, axiom-clean):

    logDeriv_coneFactor            `(log(1 - e(w)))′ = -2πi·e(w)/(1 - e(w))`
    norm_logDeriv_coneFactor_le    where the factor is within `1/2` of one, its logarithmic
                                   derivative is at most `4π` times the deviation
    summable_logDeriv_coneFactor   hence the atom series converges, by the same geometric
                                   domination as the product
    logDeriv_coneProduct_eq_tsum   **`(log Φ)′(z) = ∑_{j,k ≥ 0} -2πi e(ja + kb + z)/(1 - e(ja + kb + z))`**

`Ψ = δ log Γ` is the difference of two such series, one at `z` and one at `a + b - z`.  This is the
object the principal-part normal form `F − R_trip(F)Ψ ∈ Mer_DA` is written in, now available as an
explicit convergent series rather than as a name.

Added to the same module (wired, axiom-clean):

    ellipticGammaSource            `Ψ = δ log Γ`, as a definition rather than a name
    logDeriv_of_periodic           a period of a function is a period of its logarithmic derivative
    ellipticGammaSource_periodic   **`Ψ(z+1) = Ψ(z)`**
    ellipticGammaSource_eq_sub     **`Ψ(z) = -(log Φ)′(a+b-z) - (log Φ)′(z)`**, the splitting into
                                   two convergent atom series

So `Ψ` is now a constructed object with its `1`-periodicity proved and its two-series expansion
available.  Its mixed difference is the logarithmic derivative of the cocycle `-e(-z)`, i.e. the
constant `-2πi`, which is the statement that `Ψ` itself lies in the mixed-constraint class `Q`.

## Lean progress — the two shift laws for the source, and the atom cancellation

Added to `ExpConeProduct.lean` and `EllipticGammaConeSource.lean` (wired, axiom-clean):

    differentiable_singleFactor, hasProdLocallyUniformlyOn_singleFactor
    differentiable_singleProduct       **the single-index product `P` is entire**
    singleProduct_eq_zero_iff
    logDeriv_comp_add_const
    logDeriv_singleProduct_shift       `(log P)′(w) = (log(1 - e(w)))′ + (log P)′(w + b)`
    logDeriv_coneProduct_shift         `(log Φ)′(w) = (log P)′(w) + (log Φ)′(w + a)`
    logDeriv_one_sub_expChar           `(log(1 - e(w)))′ = -2πi·e(w)/(1 - e(w))`
    expChar_atom_sum                   **`e(z)/(1 - e(z)) + e(-z)/(1 - e(-z)) = -1`**

These are the four ingredients of the mixed-difference computation.  Writing `S = (log Φ)′` and
`T = (log P)′`, the eight terms of `Ψ(z+a+b) + Ψ(z) - Ψ(z+a) - Ψ(z+b)` pair off under the first
shift law into `-T(z) + T(z+b) - T(-z) + T(b-z)`; the second shift law turns that into
`-L(z) - L(-z)` with `L(w) = -2πi·e(w)/(1 - e(w))`; and the atom identity evaluates it to `-2πi`.

So the mixed difference of `Ψ` is the constant `-2πi`, which is exactly the membership
`Ψ ∈ Q` that the normal form is stated against — now reduced to assembling four proved identities
rather than to any analytic input.

## Lean progress — `Ψ ∈ Q` is proved

`ellipticGammaSource_mixed_difference` (wired, axiom-clean):

    Ψ(z+a+b) + Ψ(z) - Ψ(z+a) - Ψ(z+b) = -2πi

off the zeros of the eight cone products and four single-index products involved, and off the two
points where `e(±z) = 1`.  Together with `ellipticGammaSource_periodic` this is exactly the
membership of the source in the mixed-constraint class:

    Δ_1 Ψ = 0,   Δ_a Δ_b Ψ = -2πi ∈ ℂ.

The proof is the three-stage collapse the card describes, now carried out mechanically: the eight
cone-source terms pair off under `logDeriv_coneProduct_shift` into four single-index terms; those
pair off under `logDeriv_singleProduct_shift` into two atoms; and `expChar_atom_sum` evaluates the
two atoms to `-1`, giving the constant `-2πi`.  No analytic input beyond the two product shift
relations is used.

## Lean progress — the residue normal form on one orbit

The kernel identification is now formal down to a single remaining step.  Five new modules, all
wired into `GaloisForLFunctions.HTGeometry`, all `#print axioms`-clean:

```text
TripticEntireRigidity          const_of_entire_of_periodic_of_mixed_const — an ENTIRE member of `Q`
                                is constant AND its mixed constant `C` is forced to `0`.  Two
                                Liouvilles: `Δ_σ f` is entire, `1`-periodic and changes by `C` under
                                `τ`, so its derivative is lattice-periodic hence constant, so it is
                                affine, and a genuine period kills both the slope and `C`
MeromorphicLogDerivLocalForm   laurentCoeff_logDeriv_eq_zero_of_le — a logarithmic derivative has NO
                                Laurent coefficient below the residue.  The corpus previously
                                computed only the residue itself
JacobiThetaSourcePrincipalPart analyticOrderAt_jacobiTheta₂_eq_one (every theta zero is simple) and
                                the COMPLETE principal part of `Ψ_θ = δ log θ`: residue `1` on the
                                odd half-period orbit, nothing anywhere else
TripticSeparatedPrincipalPart  exists_finiteSupport_separation_of_orbit_sum_eq_zero — a vanishing
                                orbital divisor makes both separated families of the coefficient
                                array FINITELY SUPPORTED, i.e. confines the poles to finitely many
                                full `σ`-lines and finitely many full `τ`-lines
TripticLineAtom /              rowAtom, colAtom and the incidence law: a `σ`-line atom has residue
TripticAtomIncidence /          `1` at every orbit point of its own row and `0` on every other row,
TripticResidueNormalForm        by `ℚ`-independence alone; hence
                                exists_atomCombination_residue_normalForm — every source of
                                vanishing orbital divisor has the residues of an explicit finite
                                combination of theta-source translates at every orbit point
```

Also built and reusable well beyond this card:
`DifferentialAlgebraicAntiderivative.differentialAlgebraicOver_of_deriv` — differential algebraicity
is stable under **integration**, not only differentiation (`k⟨y′⟩` has finite transcendence degree,
`y` satisfies `y′ = c` over it, then finite-transcendence descent), together with its analytic form
`differentiallyAlgebraic_of_deriv`, a pure jet reindexing.

What is left is the extension from order `-1` to all orders (the jets of the theta source, with pole
order `j+1`), the passage from one orbit to the finitely many that occur, and the application of
`const_of_entire_of_periodic_of_mixed_const` to the pole-free remainder.
