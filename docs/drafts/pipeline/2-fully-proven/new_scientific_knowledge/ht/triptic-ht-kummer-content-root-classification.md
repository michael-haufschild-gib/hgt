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
