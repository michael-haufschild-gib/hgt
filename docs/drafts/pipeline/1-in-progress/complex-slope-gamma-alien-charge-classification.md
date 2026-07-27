# Arbitrary complex affine Gamma products have one complete lattice charge

- **ID:** `complex-slope-gamma-alien-charge-classification`
- **Stage:** 1-in-progress
- **Type:** THEOREM / GENERAL HYPERTRANSCENDENCE LANDSCAPE
- **Scientific status:** `[PROVED HERE] [HOSTILE AUDIT PENDING] [NOVELTY UNVERIFIED]`
- **Extends:** `../3-formalized/new_scientific_knowledge/oriented-arbitrary-scale-gamma-alien-charge-law.md`
- **Named predecessor gap:** complex nonreal slopes and their complex-frequency carrier

## 1. Exact statement

Let

```text
G(z)=C exp(a z) product_(j=1)^d Gamma(lambda_j z+mu_j)^m_j,
C in C*, a,mu_j in C, lambda_j in C*, m_j in Z\{0}.       (1)
```

For `t in C*`, define the **complex scaled Gamma lattice charge**

```text
R_G(t)=sum_(j: t/lambda_j in Z\{0})
  m_j lambda_j exp(-2 pi i (t/lambda_j) mu_j).             (2)
```

Then exactly one branch occurs:

```text
R_G=0
  iff G is a finite sine--exponential--rational gauge
  iff G is differentially algebraic over C(z);             (3)

R_G!=0
  iff G is hypertranscendental over C(z).                  (4)
```

More explicitly, the first branch means that Gamma multiplication, recurrence, and reflection
reduce `G` to

```text
C exp(b z) Q(z) product_l sin(pi(kappa_l z+eta_l))^q_l,
Q in C(z)^x, q_l in Z.                                    (5)
```

No reality, common-ray, commensurability, or sign assumption is imposed on the slopes.

## 2. Complex Borel carrier

Put

```text
Psi=G'/G,
Tau=Psi'=sum_j m_j lambda_j^2 psi'(lambda_j z+mu_j).       (6)
```

The complete trigamma expansion and the normalization

```text
B(z^(-n-1))=xi^n/n!
```

give, modulo an entire function,

```text
B hat(Tau)(xi)
 =sum_j m_j exp(-(mu_j/lambda_j)xi)
       xi/(exp(xi/lambda_j)-1).                            (7)
```

The derivation is formal in `lambda_j`, so positivity or reality of the slope is irrelevant. At

```text
xi=2 pi i k lambda_j, k in Z\{0},
```

the `j`th summand has residue

```text
2 pi i k m_j lambda_j^2 exp(-2 pi i k mu_j).               (8)
```

Consequently,

```text
Res_(xi=2 pi i t) B hat(Tau)(xi)=2 pi i t R_G(t).          (9)
```

The complex singular lattice of the `j`th factor is `lambda_j Z*`. Two such lattices intersect
exactly when

```text
lambda_i/lambda_j in Q*.                                  (10)
```

Thus the charge splits canonically over `C*/Q*`, not merely over geometric rays.

## 3. Completeness of the zero-charge branch

Fix one equivalence class for `(10)`. Choose `delta in C*` such that

```text
lambda_j=n_j delta, n_j in Z\{0},                          (11)
```

for every factor in the class. This is possible because the class is finite and all slope ratios
are nonzero rational numbers.

For every `n_j<0`, Euler reflection replaces

```text
Gamma(n_j delta z+mu_j)^m_j
```

by a sine gauge times

```text
Gamma((-n_j)delta z+(1-mu_j))^(-m_j).                     (12)
```

This operation preserves `(2)`: if `t/(n_j delta)=k`, the reflected contribution at the same `t`
is

```text
(-m_j)(-n_j delta)
  exp(-2 pi i (-k)(1-mu_j))
=m_j n_j delta exp(-2 pi i k mu_j).                       (13)
```

All remaining slopes are positive integer multiples `N delta`. Gauss multiplication writes

```text
Gamma(N delta z+nu)
=C_N exp(beta_N z)
  product_(r=0)^(N-1) Gamma(delta z+(nu+r)/N).             (14)
```

This also preserves `(2)`. At frequency `t=l delta`, the sum of the new contributions is

```text
m delta exp(-2 pi i l nu/N)
  sum_(r=0)^(N-1) exp(-2 pi i l r/N),                     (15)
```

which is zero unless `N|l`, and equals the original contribution when `l=kN`.

Gamma recurrence now groups the common-slope offsets modulo `Z`. Hence the class has the normal
form

```text
A_DA(z) product_(c=1)^q Gamma(delta z+b_c)^M_c,            (16)
```

where the `b_c` are distinct modulo `Z`, every `M_c` is a nonzero integer, and `A_DA` has the
form `(5)`. For every nonzero integer `k`,

```text
R_G(k delta)
  =delta sum_(c=1)^q M_c exp(-2 pi i k b_c).               (17)
```

Put `zeta_c=exp(-2 pi i b_c)`. Distinctness of the offsets modulo `Z` makes the nonzero numbers
`zeta_c` pairwise distinct. If the charge vanishes, `(17)` for `k=1,...,q` is an invertible
Vandermonde system, so every `M_c=0`. Thus each `Q*`-class reduces to its DA gauge. Conversely,
the reflection, multiplication, and recurrence identities show directly that every product in
the normal form `(5)` has zero charge. This proves `(3)` at the identity-classification level.

## 4. Nonzero charge forces hypertranscendence

For each factor set

```text
h_j=1/lambda_j,
Delta_j f(z)=f(z+h_j)-f(z).                               (18)
```

The trigamma recurrence gives

```text
Delta_j (m_j lambda_j^2 psi'(lambda_j z+mu_j))
  =-m_j lambda_j^2/(lambda_j z+mu_j)^2 in C(z).           (19)
```

All translations commute. Applying every `Delta_j` to `(6)`, and applying the matching difference
first in each summand, yields

```text
Delta_1 ... Delta_d hat(Tau) in C(z).                     (20)
```

Adamczewski--Dreyfus--Hardouin, Theorem 1.2 in Case `S_infinity`, allows an arbitrary
`h in C*`. Finite shift peeling applied to `(20)` therefore forces

```text
hat(Tau) in C(z) or hat(Tau) is HT over C(z).             (21)
```

If `R_G!=0`, equation `(9)` gives a nonzero finite Borel pole. But `hat(Tau)=O(z^-1)`, and the
formal Borel transform of the expansion at infinity of every proper rational function is entire:

```text
B((z-a)^(-r))=xi^(r-1) exp(a xi)/(r-1)!.                  (22)
```

The meromorphic continuation `(7)` therefore excludes the rational branch of `(21)`.
Thus `hat(Tau)` is HT.

Choose a ray avoiding the finitely many directions on which some `lambda_j z` approaches the
negative real axis. A sufficiently small common sector about that ray supports the complete
Poincare expansions of every trigamma factor. Any algebraic differential equation for analytic
`Tau` would pass to its complete expansion and contradict hypertranscendence of `hat(Tau)`.
Therefore `Tau` is HT. If `G` were DA, differential-field closure would make `G'/G` and then
`Tau` DA. Hence `G` is HT, proving `(4)`.

## 5. Hostile attacks

1. **Opposite slopes.** This is the main cancellation test, not an exception. The two factors in
   Euler reflection have the same complex singular lattice and opposite contributions in `(13)`.
   For example `Gamma(z)Gamma(-z)` has zero charge and is a sine--rational gauge.
2. **Same ray but irrational scale ratio.** The lattices are disjoint even though the rays agree.
   The correct decomposition is `C*/Q*`, not the set of rays.
3. **Different rays with a common point.** A nonzero common lattice point forces a rational slope
   ratio, so this cannot occur across distinct classes.
4. **Offsets at poles.** Since every slope is nonzero, each affine Gamma factor is a well-defined
   meromorphic function; isolated poles do not affect field identities.
5. **Negative multiplicities.** DA elements form a field, and every charge and normal-form step is
   additive in the integer multiplicity.
6. **No common Stirling sector.** A finite set of slopes excludes only finitely many ray
   directions. A ray avoiding all of them has a small common sector.
7. **Borel poles alone.** They do not imply HT. They only exclude the rational branch after the
   independent ADH finite-shift dichotomy.
8. **Beyond-all-orders reflection terms.** Opposite-slope sine terms may be invisible to the
   common formal Laurent expansion. They occur only in the explicitly DA zero-charge gauge.
9. **Infinite products.** Not claimed. Finiteness is used in the common-scale reduction,
   Vandermonde step, common-sector choice, and finite shift word.

## 6. Literature collision audit

The broad claim that complex Gamma rays force hypertranscendence is old:

- Steven B. Bank, *On Certain Canonical Products which Cannot Satisfy Algebraic Differential
  Equations*, Funkcialaj Ekvacioj 23 (1980), 335--349, proves that
  `Gamma(z)Gamma(cz)` is HT over a Nevanlinna field exactly when `c!=-1`, that every unshifted
  three-factor product `Gamma(z)Gamma(bz)Gamma(cz)` is HT, and sufficient conditions for more
  unshifted complex rays.
- Boris Adamczewski, Thomas Dreyfus, and Charlotte Hardouin,
  *Hypertranscendence and linear difference equations*, JAMS 34 (2021), 475--503,
  Theorem 1.2, explicitly treats `z -> z+h` for every `h in C*`.
- Euler reflection, Gauss multiplication, recurrence, Bernoulli Borel continuation, and finite
  Fourier/Vandermonde uniqueness are classical.

Preliminary exact searches did not locate the signed, shifted, arbitrary-finite classification
`(2)`--`(5)`. Absence from search is not priority. The possible novelty is only the exact
complex-lattice charge and its zero-charge iff DA completeness; individual HT cases and the parent
mechanisms are known.

Primary sources:

- Bank: `https://fe.math.kobe-u.ac.jp/FE/FE_pdf_with_bookmark/FE21-30-en_KML/fe23-335-349/fe23-335-349.pdf`
- Adamczewski--Dreyfus--Hardouin: `https://arxiv.org/abs/1910.01874`

## 7. RH relevance and non-overclaim

The theorem supplies an orientation-sensitive complex-frequency invariant that the real-slope
corpus theorem could not see. It can certify that a finite archimedean carrier with an off-axis
slope is irreducibly HT unless every complex lattice charge is discharged by exact
multiplication/reflection identities.

It does **not** prove RH. A fixed finite Gamma product is still an archimedean reader and carries
no zeta divisor data. An RH application requires a non-target-fed source theorem that converts an
off-critical zero, or an equivalent source defect, into a forced nonzero complex lattice charge
inside an independently DA-constrained carrier.

`[RH OPEN CORE: COMPLEX-CHARGE SOURCE WELD]`

Construct such a source map without assuming zero location and prove both:

```text
source law -> carrier is DA,
off-critical source defect -> R_G!=0.                     (23)
```

The classification would then make the off-critical defect impossible.

### Canonical Euler slopes do not discharge the weld

The corpus already supplies a canonical arithmetic family of nonreal slopes:

```text
lambda_p = i log(p)/(2 pi).
```

Euler reflection gives

```text
1-p^(-s)
 = -2 i pi exp(-s log(p)/2)
   / (Gamma(lambda_p s) Gamma(1-lambda_p s)).
```

This does **not** solve `(23)`. The two reciprocal-Gamma halves have factor data

```text
(-1, lambda_p, 0),  (-1, -lambda_p, 1),
```

and their complex charge cancels at every frequency. Hence every finite semilocal Euler product
has identically zero complex Gamma charge, off the critical line as well as on it. Reflection,
recurrence, and Gauss multiplication preserve that zero charge, so no finite identity-generated
repackaging of ordinary Euler factors can emit the needed defect.

This is the exact boundary of the source weld:

```text
finite unpolarized Euler/Gamma source  ->  R=0 identically;
successful source                     ->  chiral polarization or a genuinely cofinal limit.
```

A chiral half chosen after inserting a zero would merely restate the target and is inadmissible.
The remaining source must polarize the two halves before divisor insertion, or produce an infinite
charge boundary not reducible to finite Gamma identities.

### Positive survivor: the Gamma--Meixner boundary polarizes before divisor insertion

The successor

```text
gamma-meixner-alien-charge-polarization-flow.md
```

identifies an existing positive source which canonically chooses the two halves. The time-`theta`
Gamma--Meixner density has pole-oriented factors

```text
Gamma(theta/4+lambda s), Gamma(theta/4-lambda s).
```

At lattice frequency `k lambda`, their symmetric and chiral charges are

```text
-2 i lambda sin(pi k theta/2),
 2   lambda cos(pi k theta/2).
```

After division by the affine scale `2 lambda`, these form an exact unit vector. At the singular
time-zero endpoint the symmetric component is zero and the chiral component is one. Scaling by
`lambda_p=i log(p)/(2 pi)` gives the two Euler Gamma halves, with the second converted to
`Gamma(1-lambda_p s)` by recurrence.

Thus “chiral polarization” and “genuinely cofinal limit” are not separate escape clauses: the
positive convolution-root family canonically produces the chiral Euler phase at its cofinal
boundary. This still does not prove RH. The remaining weld is the phase-sensitive map from that
source endpoint to the FE/Schwarz relative Xi fibre.

## 8. Lean status

`[LEAN-PROVED ALGEBRAIC CORE]`

The new module

```text
formal/GaloisForLFunctions/HTGeometry/GammaComplexLatticeCharge.lean
```

proves unconditionally:

1. exact nonempty-intersection classification for complex integer singular lattices;
2. disjointness across noncommensurate classes;
3. reflection involution on arbitrary complex affine Gamma coefficient data;
4. reflection invariance of every factor charge and the complete finite charge;
5. exact finite Vandermonde zero-charge classification for a common complex scale;
6. positive detection of every nonzero orbit-multiplicity vector within the first full frequency
   block;
7. root-of-unity orthogonality for every positive Gauss multiplication degree;
8. exact Gauss-multiplication invariance on the old lattice and zero expanded charge off it;
9. exact charge-neutrality of every local reciprocal-Gamma Euler pair and every finite semilocal
   family of such pairs;
10. exact doubled nonzero reflection-odd charge on every Euler slope lattice;
11. individual detection of every factor in a finite pairwise noncommensurate odd-polarized
    family.

Existing modules formalize the abstract shift-word assembly and real-slope analytic Gamma
superselection, with ADH and Borel selectors kept as explicit hypotheses where applicable:

```text
formal/GaloisForLFunctions/HTGeometry/FiniteCommutingShiftPeeling.lean
formal/GaloisForLFunctions/HTGeometry/GammaPhaseCompletion.lean
formal/GaloisForLFunctions/HTGeometry/GammaOrientedAlienCharge.lean
```

The remaining algebraic formal target is assembly with the existing complex meromorphic
multiplication theorem into the zero-charge DA normal form.

Analytic Gamma, Borel continuation, and ADH must not be hidden as axioms. The final analytic
classification remains at paper stage until those parents have unconditional Lean realizations or
the formal statement exposes them honestly as hypotheses and is not mislabelled as the analytic
theorem.

## Gates

- [x] exact complex charge stated
- [x] complex singular-lattice support computed
- [x] `C*/Q*` separation proved
- [x] reflection and multiplication invariance proved on paper
- [x] zero-charge Vandermonde completeness proved on paper
- [x] arbitrary complex-step shift word proved on paper
- [x] nonzero-charge HT branch proved from named parent theorem
- [x] Bank complex-ray collision identified
- [ ] independent hostile proof audit
- [ ] full priority audit
- [x] unconditional Lean formalization of lattice separation, reflection invariance, and
  Vandermonde completeness
- [x] unconditional Lean formalization of multiplication invariance
- [ ] unconditional Lean formalization of DA normal-form assembly
- [ ] non-target-fed RH source weld
