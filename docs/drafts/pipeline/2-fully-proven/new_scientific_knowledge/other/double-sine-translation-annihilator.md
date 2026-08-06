# The double-sine logarithmic derivative has augmentation-ideal translation annihilator

- **ID:** `double-sine-translation-annihilator`
- **Stage:** 2-fully-proven / needs independent audit
- **Type:** THEOREM (paper)
- **Scientific status:** `[NOVELTY UNVERIFIED]` -- the proof is complete modulo the already-stated
  several-translation telescoping theorem, but multiple-sine and generalized Holder literature has
  not yet been audited for an equivalent or stronger result.
- **Statement:** For positive rationally independent periods `omega_1,omega_2`, the logarithmic
  derivative of the double sine is hypertranscendental, and its complete constant-coefficient
  structural-translation annihilator modulo differentially algebraic functions is the augmentation
  ideal `(T_1-1,T_2-1)`. Consequently a finite integer product of structural translates of the
  double sine is differentially algebraic exactly when its total exponent is zero.

## Setup

Let `omega_1,omega_2>0` and `omega_1/omega_2 notin Q`. Let `S_2(z)` be a standard double-sine
normalization. The choice between reciprocal shift conventions changes only signs below. Write

```text
L_2(z)=d/dz log S_2(z),
T_j f(z)=f(z+omega_j),
x_j=T_j-1.
```

The standard double-sine equations have the form

```text
S_2(z+omega_1)/S_2(z)=(2 sin(pi z/omega_2))^epsilon_1,
S_2(z+omega_2)/S_2(z)=(2 sin(pi z/omega_1))^epsilon_2,
epsilon_j in {1,-1}.
```

Logarithmic differentiation gives

```text
x_1 L_2=epsilon_1 a_2,
x_2 L_2=epsilon_2 a_1,                              (1)

a_j(z)=(pi/omega_j) cot(pi z/omega_j).
```

Each `a_j` is DA over `C(z)`. Thus

```text
(x_1,x_2) subset Ann_DA(L_2).                        (2)
```

The content is the reverse inclusion, whose only non-formal input is hypertranscendence of `L_2`.

## Hypertranscendence of the double-sine logarithmic derivative `[PROVED HERE]`

Put

```text
u_j(z)=exp(2 pi i z/omega_j),
E_j=C(u_j),
K=E_1 E_2.
```

Each `E_j` is a differential field of `omega_j`-periodic meromorphic functions and is DA over
`C(z)`. The fields `E_1,E_2` are algebraically independent over `C`: after clearing denominators,
an algebraic relation would be an exponential-polynomial relation

```text
sum_(m,n) p_(m,n)(z)
  exp(2 pi i (m/omega_1+n/omega_2) z)=0.
```

The frequencies are distinct because `omega_1/omega_2` is irrational, and finite exponential
polynomials with distinct frequencies are linearly independent over `C(z)`.

Hence `K` is the function field of the product of the two multiplicative cylinders.

### Common constants

Every element of `K<L_2>_delta` is meromorphic on `C`. If such an element is fixed by both `T_1`
and `T_2`, its period group contains

```text
Z omega_1+Z omega_2,
```

which is dense in the real line. A meromorphic function with this dense period group has no pole,
since one pole would generate an accumulating pole set; continuity then makes it constant on every
horizontal line, and the identity theorem makes it constant on `C`. Therefore

```text
(K<L_2>_delta)^(T_1,T_2)=C.                            (3)
```

### Paired telescoping consequence

Assume for contradiction that `L_2` is DA over `C(z)`. Since `K(z)` is DA over both `K` and
`C(z)`, transitivity makes `L_2` DA over `K`.

Apply the several-translation additive telescoping theorem proved in
`paired-quasi-elliptic-constraint-rigidity` to (1) and (3). There are a nonzero operator

```text
A in C[delta]
```

and one `g in K` such that simultaneously

```text
T_1 g-g=A(a_2),
T_2 g-g=A(a_1).                                       (4)
```

Only the first equation is needed for the contradiction.

### Descent to one cylinder

Translation by `omega_1` acts trivially on `E_1` and acts on

```text
u_2
```

by multiplication with

```text
q=exp(2 pi i omega_1/omega_2).
```

The irrationality assumption makes `q` non-torsion. Specialize the `E_1` factor at a point outside
the numerator and denominator exceptional loci of `g`. Equation (4) descends to

```text
h(qX)-h(X)=A(b(X))                                    (5)
```

for some `h in C(X)`, where

```text
b(X)=c (X+1)/(X-1),  c != 0,
```

is the rational expression for `a_2` in the coordinate `X=u_2`.

### Multiplicative-orbit residue obstruction

Let `r` be the differential order of `A`. In the coordinate `X`, differentiation in `z` is a
nonzero scalar multiple of

```text
X d/dX.
```

Since this vector field is nonzero at `X=1`, the highest derivative in `A(b)` produces a pole of
order `r+1` at `X=1` with nonzero coefficient. Lower derivatives cannot cancel this top principal
part. The rational function `A(b)` has no other pole in the multiplicative orbit

```text
q^Z * 1,
```

because `q` is not a root of unity.

For every rational `h`, each fixed-order principal-part coefficient of

```text
h(qX)-h(X)
```

sums to zero over a `q^Z`-orbit: only finitely many orbit points occur in the pole divisor of `h`,
so the coefficients telescope. The right side of (5) has one nonzero order-`r+1` contribution on
the orbit of `1`, contradicting this orbit balance.

Thus `L_2` is hypertranscendental over `C(z)`.

## Exact annihilator `[PROVED HERE]`

Let

```text
R=C[T_1^(+-1),T_2^(+-1)].
```

The evaluation map

```text
aug:R -> C,  P |-> P(1,1)
```

has kernel `(x_1,x_2)`. Hence every `P in R` has a decomposition

```text
P=aug(P)+x_1 A+x_2 B.                                  (6)
```

By (1), the last two terms of `P L_2` are DA. Therefore

```text
P L_2 is DA  iff  aug(P)L_2 is DA.
```

Hypertranscendence of `L_2` forces `aug(P)=0`. Together with (2),

```text
Ann_DA(L_2)=(T_1-1,T_2-1).                             (7)
```

The structural translation module generated by `L_2` modulo DA functions is consequently the
one-dimensional module

```text
R/(T_1-1,T_2-1) ~= C.                                  (8)
```

Every structural translate represents the same nonzero HT class.

## Classification of finite translate products `[PROVED HERE]`

Let

```text
P=sum_(m,n) c_(m,n) T_1^m T_2^n
```

have finite support and integer coefficients, and define

```text
F_P(z)=product_(m,n)
  S_2(z+m omega_1+n omega_2)^(c_(m,n)).
```

Then

```text
F_P'/F_P=P L_2.
```

If `F_P` is DA, its logarithmic derivative is DA. Conversely, if `P L_2` is DA, the equation

```text
Y'=(P L_2)Y
```

over a DA extension makes `F_P` DA by transitivity. Equation (7) therefore gives

```text
F_P is DA
  iff P(1,1)=0
  iff sum_(m,n) c_(m,n)=0.                              (9)
```

Thus net multiplicity is the complete differential-algebraic invariant of every finite structural
translate product.

### Unconditional Lean formalization

Three modules now carry the theorem's machine-checked content, all axiom-clean (`propext`,
`Classical.choice`, `Quot.sound` only).

`GaloisForLFunctions.HTGeometry.MultiplicativeOrbitNonSummability` builds the multiplicative
dilation `X |-> qX` of `C(X)` as the localization of the polynomial substitution `p |-> p(qX)`,
proves the exact regularity transport `RegularAt (sigma_q g) w <-> RegularAt g (qw)`, generalizes
the additive orbit obstruction of `RationalNonSummability` to an arbitrary injective orbit
`orb : Z -> C`, and specializes it to the multiplicative orbit. The capstone
`not_dilationTelescoped_of_unique_multOrbit_pole` is the orbit-balance obstruction of the section
"Multiplicative-orbit residue obstruction": a rational function with exactly one pole on
`p_0 q^Z` is not `h(qX) - h(X)` for any rational `h`. The module also proves
`exp_two_pi_I_zpow_ne_one`: an irrational rotation number gives a non-torsion multiplier, which is
exactly why `q = exp(2 pi i omega_1/omega_2)` is not a root of unity.

`GaloisForLFunctions.HTGeometry.DoubleSineOrbitResidueObstruction` supplies the pole computation.
It proves the exact numerator recursion `f (X-1)^k = p  ==>  f' (X-1)^(k+1) = p'(X-1) - k p`, hence
that the Euler operator `delta = X d/dX` raises the pole order at `X = 1` by exactly one; iterating
on `b(X) = c (X+1)/(X-1)` gives `A(b) (X-1)^(r+1)` a polynomial whose value at `1` is
`a_r` times a nonzero constant. Therefore `A(b)` has a pole at `1` and is regular everywhere else,
so it has exactly one pole on `q^Z`. The capstone
`not_dilationTelescoped_ratFuncEulerCombination_cotModel` (and its period form
`not_dilationTelescoped_irrationalPeriodRatio`) is equation (5) of the descent: no rational `h`
satisfies `h(qX) - h(X) = A(b)(X)`. This is the analytic contradiction of the hypertranscendence
proof, formalized without hypotheses beyond `q` non-torsion, `c != 0`, `a_r != 0`.

`GaloisForLFunctions.HTGeometry.DoubleSineAugmentationAnnihilator` formalizes (6)-(9) as an exact
theorem about any source with the double-sine step property. For `Psi` with every single-period
defect `T_j Psi - Psi` differentially algebraic and `Psi` itself hypertranscendental,

```text
differentialAlgebraicOver_transApply_iff_augMap_eq_zero :
  Q Psi is DA over C(z)  <->  augMap Q = 0,
daTranslationAnnihilator_eq_augIdeal :
  {Q | Q Psi is DA} = (T_1-1, ..., T_N-1),
differentialAlgebraicOver_transApply_iff_sum_coeff_eq_zero :
  Q Psi is DA  <->  sum of coefficients of Q = 0,
not_differentialAlgebraicOver_transApply_monomial :
  no nonzero single translate is DA.
```

The last two are (9) and (8): total exponent is the complete differential-algebraic invariant, and
every structural translate represents the same nonzero class. Compare
`differentialAlgebraicOver_transApply_barnesSource_iff`, whose annihilator is the principal ideal
`(prod_j (T_j - 1))`: the two Lean theorems exhibit the reflection-induced collapse of
`R/(x_1 x_2)` to `R/(x_1, x_2)` as a comparison of two proved annihilators, not as an analogy.

Still not formalized: the construction of the double sine itself, the several-translation
telescoping theorem, and the two-cylinder coefficient field separation, i.e. the reduction of the
hypertranscendence statement to equation (5).

### Formalization of the algebraic core

The abstract algebraic content of (9) — that the operator annihilator modulo DA is the augmentation
ideal `(T_1-1,T_2-1)`, equivalently that a finite integer translate product is DA exactly when its
total exponent `sum c_(m,n)` vanishes — is formalized axiom-clean in
`GaloisForLFunctions.OrbitBalanceAugmentation`. Modeling a finite integer combination of translates
on the orbit group as a divisor `D : (Z^2) ->0 Z`, the theorem
`mem_augmentationSubmodule_iff_orbitDegree_zero` proves

```text
D in augmentationSubmodule  <->  orbitDegree D = 0,
```

i.e. `D` is a Z-combination of balanced point-mass differences `[g]-[h]` (the augmentation ideal,
generated by the `T_j-1`) iff its total exponent (orbit degree / augmentation map) is zero. The
degree-zero telescoping direction reuses `eq_sum_single_sub_base_of_orbitDegree_zero` from
`GaloisForLFunctions.OrbitBalance`. The only non-formal input excluded from this core is the analytic
hypertranscendence of `L_2` giving the reverse inclusion `Ann_DA(L_2) subset (T_1-1,T_2-1)`.

## Reflection-induced rank collapse

The parent Barnes theorem gives, for the unsymmetrized double-gamma logarithmic derivative,

```text
Ann_DA(Psi_2)=((T_1-1)(T_2-1)).                         (10)
```

The double sine is the reflection quotient of the double gamma. Its logarithmic derivative is the
corresponding reflected combination. Equation (7) shows that reflection does not merely grade the
Barnes module: it collapses its Stanley--Reisner boundary module

```text
R/(x_1 x_2)
```

to the common rank-one class

```text
R/(x_1,x_2).
```

This is the first exact model in the project where imposing the natural special-function reflection
changes the complete DA structural matroid rather than only adding a parity label.

## RH-route consequence

`[BRIDGE / ROUTE MODEL]` The theorem does not prove an RH statement. It gives a precise model for
what the completed zeta functional equation would have to do on a divisor-enriched source module:
kill every structural difference while leaving one common hypertranscendental class. Reflection
alone does not kill that final class. A valid Euler--Gamma theorem must identify the arithmetic
constraint acting on the surviving common class; otherwise the construction is only a Gamma model.

The result therefore sharpens the source target:

```text
completed FE reflection
  -> structural rank collapse to one HT class,
exact Euler multiplicativity
  -> obstruction on that final class.
```

No limiting family, operator, positivity condition, or propagated carrier is used.

## Novelty and parent-theory audit

### Established ingredients

1. Standard double-sine functional equations.
2. Several-translation parameterized Picard--Vessiot telescoping.
3. Algebraic independence of incommensurate exponentials.
4. Multiplicative `q`-orbit residue obstruction for rational summability.
5. The augmentation-ideal identity for a Laurent polynomial ring.

### Potential scientific residue

The possibly new result is the combined theorem: differential hypertranscendence of the
incommensurate double-sine logarithmic derivative, its exact two-direction DA annihilator, and the
classification of every finite structural translate product by total exponent. The comparison with
the Barnes boundary ideal identifies an exact reflection-induced matroid quotient.

No scientific-novelty promotion is made. The full multiple-sine, generalized Holder,
parameterized-difference-Galois, and special-function product literature must be checked for the
exact statement and mechanism. Independent experts must also decide whether (7)--(10) are a
significant new classification or a routine synthesis once the question is posed.

## Boundaries

1. The proof uses positive real periods with irrational ratio. It does not cover a discrete complex
   period lattice, where the common fixed field is elliptic rather than constant.
2. Only structural translations are classified.
3. Coefficients of translation operators are constant.
4. The proof inherits the independent-audit obligation of the paired telescoping theorem.
5. The double sine itself and the several-translation parameterized telescoping theorem are not
   yet Lean objects. What is Lean-proved unconditionally is the algebraic skeleton on both ends:
   the multiplicative-orbit residue obstruction that kills the descended `q`-difference equation,
   and the exact augmentation annihilator with its total-exponent classification, stated for any
   source with the double-sine step property. The missing Lean link is the reduction of the first
   to the second.

## Gates

- [x] double-sine logarithmic-derivative equations isolated;
- [x] common-constant collapse proved;
- [x] two-cylinder coefficient field separated;
- [x] paired telescoping reduction proved;
- [x] multiplicative-orbit residue contradiction proved;
- [x] hypertranscendence proved on paper;
- [x] exact augmentation annihilator proved;
- [x] every finite translate product classified;
- [x] Barnes-versus-double-sine rank collapse identified;
- [ ] normalization and sign convention checked against a primary source;
- [ ] independent audit of paired telescoping and specialization;
- [ ] exact/equivalent/stronger literature search;
- [ ] independent significance and novelty verdict;
- [x] multiplicative-orbit residue obstruction formalized unconditionally in Lean;
- [x] Euler-operator pole computation for the cotangent model formalized unconditionally in Lean;
- [x] exact augmentation-ideal annihilator and total-exponent classification formalized
  unconditionally in Lean;
- [ ] Lean reduction of hypertranscendence to the descended `q`-difference equation (double sine
  construction, several-translation telescoping, two-cylinder separation).
