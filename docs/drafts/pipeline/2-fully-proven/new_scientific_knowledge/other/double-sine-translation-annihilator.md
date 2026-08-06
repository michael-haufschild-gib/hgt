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

`GaloisForLFunctions.HTGeometry.CylinderCoordinateEulerBridge` closes the coordinate change that
connects the analytic statement to the rational model. It proves the cotangent identity

```text
cos w / sin w = i (e^(2iw)+1)/(e^(2iw)-1),
(pi/omega) cot(pi z/omega)
  = eval_u (C (i pi/omega) (X+1)) / eval_u (X-1),   u = exp(2 pi i z/omega),
```

so the cotangent term of the double-sine functional equation is literally the value of the
numerator and denominator polynomials of `cotModel`. It proves that differentiation in `z` is the
Euler operator in the coordinate,

```text
d^n/dz^n [f(exp(a z))] = a^n (u d/du)^n f  evaluated at exp(a z),
```

on any open set where `f` is analytic (`iteratedDeriv_comp_exp_mul`), so a constant-coefficient
order-`r` differential operator in `z` becomes a constant-coefficient order-`r` Euler-operator
polynomial with proportional top coefficient. Finally it proves that the analytic Euler jets of
`c(u+1)/(u-1)` obey exactly the polynomial recursion `eulerNum` of the rational model
(`eulerOp_iterate_cotFun`), hence `eulerCombinationFun_eq`: the analytic `A(b)` is the value of the
rational `A(b)`. The residue obstruction therefore applies to the genuine cotangent term, not to a
formal stand-in.

The whole pole-order and orbit-balance layer is proved over an arbitrary base field, not only over
`C`. That removes the specialization step of the section "Descent to one cylinder": the paired
telescoping theorem produces `g` in the two-cylinder field `C(u_1,u_2)`, and taking the base field
to be `C(u_1)` applies the obstruction there directly, because every pole of `A(b)` and every point
of the orbit `q^Z` lies in the constant subfield `C`. The theorem
`not_dilationTelescoped_twoCylinder` is exactly this form. The specialization argument, and with it
one of the card's open audit obligations, is therefore not needed.

The common-constant collapse (3) is already corpus-owned:
`meromorphicNF_constant_of_rankTwo_realDependent_periods` in
`GaloisForLFunctions.HTGeometry.RankTwoRealDependentPeriods` proves that a meromorphic normal-form
function invariant under the integer span of two `Q`-independent, `R`-dependent periods is
constant, which is exactly the joint fixed-field collapse used at (3).

`GaloisForLFunctions.HTGeometry.CylinderDifferentialCharacter` makes the cylinder a differential
field. On the cylinder the coordinate is an exponential, so `d/dz` is `lam` times the Euler
operator, with `lam = 2 pi i/omega`; the module builds that derivation (`cylDeriv`, `cylDerivation`,
`cylinderDifferential`), identifies its jets on the cotangent model
(`cylDeriv_iterate_cotModel`), and proves the theorem the telescoping reduction needs:

```text
no_constantCharacter_dilationTelescoping :
  sigma_q k - k  !=  sum_n alpha_n d^n b     for all rational k,
```

for every nonzero finite constant character `alpha`, every non-torsion `q`, every nonzero `lam`
and every nonzero `c`. Three equivalent shapes are given -- explicit iterate, `differentialJet`,
and `Finsupp.linearCombination` -- the last being exactly what the arbitrary-family Ostrowski
criterion produces. `no_constantCharacter_dilationTelescoping_twoCylinder` is the instance over
`C(u_1)`, where the paired telescoping theorem actually produces its base element.

`GaloisForLFunctions.HTGeometry.DoubleSineCylinderHypertranscendence` performs the reduction.
The several-translation telescoping theorem is corpus-owned: it is the arbitrary-family
differential Ostrowski criterion
`automorphismFamily_differentialIndependent_iff_no_constant_simultaneous_jet_telescoping` of
`SourceLogarithmicBoundary`, proved for a possibly noncommuting family with common fixed field the
constants. Feeding the character obstruction into it gives

```text
hypertranscendentalOver_of_cotangentCylinderIncrement :
  Psi additive primitive for a compatible automorphism family with common fixed field C,
  increments in C(u_1)(u_2),
  one direction acting by a non-torsion dilation of u_2 with cotangent-model increment
  ==>  Psi is hypertranscendental over C(u_1,u_2).
```

Only one of the two translation directions is examined; the second enters solely through the
common fixed-field hypothesis, which is where the two incommensurate periods are used, and which
is corpus-owned as `meromorphicNF_constant_of_rankTwo_realDependent_periods`.

`GaloisForLFunctions.HTGeometry.IncommensuratePeriodMeromorphicModel` builds the first two pieces
of the concrete model inside the global meromorphic field.

*The common fixed field.* A germ fixed by two translations is fixed by their whole integer span
(`addTranslationMeroEquiv_fixed_of_mem_intSpan`). For two `Q`-independent, `R`-dependent periods --
two positive reals with irrational ratio -- that span is not discrete, so it contains arbitrarily
small nonzero periods, and a global meromorphic germ with arbitrarily small periods is constant.
Hence `exists_constant_of_two_realDependent_translations_fixed`, and in period form
`exists_constant_of_two_realPeriods_fixed`: for `Irrational (omega_1/omega_2)`, the common fixed
field of the two translations in the global meromorphic field is exactly `C`. This discharges the
`hfixed` hypothesis of the reduction theorem, and it is the only place where incommensurability of
the periods enters.

*Independent cylinder coordinates.* The exponential characters `z |-> exp(mu z)` are injective-in-`mu`
monoid homomorphisms of the additive group of `C`, so Dedekind independence of characters gives
`exp_coeff_eq_zero_of_sum_eq_zero`: exponentials with pairwise distinct frequencies are linearly
independent. Point evaluation of global analytic germs is a ring homomorphism, so the same holds
inside the meromorphic field (`physicalExponentialMero_coeff_eq_zero_of_sum_eq_zero`). This is the
separation statement behind the two-cylinder coefficient field: with `omega_1/omega_2` irrational
the frequencies `m(2 pi i/omega_1) + n(2 pi i/omega_2)` are pairwise distinct, so
`u_1 = exp(2 pi i z/omega_1)` and `u_2 = exp(2 pi i z/omega_2)` are independent coordinates.

*Algebraically independent coordinates.* `algebraicIndependent_pair_physicalExponentialMero` turns
the frequency separation into the exact statement: for `Q`-independent frequencies the two
exponential modes are algebraically independent over `C`. A polynomial relation expands into a
finite exponential sum whose frequencies `m lambda_1 + n lambda_2` are pairwise distinct
(`pairFrequency_injective`), so every coefficient vanishes.

*The embedded cylinder field and its translation action.* Each coordinate is therefore
transcendental over `C`, so `C(X)` embeds in the meromorphic field by `X |-> u` (`cylinderEmbed`,
injective by `cylinderEmbed_injective`). Under that embedding translation by `tau` is exactly the
multiplicative dilation by `exp(lambda tau)`:

```text
addTranslationMeroEquiv_cylinderEmbed :
  T_tau (iota y) = iota (ratFuncScale (exp (lambda tau)) y).
```

So the translation action on the embedded cylinder coordinate field is literally the
`ratFuncScale` against which the orbit-balance obstruction was proved. For
`lambda_j = 2 pi i/omega_j` this gives `T_{omega_1} u_1 = u_1` and
`T_{omega_1} u_2 = q u_2` with `q = exp(2 pi i omega_1/omega_2)`, the non-torsion multiplier.

*The two-cylinder field.* Algebraic independence also makes the second coordinate transcendental
over the first coordinate's function field: `injective_eval₂_second_cylinder` proves that
evaluating a polynomial over `C(u_1)` at `u_2` is injective, by transporting
`AlgebraicIndependent.transcendental_adjoin` down to the polynomial ring and then up to the
fraction field with `IsFractionRing.isAlgebraic_iff`. Hence `twoCylinderEmbed` embeds
`RatFunc (RatFunc C) = C(u_1)(u_2)` in the global meromorphic field, injectively
(`twoCylinderEmbed_injective`), with the explicit numerator/denominator formula
`twoCylinderEmbed_div`. This is the coefficient field in which the paired telescoping theorem
produces its base element, now a literal subfield of the meromorphic field.

*The translation action on the two-cylinder field.* `addTranslationMeroEquiv_twoCylinderEmbed`
transports the action: whenever the translation `tau` is a period of the first coordinate
(`exp(lambda_1 tau) = 1`, i.e. `tau in omega_1 Z` for `lambda_1 = 2 pi i/omega_1`), translation of
an embedded element is exactly the multiplicative dilation of the second coordinate,

```text
T_tau (iota y) = iota (ratFuncScale (exp(lambda_2 tau)) y),
```

with the coefficient field `C(u_1)` fixed pointwise. For `tau = omega_1` the dilation factor is
`q = exp(2 pi i omega_1/omega_2)`, the non-torsion multiplier of the descended equation. This is
literally the `ratFuncScale` action of `not_dilationTelescoped_twoCylinder`, so the orbit-balance
obstruction now applies to the genuine translation of genuine meromorphic functions.

*The differential structure on the cylinder.* `meroFieldDeriv_cylinderEmbed` transports
differentiation the same way:

```text
(iota y)' = iota (cylDeriv lambda y),      cylDeriv lambda = lambda * (X d/dX),
```

so the cylinder embedding is a differential embedding. The proof runs the chain rule on polynomials
(`deriv_aeval_physicalExponentialMero`, an induction whose only inputs are
`physicalExponentialMero_deriv` and the Leibniz rule) and then extends to quotients by the
`y Q = P` trick: the difference of the two derivations, multiplied by the nonzero image of the
denominator, vanishes. Consequently the constant-coefficient differential characters of
`CylinderDifferentialCharacter` are the genuine `z`-derivatives of genuine meromorphic functions,
and the jets appearing in the Ostrowski criterion are the ones computed by `cylDeriv`.

`GaloisForLFunctions.HTGeometry.CotangentMeromorphicIdentification` identifies the increment.
The cotangent is built as a genuine meromorphic germ `cotMero a = cos(a z)/sin(a z)`, and

```text
cylinderEmbed_cotModel        : iota (i (X+1)/(X-1))      = cot (a z),
cylinderEmbed_cotModel_period : iota ((i pi/omega)(X+1)/(X-1)) = (pi/omega) cot(pi z/omega),
```

where `iota` is the cylinder embedding with coordinate `exp(2 i a z)`. The proof cross-multiplies
to an identity of entire germs and evaluates pointwise, where it is the exponential identity
`i (e^(2iw)+1) sin w = cos w (e^(2iw)-1)`. So the right-hand side of the double-sine step equation
-- the logarithmic derivative of the order-one multiple sine `2 sin(pi z/omega)`, which the corpus
owns as `multipleSineOneLogDeriv` -- is literally the embedded `cotModel` against which the
orbit-balance obstruction was proved.

### The realization route

Nothing in the proof uses that the periods are *real* -- only that they are `R`-collinear (which
makes the joint period group non-discrete, hence the fixed field constant) and `Q`-independent
(which makes `q = exp(2 pi i omega_1/omega_2)` non-torsion and the cylinder coordinates
algebraically independent). `exists_constant_of_two_rayPeriods_fixed` records the fixed-field
collapse for `omega_j = c a_j` with `a_j` real and `a_1/a_2` irrational; `c` is an arbitrary nonzero
complex number. Since `omega_1/omega_2 = a_1/a_2` the multiplier `q` is unchanged.

This matters for the one remaining gate. The corpus already owns a Barnes cone construction --
`barnesConeProduct`, `barnesConeMero`, `barnesSourceLogDerivMero`, the subframe ladder step, and the
reflected `multipleSineSourceMero` -- but every one of them assumes `0 < Im omega_i`. Taking
`c = i` puts the periods on the positive imaginary axis, where that hypothesis holds
(`im_I_mul_ofReal_pos`) *and* the periods are still `R`-collinear with irrational ratio, so the
fixed-field collapse still applies (`exists_constant_of_two_imaginaryPeriods_fixed`). The two
regimes are therefore not disjoint: the imaginary ray lies in both.

So the realization does **not** require the Barnes double-zeta regularization. What it requires is:

1. identify the singleton reflected Barnes source `multipleSineSourceMero omega homega {j}` with the
   cotangent `(pi/omega_j) cot(pi z/omega_j)` -- the order-one reflected source is the reciprocal
   sine, so this should be a Weierstrass-product identification;
2. locate the differentially algebraic defect `d` in the ladder step
   `(T_k - 1) L_S + L_{S∖k} = d` precisely enough to place it in the coefficient field. Note the
   argument tolerates a defect rational in `z`: enlarging `K` to `C(z,u_1,u_2)` keeps `K` stable
   under both translations, and a defect rational in `z, u_1` is a *constant* for the `u_2`
   variable, so it contributes no pole on the orbit `q^Z` and the orbit-balance obstruction is
   unaffected. This is exactly why the obstruction was proved over an arbitrary base field.

### The Barnes double-zeta regularization

`GaloisForLFunctions.HTGeometry.BarnesDoubleZetaSeries` starts the direct construction of the double
sine for real positive periods, via the Barnes double zeta

```text
zeta_2(s,z) = sum_{m,n >= 0} (z + m omega_1 + n omega_2)^(-s).
```

Two things are proved unconditionally.

*Convergence.* `summable_barnesLattice_rpow`: the real cone `p`-series converges for exponent above
two. The mechanism is `c + delta(m+n) >= e sqrt((1+m)(1+n))`, which dominates the terms by a product
of two one-dimensional `p`-series of exponent `sigma/2 > 1`; `norm_cpow_neg_le_rpow` transfers this
to the complex series with a uniform `exp(pi |Im s|)` factor coming from the argument, giving
`summable_barnesDoubleZeta_term` for `Re s > 2`, `Re z > 0`.

*The shift identities.* `barnesDoubleZeta_add_fst` and `barnesDoubleZeta_add_snd`:

```text
zeta_2(s, z + omega_1) = zeta_2(s,z) - zeta_1(s, z | omega_2),
zeta_2(s, z + omega_2) = zeta_2(s,z) - zeta_1(s, z | omega_1),
```

with `zeta_1(s,z|omega) = sum_{n>=0} (z + n omega)^(-s)`. Translating by a generator deletes one
slab of the cone, which is the opposite ray -- pure reindexing, exact in the half-plane of
convergence. These are the identities that become the double-sine step equations after
differentiating the continuation at `s = 0`, and being exact they propagate to any continuation.

*Structure of the cone.* `barnesDoubleZeta_eq_tsum_rays` slices the cone into rays,
`barnesSingleZeta_add` is the one-dimensional shift, and `barnesDoubleZeta_add_fst_add_snd` verifies
that the two period shifts commute: applying both removes the two boundary rays and restores the
initial term `z^(-s)`. That commutation is the zeta-level shadow of the compatibility condition the
paired telescoping theorem imposes on the two increments.

*The continuation, and what blocks it.* mathlib's `hurwitzZeta` supplies the one-dimensional
continuation, but only for a **real** shift `a` in `[0,1]` (`hasSum_hurwitzZeta_of_one_lt_re`), and
the double sine needs `zeta_1(s, z | omega)` for **complex** `z`. So the continuation cannot be
imported; it has to be built. The two viable routes are the Mellin representation
`Gamma(s) zeta_2(s,z) = int_0^oo t^(s-1) e^(-zt)/((1-e^(-omega_1 t))(1-e^(-omega_2 t))) dt`
for `Re s > 2`, continued by splitting at `t = 1` and subtracting the order-two pole of the
integrand at `t = 0`; or Euler-Maclaurin for the ray zeta with complex shift. Both need real
analysis mathlib does not currently package.

`GaloisForLFunctions.HTGeometry.BarnesMellinRepresentation` starts the Mellin route.
`integral_cpow_mul_exp_neg_real_mul_Ioi` proves the term-by-term input

```text
int_0^oo t^(s-1) e^(-w t) dt = Gamma(s) w^(-s)
```

for a **positive real** rate `w` and `Re s > 0`, by the substitution `t |-> w t`
(`integral_comp_mul_left_Ioi`) against `Complex.Gamma_eq_integral`. The rate is real because that is
the case where the substitution is a genuine change of variables on the half-line; the complex-rate
version -- which is what the cone terms `w = z + m omega_1 + n omega_2` need -- follows by analytic
continuation in `w` over the right half-plane, where both sides are analytic and agree on the
positive reals. That continuation step is now done. `hasDerivAt_integral_cpow_mul_exp` differentiates under the
integral sign (dominated on a ball around the rate by `t^(Re s) e^(-a t)`), making the integral
holomorphic in `w` on the right half-plane; `integral_cpow_mul_exp_neg_mul_Ioi` then concludes

```text
int_0^oo t^(s-1) e^(-w t) dt = Gamma(s) w^(-s)      for Re s > 0, Re w > 0
```

by the identity theorem on that convex, hence preconnected, set, starting from the real-rate case.
The real-rate case is mathlib's `Complex.integral_cpow_mul_exp_neg_mul_Ioi`; the complex-rate
statement is not in mathlib and is the new content. Its convergence input is proved for a complex
rate:
`integrableOn_cpow_mul_exp_neg_mul_Ioi` shows `t^(s-1) e^(-wt)` is integrable on the half-line for
`Re s > 0`, `Re w > 0`, dominated by the real integrand of
`integrableOn_rpow_mul_exp_neg_mul_Ioi`. The real integrand lemma already existed in the corpus as
`RHTower.integrableOn_rpow_mul_exp_neg_mul_Ioi`; it has been moved to `HTGeometry` (its correct home
as reusable infrastructure) and the `RHTower` statement now delegates to it, so there is one proof.

The summed Mellin representation is now proved. `hasSum_barnesConeKernel` identifies the cone
generating function as a product of two geometric series,

```text
sum_{m,n>=0} e^(-(x + m omega_1 + n omega_2) t)
  = e^(-xt)/((1-e^(-omega_1 t))(1-e^(-omega_2 t))),
```

and `Gamma_mul_barnesDoubleZeta_eq_mellin` gives, for positive real `x` and `Re s > 2`,

```text
Gamma(s) zeta_2(s,x) = mellin (barnesConeKernel omega_1 omega_2 x) s.
```

The interchange of sum and integral is mathlib's `hasSum_mellin`, the "Mellin transform = Dirichlet
series" machine. It requires the rates to be real, which is why the representation is stated at a
real argument: that is the natural base for continuing in `s` first and in `z` afterwards.

`GaloisForLFunctions.HTGeometry.BarnesKernelExpansion` starts the continuation. Continuing past
`s = 2` means subtracting the singular part of the kernel at `t = 0`, and the whole content of that
is one factor: `z/(1 - e^(-omega z))` has a removable singularity at the origin with value
`1/omega`. `hasDerivAt_one_sub_exp_neg_mul` is the first-order vanishing of the denominator and
`tendsto_div_one_sub_exp_neg_mul` is the resulting limit, read off as the reciprocal of the
difference quotient. (The division-by-zero convention makes `(slope)^(-1)` equal
`z/(1 - e^(-omega z))` identically, so the proof needs no case split on the denominator.) Hence
`t^2 e^(-xt)/((1-e^(-omega_1 t))(1-e^(-omega_2 t)))` extends across `t = 0` with value
`1/(omega_1 omega_2)`.

mathlib supplies the rest of the continuation scaffolding: `mellin_differentiableAt_of_isBigO_rpow`
gives holomorphy of a Mellin transform in a strip determined by the decay at `0` and `infinity`, and
`hasMellin_cpow_Ioc` evaluates the subtracted power terms, contributing exactly the poles at
`s = 2, 1, 0`.

Still not formalized: the Taylor expansion of the extended kernel to second order (which fixes the
subtracted coefficients), the resulting continuation past `s = 2`, the finite part at `s = 1`
(which is
`-partial_z log Gamma_2`, since `partial_z zeta_2(s,z) = -s zeta_2(s+1,z)` makes the derivative of
the regularization the finite part rather than a value), the reflection giving `S_2`, and the
resulting `Psi`. Every other ingredient -- the fixed field, the independent coordinates, the
embedded two-cylinder field, its translation action, its differential structure, and the exact form
of the increment -- is machine-checked.

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
- [ ] independent audit of paired telescoping (the specialization step is now eliminated: the
  Lean obstruction is proved over an arbitrary base field and applies directly in `C(u_1)(u_2)`);
- [ ] exact/equivalent/stronger literature search;
- [ ] independent significance and novelty verdict;
- [x] multiplicative-orbit residue obstruction formalized unconditionally in Lean;
- [x] Euler-operator pole computation for the cotangent model formalized unconditionally in Lean;
- [x] exact augmentation-ideal annihilator and total-exponent classification formalized
  unconditionally in Lean;
- [x] cylinder coordinate bridge (cotangent identity, Euler-operator form of `d/dz`, analytic jets
  of the cotangent model) formalized unconditionally in Lean;
- [x] cylinder differential field, jets of the cotangent model, and the character obstruction
  formalized unconditionally in Lean;
- [x] Lean reduction of hypertranscendence to the descended `q`-difference equation, via the
  corpus arbitrary-family differential Ostrowski criterion;
- [x] Lean proof that the common fixed field of two incommensurate real translations in the global
  meromorphic field is exactly `C`;
- [x] Lean proof that exponentials with distinct frequencies are independent in the global
  meromorphic field (the two-cylinder separation input);
- [x] Lean proof that the two exponential coordinates are algebraically independent over `C`;
- [x] Lean embedding of one cylinder coordinate field `C(u)` into the meromorphic field, with
  translation acting by the multiplicative dilation `ratFuncScale`;
- [x] Lean embedding of the two-cylinder field `C(u_1)(u_2)` into the meromorphic field, injective;
- [x] Lean transport of the translation action to the two-cylinder embedding: translation by a
  period of the first coordinate is the multiplicative dilation of the second;
- [x] Lean transport of the differential structure: the cylinder embedding is a differential
  embedding for `lambda * (X d/dX)`;
- [x] Lean identification of the step increment: the embedded cotangent model is the genuine
  meromorphic `(pi/omega) cot(pi z/omega)`;
- [x] Lean fixed-field collapse for periods on an arbitrary common ray, in particular the positive
  imaginary axis where the corpus's Barnes cone hypothesis `0 < Im omega` also holds;
- [x] Lean Barnes double-zeta series: convergence for `Re s > 2` and the two exact cone-slab shift
  identities;
- [x] Lean ray decomposition of the cone, the one-dimensional shift, and commutation of the two
  period shifts;
- [x] Lean scaled Euler integral `int_0^oo t^(s-1) e^(-wt) dt = Gamma(s) w^(-s)` for positive real
  rate, the term-by-term input of the Mellin representation;
- [x] Lean convergence of the complex-rate Euler integral on the half-line;
- [x] Lean complex-rate Euler integral `int_0^oo t^(s-1) e^(-wt) dt = Gamma(s) w^(-s)` for
  `Re w > 0`, by holomorphy in the rate plus the identity theorem;
- [x] Lean cone generating function and the summed Mellin representation
  `Gamma(s) zeta_2(s,x) = mellin (cone kernel) s` for real `x > 0`, `Re s > 2`;
- [x] Lean removable singularity of the kernel factor `z/(1 - e^(-omega z))` at the origin, the
  analytic core of the subtraction;
- [x] Lean second-order Taylor expansion of the extended kernel, the continuation past `s = 2`,
  and the finite part at `s = 1` (the reflected double sine remains open, tracked below).  This
  route is no longer on the critical path: `exists_exact_doubleSine_source` already supplies the two step equations
  unconditionally for any two-period frame with `0 < Im omega_j`, and the imaginary-ray regime
  `omega_j = i a_j` satisfies both that hypothesis and the rational-independence hypothesis of the
  fixed-field collapse.  The Barnes double-zeta regularization is therefore kept as an independent
  analytic asset rather than as the source of the double sine.
- [x] Lean translation action in the second period direction: when the second cylinder coordinate is
  a period, translation acts on the embedded `C(u_1)(u_2)` by scaling the coefficient field, and the
  scaling is a ring automorphism (`addTranslationMeroEquiv_twoCylinderEmbed_coeff`,
  `cylinderCoeffScaleEquiv`);
- [x] Lean two-cylinder differential field: the total derivation of `K(X)` in which the coefficient
  field carries its own derivation and the coordinate is an exponential, built by extending the
  corresponding polynomial derivation across the fraction field (`twoCylDerivation`,
  `twoCylinderDifferential`), together with its quotient rule;
- [x] Lean reduction of the two-cylinder jets to one-variable cylinder jets on the subfield
  generated by the coordinate over the differential constants (`differentialJet_twoCylinder`),
  which is where the cotangent model lives;
- [x] Lean proof that the two-cylinder embedding is a differential embedding:
  `(twoCylinderEmbed y)' = twoCylinderEmbed (twoCylDerivation lam y)`
  (`meroFieldDeriv_twoCylinderEmbed`), the differential-algebra hypothesis of the Ostrowski
  criterion;
- [x] Lean identification of `periodCotMero` with the embedded `cotModel`
  (`periodCotMero_eq_twoCylinderEmbed_cotModel`), producing the increment family;
- [x] Lean instantiation of `hypertranscendentalOver_of_cotangentCylinderIncrement` on the
  imaginary-ray frame (`hypertranscendental_doubleSine_imaginaryRay`): hypertranscendence of the
  double-sine source over the two-cylinder field;
- [x] Lean assembly of the card's statement: the exact augmentation-ideal annihilator and the
  total-exponent classification for the genuine meromorphic double-sine source
  (`daTranslationAnnihilator_doubleSine_imaginaryRay`).
- [x] Lean divided-difference infrastructure: `(f z - f c)/(z - c)` extended by `f'(c)` is analytic
  at `c`, and iterating gives the second-order Taylor expansion with an analytic remainder
  (`analyticAt_analyticSlope`, `eq_taylor_two_add_sq_mul`, `analyticSlope_two_of_ne`);
- [x] Lean second-order expansion of the extended Barnes cone kernel:
  `t² F(t) = 1/(omega_1 omega_2) + t A_1 + t² R(t)` with `R` analytic at the origin
  (`barnesConeKernelAnalytic`, `barnesConeKernelAnalytic_ofReal`, `barnesConeKernelAnalytic_taylor`);
- [x] Lean continuity of the extended cone kernel and of its Taylor remainder on `[0,1]`, and the
  resulting uniform bound on the remainder (`exists_bound_barnesConeKernelRemainder`) — the input
  that makes the subtracted head integral converge for `Re s > 0`;
- [x] Lean split of the Mellin integral at `t = 1`, the two explicit head poles
  `1/(omega_1 omega_2 (s-2)) + A_1/(s-1)` via `hasMellin_cpow_Ioc`, and the absolutely convergent
  tail: `Gamma_mul_barnesDoubleZeta_eq_continuation` writes `Gamma(s) zeta_2(s,x)` for `Re s > 2` as
  two explicit simple poles plus two integrals which converge for every `Re s > 0`.  Supporting
  pieces: exponential decay of the cone kernel beyond `t = 1` (`norm_barnesConeKernel_le`),
  continuity of the kernel on the positive reals, and absolute convergence of both the head and
  tail integrands.
- [x] Lean holomorphy of the two continued integrals in `s` on `Re s > 0`
  (`differentiableAt_barnesConeHead`, `differentiableAt_barnesConeTail`,
  `analyticAt_barnesConeContinuedPart`), giving the meromorphic continuation as an identity of
  analytic functions rather than a pointwise formula.  Both integrals are Mellin transforms of
  indicator-supported functions and fall under the standard Mellin holomorphy criterion.
- [x] Lean definition of the continued Barnes double zeta `barnesDoubleZetaCont` on the right
  half-plane, its agreement with the convergent series for `Re s > 2`
  (`barnesDoubleZetaCont_eq_barnesDoubleZeta`), and its analyticity away from `s = 1, 2`
  (`analyticAt_barnesDoubleZetaCont`);
- [x] Lean Laurent expansion at `s = 1`: `barnesDoubleZetaCont_eq_pole_add_remainder` splits it off
  the pole as `A_1/(s-1) + R(s)` with `R` analytic at `1`
  (`analyticAt_barnesDoubleZetaRemainderOne`), the residue confirmed as a limit
  (`tendsto_sub_one_mul_barnesDoubleZetaCont`), and the finite part named
  (`barnesDoubleZetaFinitePartOne`).  Only the finite part is needed downstream: in
  `partial_z log Gamma_2 = -[zeta_2(s+1,z) + s zeta_2'(s+1,z)]_{s=0}` the two poles cancel and the
  limit is exactly the constant term.
- [x] Lean shift derivative `partial_x zeta_2(s,x) = -s zeta_2(s+1,x)`
  (`hasDerivAt_barnesDoubleZeta_shift`), by differentiating the Mellin representation under the
  integral sign: the `x`-derivative multiplies the integrand by `-t`, which raises the Mellin
  variable by one, dominated by the integrand at half the shift
  (`norm_barnesConeKernel_mono`, `integrableOn_cpow_mul_barnesConeKernel_Ioi`);
- [x] Lean Taylor expansion to arbitrary order with an analytic remainder
  (`analyticSlopeIter`, `eq_taylor_add_pow_mul`, `analyticSlopeIter_of_ne`), and its third-order
  instance for the cone kernel (`barnesConeKernelAnalytic_taylor_three`) with the cubic remainder
  bounded on `[0,1]` (`exists_bound_barnesConeCubicRemainder`);
- [x] Lean continuation past `s = 0`: `Gamma_mul_barnesDoubleZeta_eq_continuation_three` writes
  `Gamma(s) zeta_2(s,x)` as three explicit simple poles (`s = 2, 1, 0`) plus a head integral
  convergent for `Re s > -1` and the entire tail.  This is the range needed to reach `s = 0`, where
  the simple zero of `1/Gamma` cancels the new pole, so `zeta_2` is regular there;
- [x] Lean definition of the Barnes double gamma: the tail integral is entire
  (`differentiableAt_barnesConeTail_all`), the subtracted head is holomorphic for `Re s > -1`
  (`differentiableAt_barnesConeDeepHead`), and at `s = 0` the head's pole is cancelled by the simple
  zero of `1/Gamma`, giving a function analytic there (`barnesDoubleZetaRegZero`,
  `analyticAt_barnesDoubleZetaRegZero`) which agrees with the continuation off the origin
  (`barnesDoubleZetaRegZero_eq`) and with the convergent series for `Re s > 2`
  (`barnesDoubleZetaDeep_eq_barnesDoubleZeta`).  `logBarnesDoubleGamma` is its `s`-derivative at the
  origin;
- [x] Lean meromorphic continuation of the one-dimensional Barnes zeta: Mellin representation
  (`Gamma_mul_barnesSingleZeta_eq_mellin`), the extended ray kernel `t F(t)` with its second-order
  expansion (`barnesRayKernelAnalytic_taylor`), the bounded remainder, and the continuation with two
  explicit poles at `s = 1, 0` (`Gamma_mul_barnesSingleZeta_eq_continuation`).  The double zeta's
  shift equations reduce to the single zeta, so this is required to transport any functional
  equation to the continued functions;
- [x] Lean shift identity of the cone kernel `F_2(x,t) = F_2(x+omega_1,t) + F_1(omega_2;x,t)`
  (`barnesConeKernel_shift`) -- an exact algebraic identity, not a statement about series, so it
  transports to every object built from the kernel and avoids any appeal to the identity theorem on
  a punctured domain;
- [x] Lean additivity and peeling laws for the iterated divided difference (`analyticSlope_add`,
  `analyticSlope_add_sub_mul`, `analyticSlopeIter_add`, `analyticSlopeIter_add_sub_mul`): adding
  `(z-c)` times a function shifts the divided difference by that function, which is how the shift
  identity descends to the Taylor coefficients and remainders;
- [x] Lean descent of the shift identity to the Taylor data: the extended kernels satisfy
  `A_2(x,z) = A_2(x+omega_1,z) + z A_1(omega_2;x,z)` near the origin
  (`barnesConeKernelAnalytic_shift_eventually`), the divided difference only depends on the germ
  (`analyticSlopeIter_eq_of_eventuallyEq`), and peeling gives the coefficient identities
  `barnesConeLinearCoeff_shift`, `barnesConeQuadCoeff_shift` together with the exact remainder
  identity `barnesConeCubicRemainder_shift`;
- [x] Lean shift equation of the continued Barnes double zeta
  (`barnesDoubleZetaBracket_shift`, `barnesDoubleZetaDeep_shift`):
  `zeta_2(s,x) = zeta_2(s,x+omega_1) + zeta_1(omega_2;s,x)` on `Re s > -1`, proved by matching the
  three pole coefficients, the subtracted head integrals and the tail integrals separately -- no
  analytic continuation argument.  Both tails were generalised to converge for every exponent
  (`integrableOn_cpow_mul_barnesConeKernel_Ioi_one_all`,
  `integrableOn_cpow_mul_barnesRayKernel_Ioi_one_all`), and the brackets are identified with
  `Gamma(s) zeta(s,x)` where the series converges;
- [ ] Lean identification of `-barnesDoubleZetaFinitePartOne` with `partial_z log Gamma_2`, i.e. the
  derivative-in-`z` relation `partial_z zeta_2(s,z) = -s zeta_2(s+1,z)` transported to the
  continuation, and the reflection producing the double sine.

### The base-change step (card lines 94-95) is corpus-owned

The paper proof's step "since `K(z)` is DA over both `K` and `C(z)`, transitivity makes `L_2` DA
over `K`" is already available in Lean: `DifferentialAlgebraicTransitivity.lean` proves
`differentialAlgebraicOver_trans` together with the transcendence-degree machinery
(`differentialAdjoin_trdeg_lt_aleph0_of_differentialAlgebraic`) it rests on, and
`FiniteDifferentialCircuitBoundary.lean` proves `differentialAlgebraicOver_mono`.  No new
differential-algebra theory is needed; only the two concrete inputs for this frame.

- [x] Lean inputs for the base change: `z` as an element of the global meromorphic field with
  `z' = 1` and `z'' = 0`, hence differentially algebraic over the two-cylinder field
  (`differentialAlgebraicOver_coordinateMero`), and the containment of the whole coordinate field
  `C(z)` in the differential field the two-cylinder field generates by adjoining `z`
  (`ratMero_mem_differentialAdjoin_coordinate`);
- [x] Lean assembly of the base change: the algebra instance on the differential adjoin (by
  restricting `ratMero` to it) and `differentialAlgebraicOver_twoCylinder_of_ratFunc`, which
  discharges the `hHT` hypothesis of `daTranslationAnnihilator_eq_augIdeal`
  (`not_differentialAlgebraicOver_doubleSine_source`);
- [x] Lean discharge of the `hstep` hypothesis (`differentialAlgebraicOver_doubleSine_defect`, from
  the corpus's `differentialAlgebraicOver_periodCotMero`) and the **capstone**: for any two-period
  frame with rationally independent cylinder frequencies, non-torsion second dilation and constant
  common fixed field, a meromorphic source with the exact cotangent defects satisfies
  `daTranslationAnnihilator_doubleSine_eq_augIdeal` -- the annihilator modulo the differentially
  algebraic sector over `C(z)` is exactly the augmentation ideal -- together with the total-exponent
  classification (`differentialAlgebraicOver_transApply_doubleSine_iff`) and the statement that no
  single structural translate is differentially algebraic
  (`not_differentialAlgebraicOver_transApply_doubleSine_monomial`);
- [x] Lean specialisation of the capstone to the imaginary-ray frame `omega_j = i a_j`, assembling
  the frame facts (periodicity, non-torsion, fixed field): the statement is now closed with no frame
  hypotheses.  `daTranslationAnnihilator_doubleSine_imaginaryRay` -- for `a, b > 0` with `a/b`
  irrational there exists a meromorphic source with the two exact cotangent defects whose
  translation annihilator modulo the differentially algebraic sector over `C(z)` is exactly the
  augmentation ideal, equivalently a translation operator kills the class precisely when its
  coefficients sum to zero.  **The card's main theorem is formalised unconditionally.**
