# Tate-theta nodal localization and the Barnes face chain shadow

- **ID:** `tate-theta-koszul-barnes-localization-transmutation`
- **Stage:** 3-formalized local components / typed comparison open downstream
- **Type:** LOCALIZATION BRIDGE COMPONENTS / TYPED-BRIDGE NO-GO
- **Scientific status:** `[PROVED LOCAL COMPONENTS] [LEAN FORMALIZED]`
  `[CROSS-RECEIVER IDENTIFICATION OPEN] [BRIDGE]`
  `[GENERAL MECHANISM CLASSICAL] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH RESULT]`
- **Theta parent:** `tate-theta-divisor-to-winding-transgression.md`
- **Barnes parent:**
  `../new_scientific_knowledge/barnes-differential-source-face-matrix-factorization.md`
- **Observation parent:** `source-face-observation-cohomology-transmutation.md`
- **Live successor:**
  `../../1-in-progress/hypertranscendental-source-face-vanishing-cycle-conservation.md`

## 1. The coefficient mismatch

The Barnes face class is naturally a coherent `Tor_1` module over a complex coefficient ring.
The Tate node charge is an oriented integer.  A complex line alone cannot distinguish a primitive
generator from an arbitrary nonzero scalar, so equality of dimensions or of chosen numerical
labels cannot identify the two classes canonically.

The correct common parent is the integral localization class of the selected face coordinate.
Its coherent realization is the Koszul/Tor class; its divisor realization is the node charge.

## 2. Exact nodal factorization of the Tate-theta gauge `[PROVED]`

Put `q=t^4` and use the semistable nodal coordinates

```text
xy=t.                                                                    (1)
```

For

```text
theta_q(w)=product_(n>=0)(1-q^n w)(1-q^(n+1)/w),

E_q(x)=-q^(1/4)
  theta_q(q^(-1/4)x) theta_q(q^(3/4)x) / theta_q(q^(1/4)x)^2,             (2)
```

the three theta factors admit the following identities in the completed local nodal ring.

First,

```text
t theta_(t^4)(t^(-1)x)
  =(t-x)
    product_(n>=1)(1-t^(4n-1)x)
    product_(n>=0)(1-t^(4n+4)y).                                        (3)
```

Indeed, the exceptional first factor is `t(1-t^(-1)x)=t-x`, while
`t^(4n+5)/x=t^(4n+4)y` by `(1)`.

Second,

```text
theta_(t^4)(t^3x)
  =(1-y)
    product_(n>=0)(1-t^(4n+3)x)
    product_(n>=1)(1-t^(4n)y).                                          (4)
```

Third,

```text
theta_(t^4)(tx)
  =product_(n>=0)(1-t^(4n+1)x)
   product_(n>=0)(1-t^(4n+2)y).                                         (5)
```

Every displayed infinite product in `(3)`--`(5)` converges in the maximal-ideal-adic completion,
and every factor has value `1` at the node.  Their products and the denominator in `(5)` are
therefore units.  Since

```text
t-x=xy-x=-x(1-y),                                                        (6)
```

substitution into `(2)` gives the exact factorization

```text
E_(t^4)(x)=x u(x,y,t),                                                    (7)
```

where

```text
u=(1-y)^2
  product_(n>=1)(1-t^(4n-1)x)
  product_(n>=0)(1-t^(4n+4)y)
  product_(n>=0)(1-t^(4n+3)x)
  product_(n>=1)(1-t^(4n)y)
  /
  (product_(n>=0)(1-t^(4n+1)x)
   product_(n>=0)(1-t^(4n+2)y))^2                                      (8)
```

is a unit with `u(0,0,0)=1`.

Consequently the local divisor and localization classes are exact:

```text
div_node(E_(t^4))=V(x),
[E_(t^4)]=[x] in K_1 of the punctured nodal chart.                         (9)
```

Powers give `div_node(E^m)=mV(x)` and localization class `m[x]` for every integer `m`.

## 3. Integral localization boundary `[CLASSICAL BRIDGE]`

Let `A` be the completed local ring in `(1)`, `Z=V(x)`, and `B=A/(x)`.  With the orientation in
which `Z` is positive, the localization boundary is

```text
partial_K([x^m])=m[A/(x)] in K_0^Z(A).                                  (10)
```

The class `[A/(x)]` is represented by the Koszul complex

```text
K(x)=[A --x-> A].                                                        (11)
```

Derived face restriction gives

```text
K(x) tensor_A^L B=[B --0-> B],                                          (12)
```

with one copy of `B` in homological degrees one and zero.  Thus the integral node charge and the
coherent relation-death/capacity-birth pair are two realizations of `(10)`.

## 4. Abstract same-ring map to a product-face class `[PROVED]`

If `x` and a complementary factor `p` live in one commutative ring, the product presentation is

```text
K(px)=[A --px-> A].                                                       (13)
```

There is a canonical chain map

```text
phi:K(x) -> K(px),
phi_1=id_A,
phi_0=multiplication by p.                                                (14)
```

The chain identity is

```text
(px) phi_1 = phi_0 x = px.                                               (15)
```

After tensoring with `B=A/(x)`, both differentials vanish and

```text
H_1(phi tensor B)=id_B.                                                   (16)
```

The target of `(16)` is

```text
Tor_1^A(A/(px),B)=B.                                                      (17)
```

Thus, in a genuinely common ring, the supported Koszul generator maps to the product-face
`Tor_1` generator:

```text
m[K(x)] -> m times the Tor_1 generator of A/(px).                         (18)
```

The algebraic square `(14)`--`(15)` is Lean-formalized as
`selectedToProductFace_chainMap_square` in
`formal/GaloisForLFunctions/HTGeometry/SourceFaceObservationExcess.lean`.  The analytic infinite-
product factorization `(3)`--`(9)` is formalized in
`formal/GaloisForLFunctions/HTGeometry/TateThetaNodalLocalization.lean`; no special-function axiom
was introduced.

## 5. Typed-bridge no-go

The actual Tate and Barnes applications do **not** yet satisfy the same-ring hypothesis of
Section 4.  The symbol `x` in `(1)`--`(12)` is the multiplicative coordinate of the nodal curve.
The selected Barnes factor is

```text
xi_j=T_j-1                                                         (19)
```

in a differential-translation operator algebra.  These are different typed objects.  A valid
realization must send the nodal coordinate to a vector on which `xi_j` acts by zero; it cannot
identify that vector with the operator `xi_j` itself.

```text
[NO-GO]
Equating the nodal coordinate x with the source operator T_j-1 is an invalid symbol collision.
The two proved local components do not by themselves establish cross-receiver conservation.
```

The maximal positive replacement is a charge-graded character realization.  For Barnes periods
`omega_1,...,omega_N`, fix `j` and, for every `m in Z`, put

```text
lambda_(j,m)=2 pi i m/omega_j,
ell_(j,m)(z)=exp(lambda_(j,m) z),
chi_(j,m)(T_k)=exp(lambda_(j,m) omega_k),
chi_(j,m)(delta)=lambda_(j,m).                                           (20)
```

Then `chi_(j,m)(T_j)=1`, so every `chi_(j,m)` factors through the source-face algebra

```text
B_j=D_N/(T_j-1),                                                         (21)
```

and

```text
Q(delta,T) ell_(j,m)=chi_(j,m)(Q) ell_(j,m).                            (22)
```

Thus the Barnes face class `Tor_1=B_j` has a canonical one-dimensional character fibre at every
charge,

```text
B_j tensor_(chi_(j,m)) C,
1 maps to ell_(j,m).                                                     (23)
```

Distinct charges are linearly independent because their differential eigenvalues are distinct.
This is the correctly typed local analytic/source-character bridge.  It records the integral
grading and complementary source shifts by their actual phases rather than pretending that one
primitive fibre carries every charge or that `ell_(j,m)` is jointly fixed by all shifts.

For rationally independent `omega_j,omega_k`, the charge-frequency spectra of the two faces meet
only at `m=n=0`.  Therefore nonzero local fibres cannot be glued by equality.  Their maximal
positive pair object is a face-separated character fan with neutral intersection.  These laws are
Lean-formalized in `NodalChargeCharacterRealization.lean` and recorded in
`nodal-charge-character-fan-realization.md`.

## 6. No-go and positive successor

```text
[NO-GO]
A complex-linear characteristic module alone cannot recover the primitive integral node charge.
```

```text
[POSITIVE]
The Tate theta product canonically supplies the primitive nodal localization class [x], while the
Barnes face Tor module canonically supplies every graded character fibre `(23)`.  The local
analytic source action is realized by `x^m=ell_(j,m)`, with `T_j-1` acting as its annihilating
operator.  For `m>0`, however, the boundary of `[x^m]` must retain the oriented interval of sectors
`L_0 directSum ... directSum L_(m-1)`, whose forgotten rank is `m`; the endpoint `L_m` is the state
reached after multiplication by `x^m`, not the boundary crossed.  A valid integral/coherent
cross-receiver theorem must construct this interval-valued localization map.
```

The analytic nodal factorization, the algebraic product-face chain map, and the graded analytic
source-character realization are exact.  The map of localization sequences into the coherent
Barnes `Tor` module remains open and must not be inferred from matching one-dimensional fibres.

## 7. Novelty and significance gate

The following mechanisms are classical:

- localization sequences in algebraic K-theory;
- the boundary of a unit as its supported divisor/Koszul class;
- Koszul resolution and derived restriction;
- formal unit arguments for convergent infinite products;
- the Tate theta product and its nodal degeneration.

Once `(7)` is written down, `(10)`--`(18)` are natural consequences of those parents.  Equations
`(20)`--`(23)` are elementary character theory.  These results therefore do not pass the
anti-theatre gate as new scientific knowledge and are deliberately filed as bridge components.

Their significance is diagnostic.  They show exactly what a valid bridge must preserve: integral
localization, the full charge grading, the differential-translation character, face separation,
and the distinction between operator and vector.  A paper-significant new result requires a map
of localization sequences and global DA-relative naturality across a nontrivial HT hierarchy.

## 8. Downstream open core (not a theorem claimed by this classical component card)

Construct a source-presentation-invariant face-poset realization for the actual multiple-gamma
degeneration and prove that:

```text
the DA-relative Tate-theta class is nonzero;
the localization boundary maps `[x^m]` to the filtered charge interval
`L_0 directSum ... directSum L_(m-1)`, not to the endpoint fibre `L_m` or the operator `T_j-1`;
the local character fans glue across all source faces by their exact resonance lattices;
the coherent image is the source-face Tor class represented by `(14)`;
iterated face boundaries satisfy the required coherence/anti-commutation law;
an independently defined analytic reporter and the characteristic presentation remain jointly
conservative after global completion.                                    (24)
```

Only this typed, global comparison, not the local Koszul computation, is a candidate for new
scientific knowledge.

## 9. Lean formalization

Formal artifacts:

- `formal/GaloisForLFunctions/HTGeometry/TateThetaNodalLocalization.lean`
- `formal/GaloisForLFunctions/HTGeometry/SourceFaceObservationExcess.lean`
- `formal/GaloisForLFunctions/HTGeometry/NodalChargeCharacterRealization.lean`
- `formal/GaloisForLFunctions/HTGeometry/GrothendieckKTheoryIntersectionApplications.lean`

Closed endpoints include:

- `root_mul_multiplicativeTheta_root_inv_mul`,
  `multiplicativeTheta_root_cube_mul`, and `multiplicativeTheta_root_mul`: exact product identities
  `(3)`--`(5)` on every analytic nodal chart point `xy=t`.
- `tateThetaGauge_eq_coordinate_mul_nodalUnit`: exact `E=xu` factorization.
- `TateNodalUnitDatum.nodalUnitFactor_ne_zero` and
  `tendsto_tateThetaNodalUnitFactor_one`: analytic unit property and constant term one.
- `tateNodalLocalizationBoundary_class`: signed formula `∂[x^m]=m[A/(x)]` in the Grothendieck
  completion of the supported multiplicity monoid.
- `selectedToProductFace_chainMap_square`: canonical selected-to-product Koszul chain square.
- `nodalChargeModes_linearIndependent`, `nodalChargeFrequency_pair_eq_iff_neutral`, and
  `nodalChargeBoundaryIntervalPairing_eq`: graded source-character realization, face separation,
  and complete oriented interval multiplicity.
- `tateNodalLocalizationBoundary_eq_chargeInterval`: equality of coherent localization
  multiplicity with the analytic charge-interval multiplicity.

Verification:

- `lake env lean GaloisForLFunctions/HTGeometry/TateThetaNodalLocalization.lean` passed.
- `lake build GaloisForLFunctions.HTGeometry.TateThetaNodalLocalization` passed.
- `#print axioms` on every new endpoint reports only `propext`, `Classical.choice`, and
  `Quot.sound`; no project axiom and no `sorryAx` occurs.
- Module is wired into `GaloisForLFunctions.HTGeometry`; umbrella build intentionally omitted.

All unconditional local-component theorems claimed by this card are Lean-formalized.  The
cross-receiver map in `(24)` is explicitly candidate-new downstream work assigned to the live
successor; no equality between the nodal coordinate and the Barnes operator is asserted here.

## References checked

- Stacks Project, Section 15.121 / tag `0FJG`, perfect complexes and K-groups.
- Stacks Project, Section 15.29 / tags `0628`--`0629`, Koszul complexes as mapping cones.
- A. Blumberg, D. Gepner, G. Tabuada, *A universal characterization of higher algebraic
  K-theory*, `arXiv:1001.2282`.
- A. Neeman, A. Ranicki, *Noncommutative localisation in algebraic K-theory I*,
  `arXiv:math/0410620`.
