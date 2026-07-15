# Projective tail defects obey a finite-source Hurwitz budget

- **ID:** nonautonomous-projective-tail-defect-collapse-law
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Scientific status:** `[PROVED HERE] [CANDIDATE NEW SCIENTIFIC KNOWLEDGE]`
- **Source:** rational projective-connection pullback + genus-zero Riemann--Hurwitz
- **Statement:** A fixed rational projective connection on the source sphere cannot be the pullback of hyperbolic projective-orbifold connections through rational maps of unbounded degree.  Irregular terminal singularities have a degree-amplified defect, at most two terminal fibres can remain non-orbifold, and a hyperbolic orbifold core forces the explicit bound `degree <= 42(|S|-2)`, where `S` is the fixed source singular set.

## Setup

Let `Q_0` be a rational projective connection on `P1`, written in a coordinate as

```text
Q_0=q_0(z)(dz)^2,
```

and let `P:P1->P1` be rational of degree `D`.  Suppose a rational terminal projective connection
`Q` satisfies the exact projective pullback law

```text
q_0=(q composed P)(P')^2+S_2(P),                           (1)
S_2(P)=2P'''/P'-3(P''/P')^2.
```

Let `S` be the finite singular support of `Q_0`, and put `s=|S|`.  No Galois action is assumed:
all arguments are fibrewise and therefore apply to a nonnormal rational cover.

## Theorem A: irregularity has a finite transient budget

If `q` has a pole of order `r>2` at `y`, define its irregularity by `I_y=r-2`.  At a point `x`
over `y` with ramification index `e_x`, equation (1) gives a pole of order

```text
2+e_x I_y.
```

The Schwarzian term has order at most two and cannot cancel it.  Therefore, writing `I_0` for the
total irregularity of `Q_0`,

```text
I_0 >= sum_(x in P^(-1)(y)) e_x I_y = D I_y.              (2)
```

Consequently every terminal connection seen through a prefix of degree `D>I_0` is Fuchsian: all
of its poles have order at most two.  This is a finite-transient theorem, not an asymptotic
regularity assumption.

## Theorem B: local exponent multiplication

At a Fuchsian pole let `c_y` be the coefficient of `dw^2/w^2` and define its exponent
discriminant by

```text
theta_y^2=1-c_y.                                          (3)
```

For a local map `w=t^e`, the double-pole coefficient in (1) is

```text
c_x=e^2 c_y+(1-e^2).
```

Hence

```text
theta_x^2=e^2 theta_y^2.                                  (4)
```

This is the projective analogue of the tensor shifted-order law.  The affine rank has the same
arithmetic: if `r_y` is the residue of an affine connection and `a_y=1+r_y`, then

```text
a_x=e a_y.                                                (5)
```

Both identities are exact polynomial identities and are formalized in Lean.

## Theorem C: only two non-orbifold fibres can survive

Call a terminal singular value `y` *regularizable* if its fibre contains a point `x` outside `S`.
At such a point `theta_x^2=1`; equation (4) forces

```text
theta_y^2=1/e_x^2.
```

Thus `y` has an integral cone weight `nu_y=e_x`.  A terminal singular value that is not
regularizable has its entire fibre in `S`.

For any marked target value write `r_y` for the number of distinct points in its fibre.  The
ramification spent over that fibre is `D-r_y`.  If three distinct fibres were wholly contained in
`S`, their fibre sets would be disjoint and Riemann--Hurwitz would give

```text
3D-s <= sum_y (D-r_y) <= 2D-2,
D+2 <= s.                                                 (6)
```

Therefore a prefix of degree `D>s-2` has at most two nonregularizable singular values.  The same
conclusion includes terminal simple poles: an unramified preimage retains the simple pole, while
a ramified preimage acquires a Schwarzian double pole, so every preimage of such a value belongs
to `S`.

## Theorem D: hyperbolic excess is degree-amplified

For each regularizable singular value, all preimages outside `S` have the same ramification index
`nu_y`.  If `s_y` is the number of exceptional preimages in `S` and `Ram_y` is the ramification
spent over the fibre, then direct fibre counting gives

```text
D(1-1/nu_y) <= Ram_y+s_y.                                 (7)
```

Treat each wholly exceptional fibre as a cusp, with `nu_y=infinity`; then (7) remains true because
`Ram_y=D-r_y` and `r_y<=s_y`.  Summing over the marked values, using disjointness inside `S` and
Riemann--Hurwitz, yields the exact projective-defect law

```text
D A <= 2D-2+s,
D(A-2)+2 <= s,                                            (8)
A=sum_y (1-1/nu_y).
```

The classical Hurwitz gap says that a hyperbolic orbifold on the sphere has

```text
A-2 >= 1/42,                                              (9)
```

with equality for signature `(2,3,7)`.  For completeness, the gap is elementary.  With at least
four marked points, compare against four order-two points; with three weights `2<=a<=b<=c`, split
into `a>=3`, `a=2,b>=4`, and `a=2,b=3`, whose nearest hyperbolic signatures are respectively
`(3,3,4)`, `(2,4,5)`, and `(2,3,7)`.  The last gives the smallest excess `1/42`.

Combining (8) and (9) proves

```text
D <= 42(s-2).                                             (10)
```

Thus no fixed source projective connection admits hyperbolic terminal orbifold geometry through
unbounded rational constraint degree.  Deep terminal geometry is forced to the spherical or
parabolic side, with at most two non-orbifold fibres.

## What this proves and what it does not

The theorem closes the singularity and Euler-characteristic part of the higher-order tail
problem.  It does **not** yet prove that every surviving parabolic projective connection has the
uniformizing accessory parameter, nor that the resulting rational tensor descends compatibly
through every phase.  That holonomy/accessory reduction is the remaining open core before the
complete finite-order tail classification can be promoted.

## Physical/topological meaning

Projective curvature behaves as a holographic defect: a terminal defect must appear on every
inverse sheet of the fixed source surface.  Genus zero supplies only `2D-2` units of ramification,
while negative orbifold Euler characteristic demands strictly more than `2D` units at a universal
rate of at least `D/42`.  A fixed finite singular set can pay that excess only finitely many times.
Unbounded coarse-graining therefore expels hyperbolic curvature and leaves zero- or
positive-Euler holonomy.  This is a static topology of compatible constraints, not time evolution.

## Novelty and significance gate

The ingredients are classical: Schwarzian pullback, local exponents, Riemann--Hurwitz, and the
`(2,3,7)` Hurwitz gap.  The candidate-new content is their nonautonomous tail synthesis: a fixed
source singular budget gives the quantitative obstruction (8)--(10) for arbitrary nonnormal
rational quotient maps and isolates exactly two possible non-orbifold worldlines.  Targeted parent
auditing is still required before publication status.

This is significant infrastructure for the proposed HT classification, but it is not by itself a
Fields-Medal result.  Its value is that the complete converse no longer has an uncontrolled
singular-projective sector; only the parabolic accessory/holonomy descent remains.

## RH impact audit

Any RH-sensitive finite-order rational tail would now be unable to retain hyperbolic projective
holonomy at unbounded depth.  It would have to enter the spherical/parabolic sector and, if the
remaining descent theorem succeeds, become an orbifold current.  No completed-zeta protocol is
constructed here, so there is no direct RH implication.

## Lean status

`NonautonomousProjectiveTailCollapse.lean` formalizes the affine shifted-residue law, the
projective exponent-discriminant law, the genus-zero marked-fibre budget, the three trapped-fibre
cutoff, the normalized projective excess budget, and the algebraic consequence of the `1/42`
Hurwitz gap.  The analytic interpretation of rational projective connections and the orbifold
signature lemma remain paper-level rather than being asserted as axioms.

## Gates

- [x] 0 -> 1: exact source-pure statement and non-Galois fibre formulation
- [x] 1 -> 2: complete local and global defect proof
- [ ] 2 -> 3: formalize the local divisor interpretation and Hurwitz signature gap
- [ ] 3 -> 4: primary-source novelty audit and independent projective-structure review
