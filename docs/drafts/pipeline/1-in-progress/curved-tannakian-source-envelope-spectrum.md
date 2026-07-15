# Curved Tannakian source envelope and common obstruction spectrum

- **ID:** `curved-tannakian-source-envelope-spectrum`
- **Stage:** 1-in-progress
- **Type:** CONJECTURE PROGRAM
- **Scientific status:** `[CONJECTURE] [MEDAL-LEVEL OPEN CORE]`
- **Claim:** The complete invariant of a finite-source hypertranscendental observable is a pointed
  differential-Tannakian source envelope, not a jet space.  Its derived source cohomology carries
  both the free clock-capacity module and the curved holonomy needed for continuation, monodromy,
  spectral, positivity, and boundary-condition realizations.

## Proven base case forcing the conjecture

For arbitrary possibly noncommuting source automorphisms, the following are now proved:

1. additive primitives have a complete simultaneous source-boundary matroid;
2. multiplicative primitives have the exact logarithmic source-boundary criterion, with the
   singleton equivalence formalized in Lean;
3. every split commutative source group `G_a^r x G_m^s` has a complete linear boundary
   polymatroid;
4. every finite-dimensional commutative algebraic `D`-group has the same complete linearization;
5. its sharp kernel has zero differential transcendence degree over the logarithmic image and
   therefore cannot be a hidden HT-capacity layer.

Thus the first genuinely unknown layer cannot occur inside finite-dimensional commutative
logarithmic geometry.  It must be the obstruction to such a linearization.

## The pointed source envelope

Let `f` be an observable over a differential field `K` with a finite set of source operations.
A source presentation consists of a differential field extension containing `f`, compatible
source automorphisms, and finite-dimensional differential-rational coordinates in which the
source action is defined.

`[CONJECTURE]` The 2-category of faithful source presentations of `f` has a presentation-independent
minimal pro-algebraic differential groupoid `G_f`, unique up to Morita equivalence.  Its finite
differential-rational representations form a neutral differential-Tannakian category `T_f`.

For a representation `(V,nabla)` and source arrows `i`, write the semilinear action as

```text
sigma_i(z) = A_i z + omega_i.                            (1)
```

The linear parts define a local system and the increments define an extension class.  The
associated source complex begins

```text
C^0(V) = K tensor V
   --delta_A-->
C^1(V) = product_i (K tensor V),

delta_A(v)_i = tau_i(v) - A_i v.                        (2)
```

Relations in the source groupoid supply the higher terms and cocycle conditions.  The
distinguished affine source action gives a pointed class

```text
[omega_f,V] in H^1(G_f,V).                              (3)
```

Compatibility with the differential connection makes these cohomology objects modules over the
appropriate differential-operator algebra.

Define the curved capacity object

```text
B_f = (T_f, RGamma(G_f,-), [omega_f,-]).                 (4)
```

It is a tensor-valued derived object, not one vector space.

## The affine law is one extension object

Equation (1) is canonically the block semilinear representation

```text
E_i = [ A_i  omega_i ]
      [  0       1    ].                                (5)
```

It represents an extension in the source-module category

```text
0 -> V_A -> E_(A,omega) -> 1 -> 0.                      (6)
```

The gauge change `(B,u)` is exactly a change of splitting of (6), together with an isomorphism of
its local system `V_A`.  Thus the capacity class and the curvature carrier are not two unrelated
decorations: they are the extension class and its coefficient object.

At the first cohomological level the correct boundary is already forced:

```text
Q_A(K) = Coker(delta_A),
delta_A(u)_i = tau_i(u)-A_i u.                           (7)
```

The capacity class is `[omega] in Q_A(K)`.  The ordinary scalar boundary is only the special case
`A_i=1`.  In the twisted `-1` counterexample, `[tau_i(h)+h]` is zero in `Q_(-1)` even though its
image after forgetting `A` is non-torsion in `Q_(+1)`.  The corrected boundary therefore predicts
zero capacity exactly.

The twisted affine counterexample proves why the coefficient object cannot be forgotten.  For
`A_i=-1`, `z=h`, and `omega_i=tau_i(h)+h`, the projection of `omega` to the trivial scalar quotient
is non-torsion, but (6) is split by the base section `h` in the `-1` local system.  Its true
extension capacity is zero.  Scalar projection destroys the twisting and creates a false free
rank.

## `[NO-GO]` Capacity is not the unipotent radical

The first capacity--curvature conjecture assigned all HT capacity to the unipotent radical of the
pointed extension.  A multiplicative primitive kills it.  The homogeneous equation

```text
sigma_i(x)=b_i x
```

has no affine extension class and may have trivial unipotent radical, while the exact
source-logarithmic theorem proves that `x` is hypertranscendental whenever
`[D(b_i)/b_i]` is non-torsion.  Its capacity lives in the differential structure of the
`G_m`-type holonomy itself.

`[POSITIVE STATEMENT]` A Levi/unipotent exact sequence may organize the envelope, but capacity is
the differential growth of the entire group, not one factor.  Under hypotheses where

```text
1 -> U_f -> Gal_D(B_f) -> H_f -> 1                     (8)
```

exists, the Kolchin dimension polynomials of all factors and the coupling class must be retained.
Neither `U_f` nor `H_f` alone is complete.

## Corrected capacity--curvature conjecture

For a finite observable tuple `f`, define its jet-growth function

```text
kappa_f(n) = trdeg_K K(D^j f : 0 <= j <= n).            (9)
```

Kolchin theory makes `kappa_f(n)` eventually polynomial.  A single HT observable has leading
growth `n+1`; a differentially algebraic observable has eventually bounded growth.  This is the
literal algebraic clock capacity: the number of algebraically new observable readings available
by resolution `n`.

`[CONJECTURE]` The minimal source envelope carries two transverse invariants:

```text
capacity  = Kolchin polynomial of the full differential Tannaka orbit/group,
curvature = algebraic holonomy local system + torsor/extension class. (10)
```

The pointed twisted boundary modules compute the leading capacity term representation by
representation.  In the proved commutative source class, their generic ranks equal differential
transcendence ranks.  Their torsion support records finite annihilating characters.  Lower-order
finite algebraic state may remain in logarithmic fibres and is not falsely claimed to be recovered
by the generic boundary rank.

`[CONJECTURE]` The complete source-orbit differential matroid and its Kolchin growth filtration are
reconstructed from the tensor family of twisted modules `Q_A`, together with the algebraic
holonomy and coupling classes.  The scalar module is one fibre; the whole tensor family is the
field.

**Falsifier:** two minimal pointed envelopes with isomorphic algebraic holonomy, equivalent torsor
classes, and isomorphic twisted boundary modules in every tensor representation, but different
Kolchin growth functions for some source-orbit subfamily.

## Completeness conjecture

`[CONJECTURE]` Every algebraic differential relation among the full source orbit of `f` belongs to
the tensor ideal of representations and differential characters that annihilate the pointed
classes (3).  Conversely, every such annihilator produces an algebraic differential relation.

Equivalently:

```text
differential-algebraic geometry of the source orbit
  = tensor annihilator geometry of B_f.                (11)
```

The ordinary simultaneous boundary module is the trivial-adjoint fibre of (4).  The proved
commutative theorem is therefore not an analogy but the rank-one flat case of (11).

**Falsifier:** a faithful finite-source presentation with a differential relation invisible in
every finite differential-rational representation and every derived source-cohomology class, or
two Morita-equivalent pointed envelopes with different source-orbit differential matroids.

## Exact flat/curved boundary

Under a base-affine gauge change `y=Bz+u`, equation (1) becomes

```text
A'_i     = tau_i(B) A_i B^(-1),
omega'_i = tau_i(B) omega_i + tau_i(u) - A'_i u.        (12)
```

Therefore the system reduces to pure translations if and only if one `B` satisfies

```text
tau_i(B) A_i = B                                       (13)
```

for every source direction.  When (13) holds, the existing arbitrary-family additive theorem
classifies the complete differential matroid of `y`, and invertibility of the base gauge transfers
that classification back to `z`.

`[PROVED PAPER REDUCTION]` The simultaneous semilinear gauge class of `(A_i)` is exactly the
obstruction to entering the proved linear source-boundary theory.  For a source groupoid this is
the nonabelian `H^1`/holonomy class of the local system.

`[NO-GO]` A topology built only from the scalar quotient `K^I/delta K` cannot be universal: it
forgets nontrivial adjoint holonomy.

`[POSITIVE THEOREM]` On the entire gauge-flat locus, nonlinear differential dependence still
collapses exactly to the simultaneous linear boundary after one canonical type of gauge
trivialization.  The first new invariant beyond the proved theory is precisely the gauge class,
not an unspecified nonlinear remainder.

### Proof of the gauge-flat reduction

Apply `sigma_i` to `y=Bz+u`, use semilinearity on the base coefficients, and substitute
`z=B^(-1)(y-u)`.  This gives (12) identically.  The transformed action is translational precisely
when `A'_i=1` for every `i`, which is equivalent to (13); the translation vector is then

```text
omega'_i = tau_i(B)omega_i + tau_i(u)-u.                (14)
```

The coordinate fields generated by `y` and `z` are equal because `B` is invertible and `B,u`
belong to the base.  Hence their differential transcendence ranks agree for every subfamily.  The
arbitrary-family additive Ostrowski theorem applied to `y` classifies those ranks by the
simultaneous coboundary classes of the coordinates of `omega'_i`.  Conversely, the linear part of
an affine source action is unaffected by translation `u`, so any base-affine reduction to pure
translations necessarily supplies a `B` satisfying (13).  `QED`

## Capacity topology and curvature

For a finite family in the flat commutative case, the boundary classes generate a coherent module
over `C[D]`.  Its generic fibre is the differential matroid, and its torsion support is the finite
annihilator divisor.  Thus HT means support reaches the generic point of the operator line.

`[CONJECTURE]` For the curved envelope (4), there is a derived support theory with two independent
pieces:

```text
generic support  = infinite algebraic clock capacity,
holonomy support = obstruction to simultaneous logarithmic linearization. (15)
```

This is the proposed topology of hypertranscendental functions.  It distinguishes infinite
capacity from curvature instead of conflating both under the word “complexity.”

## Five realization conjecture

`[CONJECTURE]` The five obstruction types seen in the RH research are realization failures of one
pointed envelope:

1. **continuation failure:** the de Rham/analytic fibre functor does not extend the pointed class;
2. **monodromy:** the extended class has nontrivial holonomy in the Betti fibre functor;
3. **spectral incompleteness:** an operator realization of the boundary complex is not perfect or
   its comparison cone has nonzero cohomology;
4. **positivity failure:** the self-dual realization admits no positive polarization compatible
   with the pointed class;
5. **noncanonical boundary conditions:** the polarized realization has more than one admissible
   self-dual extension.

These predicates are not asserted to be equal.  They are conjectured to be images of the same
class under different realization functors.

**Falsifier:** two source-matched obstruction chains whose minimal pointed envelopes have no common
Morita refinement, or a pair of realization functors that assign incompatible obstruction classes
to a shared refinement.

## Determinant-spectrum conjecture

Let `S` be a complex parameter space with duality `iota`.  Suppose a polarized realization of
`B_f` gives a perfect comparison complex `C_s` and determinant line

```text
Det(C) -> S.                                            (16)
```

`[CONJECTURE]` The intrinsic degeneracy spectrum of the source object is the support of the
cohomology of `C_s`, equivalently the zero divisor of its determinant section.  Duality gives

```text
C_(iota(s)) ~= C_s^vee,                                 (17)
```

so the divisor is self-dual.  Positivity is an additional structure selecting whether all
degeneracies are of fixed-point type; duality alone does not do so.

This separates three facts that earlier RH chains repeatedly conflated:

- a determinant produces a divisor;
- self-duality produces symmetric degeneracies;
- positivity is the extra condition that could force the degeneracies onto the fixed locus.

## Zeta pressure test `[CONJECTURE]`

The completed zeta function is conjectured to be the determinant section of a polarized
prime--archimedean realization of one pointed source envelope:

```text
det(C_s) = unit(s) * Xi(s).                             (18)
```

The critical zeros would then be the non-acyclicity spectrum of the common comparison complex.
The functional equation would realize (17) with `iota(s)=1-conj(s)`, whose fixed locus is the
critical line.  RH would say that every degeneracy of (18) is of fixed-locus type.

This is not an RH result.  The conjecture is falsified if no source-pure prime--archimedean
envelope can produce (18), if two of the five source-matched realizations force inequivalent
determinant divisors, or if the required polarization permits compatible off-fixed-locus
degeneracies.

## Anti-theatre gate

### Parent collision that must not be claimed as new

León Sánchez--Meretzky, *Parameterized D-torsors in differential Galois theory* (2026), prove that
generalized strongly normal extensions arise as differential Galois extensions of parameterized
`D`-torsors and give a differential-cohomological criterion for when such a torsor comes from a
logarithmic differential equation on its Galois group.  Kolchin--Pillay strongly normal theory,
parameterized Picard--Vessiot theory, Tannakian extension objects, and nonabelian `H^1` are further
direct parents.

Therefore none of the following is a novelty claim here:

- encoding an affine law as a torsor or extension;
- associating a differential Galois group;
- using cohomology to test triviality of a torsor;
- separating a unipotent radical from a holonomy quotient in a linear Galois group.

The candidate-new delta is the combination of:

1. an arbitrary external source groupoid, allowing genuinely noncommuting difference-field
   automorphisms rather than a chosen commuting derivation system or one difference operator;
2. a complete differential-matroid theorem for the pointed extension across every finite
   subfamily;
3. Morita invariance under different faithful source presentations;
4. one polarized determinant object whose realization failures recover the five independently
   source-matched obstruction chains.

If these four items collapse to an existing generalized strongly normal/torsor theorem, this
program is not new and must be retired.

- `[PASS]` The conjectured object is defined by a universal property and exact complexes, not by
  metaphor.
- `[PASS]` The commutative flat fibre is a proved theorem, including an exact Lean singleton.
- `[PASS]` The first unproved invariant is named precisely: simultaneous adjoint gauge class.
- `[PASS]` Every conjectural promotion has an explicit falsifier.
- `[OPEN]` Existence and Morita uniqueness of the minimal source envelope.
- `[OPEN]` Tannakian completeness theorem (11).
- `[OPEN]` Derived support and determinant comparison.
- `[OPEN]` One noncommutative analytic example with nontrivial gauge class.
- `[FAIL if oversold]` Tannakian, `D`-groupoid, derived-support, and determinant-line parent
  theories are classical.  Novelty must lie in the pointed source-envelope completeness theorem
  and its common-obstruction realization, not in the vocabulary.

## References at the parent boundary

- O. León Sánchez and D. Meretzky, *Parameterized D-torsors in differential Galois theory*, 2026.
- E. Kolchin, *Differential Algebra and Algebraic Groups*, 1973.
- A. Pillay, *Differential Galois theory I*, 1998.
- C. Hardouin and M. F. Singer, *Differential Galois Theory of Linear Difference Equations*, 2008.

## Next theorem-level attacks

1. Prove the gauge-flat affine source rank theorem in full family form.
2. Construct and compare minimal pointed envelopes for a noncommutative linear
   difference--differential system.
3. Produce an example where the scalar boundary rank is identical but the adjoint gauge classes
   differ, proving curvature is an independent invariant.
4. Build a determinant line for that example and verify that continuation and monodromy are two
   realizations of the same pointed class.
5. Only then source-match a prime--archimedean system; do not use RH to select the theory.

## Log

- 2026-07-15 -- Conjecture sharpened after the commutative `D`-group theorem killed the proposed
  hidden radical layer.  The live nonlinear object is now the pointed Tannakian source envelope and
  its adjoint gauge curvature.
