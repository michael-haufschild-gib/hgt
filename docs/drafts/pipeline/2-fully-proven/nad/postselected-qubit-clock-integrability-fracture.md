# Postselected-qubit clock integrability fracture

- **ID:** `postselected-qubit-clock-integrability-fracture`
- **Stage:** 2-fully-proven / needs-audit
- **Type:** THEOREM (paper) / MEASUREMENT-CONDITIONED QUANTUM DYNAMICS
- **Scientific status:** `[PROVED] [CANDIDATE NEW SCIENTIFIC KNOWLEDGE]`
  `[NEEDS COMPLEX-DYNAMICS AND QUANTUM-INFORMATION AUDIT]`
- **General tail parent:**
  `../new_scientific_knowledge/rational-coarse-graining-orbifold-tail-classification.md`
- **Statement:** Two physically realizable degree-two postselected-qubit protocols lie on opposite
  sides of differential-algebraic integrability.  The experimentally realized orthogonalizer
  `f(z)=2z/(1+z^2)` has a DA exact depth clock because it is Moebius-conjugate to squaring.  The
  balanced XOR--rotation protocol `F(z)=(z^2+1)/(1-z^2)` has an HT exact depth clock because its
  critical portrait excludes every Ritt-integrable rational class.  Measurement-induced chaos is
  therefore not the criterion for physical hypertranscendence; the exact critical portrait is.

## Physical construction

Represent a pure qubit ray by

```text
|psi(z)> = (z|0>+|1>)/sqrt(1+|z|^2),       z in C-hat.           (1)
```

Take two identically prepared copies.  Apply the quantum XOR gate and postselect the second qubit
on `|0>`.  Up to normalization, the first-qubit amplitudes become

```text
(z,1) |-> (z^2,1).                                             (2)
```

A subsequent one-qubit rotation with `x=pi/4` and phase zero sends the projective amplitude pair
to

```text
(z^2,1) |-> (z^2+1,1-z^2).                                    (3)
```

Thus the successful conditional branch acts on the physical ray by

```text
                         z^2+1
F(z)= ---------------------------------.                        (4)
                         1-z^2
```

This is an exact protocol inside ordinary quantum mechanics.  The unitary and measurement are
linear on the two-copy state; the nonlinear one-qubit map appears only after conditioning and
renormalization.  It is not deterministic CPTP evolution of one copy, and its ensemble cost grows
because unsuccessful branches and one member of each pair are discarded.

## Exact critical portrait of the balanced XOR protocol

The primitive projective pair of `(4)` is

```text
N(z)=z^2+1,                 D(z)=1-z^2.                          (5)
```

It has no common zero.  Its finite derivative cross-numerator is

```text
N'(z)D(z)-N(z)D'(z)=4z,                                      (6)
```

so the only finite critical point is `0`.  In the local coordinate `w=1/z` at infinity,

```text
F(1/w)+1 = 2w^2/(w^2-1),                                     (7)
```

so infinity is the second simple critical point.  Their exact projective orbits are

```text
infinity -> -1 -> infinity,
0        ->  1 -> infinity.                                  (8)
```

Consequently infinity is critical of exact period two, while zero is strictly preperiodic and
lands on that superattracting two-cycle.

## Ritt exclusion

The portrait `(8)` is incompatible with every rational class whose Poincare/Schroeder functions
can be differentially algebraic:

1. A quadratic monomial conjugate to `z^2` has two fixed critical points.
2. A quadratic reciprocal monomial conjugate to `z^(-2)` has both critical points on the same
   two-cycle.
3. A quadratic map conjugate to `+T_2` or `-T_2` has a fixed critical point, inherited from the
   polynomial point at infinity.
4. A Lattes map has no periodic critical point; a periodic critical point would create a
   superattracting Fatou component, whereas a Lattes map has Julia set the whole sphere.

Critical points and their exact preperiod/period data are preserved by Moebius conjugacy.  Since
`F` has one period-two critical point and one strictly preperiodic critical point, `(4)` is in none
of the Ritt-integrable classes.

Both critical orbits enter the superattracting two-cycle, so `F` is hyperbolic.  Its fixed points
are repelling.  Let `a` be any such fixed point, `lambda=F'(a)`, and let `L` be the normalized
Poincare linearizer

```text
L(0)=a,          L'(0)=1,          L(lambda t)=F(L(t)).         (9)
```

The Ritt--Becker--Bergweiler classification applied to the exclusion above gives

```text
L is hypertranscendental over C(t).                             (10)
```

Equivalently, the local exact conditional-depth clock and beta obtained from `(9)` are HT in every
locally invertible DA coordinate on the qubit ray.  There is no finite algebraic differential
equation whose flow reproduces the successful discrete protocol at every integer depth.

This obstruction concerns exact interpolation in iteration depth.  It does not prevent the finite
quantum circuit for one step, numerical iteration, finite-depth tomography, or asymptotic
description of an attracting basin.

## Exact DA control: the experimentally realized orthogonalizer

Zhu--Kalman--Wang--et al. experimentally implemented a two-copy entangling/postselection protocol
on the polarization and spatial qubits of single photons.  Its exact ray map is

```text
                         2z
f(z)= ---------------------------------.                        (11)
                         1+z^2
```

Let

```text
M(z)=(1+z)/(1-z).                                               (12)
```

Then direct algebra gives

```text
M(f(z))=M(z)^2.                                                 (13)
```

Thus `f=M^(-1) o (z |-> z^2) o M`.  Its two critical points `+1` and `-1` are fixed,
exactly matching the power-map portrait.  A DA Schroeder coordinate at the repelling fixed point
zero is

```text
phi(z)=log M(z),             phi(f(z))=2 phi(z).                (14)
```

On a chosen logarithmic branch, an explicit exact continuous-depth interpolation is

```text
f^t(z)=M^(-1)(M(z)^(2^t)).                                     (15)
```

The clock, beta, and every fixed-`t` slice in `(15)` are DA.  The experimentally observed Julia
boundary and rapid state separation are therefore compatible with differential-algebraic exact
depth dynamics.

## Founding physical distinction

Equations `(4)` and `(11)` are both quadratic rational maps generated by two-copy unitary
processing plus postselection.  Both can exhibit sensitive nonlinear quantum behavior.  Yet their
exact clocks have opposite differential-algebraic type:

```text
postselection + rational nonlinearity + Julia dynamics          insufficient;
nonexceptional critical portrait                                HT clock;
power/Chebyshev/Lattes critical portrait                        DA clock.        (16)
```

This is a falsifiable physical classification, not a metaphor.  A protocol's gate and measurement
data determine a rational map; the map's critical orbit portrait determines whether an exact
finite differential generator can exist.  The classification separates protocols that ordinary
chaos diagnostics place in the same qualitative bucket.

## Infinite-depth finite-jet information fracture

The live corpus now contains a general classification of stable differential-observable tails for
rational coarse-graining.  Apply it to a differential-generic source family `z=z(s)`, with `delta`
denoting differentiation in the external source parameter `s`.

Because the balanced protocol `F` is nonexceptional, its stable finite-jet observable field is

```text
Tail(F)=intersection_(n>=0) F^(n)* C<z> = C.                    (17)
```

No nonconstant rational expression in finitely many source derivatives can be reconstructed after
arbitrarily many successful conditional depths.

For the experimental control `f`, use the exact power coordinate `w=M(z)`.  Squaring preserves the
logarithmic orbifold current `delta w/w`.  Pulling it back through `(12)` gives

```text
delta w/w = 2 delta z/(1-z^2),
Tail(f)=C<delta z/(1-z^2)>.                                   (18)
```

The irrelevant nonzero scalar two does not change the generated differential field.  Thus the
clock fracture is accompanied by an information-horizon fracture:

```text
balanced XOR protocol:       HT clock, trivial finite-jet tail;
experimental orthogonalizer: DA clock, one flat orbifold-current tail.             (19)
```

Equation `(17)` is not a claim that a finite qubit state literally becomes unknowable.  It concerns
the intersection of exact finite-order differential observable fields of a generic source family.
Finite-depth tomography and arbitrary nonlocal functions of the full orbit remain outside that
intersection.

## Genuine quantum content and its boundary

The HT protocol is not a renamed classical population recursion.  Its state coordinate is a
coherent amplitude ratio.  Successive pure-state projectors need not commute.  For example,

```text
2 -> F(2)=-5/3,                                                  (20)
```

and the unnormalized rank-one projector numerators

```text
P(z)=[[z^2,z],[z,1]]
```

satisfy

```text
(P(z)P(w)-P(w)P(z))_(0,1)=(z-w)(zw+1).                          (21)
```

At `(z,w)=(2,-5/3)`, both factors in `(21)` are nonzero.  Hence adjacent physical state
projectors in this exact orbit do not commute.  Coherent amplitudes and the balanced rotation are
load-bearing.

This still does not prove an operator-valued quantum-belief-propagation theorem: after restriction
to pure rays, the state dynamics is one complex rational coordinate.  Nor is it a continuum QFT
theorem.  The advance is the first exact noncommuting quantum-state realization in this project for
which the HT/DA clock distinction is proved and experimentally adjacent.

## QFT and tensor-network successor

`[CONJECTURE]` Let an exact postselected tensor-network coarse-graining step preserve a projective
bond-state curve and induce a nonexceptional rational self-map on that curve.  If the curve is not
contained in a commuting operator algebra, then the exact scale clock of every nonconstant DA
observable separating the curve is HT.

The finite-qubit theorem proves the local model behind this conjecture.  A novelty-bearing QFT
successor must now supply all three missing structures simultaneously:

1. a field-theoretic or continuum-limit tensor network with a physically specified instrument;
2. an invariant projective family of boundary states or sources not reducible to a commuting
   population algebra;
3. an observable whose exact coarse-graining law is the nonexceptional rational map, with the
   continuum limit and postselection cost controlled.

Merely inserting `(4)` as an arbitrary auxiliary coordinate into a tensor network would be
redressing, not inheritance.

## Anti-theatre and novelty verdict

Measurement-induced nonlinear qubit maps, their Julia sets, the two explicit protocols, and the
Ritt classification are parent theory.  The new candidate contribution is the exact differential-
algebraic fracture `(16)`, its proof from the two physical critical portraits, and its consequence
that a concrete coherent quantum protocol admits no finite algebraic-differential depth generator
while an experimentally realized chaotic orthogonalizer does.

Targeted searches for `hypertranscendence`, `differentially algebraic`, Schroeder, Abel, and
Poincare clocks together with conditional qubit dynamics, purification, postselection, and the
specific rational maps found no prior quantum-information statement of this fracture.  The physics
literature studies chaos, Julia geometry, purification, state discrimination, success probability,
and experimental realization; the differential-algebra literature classifies rational iteration
functions without this operational quantum comparison.  This is provisional negative evidence,
not a completed specialist citation audit.

The theorem clears the significance gate as a founding example for physical HT: it gives an exact
laboratory-defined distinction that chaos does not detect.  It remains in `needs-audit` until a
specialist search confirms that the Ritt classification has not already been applied to these
postselected-qubit protocols.

## Lean boundary

The two projective amplitude maps, XOR/postselection and balanced-rotation factorization, primitive
noncancellation, derivative cross-numerator, exact critical orbits, the experimental map's Moebius
conjugacy, and an explicit noncommuting projector witness are unconditional algebra.  They are
formalized in
`formal/GaloisForLFunctions/HTGeometry/PostselectedQubitRationalDynamics.lean`.

The complex-dynamical facts about hyperbolicity, the classification of Lattes critical points, and
the external Ritt--Becker--Bergweiler HT theorem remain paper-level inputs and are not postulated in
Lean.

## Primary sources

- T. Kiss, I. Jex, G. Alber, and S. Vymetal, *Complex chaos in the conditional dynamics of
  qubits*, *Physical Review A* 74, 040301(R) (2006),
  <https://arxiv.org/abs/quant-ph/0511208>.
- T. Kiss, I. Jex, G. Alber, and S. Vymetal, *Complex chaos in conditional qubit dynamics and
  purification protocols*, <https://arxiv.org/abs/0705.1979>.  Equations (1)--(7) give the
  XOR, postselection, rotation, and family containing `(4)`.
- G. Zhu, O. Kalman, K. Wang, et al., *Experimental orthogonalization of highly overlapping
  quantum states with single photons*, *Physical Review Research* 1, 033019 (2019),
  <https://arxiv.org/abs/1910.10377>.  Equations (1)--(6) give the implemented map `(11)` and its
  success probability.
- O. Kalman and T. Kiss, *Quantum state matching of qubits via measurement-induced nonlinear
  transformations*, *Physical Review A* 97, 032125 (2018),
  <https://arxiv.org/abs/1708.03610>.
- G. Fernandes, *A survey on the hypertranscendence of the solutions of Schroeder's, Boettcher's
  and Abel's equations*, <https://arxiv.org/abs/2102.12168>.
- W. Bergweiler, *Solution of a problem of Rubel concerning iteration and algebraic differential
  equations*, *Indiana University Mathematics Journal* 44 (1995), 257--267.

## Gates

- [x] Exact successful-branch qubit map derived from XOR, measurement, and balanced rotation.
- [x] Primitive noncancellation and both critical points identified.
- [x] Exact preperiod/period portrait proved.
- [x] Power, reciprocal-power, Chebyshev, and Lattes classes excluded.
- [x] HT Poincare/clock consequence obtained from the external classification.
- [x] Experimentally realized DA control map proved Moebius-conjugate to squaring.
- [x] Exact DA continuous-depth interpolation of the control exhibited.
- [x] Trivial finite-jet tail of the nonexceptional protocol derived from the general tail theorem.
- [x] Surviving orbifold current of the experimental power protocol identified exactly.
- [x] Explicit noncommuting adjacent-state witness proved.
- [x] Postselection cost and non-CPTP conditional scope stated.
- [x] Targeted cross-literature novelty search provisionally passed.
- [ ] Specialist complex-dynamics novelty audit completed.
- [ ] Specialist quantum-information priority audit completed.
- [ ] Balanced XOR map implemented experimentally with clock-sensitive observable.
- [ ] Noncommuting tensor-network/QFT inheritance conjecture proved.
