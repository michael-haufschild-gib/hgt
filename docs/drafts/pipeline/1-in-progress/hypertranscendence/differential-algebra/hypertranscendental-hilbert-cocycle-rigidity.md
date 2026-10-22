# Hypertranscendental Hilbert-cocycle rigidity

- **ID:** `hypertranscendental-hilbert-cocycle-rigidity`
- **Stage:** 1-in-progress
- **Type:** UNIFIED FIELD THEORY / RH RESOLUTION PROGRAM
- **Scientific status:** `[CONJECTURE] [RANK-JUMP CORE LEAN-FORMALIZED] [POINTWISE PROPERTY-T ROUTE RETIRED] [NOVELTY OPEN]`

## Foundational claim

The terminal obstructions in the current RH chains are not values of one scalar.  They are
finite-packet norms built from affine Hilbert cocycles on different rank-one subgroupoids of one
constraint groupoid.  The object to construct is therefore a **polarized affine Hilbert local
system over the branch--clock--orientation groupoid of the HT source, together with a higher-rank
packetization map**.

The unified theory succeeds only if the completed source couples those rank-one directions into a
higher-rank root-graded group.  Each finite obstruction packet must be the value of the global
cocycle on one group element.  Fixed-point rigidity then bounds all packet energies at once, while
failure of RH supplies packets of arbitrarily large energy.  Pointwise realization of the prime
arrows is insufficient.

## The canonical orientation cocycle

On the Boolean orientation cube, an ordinary finite-tail arrow `epsilon -> delta` has the finitely
supported vector

```text
b(epsilon,delta)_n = charge(epsilon_n)-charge(delta_n) in l2_fin(N).       (1)
```

It satisfies the exact cocycle law

```text
b(epsilon,eta)=b(epsilon,delta)+b(delta,eta).                            (2)
```

After the Pauli normalization, `||b||²/4` is the Hamming distance.  On finite prime chambers its
positive and negative coordinate supports are exactly the two directed Krein inertias already
formalized in `UniversalPrimeKreinHamming.lean`.  Simultaneous global complement sends `b` to
`-b`, so `(1)` is a cocycle in the sign-twisted Hilbert local system on the projective tail
groupoid, not a scalar invariant of its indiscrete orbit space.

This is the stable positive replacement forced by the no-go corpus.  A scalar cohomology class
would cancel a hyperbolic positive--negative pair; the Hilbert cocycle retains both directions.

## The Xi seam is a Plucker packet, not a pointwise proper cocycle

For one Xi fibre put

```text
a_p = orbitwiseNatPrimeSeamCharge(p,rho),   mu_p=1/p.
```

On the reciprocal-prime pair groupoid the scalar coboundary is

```text
d a(p,q)=a_p-a_q.
```

The formalized pair energy is exactly its finite `L2(mu x mu)` norm.  Equivalently, on the finite
weighted Hilbert packet it is the squared norm of the antisymmetric Plucker tensor

```text
a_s tensor 1_s - 1_s tensor a_s,
```

and hence twice the Gram determinant

```text
E_s(a)=2(det Gram_mu(1_s,a_s))
      =2(M_s S_s-|A_s|^2).                                (3)
```

This is the first exact higher-rank form of the obstruction: it is the area of the source plane
spanned by the constant section and the seam section.  The critical-line condition collapses that
plane to the constant line; cofinal decay then collapses the constant to zero.

The pointwise property-`(T)` argument is false.  Throughout the open strip `a_p -> 0`; in
particular every individual difference `a_p-a_q` is bounded even off the critical line.  The
divergence in the existing RH theorem comes from accumulated infinite reciprocal-prime mass, not
from an unbounded value on one pair-groupoid arrow.  Thus fixed-point rigidity becomes relevant
only after a packetization

```text
s |-> g_s,    ||b(g_s)||^2=E_s(a).                         (4)
```

Equation `(4)`, not a pointwise restriction statement, is the exact bridge to construct.

## Why every existing chain stops

| Chain | Rank-one groupoid seen by the chain | Cocycle residue |
|---|---|---|
| prime/Hurwitz orientation | finite-tail Boolean flips | Krein--Hamming vector and common seam energy |
| Böttcher | dyadic branch/deck tree | branch-edge cocycle / unbounded monodromy length |
| Gamma inverse branches | local-unit time change and jet horizon | clock-jet translation cocycle |
| determinant/spectral flow | one-parameter crossing groupoid | signed crossing/Maslov cocycle |
| Sonin/Weil/Hedenmalm | compression of the same orientation local system | negative-index or norm-defect projection |

Each row retains a proper rank-one cocycle.  No argument internal to that row can force its
vanishing without additional rigidity; this explains the repeated obstruction pattern.

## Higher-rank coupling

The formal projective-horizon algebra currently generates the parabolic current algebra

```text
sl2(K[t]) semidirect (K[t]^2)^*.
```

The paper-proven theorem `projective-horizon-a2-current-rank-jump.md` shows that one opposite
transverse shear from a third horizon chart generates all Chevalley modes of `sl3(K[t])`.  This is
the minimal rank jump to the irreducible root system `A₂`.

For finitely generated rings, property `(T)` of the corresponding elementary root-graded groups is
parent theory.  The proposed completed HT constraint group must be a source-defined quotient or
representation of this universal group, with the cocycle `(1)` and its Gamma/Böttcher analogues
forming one affine Hilbert action.  Its root elements must encode complete finite packets as in
`(4)`, rather than only individual prime directions.

## RH contradiction target

The live Lean tree already proves the right-hand implication

```text
not RH
  -> one actual Xi fibre has unbounded finite reciprocal-prime pair energy.              (3)
```

The unified theory must prove the source-side implication

```text
completed A2 constraint action
  + source packetization s |-> g_s with ||b(g_s)||^2=E_s
  -> the canonical HT packet energies are uniformly bounded.                            (5)
```

Then `(1)`--`(5)` give

```text
not RH -> unbounded packet norms -> contradiction -> RH.                                 (6)
```

The use of property `(T)` is not decorative.  Delorme--Guichardet identifies it with the fixed
point property for affine isometric Hilbert actions.  The exact remaining theorem is the
source-defined integration, packetization, and equivariance that make the already-formalized Xi
pair energy the norm of a *single* cocycle value for every finite prime packet.

## Falsification gates

1. If the third horizon shear cannot be derived from the completed prime--Gamma--FE source, the
   `A₂` group is imposed rather than discovered and the route dies.
2. Lie-algebra generation alone is insufficient; the action must integrate to a discrete
   root-graded group over a finitely generated ring to invoke the parent rigidity theorem.
3. Property `(T)` yields a fixed point after affine recentering.  The source pointing must make the
   boundedness conclusion apply to the actual normalized cocycle, not to an unrelated gauge.
4. The cocycle norm on one packet element `g_s` must equal the existing pair energy on the same Xi
   fibre.  Realizing each pair difference as a separate bounded cocycle value is not a bridge.
5. A cofinal union of property-`(T)` groups need not have property `(T)`.  Either one fixed
   finitely generated `A₂` group acts on all prime coordinates or uniform relative rigidity must be
   proved.
6. If the cocycle factors through a target-defined zero divisor, the construction is circular.
7. Since the seam values tend to zero off-line as well as on-line, any argument claiming that
   property `(T)` contradicts an unbounded individual prime-arrow cocycle is false.

## Formalization plan

- [ ] formalize finite-tail arrows and the finitely supported Hilbert cocycle;
- [ ] prove cocycle additivity, complement anti-equivariance, and squared-norm/Hamming identity;
- [ ] splice the finite chamber cocycle to exact positive and negative Krein inertias;
- [x] formalize the Xi pair energy as the squared Plucker-packet norm and twice the weighted Gram
      determinant;
- [x] formalize the one-opposite-shear `A₂` current rank jump;
- [ ] define the abstract affine-isometric action/fixed-point interface needed by `(4)`;
- [ ] construct the source-derived third horizon and integrated root-group action;
- [ ] construct packet elements `g_s` and prove `||b(g_s)||^2=E_s`;
- [ ] close `(6)` and run the dual novelty/significance gate.

## Parent boundary

- Hilbert cocycles, conditionally negative definite kernels, the Haagerup property, and property
  `(T)` are classical.
- Hyperfinite `E_0` groupoids and their lack of separated selectors are classical.
- Higher-rank property `(T)` for elementary groups over finitely generated rings is classical.
- Candidate new content is the exact analytic identification of all three HT obstruction layers as
  packet norms of one cocycle, the Plucker-plane interpretation of the Xi seam, the minimal
  horizon-induced `A₂` rank jump, and the source-derived packet action whose fixed-point rigidity
  kills the RH obstruction.

## Fired no-go and positive residue

The first fixed-point formulation treated the Xi energy as though its divergence came from an
unbounded prime-pair cocycle value.  This is impossible because every seam charge tends to zero.
The strong positive residue is the exact packet criterion `(4)`: property `(T)` can still close the
route if and only if the whole finite Plucker packet is realized as one group-cocycle value.  This
turns a vague integration problem into a sharply falsifiable representation theorem.
