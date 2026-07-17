# Elliptic-gamma source actions fracture from groups to boundary monoids

- **ID:** `elliptic-gamma-source-face-fracture`
- **Stage:** 3-formalized
- **Type:** SOURCE-DEGENERATION NO-GO / MAXIMAL POSITIVE ALGEBRAIC CORRECTION
- **Scientific status:** `[PROVED; LEAN-FORMALIZED] [PARENT BRIDGE]`
  `[NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH RESULT]`
- **Lean:**
  `formal/GaloisForLFunctions/HTGeometry/EllipticGammaSourceFaceFracture.lean`
- **Successor:**
  `../../1-in-progress/hypertranscendental-source-face-vanishing-cycle-conservation.md`

## The no-go

Let `x` be an invertible orbit coordinate in a commutative ring and let `phi` be a ring
endomorphism satisfying

```text
phi(x)=q*x.                                                  (1)
```

Lean proves

```text
x a unit and (1)  ->  q a unit.                             (2)
```

In particular, no endomorphism of an algebra in which `x` remains invertible can specialize the
scaling source to `q=0`.  A family of source automorphisms therefore cannot cross the zero-nome
wall while remaining an action of the same group on the same orbit algebra.

This rules out the proposed universal reconstruction object

```text
unlabelled period subgroup + topology, even derived topology. (3)
```

The failure in `(2)` occurs before topology: the source category changes because the generator
ceases to be invertible.  Period topology may still be a useful shadow, but it cannot reconstruct
the labelled boundary ideal and specialized multiplier that it has forgotten.

## Maximal positive correction

Compactify the multiplicative orbit algebra to the polynomial algebra `R[X]` and define

```text
S_q(P)(X)=P(qX).                                             (4)
```

At the singular face Lean proves the exact classification

```text
S_0(P)=P(0),
ker S_0=(X),
im S_0=R.                                                    (5)
```

Thus zero scaling is not a deleted action.  It is a boundary retraction.  The lost information is
the explicit boundary ideal `(X)`, and the retained information is the boundary coefficient
algebra.  This is the minimal algebraic replacement of the failed group-action compactification.

## Elliptic-gamma face theorem

For the multiplicative elliptic-gamma atoms

```text
F_(j,k)=p^(j+1) q^(k+1)/x,
B_(j,k)=p^j q^k x,                                          (6)
```

zero-nome specialization gives

```text
F_(j,k)|_(q=0)=0,
B_(j,0)|_(q=0)=p^j x,
B_(j,k+1)|_(q=0)=0.                                        (7)
```

Consequently every nonempty finite backward rectangle collapses exactly to the same
one-dimensional Pochhammer boundary:

```text
prod_(j<J) prod_(k<K+1) (1-B_(j,k)|_(q=0))
  = prod_(j<J) (1-p^j x).                                  (8)
```

The surviving boundary obeys the source recurrence

```text
D_(J+1)(p,x)=(1-x) D_J(p,px).                              (9)
```

The atomic statement holds in every multiple-elliptic-gamma rank: setting one labelled nome to
zero kills the entire forward sector and every positive slice of the backward sector, while the
zero slice is exactly the coordinate-deletion face.  Hence degeneration lowers source height by a
face map rather than erasing a period.

## What this means

`[NO-GO]` Period topology, orientation, and coefficient-blind derived topology cannot be the
unified HT object: they assume the source generators remain invertible and cannot carry the
boundary ideal or the specialized multiplier.

`[POSITIVE]` The correct base object must be a compactified **labelled source monoid**.  Its
noninvertible faces carry a boundary ideal and a specialized coefficient cocycle.  Period closure
is only one forgetful realization of this object.

The theorem does not yet prove that a hypertranscendence anomaly is conserved across the face.
It identifies the only category in which that statement can even be formulated without losing the
data at the wall.

## Novelty and anti-theatre gate

The ingredients are classical:

1. the elliptic gamma function has a trigonometric degeneration to a q-gamma or Pochhammer
   product;
2. a homomorphism sends units to units;
3. `P(X) -> P(0)` has kernel `(X)` and constant image;
4. toric and logarithmic compactifications replace group actions by monoid actions at boundary
   faces.

Therefore `(2)`--`(9)` are not claimed as new science.  Their role is discriminatory: they kill a
too-small proposed unifier and expose a precise positive successor.  Renaming `(5)` a
"vanishing-cycle theorem" would be theatre.  New knowledge requires proving conservation of the
actual DA-filtered HT class across `(8)`--`(9)`.

The primary special-function parents are Felder--Varchenko's elliptic-gamma degeneration and
Felder--Henriques--Rossi--Zhu's gamma-gerbe construction.  Targeted searches found no theorem
coupling this source-action fracture to a differential-algebraic anomaly specialization.

## Verification

- exact module cache build passed;
- direct touched-file `lake env lean` verification passed;
- no full or area build was run.
