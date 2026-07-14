# Signed-cancellation balanced-quotient law

- **ID:** `signed-cancellation-balanced-quotient-law`
- **Stage:** 1-in-progress
- **Type:** THEOREM / FINITE SIGNED CONSTRAINT GEOMETRY
- **Scientific status:** `[PROVED FINITE CORE] [FORMALIZED FINITE CORE] [NOVELTY UNVERIFIED]`
- **Statement:** Exact cancellation of a nonzero signed source shell can survive only after the
  observable geometry descends to a quotient whose every fiber is charge-balanced; such a quotient
  has at most half as many distinguishable points as the shell, while positivity on a
  point-separating quotient forces sign coherence.

## Finite geometry

Let `P` be a finite source shell, let `mu_p` be nonzero real signed masses, and let
`kappa : P -> K` be a surjective observational quotient.  Define the fiber charge

```text
M_k = sum_(p : kappa(p)=k) mu_p.                             (1)
```

Every quotient observable has the form `f o kappa`, and its signed value is

```text
L_mu(f o kappa) = sum_k M_k f(k).                           (2)
```

Consequently

```text
L_mu(f o kappa)=0 for every f    iff    M_k=0 for every k.  (3)
```

Equation `(3)` identifies cancellation-compatible observable geometries exactly with balanced
quotients.

## Distinguishability cost

Assume every `mu_p` is nonzero and every fiber is balanced.  No fiber can be a singleton, since a
singleton fiber would have charge `mu_p != 0`.  Choosing two distinct representatives from every
fiber gives an injection

```text
K x {0,1} -> P,
```

and therefore

```text
2 |K| <= |P|.                                               (4)
```

Thus exact signed cancellation destroys at least half of the atomic distinguishability.  In
particular, a point-separating quotient is incompatible with cancellation unless the signed shell
itself is zero.

## Positivity and sign coherence

Let `Q=sum_p mu_p` be nonzero and normalize `(2)` by `Q`.  The quotient functional is positive on
all squares exactly when

```text
M_k/Q >= 0 for every k.                                    (5)
```

Now write `mu_p=epsilon_p a_p`, where `a_p>0` and `epsilon_p in {+1,-1}`.  For the point-separating
quotient, `(5)` forces all `epsilon_p` to be equal.  Hence

```text
positive + point-separating + normalized
    implies sign-coherent exposed face.                    (6)
```

Mixed signs can survive positivity only inside nontrivial quotient fibers whose net charges have
the common sign of `Q`; neutral fibers are completely dark.

There is also a sharp minority-confinement capacity bound.  Let `g_+` and `g_-` be the numbers of
positive- and negative-orientation atoms.  If `Q>0`, every positive quotient fiber must contain a
positive atom, so distinct fibers inject into the positive sector.  If `Q<0`, the analogous
statement holds for the negative sector.  Hence

```text
Q>0  implies  |K| <= g_+,
Q<0  implies  |K| <= g_-.                                 (7)
```

Equivalently, converting a mixed signed shell into a positive quotient loses at least the complete
minority-sign cardinality.  The point-separating case `|K|=g_++g_-` forces the minority sector to be
empty and recovers `(6)`.

## Signed tropical consequence

For a finite exponential or Gibbs sum, suppose the scalar leading coefficient on an exposed shell
cancels.  A normalized observable has no contribution above the next nonzero scalar level only if
its leading signed shell moment also cancels.  If this is required for a quotient algebra of
observables, `(3)` says that the leading shell must be balanced in every observational fiber.
Equation `(4)` then quantifies the information lost at that cancellation step.

This gives a positive form of the signed-normalization constraint: a cancellation step creates a
balanced observational quotient.  It does not merely remove a leading term.

## HT significance

The law couples three structures that were previously separate in the corpus:

1. orientation signs on a source face;
2. tropical or zero-temperature normalization;
3. the point-separation capacity of the constraint algebra.

A universal finite HT carrier must separate arbitrarily rich finite source patterns.  It therefore
cannot use neutral signed leading shells without paying a cofinal loss of at least one half of the
available atomic resolution at each cancellation layer.  If its limiting metric is positive and
point-separating, every exposed face must instead be sign-coherent.

## Product target

For product quotients `kappa_A x kappa_B`, fiber charges multiply:

```text
M_(k,l) = M^A_k M^B_l.                                     (8)
```

The balanced quotient property is therefore absorbing: if either factor is balanced, the product
is balanced.  The positive effective support is multiplicative after neutral fibers are removed.
The exact product theorem and the induced filtration on iterated cancellation quotients remain to
be added.

## RH audit

The theorem is a route constraint, not an RH criterion.  An RH-facing signed Gram, Krein, or
thermal construction must choose between two positive alternatives:

1. retain point separation, in which case every exposed positive boundary is sign-coherent; or
2. exploit cancellation, in which case it must identify the resulting balanced quotient and prove
   that the lost source distinctions are irrelevant to the Xi divisor.

No known source theorem supplies the second implication.  In particular, scalar cancellation or a
finite Krein index alone cannot preserve a cofinally complete prime- or zero-separating geometry.

## Dual gate

- **Parent theory:** finite signed measures, quotient function algebras, finite
  Stone--Weierstrass separation, and elementary cardinality.
- **Candidate residue:** the balanced-quotient classification as the geometry forced by signed
  tropical normalization, the sharp half-capacity loss, and its cofinal HT consequence.
- **Retirement condition:** downgrade to `[BRIDGE]` if the exact cancellation--quotient--capacity
  package is already standard in signed exponential-family, sign-problem, or finite function
  algebra literature, or if no source-canonical signed exposed shell occurs in an HT application.

## Formal certificate

File:
`formal/GaloisForLFunctions/HTGeometry/SignedCancellationQuotient.lean`

Theorems:

- `finiteSignedFunctional_quotient_eq_fiberMass`
- `finiteSignedFunctional_annihilates_quotient_iff`
- `finiteSignedFiberMass_zero_injective_iff`
- `exists_two_in_fiber_of_balanced_nonzero`
- `twice_card_le_card_of_balanced_nonzero`
- `finiteSignedQuotientState_positive_iff`
- `card_quotient_le_card_positiveOrientation_of_positive`
- `card_quotient_le_card_negativeOrientation_of_negative`
- `orientation_constant_of_normalized_orientedMass_nonneg`

## Gates

- [x] quotient evaluation identity proved
- [x] balanced-fiber equivalence proved
- [x] point-separating obstruction proved
- [x] sharp universal half-capacity bound proved
- [x] quotient positivity criterion proved
- [x] minority-sign confinement capacity proved
- [x] exposed sign-coherence theorem proved
- [ ] product and iterated-cancellation filtration formalized
- [ ] signed exponential-shell asymptotic capstone formalized
- [ ] primary-literature novelty audit completed
- [ ] HT cofinal specialization formalized
- [ ] pure-mathematical paper integration after novelty verdict
