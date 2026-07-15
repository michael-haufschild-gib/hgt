# A scalar parabolic HT tail has at most one holonomy enhancement

- **ID:** `parabolic-tail-single-holonomy-enhancement-law`
- **Stage:** 3-formalized / needs novelty audit
- **Type:** THEOREM (paper) + LEAN-FORMALIZED CRYSTALLOGRAPHIC TOWER LAW
- **Scientific status:** `[PROVED HERE] [FORMALIZED IN LEAN 4] [NOVELTY UNVERIFIED]`
- **Depends on:** `nonautonomous-rational-complete-tail-orbifold-classification`
- **Statement:** After the finite non-parabolic prefix of a nonconstant scalar rational HT tail,
  the Euclidean orbifold signature can change at most once.  Every covering degree factors into a
  finite-holonomy enlargement and a translation-lattice index; after the possible single
  enlargement, all further degree is pure isogeny index.  The tower has a sharp
  protocol-specific current charge in `{1,2,3,4,6}`, hence at most `6`; weight `12` is needed only
  as a single charge chosen uniformly before the protocol is known.

## The theorem

Let

```text
R_i : O_i -> O_(i+1),  i>=N,
```

be the parabolic-orbifold covering tail supplied by the complete scalar classification.  Let
`Gamma_i` be the Euclidean orbifold deck group on the affine universal cover, `Lambda_i` its
translation subgroup, and `H_i=Gamma_i/Lambda_i` its rotational holonomy.  Put

```text
h_i=|H_i|.
```

Then:

1. `h_i` lies in `{1,2,3,4,6}` and

   ```text
   h_i divides h_(i+1).                                      (1)
   ```

2. Compact versus cuspidal type is independent of `i`.

3. The sequence of signatures changes at most once.  Equivalently, there do not exist
   `i<j<k` with both `h_i<h_j` and `h_j<h_k`.

4. For a positive lattice index `ell_i`,

   ```text
   degree(R_i)=(h_(i+1)/h_i) ell_i.                          (2)
   ```

   In particular the holonomy-enlargement factor divides `degree(R_i)`.

5. There are `N_0>=N` and

   ```text
   h_infinity in {1,2,3,4,6}
   ```

   such that `h_i=h_infinity` for every `i>=N_0`.  This `h_infinity` is a tensor charge for
   the entire parabolic tower, `h_i` divides `h_infinity` at every earlier parabolic phase, and
   after `N_0`

   ```text
   degree(R_i)=ell_i.                                        (3)
   ```

Thus the topology of the Euclidean quotient freezes after at most one strict symmetry
enhancement.  Unbounded later degree lives entirely in the translation lattice.

## Proof

Choose universal orbifold covers

```text
p_i : C -> O_i.
```

The covering `R_i` lifts to an affine map `A_i(z)=a_i z+b_i` and gives a finite-index inclusion

```text
A_i Gamma_i A_i^(-1) subset Gamma_(i+1).                    (4)
```

Conjugation by an affine map does not change the linear part of an affine transformation.
Applying the linear-part homomorphism to (4) therefore injects `H_i` into `H_(i+1)`, proving
(1).  A finite-index inclusion of Euclidean crystallographic groups preserves the rank of the
translation subgroup, so a rank-one cuspidal group cannot turn into a rank-two compact group or
conversely.

The six parabolic sphere signatures, with rotational order and translation rank, are

```text
signature          h    rank(Lambda)
(infinity,infinity) 1         1
(2,2,infinity)      2         1
(2,2,2,2)           2         2
(3,3,3)             3         2
(2,4,4)             4         2
(2,3,6)             6         2.                            (5)
```

Inside rank one the only strict divisibility is `1|2`.  Inside rank two the only strict
possibilities are

```text
2|4,  2|6,  3|6.                                            (6)
```

Every target in (6) is terminal in the same divisibility poset.  Hence two strict enlargements
are impossible.  Rotational order together with translation rank uniquely determines the row of
(5), so the complete signature changes at most once.

For (2), take translation subgroups in (4).  The translation subgroup of the left-hand group is
exactly its intersection with `Lambda_(i+1)`.  The index formula for the resulting exact diagram
gives

```text
[Gamma_(i+1):A_i Gamma_i A_i^(-1)]
  =[H_(i+1):H_i]
   [Lambda_(i+1):A_i Lambda_i A_i^(-1)].                    (7)
```

The left side is `degree(R_i)`, the first factor on the right is `h_(i+1)/h_i`, and the second is
`ell_i`.  This proves (2).  The finite divisibility chain stabilizes, proving (3).

Finally, the translation-invariant current `dz` on the universal cover transforms through the
faithful rotational character of order `h_i`.  Since every earlier `h_i` divides `h_infinity`,
the power `(dz)^(h_infinity)` descends at every parabolic phase.  Affine lifts multiply it only by
a nonzero scalar; phasewise rescaling removes those scalars.  Pullback through the arbitrary
finite prefix supplies the claimed fixed-charge HT-tail witness.

## Physical/topological meaning

The finite holonomy is the discrete topology visible to the surviving current.  Rational
coarse-graining can enlarge that symmetry, but only once.  Thereafter no covering degree can be
spent on new cone topology: all of it is translation-lattice index, so position is erased while
the Maurer--Cartan current and its frozen finite charge remain.

This is a static theorem about nested constraints.  It does not construct a time evolution,
Hamiltonian, quantum state, or black-hole model.  Its physically precise content is a one-time
topological phase lock followed by pure lattice coarse-graining.

## Novelty and significance gate

The affine lift of Euclidean orbifold coverings, the six signatures, and the crystallographic
index formula are classical.  The theorem is a new consequence inside the scalar HT-tail
classification only if the literature does not already package nonautonomous parabolic covering
towers this way.  No such source has yet been located, but that negative search is not enough to
promote novelty.

The result strengthens the complete classification by replacing an unspecified varying
parabolic tail with a fixed-signature isogeny tail after at most one change.  It is structurally
useful but does **not** by itself clear the Fields-Medal significance gate.

## RH impact audit

Any future scalar rational coarse-graining protocol for a completed zeta or `L`-function cannot
store RH information in an indefinitely changing cone topology.  Once its nonconstant tail is
parabolic, at most one holonomy enhancement is possible; every later scale is a fixed-signature
isogeny scale and the only persistent differential datum is its finite-charge current field.
No such zeta protocol or RH-sensitive current is constructed, so this is a no-go diagnostic, not
an RH implication.

## Lean status

`formal/GaloisForLFunctions/HTGeometry/ParabolicOrbifoldTwelveCharge.lean` formalizes:

- the rotational order and compact/cuspidal type of all six signatures;
- uniqueness of a signature from those two invariants;
- impossibility of two strict holonomy enlargements;
- composition of phasewise holonomy divisibility;
- eventual holonomy and signature freezing;
- existence of the sharp protocol-specific charge `<=6`, dividing the uniform charge `12`.

`formal/GaloisForLFunctions/HTGeometry/ParabolicCrystallographicIndex.lean` closes the remaining
affine group diagram.  A lifted covering is presented by its conjugated source deck subgroup `K`
inside the target deck group and the normal target translation subgroup `N`; the conjugated source
translation group is then `K ∩ N`.  The module proves:

- `crystallographic_sourceHolonomy_dvd_targetHolonomy`;
- the exact cross-index identity
  `crystallographic_degree_mul_sourceHolonomy_eq_targetHolonomy_mul_latticeIndex`;
- the literal quotient-times-lattice factorization in
  `crystallographic_degree_factorization`;
- the tower-level exclusion of two separated strict enhancements; and
- `parabolicCrystallographicTower_singleEnhancement_indexFactorization`, which assembles phasewise
  factorization, eventual signature/charge freezing, and equality of covering degree with lattice
  index after the freeze.

The affine-lift geometry is explicit input data rather than an axiom: the capstone is universally
quantified over every such deck inclusion.  All group-index consequences and all parabolic tower
conclusions are proved in Lean.  The principal declarations use only `propext`,
`Classical.choice`, and `Quot.sound`.

## Gates

- [x] exact group inclusion and index-factorization proof
- [x] finite signature-poset core formalized in Lean
- [ ] broad orbifold-covering literature audit
- [x] formal affine crystallographic group and index diagram

## Status

`[FORMALIZED IN LEAN 4] [NOVELTY UNVERIFIED]` The complete theorem surface now consists of the
classical affine deck-inclusion datum plus an axiom-free Lean derivation of holonomy divisibility,
the crystallographic degree formula, the single-enhancement law, stable protocol charge, eventual
signature freezing, and pure lattice degree after the freeze.  Only the independent literature
and novelty audit remains open.
