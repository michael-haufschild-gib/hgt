# The Ulrich commutator discriminant

- **ID:** `ulrich-commutator-discriminant`
- **Stage:** 1-in-progress
- **Type:** THEOREM / MODULI / ULRICH BUNDLES / QUANTUM HORIZON
- **Scientific status:** `[PAPER PROOF OUTLINE COMPLETE] [LEAN PENDING] [NOVELTY UNVERIFIED]`
- **Depends on:** `waring-quantum-torus-universal-horizon`

## 1. The new moduli object

Fix a concise degree-`d` form `F` on an `n`-dimensional law space `V` over an algebraically closed
characteristic-zero field.  For a positive integer `m`, let `Rep_m(C_F)` be the affine
representation scheme of the Roby generalized Clifford algebra of `F` on `K^m`.

Every point `rho` has an exterior commutator symbol

```text
beta_rho : exterior^2 V -> End(K^m),
beta_rho(u wedge v) = [rho(u),rho(v)].                                (1)
```

Put `r=dim(exterior^2 V)`.  The top exterior map

```text
exterior^r(beta_rho) : det(exterior^2 V) -> exterior^r End(K^m)       (2)
```

varies regularly with `rho`.  Define the **commutator discriminant**

```text
Delta_comm(F,m) = { rho : exterior^r(beta_rho)=0 }.                   (3)
```

It is the locus where at least one oriented two-plane of laws becomes invisible to the internal
quantum symbol.

## 2. The theorem

1. `Delta_comm(F,m)` is a Zariski-closed, conjugation-invariant determinantal subscheme of
   `Rep_m(C_F)`.
2. Its complement is exactly the locus where `beta_rho` is injective.
3. For the dimension `m` produced by any spanning Waring quantum-torus representation,
   `Delta_comm(F,m)` is proper.  Hence the maximal-commutator locus is nonempty and Zariski open.
4. The general principal-symbol kernel theorem carries this open locus to shift-separable rational
   differential-field laws with exact dependence horizon `Z(F)` and injective exterior
   derivation-commutator symbol.

Under the Clifford/Ulrich correspondence, `(3)` defines a conjugation-invariant closed substack of
the corresponding Ulrich moduli stack on the cyclic cover `X_F : w^d=F`.  At least one component
has a nonempty open complement.

## 3. Proof

Choose bases of `V` and `K^m`.  A representation is a tuple of `n` matrices satisfying the finite
polarized degree-`d` Roby relations.  The entries of each commutator are quadratic polynomials in
the matrix entries.  A matrix for `(1)` therefore has polynomial entries on `Rep_m(C_F)`.

The condition `rank(beta_rho)<r` is the common zero locus of its `r` by `r` minors, proving
closedness.  Simultaneous conjugation acts on the codomain `End(K^m)` and preserves rank, so the
locus is invariant.  The Waring quantum-torus theorem supplies a representation at which
`beta_rho` is injective, so at least one top minor is not the zero regular function.  This proves
properness and nonempty openness.

The differential-field statement is not an analogy: the Lean-targeted principal-symbol theorem
proves equality of the internal and differential-field commutator kernels.

## 4. Scientific significance

The scalar horizon `F=0` is constant across the entire representation space.  What changes is the
antisymmetric law information retained by matter.  Thus `Delta_comm` is a second phase boundary
living over one classical holographic surface:

- outside it, every oriented law plane is observable through a nonzero commutator channel;
- on it, one or more channels collapse;
- deeper rank strata measure the amount of collapsed pretemporal information.

This turns the many-worlds language into a precise moduli stratification.  The worlds are Ulrich
bundles; the common classical surface is `Z(F)`; the discriminant records which worlds fail to
distinguish which pairwise laws.

The natural next invariant is the cycle class, degree, and singularity structure of
`Delta_comm(F,m)` and its descent to stable Ulrich moduli.  Those data can vary with `F` even though
generic existence of a maximal-rank representation does not.

## 5. Novelty and parent gate

Known parent ingredients are determinantal rank loci, representation schemes, generalized
Clifford representations, and Ulrich moduli.  The 1994 polynomial-linearization literature already
contains the root-of-unity matrix constructions that make the Waring point possible.

Targeted searches found no definition or theorem for the commutator-rank determinantal
stratification of generalized-Clifford/Ulrich moduli, and no link to exact varying-derivation
hypertranscendence horizons.  This is not a priority certificate.  Equivalent constructions must
still be checked in representation-variety, PI-algebra, and Ulrich Brill--Noether literature.

## 6. Physical and RH gates

The proposed physical statement is conditional but precise: if pretemporal law constraints are
modeled by `C_F`-matter, loss of pairwise quantum distinguishability is algebraic and occurs on
`Delta_comm`, not on the classical horizon itself.  A QFT interpretation still requires locality,
a star/Krein structure, states, and analytic control.

For RH, generic maximal rank is nonselective and therefore not evidence.  A distinguished
arithmetic Clifford/Ulrich point and its location relative to the commutator discriminant could be
source data; no such point is currently known.

## 7. Lean route

1. Finish the principal-symbol kernel theorem.
2. Formalize the spanning Waring quantum-torus representation.
3. For finite free law and state spaces, define the coordinate commutator matrix.
4. Prove injectivity is equivalent to nonvanishing of a top exterior minor.
5. Formalize the polynomial dependence and determinantal closed-locus statement.
6. Instantiate nonemptiness with the Waring representation.
