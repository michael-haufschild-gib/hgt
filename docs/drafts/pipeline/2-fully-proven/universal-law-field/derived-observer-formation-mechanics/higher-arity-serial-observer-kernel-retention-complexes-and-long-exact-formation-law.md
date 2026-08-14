# Higher-arity serial observer kernel/retention complexes and long-exact formation law

- **ID:** ULF-DOFM-1
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / HIGHER-ARITY FIELD LAW
- **Programme:** `../../../1-in-progress/universal-law-field/derived-observer-formation-mechanics/field-programme.md`
- **Parents:** ULF-TFIM-1 and ULF-TFIM-2
- **Status:** `[PAPER-PROVED] [DEPENDENCY-CLOSED] [HIGHER ARITY]`
  `[TWO SHORT-EXACT COMPLEXES] [TWO LONG-EXACT SEQUENCES]`
  `[KERNEL ERASURE] [RETENTION COMPARISON] [SERIAL NATURALITY]`
  `[TWO-LEG FIVE-TERM RECOVERY] [NOT RH] [LEAN OPEN: READ-ONLY AUDIT]`
- **Statement:** A finite family of formation legs and two serial observers canonically determine
  an erasure complex and a retention-comparison complex.  Two short exact sequences of augmented
  incidence complexes yield long exact formation-homology laws.  Their two-leg boundary recovers
  the exact old-minus-erased-plus-new charge conservation theorem.

## 1. Ordered formation families

Let `k` be a field, let `I={1,...,m}` be a finite ordered set, and let

\[
 W_i\subset V\qquad(i\in I)
 \tag{HOF.1}
\]

be subspaces.  For a nonempty subset `J subset I`, write

\[
 W_J=\bigcap_{j\in J}W_j.
 \tag{HOF.2}
\]

For a linear observer `L:V->Y`, define its augmented formation complex

\[
 \begin{aligned}
 \mathsf F_L(W)_p
   &=\bigoplus_{|J|=p+1}L(W_J), &&p\ge0,\\
 \mathsf F_L(W)_{-1}
   &=L\left(\sum_{i\in I}W_i\right).
 \end{aligned}
 \tag{HOF.3}
\]

The boundary is the alternating sum of the inclusion maps

\[
 L(W_J)\hookrightarrow L(W_{J\setminus\{j\}}),
 \tag{HOF.4}
\]

and the augmentation in degree zero is addition of the singleton components.

### Lemma 1.1 -- formation is a chain complex

The alternating boundary squares to zero, and the augmentation composed with the degree-zero
boundary is zero.

### Proof

Every codimension-two face occurs twice with opposite signs.  At the augmentation, an element of a
pairwise intersection enters its two singleton legs with opposite signs.  QED.

Define higher observer-formation charges

\[
 \mathsf H_p(L;W):=H_p(\mathsf F_L(W)).
 \tag{HOF.5}
\]

For two legs `W_1=A,W_2=B`, the only possible charge is

\[
 \mathsf H_0(L;A,B)
 =\frac{L(A)\cap L(B)}{L(A\cap B)},
 \tag{HOF.6}
\]

the charge of ULF-TFIM-1.

## 2. Serial observers and three formation complexes

Let

\[
 V\xrightarrow{L}Y\xrightarrow{M}Z
 \tag{HOF.7}
\]

be linear maps and put `K=ker M`.

There are three different formation complexes which must not be conflated.

### 2.1 Upstream formation

\[
 \mathsf F_L(W)_p=\bigoplus_{|J|=p+1}L(W_J).
 \tag{HOF.8}
\]

### 2.2 Composite formation from source intersections

\[
 \mathsf F_{ML}(W)_p=\bigoplus_{|J|=p+1}M L(W_J).
 \tag{HOF.9}
\]

### 2.3 Downstream formation from already observed legs

First form the upstream legs `L(W_i) subset Y`, then take their intersections, then apply `M`:

\[
 \mathsf F_{M\mid L}(W)_p
 =\bigoplus_{|J|=p+1}
 M\left(\bigcap_{j\in J}L(W_j)\right).
 \tag{HOF.10}
\]

The augmentations of `(HOF.9)` and `(HOF.10)` are equal because

\[
 M L\left(\sum_iW_i\right)
 =M\left(\sum_iL(W_i)\right).
 \tag{HOF.11}
\]

Likewise their degree-zero singleton terms are equal.  They can differ only in intersection
degrees `p>=1`.

## 3. Kernel-erasure complex

Define

\[
 \begin{aligned}
 \mathsf K_{M\mid L}(W)_p
  &=\bigoplus_{|J|=p+1}\bigl(K\cap L(W_J)\bigr), &&p\ge0,\\
 \mathsf K_{M\mid L}(W)_{-1}
  &=K\cap L\left(\sum_iW_i\right).
 \end{aligned}
 \tag{HOF.12}
\]

The boundary is inherited from inclusions.  This is a subcomplex of `F_L(W)`.

### Theorem 3.1 -- erasure short exact sequence

Coordinatewise application of `M` gives a short exact sequence of augmented chain complexes

\[
 \boxed{
 0\longrightarrow\mathsf K_{M\mid L}(W)
 \longrightarrow\mathsf F_L(W)
 \xrightarrow{M_\#}\mathsf F_{ML}(W)
 \longrightarrow0.}
 \tag{HOF.13}
\]

### Proof

On the summand `L(W_J)`, the map is the restriction

\[
 L(W_J)\xrightarrow{M}ML(W_J).
\]

It is surjective by definition of the image and has kernel `K cap L(W_J)`.  The same statement
holds in augmentation degree.  The maps commute with all inclusion boundaries because `M` is
linear.  Direct sums preserve the coordinatewise short exact sequences.  QED.

### Corollary 3.2 -- erasure long exact law

There is a natural long exact sequence

\[
 \boxed{
 \cdots\to H_p(\mathsf K_{M\mid L})
 \to\mathsf H_p(L;W)
 \to\mathsf H_p(ML;W)
 \xrightarrow{\partial^{\rm erase}_p}
 H_{p-1}(\mathsf K_{M\mid L})\to\cdots.}
 \tag{HOF.14}
\]

The image of `H_p(K)->H_p(F_L)` is exactly upstream formation charge erased when passing to the
composite observer.  The connecting map records a composite class whose upstream lift fails to be
a cycle by a kernel-valued boundary.

### Proof

Apply the standard homology long-exact-sequence construction to `(HOF.13)`.  Explicitly, lift a
composite cycle to `F_L`; its boundary lies in `K` because its image under `M` is zero.  Changing
the lift changes the resulting kernel cycle by a boundary.  QED.

## 4. Retention-comparison complex

For every `J`,

\[
 L(W_J)\subseteq\bigcap_{j\in J}L(W_j),
 \tag{HOF.15}
\]

and hence

\[
 ML(W_J)\subseteq
 M\left(\bigcap_{j\in J}L(W_j)\right).
 \tag{HOF.16}
\]

These inclusions define a chain monomorphism

\[
 \mathsf F_{ML}(W)\hookrightarrow\mathsf F_{M\mid L}(W).
 \tag{HOF.17}
\]

Define the retention-comparison quotient complex

\[
 \mathsf R_{M\mid L}(W)
 :=\mathsf F_{M\mid L}(W)/\mathsf F_{ML}(W).
 \tag{HOF.18}
\]

Its augmentation and singleton degrees are zero.  In degree `p>=1`,

\[
 \mathsf R_{M\mid L}(W)_p
 =\bigoplus_{|J|=p+1}
 \frac{M(\bigcap_{j\in J}L(W_j))}{ML(W_J)}.
 \tag{HOF.19}
\]

### Theorem 4.1 -- retention short exact sequence

There is a canonical short exact sequence

\[
 \boxed{
 0\longrightarrow\mathsf F_{ML}(W)
 \longrightarrow\mathsf F_{M\mid L}(W)
 \longrightarrow\mathsf R_{M\mid L}(W)
 \longrightarrow0.}
 \tag{HOF.20}
\]

### Proof

The first map is the degreewise inclusion `(HOF.16)`.  Boundaries are induced by subspace
inclusions and therefore preserve these subspaces.  The final complex is the degreewise quotient,
so exactness is definitional.  QED.

### Corollary 4.2 -- retention long exact law

There is a natural long exact sequence

\[
 \boxed{
 \cdots\to\mathsf H_p(ML;W)
 \to\mathsf H_p(M;L(W))
 \to H_p(\mathsf R_{M\mid L})
 \xrightarrow{\partial^{\rm retain}_p}
 \mathsf H_{p-1}(ML;W)\to\cdots.}
 \tag{HOF.21}
\]

Here `H_p(M;L(W))` means the homology of downstream formation from the already observed family.
The comparison complex stores source-intersection information retained inside downstream
intersections but absent from direct composite source intersections.

## 5. Two-leg reduction to the five-term law

Let `I={1,2}`, `W_1=A`, and `W_2=B`.  Set

\[
 S_0=L(A\cap B),
 \qquad S_1=L(A)\cap L(B).
 \tag{HOF.22}
\]

Then `R_{M|L}` is concentrated in degree one and

\[
 \mathsf R_{M\mid L}(A,B)_1=M(S_1)/M(S_0).
 \tag{HOF.23}
\]

The long exact sequences collapse to the following facts.

1. The image of the upstream charge in the composite charge is the retained quotient
   `M(S_1)/M(S_0)`.
2. Its kernel is
   \[
    \frac{\ker M\cap S_1}{\ker M\cap S_0}.
    \tag{HOF.24}
   \]
3. The quotient of composite charge by retained charge is the downstream-created charge
   \[
    \frac{M(L(A))\cap M(L(B))}{M(S_1)}.
    \tag{HOF.25}
   \]

Therefore `(HOF.14)` and `(HOF.21)` splice to

\[
 \boxed{
 0\to
 \frac{\ker M\cap S_1}{\ker M\cap S_0}
 \to\mathsf O_L(A,B)
 \to\mathsf O_{ML}(A,B)
 \to\mathsf O_M(L(A),L(B))
 \to0,}
 \tag{HOF.26}
\]

which is exactly ULF-TFIM-2.

### Proof

For two legs, the degree-one term is the only intersection term.  Both formation complexes are
injective on the left and surjective at augmentation, so their only homology lies in degree zero.
The quotient complex has zero degree-zero and augmentation terms, hence its degree-one vector
space is its homology.  Reading the relevant segment of both long exact sequences gives
`(HOF.23)--(HOF.26)`.  QED.

## 6. Finite-dimensional Euler conservation

Assume finite dimension.  Every short exact sequence of finite chain complexes has additive Euler
characteristic.  Hence

\[
 \boxed{
 \chi(\mathsf F_L)
 =\chi(\mathsf K_{M\mid L})+\chi(\mathsf F_{ML}),}
 \tag{HOF.27}
\]

and

\[
 \boxed{
 \chi(\mathsf F_{M\mid L})
 =\chi(\mathsf F_{ML})+\chi(\mathsf R_{M\mid L}).}
 \tag{HOF.28}
\]

Equivalently, the alternating sums of homology ranks obey the same identities.  The two-leg
dimension budget `old - erased + new` is the first nontrivial edge of these higher Euler laws.

## 7. Naturality and neutral higher lifts

Suppose a commutative diagram of observers and formation-family maps preserves every marked
subspace.  It induces maps on `F`, `K`, and `R`, commutes with the two short exact sequences, and
therefore commutes with both connecting homomorphisms.  Thus `(HOF.14)` and `(HOF.21)` are natural,
not coordinate artifacts.

If `M` is injective on `sum_i L(W_i)`, then:

1. `K_{M|L}=0` in every degree;
2. `M` preserves all intersections of the upstream image subspaces;
3. each degree of `R_{M|L}` is canonically the `M`-transport of the corresponding upstream
   comparison quotient
   \[
   \left(\bigcap_{j\in J}L(W_j)\right)/L(W_J);
   \]
4. `F_L -> F_{ML}` is a chain isomorphism onto its image and all formation-homology groups are
   preserved.

Hence an invertible functional-equation or gauge lift is neutral in every arity, not only for two
legs.

## 8. Positive Hodge realization

Over `R` or `C`, equip every finite chain group with an inner product.  Each homology group in the
two long exact sequences has a harmonic representative

\[
 \ker(d d^*+d^*d).
 \tag{HOF.29}
\]

The long exact maps need not be isometries for arbitrary metrics, but their kernels, images,
dimensions, and zero loci are metric-independent.  Taking harmonic dimensions recovers the Euler
laws `(HOF.27)--(HOF.28)`.  Positivity therefore realizes the higher charges without creating the
exact-sequence structure.

## 9. Hostile scope and countermodels

1. **No monotonicity.** Even in degree zero, a downstream observer may erase old charge or create
   new charge.  ULF-TFIM-2 gives explicit independent examples.
2. **No automatic presentation invariance.** The theorem is natural for a fixed marked family and
   legal maps.  Arbitrary replacement of the family can change its incidence complex.  Dominated
   refinement invariance is a separate theorem, not assumed here.
3. **No automatic source exactness.** Source formation homology can already be nonzero before any
   observer.  The complexes record rather than forbid it.
4. **No scalar completeness.** Euler characteristic can vanish while homology exists in multiple
   degrees.  Full graded charge, not one alternating number, is load-bearing.
5. **No physical action.** Hodge norms are available after metric choice, but the theorem does not
   derive the source action required for cofinal selection.
6. **No RH landing.** No Xi divisor or arithmetic endpoint enters any proof.

## 10. Collision and significance audit

Short exact sequences of complexes, long exact homology sequences, Čech/Mayer--Vietoris
constructions, and exact-functor theory are classical.  Formation-lattice homology also has
parents, including Przytycki--Putyra,
[*Homology of Distributive Lattices*](https://arxiv.org/abs/1111.4772).

The honest status is `[CLASSICAL MACHINERY] [NEW-TO-CORPUS HIGHER COUPLING] [NOVELTY UNVERIFIED]`.
The field-level residue is the specific two-filtration mechanism:

\[
 \text{serial observation}
 \rightsquigarrow
 \begin{cases}
 \text{kernel complex for erased prior law},\\
 \text{comparison quotient for retained prior law},
 \end{cases}
 \rightsquigarrow
 \text{new downstream formation homology}.
\]

This is stronger than stating that observers are nonexact.  It gives the exact groups, connecting
maps, Euler budgets, naturality, and two-leg five-term boundary that every proposed cross-route
comparison must satisfy.

## 11. Research consequence

Conjecture B of the DOFM field programme is now proved in the linear finite-family setting.  The
next gate is not another binary example.  It is one of:

1. dominated-refinement invariance, giving a presentation-stable formation homology;
2. source prolongation, showing HT as unbounded graded formation rank;
3. literal Euler--Gamma--theta realization of `F`, `K`, and `R` before Xi specialization;
4. source-derived action/properness on the resulting coherent higher charge.

## 12. Lean status

The Lean corpus contains chain complexes, homology, submodules, quotients, and long exact sequence
machinery, but the present formation complexes and comparison diagrams are not packaged.  Per the
active goal, this was a read-only audit: no Lean file was written and no build was run.

## Gates

- [x] 0 -> 1: typed higher complexes, serial comparison, and two-leg calibration
- [x] 1 -> 2: both short exact sequences, both long exact sequences, Euler laws, naturality, and
  sharp scope proof
- [ ] 2 -> 3: Lean construction of augmented formation complexes and exact-sequence capstone
- [ ] 3 -> 4: literal arithmetic higher-family realization and source-action theorem

## Log

- 2026-08-14 -- higher-arity serial observer law closed on paper; DOFM Conjecture B proved for
  finite linear formation families.
