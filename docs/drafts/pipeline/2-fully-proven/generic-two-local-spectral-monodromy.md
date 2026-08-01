# Generic two-local spectral monodromy

- **ID:** generic-two-local-spectral-monodromy
- **Stage:** 2-fully-proven
- **Type:** THEOREM
- **Status:** `[PROVED HERE]`; Lean formalization pending
- **Parent:** `../1-in-progress/static-local-complexity-law.md`, obligation O2

## Statement

Let `n >= 2`, `D = 2^n`, and let `V_(n,2)` be the complex vector space spanned
by all nonidentity Pauli strings on `n` qubits of weight at most two.  Over the
simple-spectrum locus, the roots of

\[
  det(lambda I-H), \qquad H\in V_(n,2),
\]

form a `D`-sheeted analytic cover.  Its monodromy group is the full symmetric
group `S_D`.

Consequently, on the real Hermitian slice, any probability law having a density
with respect to Lebesgue measure has, almost surely,

1. simple spectrum; and
2. no rational linear relation among the eigenvalues other than the trace
   relation.

In particular, for every full-density fixed-`q` Pauli ensemble with `q >= 2`,
the `D-1` projective frequencies

\[
  E_1-E_D,\ldots,E_(D-1)-E_D
\]

are rationally independent almost surely.

The conclusion is finite-size and unconditional.  It does not assume chaos,
ETH, random-matrix eigenvectors, a thermodynamic limit, or a complexity-class
separation.

## Proof

### 1. Isolate any hypercube edge with a two-local diagonal Hamiltonian

Fix a qubit `i`.  Write a computational basis label as `(s,z)`, where
`s in {+1,-1}` is the `Z_i` eigenvalue and
`z in {+1,-1}^(n-1)` records the other qubits.  Fix one label `z_0`.

Choose affine functions of the remaining spins

\[
  g(z)=g_0+\sum_(j ne i) a_j z_j,
  \qquad
  h(z)=h_0+\sum_(j ne i) b_j z_j
\]

such that

\[
  h(z_0)=0,\qquad h(z)\ne0\quad(z\ne z_0).
\]

An explicit nonempty choice region is obtained from

\[
  h(z)=\sum_(j ne i)b_j(1-z_j(z_0)_j),\qquad b_j>0.
\]

Now set

\[
  H_0=g(Z_\widehat{i})+Z_i h(Z_\widehat{i}),
\]

and subtract its scalar trace part.  This is two-local: `g` contains only
one-body `Z_j` terms, while `Z_i h` contains only `Z_i` and `Z_i Z_j` terms.
Its computational-basis energies are

\[
  e_(s,z)=g(z)+s h(z).
\]

The two states `(+1,z_0)` and `(-1,z_0)` have the common energy `g(z_0)`.
For fixed admissible `h`, every other unwanted equality between two energies
is a proper affine hyperplane in the coefficients of `g`: if the two labels
have different `z`, their evaluation functionals on affine `g` differ; if
they have the same `z` and opposite `s`, their energy difference is
`2h(z) ne 0`.  A finite union of proper hyperplanes cannot fill coefficient
space.  We may therefore choose `g` so that the displayed pair is the only
degeneracy and its common energy differs from every other energy.

This construction works for every edge of the Boolean hypercube: choose `i`
as the flipped coordinate and `z_0` as the common remaining label.

### 2. The isolated double root supplies its transposition

Add the two-local perturbation

\[
  w Z_i+uX_i.
\]

The Hamiltonian remains block diagonal in `z`.  On the distinguished
two-dimensional block its characteristic polynomial is exactly

\[
  (lambda-g(z_0))^2-(w^2+u^2).
\]

Fix a sufficiently small nonzero complex `u`.  A small loop of `w` around one
of the simple branch points `w=iu` or `w=-iu` changes the sign of
`sqrt(w^2+u^2)` and therefore exchanges precisely the two distinguished
eigenvalues.  Because the original double level was isolated, the loop can be
chosen so small that all other eigenvalues stay simple and separated.  Thus
the spectral monodromy contains the transposition of the two roots labelled
by the chosen hypercube edge.

To compare different edge constructions at one base point, use a generic
simple diagonal two-local Hamiltonian as base.  Complex diagonal coefficient
space minus its finitely many level-equality hyperplanes is path connected.
Along that diagonal complement the computational labels are global linear
root labels.  Hence the local loop above transports back to the transposition
of the same two computational labels at the common base, with no unknown
relabeling.

### 3. Hypercube transpositions give full symmetric monodromy

Step 2 gives the transposition associated with every edge of the `n`-cube.
For any connected graph, its edge transpositions generate the full symmetric
group on its vertices: along a path from `x` to `y`, conjugating successive
edge transpositions produces the transposition `(x y)`, and all
transpositions generate the symmetric group.  The Boolean hypercube is
connected.  The monodromy group is therefore `S_D`.

### 4. Full monodromy removes all universal linear resonances

Label the simple roots locally by `lambda_1,...,lambda_D`.  Suppose a constant
coefficient relation

\[
  \sum_j c_j lambda_j=0
\]

held identically.  Analytic continuation around a monodromy loop preserves an
identity.  Since monodromy contains every transposition `(a b)`, subtracting
the continued relation from the original gives

\[
  (c_a-c_b)(lambda_a-lambda_b)=0.
\]

The roots are distinct on the covering locus, so `c_a=c_b` for all `a,b`.
Thus every universal constant-coefficient relation is a scalar multiple of
the trace relation.  Pauli Hamiltonians here are traceless, so that relation
is exactly `sum_j lambda_j=0`.

### 5. Proper analytic relations have probability zero

The discriminant is a nonzero polynomial in the Pauli coefficients because
Step 1 also exhibits simple spectra.  Its real zero set has Lebesgue measure
zero.

Fix a nonconstant integer vector `m in Z^D`.  Step 4 says that the locally
analytic function `sum_j m_j E_j` is not identically zero.  Its zero set on
each simple-spectrum chart has Lebesgue measure zero.  A countable chart cover
shows the same globally.  Taking the countable union over integer vectors
leaves a null set.

A projective relation

\[
  \sum_(j<D) k_j(E_j-E_D)=0
\]

is the eigenvalue relation with coefficient vector

\[
  (k_1,\ldots,k_(D-1),-\sum_(j<D)k_j),
\]

whose entries sum to zero.  It is constant only when every `k_j=0`.
Therefore the projective frequencies are rationally independent almost
surely.  The same conclusion holds for every `q >= 2` full-density ensemble,
because the two-local coefficient slice already makes each forbidden
relation a nonzero analytic function.

## What this proves for the master programme

Combined with the existing deterministic finite-spectral Haar theorem, this
result proves that a full-density fixed-`q` Pauli Hamiltonian has maximal
projective temporal rank `D-1` almost surely.  Applied to the Choi trajectory

\[
  (e^(-itH) tensor I)|Phi_D>
    =D^(-1/2)\sum_j e^(-itE_j)|E_j>tensor|conj(E_j)>,
\]

it also supplies exactly uniform spectral weights without any eigenvector
delocalization hypothesis.  Hence spectral-torus Haar occupation and
recurrence can be developed independently of ETH.

It does **not** prove circuit-complexity growth.  In particular it does not
exclude global shortcuts in complexity geometry; that remains O4 of the
parent card.

## Novelty audit

Initial exact-title/concept searches found literature on generic spectral
nonresonance, Hamiltonian monodromy in unrelated integrable/non-Hermitian
settings, and generic polynomial Galois groups, but no theorem identifying the
generic fixed-two-local Pauli characteristic-polynomial monodromy as
`S_(2^n)` or deriving maximal projective temporal rank from hypercube-edge
branch loops.  This is an initial clean result, not a final publication claim;
the paper still requires a citation-graph and expert collision audit.

## Formalization plan

1. Define finite Pauli labels, weight-two star-Ising energy functions, and the
   isolated-edge construction without matrices larger than finite types.
2. Prove finite-hyperplane avoidance algebraically, without numerical search.
3. Formalize the exact two-by-two characteristic factor and root exchange in
   a polynomial/Galois formulation.
4. Prove hypercube connectedness and generation of `Equiv.Perm` by edge
   transpositions.
5. Formalize the full-symmetry linear-relation rigidity and projective
   rational-independence corollary.
6. Audit `#print axioms`; wire the resulting module into the HTGeometry
   umbrella before any paper claim is promoted.

No Lean theorem currently certifies this card.  It may not move to stage 3 or
be cited in the paper until that formalization is complete.

## Log

- 2026-08-01 -- Paper proof completed after corpus-first and immediate
  literature collision audit.  Key construction: isolate every Boolean-cube
  edge with a star-Ising diagonal Hamiltonian; its exact two-level branch loop
  supplies every edge transposition and therefore full symmetric monodromy.
