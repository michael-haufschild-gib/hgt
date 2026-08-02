# Generic two-local spectral monodromy

- **ID:** generic-two-local-spectral-monodromy
- **Stage:** 2-fully-proven
- **Type:** THEOREM
- **Status:** `[PARTIALLY FORMALIZED]`; exact full common-base symmetric
  monodromy, monodromy relation rigidity, and characteristic-polynomial
  irreducibility over both parameter ring and rational-function field
  complete; real-slice all-order genericity pending
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

1. [partial] Define finite Pauli labels, weight-two star-Ising energy
   functions, and the isolated-edge construction without matrices larger than
   finite types.  Exact diagonal energy and its two-local Boolean
   decomposition are complete; explicit Pauli-matrix embedding remains.
2. [x] Replace finite-hyperplane avoidance by the explicit injective binary
   disagreement code and symmetric energies `+c,-c`.
3. [x] Formalize the exact two-by-two characteristic factor and an explicit
   closed parameter loop.  Lean certifies all eigenvalue lifts, global
   simplicity at every loop point, zero winding and closed continuation for
   every nonselected block, and exactly one endpoint transposition.
4. [x] Prove hypercube connectedness and generation of `Equiv.Perm` by edge
   transpositions.
5. [x] Formalize the full-symmetry linear-relation rigidity and centered trace
   classification.
6. [x] Realize every edge of every finite Boolean cube as an exact closed
   simple-spectrum parameter loop in one universal all-qubit two-local
   polynomial family, including arbitrary coordinate relabeling.
7. [x] Prove the missing global continuation theorem: characteristic roots
   over every continuous finite-matrix simple-spectrum path form a covering
   and every chosen initial root has a continuous global lift.
8. [x] Construct label-controlled common-base anchoring and prove that every
   permutation is realized by an exact closed simple-spectrum loop at one
   fixed diagonal Hamiltonian.
9. [x] Prove that factor-root membership is clopen along every labelled
   simple-spectrum path.  Full symmetric monodromy then proves irreducibility
   of the universal two-local characteristic polynomial over both the full
   parameter ring and its rational-function field.
10. [partial] Capstones pass `#print axioms` with only `propext`,
    `Classical.choice`, and `Quot.sound`; modules are wired into the
    HTGeometry umbrella.  The probability-zero real-slice transfer remains
    before promotion to stage 3.

Lean now certifies the complete local Hamiltonian branch loop, every named
hypercube-edge transposition at one common base, the full symmetric
monodromy group, global simple-spectrum root continuation, trace-only
monodromy-invariant linear relations, and irreducibility over the parameter
ring and rational-function field.  It does not yet certify the real-slice
almost-sure all-order nonresonance conclusion.  This card may not move to
stage 3 or be cited for that conclusion until the remaining transfer closes.

## Log

- 2026-08-01 -- Paper proof completed after corpus-first and immediate
  literature collision audit.  Key construction: isolate every Boolean-cube
  edge with a star-Ising diagonal Hamiltonian; its exact two-level branch loop
  supplies every edge transposition and therefore full symmetric monodromy.
- 2026-08-01 -- Lean module
  `HTGeometry/SpectralMonodromyRelationRigidity.lean` certifies the exact
  swap-defect identity, permutation-invariant relation rigidity, and the
  classification of centered generic-root relations as scalar trace
  relations. The local star-Ising isolation and Galois/branch-loop bridge
  remain to be formalized before stage 3.
- 2026-08-01 -- Lean module
  `HTGeometry/BooleanHypercubeTranspositionLaw.lean` certifies that the
  transpositions along Boolean-hypercube edges generate the full symmetric
  group. This closes the finite group-theoretic generation step, not the
  analytic realization of each edge transposition by a local Hamiltonian.
- 2026-08-01 -- Replaced finite-hyperplane avoidance in Step 1 by an explicit
  binary separation construction and formalized it in
  `HTGeometry/TwoLocalIsolatedEdgeSpectrum.lean`.  For a selected environment,
  its disagreement code satisfies `c < 2^m`; the two distinguished layers
  have energies `c` and `2^m c`.  Their only common energy is the selected
  zero-code edge.  Lean also proves the exact equality classification and an
  onsite-plus-distinguished-star bilinear decomposition, so the construction
  is genuinely two-local.  Foreground compilation passes and the four
  capstones use only `propext`, `Classical.choice`, and `Quot.sound`.  The
  analytic branch-loop frontier is now closed by
  `HTGeometry/OddWindingSheetSwap.lean` and
  `HTGeometry/TwoLocalEdgeMonodromy.lean`: an explicit inverse-branch loop has
  selected radicand `(1/4)e^{2πis}`, selected roots exchange sheets, all
  nonselected radicands stay in the right half-plane with winding zero, and
  cross-block roots never collide.  Lean labels the complete simple spectrum
  continuously and proves that its endpoint action is exactly
  `twoLocalSelectedEdgeSwap`.  The remaining frontier is transport of these
  loops to one common base in the complex discriminant complement, then
  real-slice null-set transfer.
- 2026-08-01 -- Extended the construction from one selected star edge to
  every edge of every finite Boolean cube in
  `HTGeometry/TwoLocalHypercubeCoordinateRelabel.lean` and
  `HTGeometry/TwoLocalUniversalEdgeMonodromy.lean`.  Each edge now has an
  exact closed parameter loop in the same universal all-qubit two-local
  polynomial family, a complete injective root packet, and precisely that
  edge transposition as endpoint permutation.
- 2026-08-01 -- Closed the previously implicit global-continuation gap in
  `HTGeometry/SpectralPathCovering.lean`: the characteristic-root incidence
  space over a continuous simple-spectrum finite-matrix path is a covering of
  the interval, hence every initial root admits a global continuous lift.
  The proof obtains compactness from a uniform Cauchy root bound and local
  triviality from the complex implicit-function theorem.
- 2026-08-01 -- Antagonistic audit rejected the tempting inference from
  simple-spectrum path connectedness to named common-base generators.
  Transport along an uncontrolled connector conjugates a local transposition
  by an unknown permutation; the resulting transposition graph need not be
  connected.  New frontier theorem: construct a controlled deformation from
  each local branch loop to a simple diagonal two-local Hamiltonian, track
  every signed root algebraically, and only then use the diagonal
  discriminant complement, where computational labels are global.
- 2026-08-01 -- Closed common-base anchoring and the first algebraic
  Galois-level consequence.  `HTGeometry/TwoLocalCommonBaseEdgeMonodromy.lean`
  realizes every permutation at one fixed diagonal base.
  `HTGeometry/TwoLocalMonodromyRelationRigidity.lean` proves that only the
  trace direction survives all exact continuations.
  `HTGeometry/TwoLocalCharacteristicIrreducibility.lean` proves a new
  factor-membership transport law: a root cannot switch polynomial factors
  along any labelled simple-spectrum path.  Full symmetric monodromy then
  forces the universal two-local characteristic polynomial to be
  irreducible over both its multivariate parameter ring and its
  rational-function field.  Foreground compilation and axiom audits pass
  with only `propext`, `Classical.choice`, and `Quot.sound`.
