# Pauli-character first-defect selector law

- **Stage:** 3-formalized
- **Status:** `[LEAN-FORMALIZED] [UNCONDITIONAL] [BRIDGE] [NOVELTY UNVERIFIED]`
- **Lean certificate:** `pauli-character-first-defect-selector-law-formalized.md`
- **Parent:** `../1-in-progress/static-local-complexity-law.md`, O4.12z25
- **Formal status:** every numbered claim is closed in Lean, unconditionally, with a clean
  `#print axioms`.  The graded output assembly, the last outstanding item, is
  `invariantSubspace_inf_nonzeroCharacter_finrank_le_shadow`.

## Exact statement

Let `I` be a nonempty finite linearly ordered set of qubit sites and let

\[
  \mathcal P=\{0,X,Y,Z\}\cong\mathbb F_2^2
\]

be the phase-free one-qubit Pauli labels. Write `[p,q]` for their symplectic commutation form: it
vanishes if either label is zero or the labels agree, and equals one for two distinct nonzero
labels. A global Pauli character is a word `delta in P^I`.

On the two-replica operator space let `T_(i,a)` be conjugation by Pauli `a` on site `i` in both
replicas. These are commuting involutions. Their simultaneous character spaces are

\[
  \mathcal X_\delta
   =\{x:T_{i,a}x=(-1)^{[a,\delta_i]}x\text{ for every }i,a\},
  \qquad
  \mathcal X=\bigoplus_{\delta\in\mathcal P^I}\mathcal X_\delta.       \tag{1}
\]

Let `A_(i,p)` be the collective commutator of Pauli `p` at site `i`, summed over the two replicas.
For every nonzero character `delta`, define `i(delta)` to be its first nonzero site. Let `rho` be the
cycle `X -> Y -> Z -> X`, put

\[
  f(\delta)_{i(\delta)}=\rho(\delta_{i(\delta)}),\qquad
  f(\delta)_j=\delta_j\ (j\ne i(\delta)),                              \tag{2}
\]

and let `p(delta)` be the unique nonzero local Pauli satisfying

\[
  f(\delta)=\delta+p(\delta)e_{i(\delta)}.                              \tag{3}
\]

Then:

1. `f` is a permutation of all nonzero Pauli characters;
2. `[p(delta),delta_(i(delta))]=1`;
3. `A_(i(delta),p(delta))` maps `X_delta` into `X_(f(delta))` and its square is exactly `4I` on
   `X_delta`.

Consequently, if a subspace `U` is invariant under every paired-Pauli conjugation and

\[
  U_{\ne0}=U\cap\bigoplus_{\delta\ne0}\mathcal X_\delta,
\]

then

\[
 \boxed{\quad
 \dim\operatorname{span}_{i,p} A_{i,p}U_{\ne0}\ge\dim U_{\ne0}.
 \quad}                                                                 \tag{4}
\]

Only weight-one collective Pauli commutators occur in `(4)`.

## Proof

The paired local conjugations commute: exchanging two distinct one-replica Paulis contributes a
minus sign in each replica, and the two signs cancel. Their local character group has four
characters, indexed by `0,X,Y,Z`; finite character averaging gives `(1)`. If `U` is invariant under
all involutions, every averaging projector preserves `U`, so

\[
  U=\bigoplus_\delta U_\delta,
  \qquad U_\delta=U\cap\mathcal X_\delta.                               \tag{5}
\]

The map `f` preserves the first nonzero site and all later coordinates. On each stratum with fixed
first nonzero site and fixed remaining word it is the three-cycle `rho`; hence it is bijective, with
inverse obtained by `rho^{-1}` at the same site. The two different nonzero local labels
`delta_i` and `rho(delta_i)` anticommute. Their phase-free sum is the third nonzero Pauli
`p(delta)`, proving `[p(delta),delta_i]=1` and `(3)`.

Paired-Pauli covariance gives

\[
  T_{j,a}A_{i,p}T_{j,a}=(-1)^{\mathbf1_{i=j}[a,p]}A_{i,p}.              \tag{6}
\]

Thus `A_(i,p)` translates character `delta` to `delta+p e_i`. The exact two-involution identity for
the Pauli acting on the left and right replicas gives

\[
  A_{i,p}^2x=4x
  \quad\text{whenever}\quad T_{i,p}x=-x.                               \tag{7}
\]

The symplectic condition above is exactly `T_(i(delta),p(delta))x=-x` on `X_delta`. Therefore the
selected map is injective on every `U_delta` and lands in `X_(f(delta))`. Since `f` is injective,
the selected output spaces for distinct `delta` lie in distinct direct-sum grades. Hence

\[
\begin{aligned}
 \dim\operatorname{span}_{i,p}A_{i,p}U_{\ne0}
 &\ge \sum_{\delta\ne0}
    \dim A_{i(\delta),p(\delta)}U_\delta\\
 &=\sum_{\delta\ne0}\dim U_\delta
 =\dim U_{\ne0},
\end{aligned}
\]

which proves `(4)`.

## What this changes

The arbitrary mixed-subspace problem is not structureless. Canonical maximum deficiency plus exact
Pauli covariance forces a character grading, and all nonzero character grades possess an explicit
collision-free weight-one inverse selector. The remaining two-replica Hall obstruction is confined
to the zero Pauli-character grade and to overlap between its edge-generated images and these
nonzero-grade outputs.

The zero Pauli-character grade is larger than the sitewise `SU(2)` singlet algebra: locally it also
contains the two-dimensional anisotropic diagonal-correlation sector. Therefore `(4)` must not be
misstated as the full nonsinglet Hall theorem or as the full O4.12z25 law.

## Hostile audit

- This theorem does not pay for edge images originating in the sitewise singlet quotient.
- Paired-Pauli invariance alone leaves anisotropic zero-character modes; local `SU(2)` or Clifford
  isotypic resolution is still required there.
- Separate injective selectors do not prove mixed Hall when their output grades overlap.
- Higher replica order has a different local commutant and requires a new character/isotypic
  selector theorem.
- No complexity-growth, plateau, recurrence, or anti-concentration statement follows from `(4)`
  alone.

## Next exact theorem

Use visible-kernel recovery rather than demanding a reverse image as large as the complete forward
overlap. Split the canonical obstruction into the sitewise-singlet layer and its local-Casimir
complement. Independent Pauli-character edge outputs define a quotient detector on the singlet
layer. Visible detector rank pays exposed directions; on its kernel every edge image already lies
in the nonsinglet input, so applying the same generators once more produces the injective edge
Casimir recovery in the singlet layer. Exact theorem and proof are in
`visible-kernel-recovery-hall-law.md`. Concrete local-Casimir splitting and quotient-detector
instantiation are the remaining formal gates for two-replica O4.12z25.

## Formal bridge

- `PauliCharacterFirstDefectSelector.lean` proves, on every finite linearly ordered register, that
  first-active-site rotation is an equivalence of nonzero Pauli characters. It constructs the
  selected label, proves its Pauli weight is exactly one, and proves exact anticommutation with the
  source local axis.
- `FinitePauliConjugationLaw.lean` proves that an arbitrary finite Pauli string conjugates every
  other finite Pauli string by the product of its local signs. The proof factors arbitrary products
  of one-qubit matrices; no coordinate enumeration of the global matrix is used.
- `TwoReplicaGlobalPauliHallSymmetryReduction.lean` proves that paired global Pauli strings are
  commuting involutions, every global collective Pauli commutator is covariant by its exact sign,
  every conjugated weight-at-most-`q` generator lies in the original family span, and the canonical
  greatest maximum-defect subspace is fixed by every paired Pauli string.
- `FiniteCommutingInvolutionParityDecomposition.lean` proves that a subspace stable under any finite
  commuting list of involutions is exactly the sum of its recursively resolved simultaneous parity
  pieces, with an exact sum formula for their finranks. The global module instantiates both capstones
  for every finite list of paired Pauli strings acting on the canonical weight-at-most-`q` defect
  subspace.

Targeted compilation passes. Axiom audits of the selector equivalence, exact weight, arbitrary-string
conjugation, paired commutation, covariance, span preservation, canonical invariance, simultaneous
parity decomposition, and its finrank identity contain only `propext`, `Classical.choice`, and
`Quot.sound`.

## Graded output assembly — closed

The Lean capstone `finiteTwoReplicaNonzeroPauliResolvedSubspace_finrank_le_shadow` proves `(4)` for
`⨆_{δ≠0}(U ⊓ X_δ)`.  The card states `(4)` for `U ∩ ⊕_{δ≠0} X_δ`.  These agree exactly when `U` is
graded by the character decomposition — the card's step `(5)`.  That step, and with it the card's
own form of `(4)`, is now proved:
`GaloisForLFunctions.HTGeometry.invariantSubspace_inf_nonzeroCharacter_finrank_le_shadow`.

Five modules, all unconditional and axiom-clean:

- `HTGeometry/SimultaneousParityGrading.lean` — a subspace stable under a finite family of commuting
  involutions is the sum of its simultaneous parity components, indexed by sign patterns.  The
  induction peels one involution at a time and records its sign, so no averaging projector and no
  character orthogonality is used, unlike the paper proof.  Also
  `inf_biSup_eq_biSup_inf_of_graded`: a subspace graded by an independent family meets every partial
  sum gradewise, by the modular law and disjointness of complementary partial sums.
- `HTGeometry/FiniteQubitPauliComplexBasis.lean` — the Pauli strings are a *complex* basis of the
  qubit matrix algebra.  The corpus had only the real Hermitian basis, which cannot see the
  non-Hermitian directions the two-replica space contains.
- `HTGeometry/TwoReplicaPauliCharacterCompleteness.lean` — the character subspaces exhaust the
  two-replica space.  The phase-free labels carry a product, the conjugation sign is multiplicative
  in it, so a Kronecker product of Pauli strings lies in the character subspace of the product
  label; and Kronecker products of Pauli strings span, since a standard basis matrix on a product
  index is a Kronecker product of standard basis matrices.
- `HTGeometry/JointEigenspaceExhaustion.lean` — if an independent family of subspaces exhausts the
  module and each member is a simultaneous eigenspace, an unrealized scalar pattern has no joint
  eigenvector.  A finite induction along partial sums; the operator separating the pattern from the
  leading component's character forces that component down, and independence deletes it.  No
  projector and no direct-sum machinery.
- `HTGeometry/PauliCharacterGradedAssembly.lean` — the assembly.  Character subspaces are joint
  eigenspaces, parity subspaces are joint eigenspaces at `±1` patterns, unrealized patterns vanish,
  hence `U = ⨆_P (U ⊓ X_P)` for invariant `U`, hence
  `U ⊓ (⨆_{P≠0} X_P) = finiteTwoReplicaNonzeroPauliResolvedSubspace U`, hence `(4)` verbatim.

## Formal completion of nonzero channel

`PauliCharacterFirstDefectCovariance.lean` proves distinct global Pauli words have distinct
simultaneous conjugation characters and the complete family of exact character subspaces is
`iSupIndep`. `PauliCharacterFirstDefectHallExpansion.lean` defines the sum of all nonzero character
components contained in an arbitrary subspace and proves
`finiteTwoReplicaNonzeroPauliResolvedSubspace_finrank_le_shadow` for the literal weight-one
collective Pauli family. Targeted elaboration passes. Axiom audit of character injectivity,
independence, and Hall capstone contains only `propext`, `Classical.choice`, and `Quot.sound`.
