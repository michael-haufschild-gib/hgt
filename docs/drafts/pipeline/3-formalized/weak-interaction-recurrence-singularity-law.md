# Weak-interaction recurrence singularity law

- **ID:** `weak-interaction-recurrence-singularity-law`
- **Stage:** 3-formalized
- **Type:** FINITE QUANTUM RECURRENCE / WEAK JOINT INTERACTION /
  NONCOMMUTING LIMITS / ALL-ORDER COLLISION EXTREMALITY
- **Date:** 2026-07-30
- **Status:** `[PAPER-PROVED] [LEAN-PROVED]`
  `[EXTERNAL PRIORITY AUDIT OPEN] [NATURE SIGNIFICANCE OPEN]`
- **Formal file:**
  `formal/GaloisForLFunctions/HTGeometry/WeakInteractionRecurrenceSingularityLaw.lean`

## Theorem

Let \(E=(E_i)_{i=1}^d\) be any finite real spectrum and let
\(\delta>0\). There is a real spectrum \(E'\) such that:

1. the corresponding diagonal Hamiltonians obey
   \[
     \|H_{E'}-H_E\|\le\delta;
   \]
2. \(E'\) has maximal projective rational rank;
3. for every full-support positive spectral weight and every replica order,
   the long-time survival-fidelity collision mass attains its unavoidable
   permutation floor;
4. the completed relative-phase law is full Haar measure on the
   \((d-1)\)-torus;
5. for every operator-normalized observable \(O\) and every real time \(t\),
   \[
   \left\|
     e^{-itH_{E'}}Oe^{itH_{E'}}
     -
     e^{-itH_E}Oe^{itH_E}
   \right\|
   \le 2|t|\delta\|O\|.
   \]

For any two finite systems with spectra \(A=(A_a)\) and \(B=(B_b)\), apply
the theorem to the uncoupled tensor-sum spectrum
\[
  E_{ab}=A_a+B_b.
\]
The difference \(E'_{ab}-E_{ab}\) is a Hermitian joint interaction diagonal
in the uncoupled product eigenbasis. It may be smaller than any prescribed
positive operator-norm budget.

The uncoupled product does not merely have some recurrence relations. After
choosing one reference level in each factor, it contains the standard
rectangle sector
\[
  E_{ab}+E_{a_0b_0}-E_{ab_0}-E_{a_0b}=0
\]
of exactly
\[
  (d_A-1)(d_B-1)
\]
linearly independent projective characters. The arbitrarily weak coupled
spectrum above erases every member of this sector because it has no
nonzero projective rational relation at all. Hence the theorem proves an
exact product-sized recurrence-constraint loss, not only a change of a
qualitative rank label.

Thus:
\[
\boxed{
\begin{gathered}
\text{arbitrarily weak joint interaction can change completed recurrence}\\
\text{to its maximally independent, all-order-minimal law, while every}\\
\text{bounded-time operator observable remains uniformly close.}
\end{gathered}}
\]

This is an exact noncommutation of limits:
\[
  \lim_{\delta\downarrow0}\lim_{T\to\infty}
  \quad\text{need not equal}\quad
  \lim_{T\to\infty}\lim_{\delta\downarrow0}.
\]
The manuscript must state this through the quantified inequalities and
completed phase laws above, not as an unproved interchange formula.

## Why this expands the previous recurrence papers

- Their recurrence deadlines and rate--distortion targets quantify finite
  return once the phase geometry is fixed.
- Their collision hierarchy gives the scalar long-time laws.
- Their operator-probe normalization controls what finite experiments see.
- Their observer and arbitrary-spectrum results delimit the domain.

The present theorem joins those pieces into a physical singularity:
finite-horizon continuity coexists with maximal completed-time change under
arbitrarily weak coupling. The previous results become measurements of two
different faces of this one limit law.

## Exact formal declarations

- `linearIndependent_maximallyProjectiveEnergy`;
- `exists_maximallyProjectiveEnergy_close`;
- `exists_maximallyProjectiveEnergy_close_fintype`;
- `finiteIndexDiagonalHamiltonian_sub`;
- `finiteIndexDiagonalHamiltonian_norm_sub_le`;
- `finiteIndexDiagonalHamiltonian_isSelfAdjoint`;
- `exists_arbitrarilyWeak_fullRecurrenceCompletion`;
- `exists_arbitrarilyWeak_fullRecurrenceCompletion_fintype`;
- `bipartiteProductEnergy`;
- `bipartiteProductEnergyUnflattened`;
- `rectangleIntegerCharacter`;
- `rectangleIntegerCharacter_balanced`;
- `rectangleIntegerCharacter_ne_zero`;
- `rectangleIntegerCharacter_annihilates_productEnergy`;
- `exists_arbitrarilyWeak_bipartiteInteraction_fullRecurrenceCompletion`;
- `exists_arbitrarilyWeak_bipartitePerturbation_erases_rectangleSector`.

Target compilation passes:

```text
lake env lean GaloisForLFunctions/HTGeometry/WeakInteractionRecurrenceSingularityLaw.lean
```

Axiom audit reports only:

```text
propext, Classical.choice, Quot.sound
```

## External priority attack

Close parents found so far:

1. Anand, Valluri, Davis and Ghose, *Quantum recurrences and the arithmetic
   of Floquet dynamics*, Quantum 10, 2074 (2026), gives an arithmetic
   framework for exact state-independent Floquet recurrences and proves
   that rational parameters do not guarantee them.
2. Kotowski and Oszmaniec, *Tight bounds on recurrence time in closed
   quantum systems*, arXiv:2601.10409v2 (2026), proves deterministic
   recurrence-time bounds, generic random-Hamiltonian saturation, and
   improved noninteracting-particle bounds. It explicitly leaves tight
   recurrence bounds for physical local noncommuting Hamiltonians open.
3. Classical Kronecker--Weyl theory already gives full-torus
   equidistribution from rational independence.
4. Standard Duhamel estimates already give finite-time continuity.

No novelty credit is assigned to any one ingredient. Candidate novelty is
the exact joined singularity for every finite base spectrum and every weak
interaction budget, simultaneous erasure of the
\((d_A-1)(d_B-1)\)-dimensional rectangle sector, full-torus completion, and
all-order collision extremality.

## Hostile limitations

Current theorem is not by itself Nature-ready:

- returned interaction is diagonal in the uncoupled product eigenbasis;
- it is a legitimate bipartite joint interaction but need not be spatially
  local inside either composite subsystem;
- theorem is existential, not a device-feasible construction;
- it does not yet solve the local noncommuting-Hamiltonian open problem
  identified by Kotowski and Oszmaniec;
- dense/full-measure genericity inside a prescribed local coefficient
  family is not yet included;
- infinite-volume and open-system singularities are not asserted.

The Nature upgrade requires the formal nearest-neighbour/local-generator
capstone or a different model-specific physical mechanism of comparable
strength.
