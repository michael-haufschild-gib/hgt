# Finite-unitary energy-defect law

- **ID:** `finite-unitary-energy-defect-law`
- **Stage:** 3 -- formalized in Lean 4
- **Type:** theorem / gap-free approximate-centralizer invariant / Brown-frontier support
- **Parent:** `../1-in-progress/energy-matched-eigenframe-source-memory-law.md`
- **Status:** `[LEAN-PROVED] [AXIOM-AUDITED] [NOVELTY UNVERIFIED] [NOT BROWN GROWTH]`
- **Date:** 2026-08-11

## Exact theorem

For every finite Hermitian matrix `H` and unitary `U`, define

\[
 \mathcal E(A)=\operatorname{Re}\operatorname{tr}(A^*A).
\]

Then

\[
 \boxed{
 \mathcal E(HU-UH)
 =2\left(\operatorname{Re}\operatorname{tr}(H^2)
 -\operatorname{Re}\operatorname{tr}(HU^*HU)\right). }
\]

The energy is the entrywise squared Hilbert--Schmidt norm,

\[
 \mathcal E(A)=\sum_{i,j}|A_{ji}|^2,
\]

so it is nonnegative and vanishes exactly when `A=0`. Consequently

\[
 \operatorname{Re}\operatorname{tr}(HU^*HU)
 =\operatorname{Re}\operatorname{tr}(H^2)
 \quad\Longleftrightarrow\quad HU=UH.
\]

If `H` is nonzero, traceless and Hermitian on a `D>=2` dimensional register, the exact Haar
second-moment law then gives the gap-free approximate-centralizer tail

\[
 \boxed{
 \Pr_{U\sim\mathrm{Haar}}
 \left\{\|HU-UH\|_{HS}^2\leq\operatorname{tr}(H^2)\right\}
 \leq {4\over D^2-1}. }
\]

No minimum spectral gap, eigenvalue nondegeneracy, dictionary size, or asymptotic limit occurs.

## Proof

Expand

\[
 (HU-UH)^*(HU-UH)
 =(U^*H-HU^*)(HU-UH).
\]

Unitarity and cyclicity of trace turn the two diagonal terms into `tr(H^2)` and the two cross
terms into `tr(HU^*HU)`. Taking real parts gives the defect identity. Expanding the trace in
matrix coordinates gives the entrywise norm-square formula and its zero classification.

On the displayed commutator event, the defect identity implies

\[
 \operatorname{Re}\operatorname{tr}(HU^*HU)\geq\tfrac12\operatorname{tr}(H^2).
\]

The already formalized exact Haar second moment and Markov inequality give `4/(D^2-1)`.

## Lean realization

Module:
`formal/GaloisForLFunctions/HTGeometry/FiniteUnitaryEnergyDefectLaw.lean`

Headline declarations:

- `finiteMatrixHilbertSchmidtEnergy_eq_sum_normSq`
- `finiteMatrixHilbertSchmidtEnergy_eq_zero_iff`
- `finiteUnitary_commutator_hilbertSchmidtEnergy_eq_autocorrelationDefect`
- `finiteUnitary_full_adjointAutocorrelation_iff_commute`
- `haar_measureReal_commutatorEnergy_le_traceEnergy_le`

Development audit:

- `lake env lean GaloisForLFunctions/HTGeometry/FiniteUnitaryEnergyDefectLaw.lean` passes.
- Module is wired into `GaloisForLFunctions.HTGeometry`.
- `lake build GaloisForLFunctions.HTGeometry.FiniteUnitaryEnergyDefectLaw` passes.
- `#print axioms` on every headline theorem reports only `propext`, `Classical.choice`, and
  `Quot.sound`.

## Hostile frontier audit

This closes one real normalization gap: operator source memory is exactly a Hilbert--Schmidt
commutator defect, rather than a heuristic centralizer proxy. It also gives a literal approximate
tube and a dimension-only Haar false-positive bound.

It does **not** prove Brown--Susskind growth. Static evolution lies in this commutator tube at every
time, so Haar rarity cannot be transferred to an ordinary static-local Hamiltonian ensemble. A
circuit target selected after seeing `H` also invalidates any fixed-target Haar argument. The live
core remains a quenched, selector-aware Bellman escape estimate inside this low-defect sector,
after explicit return and fast-forwardable-carrier removal.

The defect identity itself is standard finite-dimensional operator algebra. External novelty of
the exact composition with the Haar tail has not been established; no novelty claim is made.
