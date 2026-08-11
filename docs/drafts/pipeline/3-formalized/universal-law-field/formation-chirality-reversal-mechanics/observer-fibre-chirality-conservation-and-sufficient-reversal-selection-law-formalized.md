# Observer-fibre chirality conservation and sufficient-reversal selection law — formalized

- **Paper card:**
  `docs/drafts/pipeline/2-fully-proven/universal-law-field/formation-chirality-reversal-mechanics/observer-fibre-chirality-conservation-and-sufficient-reversal-selection-law.md`
- **Lean module:**
  `GaloisForLFunctions.HTGeometry.ConstitutiveObserverFibreChirality`
- **Umbrella:** `GaloisForLFunctions.HTGeometry.UniversalLawField`
- **Status:** [LEAN 4 FORMALIZED] [PAPER/LEAN BOUNDARY EXPLICIT] [NOT RH]

## Certified mechanism

Lean defines directed KL chirality

\[
\chi(P,R)=D(P\Vert R)-D(R\Vert P)
\]

using real parts of mathlib's extended-real `klDiv`, and observer-fibre current

\[
\mathfrak F_q(P,R)=\chi(P,R)-\chi(q_*P,q_*R).
\]

Certified declarations:

- `klChirality_swap`: reversing an ordered law pair negates chirality;
- `klChirality_observer_conservation`: source chirality is observed chirality plus fibre current;
- `observerFibreChirality_comp`: exact additive composition through two deterministic observers;
- `conditionalForwardKL` and `observerFibreChirality_eq_conditionalDifference`: under the exact
  finiteness boundary, the abstract current is the difference of forward and reverse conditional
  KL terms from disintegration;
- `measurableEmbedding_of_measurable_involution`: measurable involutions preserve the full
  information content needed by KL;
- `klChirality_eq_zero_of_reversal`: an involution exchanging two finite laws kills their
  chirality;
- `IsKLPairSufficient` and `observerFibreChirality_eq_zero_of_pairSufficient`: preserving both
  directed KL costs is exactly a zero-current sufficient comparison interface;
- `klChirality_eq_zero_of_sufficient_reversal`: sufficient observation transports observed
  reversal back to zero source chirality;
- `StrictKLChronology`, `SufficientReversalComparison`, and `sufficientReversalSelection`: all
  formation, finiteness, sufficiency, and reversal data are internalized in structures, and the
  capstone unconditionally selects equal parameters.

## Exact paper/Lean boundary

The paper card also spells out the finite conditional-probability formula, the arbitrary-length
observer-tower sum, and the quantitative `max current >= source chirality / n` consequence. Lean
certifies the measure-theoretic one-stage law, exact two-stage composition, conditional
disintegration bridge, and structure-encoded selection capstone. Arbitrary finite-chain notation
and the numerical averaging corollary remain paper-level conveniences; neither is needed for the
selection theorem.

The Abelian-zeta positive-jump source supplies a strict KL chronology on paper. This module does not
yet construct that source family as a `StrictKLChronology`; it proves the route-independent receiver
theorem into which that construction must land.

## Verification

- `lake env lean GaloisForLFunctions/HTGeometry/ConstitutiveObserverFibreChirality.lean` — passed.
- `lake build GaloisForLFunctions.HTGeometry.UniversalLawField` — passed, 11,826 jobs.
- `scripts/formal_tools.py lint` — passed.
- `#print axioms` for conservation, serial composition, conditional difference, reversal, and
  selection — only `propext`, `Classical.choice`, and `Quot.sound`.

## Remaining selection landing

RH is not proved. Required external construction is now sharply typed:

1. realize centered physical displacement as two parameters of a strict source chronology;
2. transport the scalar sufficient formation statistic before zero specialization;
3. prove the physical reflection exchanges its two pushed-forward laws;
4. prove pair sufficiency, equivalently preservation of both directed KL divergences.

Once those fields of `SufficientReversalComparison` are constructed, Lean theorem
`sufficientReversalSelection` returns equality of the two formation parameters with no further
analytic argument.
