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
- `observerTowerCurrent`, `observerTower_chirality_conservation`, and
  `observerTower_chirality_eq_sum_of_terminal_zero`: exact conservation and terminal-reversal
  localization for arbitrary finite observer towers;
- `exists_observerTowerCurrent_ge_average_of_terminal_zero`: some stage current is at least source
  chirality divided by tower length whenever the nonempty tower has zero terminal chirality;
- `conditionalForwardKL` and `observerFibreChirality_eq_conditionalDifference`: under the exact
  finiteness boundary, the abstract current is the difference of forward and reverse conditional
  KL terms from disintegration;
- `measurableEmbedding_of_measurable_involution`: measurable involutions preserve the full
  information content needed by KL;
- `klChirality_eq_zero_of_reversal`: an involution exchanging two finite laws kills their
  chirality;
- `map_reversal_reverse_of_involution` and `klChirality_eq_zero_of_reversal_left`: the paper's
  single endpoint-exchange equality implies the reverse equality and zero chirality;
- `observerFibreChirality_eq_source_of_reversal` and
  `observerFibreChirality_pos_of_reversal`: reversible observation localizes all source chirality
  in the fibres and strict source chronology forces a positive fibre current;
- `IsKLPairSufficient` and `observerFibreChirality_eq_zero_of_pairSufficient`: preserving both
  directed KL costs is exactly a zero-current sufficient comparison interface;
- `klChirality_eq_zero_of_sufficient_reversal`: sufficient observation transports observed
  reversal back to zero source chirality;
- `klChirality_eq_zero_of_sufficient_reversal_left`: pair sufficiency plus the paper's single
  observed endpoint exchange already kills source chirality;
- `StrictKLChronology`, `SufficientReversalComparison`, and `sufficientReversalSelection`: all
  formation, finiteness, sufficiency, and reversal data are internalized in structures, and the
  capstone unconditionally selects equal parameters.

## Exact paper/Lean boundary

Lean now certifies the arbitrary-length observer-tower sum, terminal-reversal localization, and
quantitative average-current consequence in addition to the measure-theoretic one-stage law, exact
two-stage composition, conditional disintegration bridge, one-sided endpoint-exchange reversal,
and structure-encoded selection capstone. The paper's displayed finite conditional-probability
sum remains represented by the stronger measure-theoretic disintegration theorem rather than by a
second finite-only definition.

The Abelian-zeta positive-jump source supplies a strict KL chronology on paper through the parent
formation-cumulant card. That parent theorem has no exact Lean construction yet. Consequently this
paper card remains in Stage 2: the module proves the route-independent receiver theorem, but does
not replace the source-native likelihood factorization and chronology with an assumption.

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
