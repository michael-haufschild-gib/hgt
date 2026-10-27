# Arithmetic index descent

Objective: develop the programme described in `docs/reports/review-2710/astra2.md`, including its
arithmetic producers and transfer theorems. Full success is not established by a README or by
repackaging existing RH criteria.

Owner: `formal/GaloisForLFunctions/ArithmeticIndexDescent/`.
Umbrella: `formal/GaloisForLFunctions/ArithmeticIndexDescent.lean`.
Durable log: `logs/arithmetic-index-descent.log`.

## Mathematical scope

1. Completed-form refinement and signed overlap with actual prime, Gamma and pole terms.
2. Charged near-incidence estimates at the Euler source.
3. Finite-Gram limits and growing arithmetic presentations.
4. Rigidity of Gram equality and shared multi-window resources.
5. Quantitative index–transverse-work comparison.
6. Terminal boundary-to-interior estimates and individual-defect exclusion.
7. Finite-field source calibration.

## Initial questions

Determine which of the following advances are already in the corpus, then pursue missing results:

- A quantitative index–energy inequality for every finite actual Weil Gram, stronger than separate
  RH equivalences and with multiplicities/normalizations explicit.
- Stability of finite negative-index budgets under entrywise limits and pullbacks, including
  singular overlap Grams.
- A source estimate for interacting section spaces beyond the currently proved shrinking spaces.

## Evidence and status

The initial foundational README has been written. No new mathematical theorem is claimed yet.
Corpus searches are running; existing local section positivity, polar gluing, spline index laws,
source-work exhaustion and matrix inertia are starting tools.

No missing analytic estimate may be introduced as a hypothesis to obtain the desired endpoint.
General structural theorems must expose their conditions and discharge them in actual arithmetic
applications. No numerical experiments or full builds. Lean checks use `lake --old env lean` from
`formal/`, one foreground process at a time. Existing unrelated workspace changes are preserved.

## Completion conditions

Each contribution has a source-defined statement, paper argument, Lean proof, direct final check,
umbrella import and README explanation. The full programme stays open while its producer,
exhaustion, surplus or extinction questions remain unresolved. Every no-go retains its strongest
positive survivor and formalizes it when ready.

## Contributions under development

- `TheIndexIsPaidByTransverseEnergy.lean`: the distinct transverse energy bounds every finite
  smooth Weil Gram's negative index; the pole plane adds one to the corresponding intersection
  positive index. The module has passed its dependency-producing Lean check; a final direct audit
  remains.
- `TheArithmeticSourcePaysTheIndex.lean`: select one multiplicity copy per support point to compare
  distinct and copied energy. Ordered damping/taper limits turn each finite index witness into a
  finite arithmetic source-work witness. Draft, not yet checked.
- `BoundedSourceWork.lean`: the angular kernel is bounded rowwise by the summable Cauchy height
  weight. Finite off-line support therefore gives finite copied energy; the reverse follows from
  the distinct-energy bound. Draft, not yet checked.
- `TheWorkAndIndexHaveTheSameFiniteStratum.lean`: the fixed spline integer-log index is uniformly
  bounded iff damped source work is eventually bounded. Both are exactly finite off-line support.
  Draft, not yet checked. This is a finiteness classification, not an extinction theorem.
- `SingularRefinement.lean`: for a mixed block `B=A X`, triangular congruence gives all three
  inertia additivity laws without inverting `A`; the Schur complement is independent of the lift
  `X`. Draft, not yet checked. Arithmetic range compatibility and payment remain separate duties.

## Strict energy margin: proposed proof

Let `rho=beta+i gamma` be an off-line Xi support. Its horizontal partner `1-conj(rho)` contributes
one to its angular row. The second zero `1-rho` is distinct from that partner because Xi has no
real zeros. Its contribution is

`(2 beta-1)^2 / ((2 beta-1)^2 + (2 gamma)^2) > 0`.

Thus every off-line angular row exceeds one. A nonempty finite right packet together with its
reflected packet has twice as many members, so its global transverse-energy cost strictly exceeds
its cardinality. Extracting a packet of size equal to a positive finite Weil negative index gives
`index < distinct energy <= copied energy`. Source work should then eventually exceed the index
itself. Conjugation supplies two right zeros when RH fails, hence a strict global gap above two.
There is no claimed uniform extra margin: the displayed surplus can tend to zero.

This proof must be formalized before it is recorded as a theorem. The central arithmetic upper
estimate, signed-overlap payment, exhaustive descent, signed prime surplus, terminal exclusion and
finite-field realization remain open programme tasks.
