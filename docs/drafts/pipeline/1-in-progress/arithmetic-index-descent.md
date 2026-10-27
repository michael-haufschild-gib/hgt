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
