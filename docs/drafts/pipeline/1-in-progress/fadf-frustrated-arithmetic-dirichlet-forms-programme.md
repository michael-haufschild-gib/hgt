# Frustrated Arithmetic Dirichlet Forms (FADF) programme

- **ID:** fadf
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean) programme
- **Source:** docs/reports/review-0411/obstacles-summary.md §2.7 (and §2.8)
- **Statement:** Signed positivity, at exact criticality, of frustrated nonlocal Dirichlet forms with
  arithmetic jumps on intervals: the field asked for in §2.7, with Weil's form on windows as its
  arithmetic instance.

## Goal
Develop the field of §2.7: fix its objects and language, build its tools, answer its eight questions as
theorems (equivalences, classifications, sharp no-gos with positive survivors, or unconditional partial
results), and formalize under `formal/GaloisForLFunctions/FrustratedArithmeticDirichletForms/` with
umbrella `FrustratedArithmeticDirichletForms.lean`.

## Gates
- [x] 0 → 1  README first draft; objects and questions fixed
- [x] 1 → 2  paper proofs of the pillars (module docstrings)
- [x] 2 → 3  pillars formalized (13 modules, each checked with `lake --old env lean`, wired into the umbrella; `#print axioms` of the main theorems: `propext`, `Classical.choice`, `Quot.sound` only)

## Questions (§2.7) and planned answers
| Q | Question | Answer (README §5) |
|---|---|---|
| Q1 | arithmetic part an optimal Hardy weight? | iff RH; all other optimality properties unconditional |
| Q2 | nodal structure past `log ρ`; stability across entries | frustration survives every sign gauge; even locus weight-independent; each entry adds an odd anti-diagonal |
| Q3 | gauge family exact on the line, nonnegative remainder in both sectors | retained-variance theta / shifted gauges, iff RH; signed gauges reverse the even deficit |
| Q4 | collective law on reflection pairs | mirror pairing; orbit correlation for even bumps; stage-uniform ⇔ RH |
| Q5 | trace theory of critical extremals; boundary data | no trace; edge killing; Weil's form cannot read point values; centre pays trivial zeros |
| Q6 | margin transport across entries | stage fibre compact; entry logarithmically soft from both sides; beyond the sliver the edge law, which dies at `E_c = 1` |
| Q7 | global canonical system; stage propagation | contraction law; stage step = interval constraint; continuum system open (B17) |
| Q8 | Euler product as repulsion at near-coincidences | RH ⇔ no heat collision; size cannot repel; input open (B44) |

## Status
Modules (folder `FrustratedArithmeticDirichletForms/`; checked with `lake --old env lean`):
- `TheArithmeticHardyInterval` (Q1): `ℋ(c)` closed convex antitone; `= ℝ` for `2c < log 2`; bounded for
  `2c > log 2`; scaling optimality; no Hardy weight; optimal Hardy term iff RH.
- `FrustrationCannotBeSwitchedAway` (Q2): balance thresholds; frustration in every sign gauge.
- `TheWindowEnergyHasNoTrace` (Q5): regional–edge decomposition; plateau = edge; no point traces.
- `WeilsFormCannotReadPointValues` (Q5): height-one spikes move Weil's form by at most `ε`.
- `SignedThetaGaugesReverseTheEvenDeficit` (Q3 survivor): signed gauge positive on the window with
  negative outside cosh charge.
- `SoftEntryInEveryStageFibre` (Q6): two-sided entry law; real tests decide `𝒜(c)`; summed edge law
  and edge-law certificate; it dies at `E_c = 1`, for `ζ` by `2c = log 2 + 8`.
- `BeyondAFiniteWindowThePrimesPayBySign` (Q6): from a finite window on, one real test forces
  `P_λ < 0` for every `λ ∈ 𝒜(c)`; every size-only certificate dies.
- `TheEdgeLawCrossesOneBetweenLogFiveAndLogSix` (Q6, criterion 6): unique threshold `c*` with
  `E_{c*}(Λ) = 1`, `2c* ∈ (log 5, log 6]`; edge costs continuous across entries.
- `TheEntryConstantIsOne` (Q6): `|λ(n₀)| ≤ √n₀(log(1/δ) + B)`; inner half-length `√n₀η(½log(1/δ) − ¼)`.
- `TheCentreReflectsTheTrivialZeros` (Q5): mode identities; mirror mass ≤ centre killing; sector forms.
- `EachEntryConfinesItsWeight` (Q6/Q7): calibration space convex; entry confinement; stage fibre interval.
- `TheEntryIsLogarithmicallySoft` (Q6): `|λ(n₀)| ≤ √n₀(A log(1/δ) + B)` after entry.
- `TheQuestionsOfTheField`: Q1–Q8 in exact form.

## Open
(see README §7)
