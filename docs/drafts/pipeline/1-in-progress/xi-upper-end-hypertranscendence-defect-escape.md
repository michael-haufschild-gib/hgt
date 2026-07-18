# Xi upper-end hypertranscendence by defect escape

- **ID:** xi-upper-end-defect-escape
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** Lean-corpus synthesis: `XiShiftPrimeHypertranscendence`,
  `DifferentialAutomorphismDefectEscape`, `UpperEndDifferentialField`, and
  `DifferentialAlgebraicBaseChange`
- **Statement:** The actual upper-end meromorphic carriers of `xi'/xi` and `xi` are
  hypertranscendental over the genuine rational coordinate field; this should yield the global
  `Hypertranscendental xi` theorem without the `XiFrequencyCollapse` proposition.

## Goal

Turn the already-formalized hypertranscendental `+2` shift defect into hypertranscendence of its
primitive.  This discharges the principal proposition interface left in
`XiHypertranscendenceChain` and closes the value-level prime-source relation back onto the actual
completed function.

## Gates

- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [ ] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3  formalized: Lean theorem, exact leaf checks green, ordinary-axioms audit PASS
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Approach

1. Prove that the upper-end rational coordinate field is exactly the differential field generated
   by the coordinate `z`, and that every rational coordinate gauge is DA over `C`.
2. Embed the entire function `z ↦ xi(-I z)` into the upper-end analytic domain and define its
   logarithmic derivative in the fraction field.
3. Prove the exact field identity: translation by `2I` minus the identity equals the filtered von
   Mangoldt carrier plus the explicit rational correction.
4. The correction is DA.  Hence the translation defect is HT; differential-automorphism defect
   escape makes the logarithmic derivative HT over `C`, and differential-adjoin base change upgrades
   it to `C(z)`.
5. If the xi carrier were DA, its logarithmic derivative would be DA.  Contradiction.  Finally map a
   hypothetical global differential equation for `xi` into the upper-end field.

## No-go closure (mandatory when falsified)

- **Exact killing theorem/mechanism:** Not falsified.
- **Strongest positive survivor:** Pending exact fraction-field identity.
- **New insight:** The classical Ostrowski prime source can discharge the corpus's completed-xi
  frequency-collapse interface through an automorphism defect, with no asymptotic computation.
- **Status:** Internal route audit complete; exact Lean construction in progress.

## Log

- 2026-07-18 — created in 1-in-progress after the filtered-prime carrier theorem passed.
