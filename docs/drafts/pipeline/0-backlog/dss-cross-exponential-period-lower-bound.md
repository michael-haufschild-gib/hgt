# DSS-cross exponential-period lower bound

- **ID:** dss-cross-exponential-period-lower-bound
- **Stage:** 0-backlog
- **Type:** CONJECTURE
- **Source:** `../../door/00-status.md` rows #18/#27/#75/#103/#124/#152/#165; parent-corpus extraction ticket `../library-done/2026-06-19-professor-extract-exponential-period-frame.md`
- **Statement:** Aim the DSS lower-bound problem at the `s=1` Laurent data `{γ_n}` as conjectural exponential periods beyond the motivic period field, not merely at motivic ζ-values.

## Goal
Extract the missing parent-corpus frame into the pipeline: DSS crosses the Kontsevich-Zagier period / non-period boundary. The `{π, ζ(odd)}` side is motivic/mixed-Tate, while the Stieltjes side `{γ_n}` is conjecturally exponential-period / irregular-singular data. Modulo the standard period conjectures, the DSS lower bound should reduce to algebraic independence of `{γ_n}` over the motivic period field.

## Gates
- [ ] 0 -> 1 in-progress: identify the exact exponential-period category and formulate the target field extension cleanly.
- [ ] 1 -> 2 fully-proven: prove a lower-bound theorem or a no-go/reduction that is independent of unproved period conjectures.
- [ ] 2 -> 3 formalized: formalize any finite algebraic reduction or obstruction lemma that survives without importing the apex conjecture.
- [ ] 3 -> 4 publication-ready: standalone note tying DSS-cross, exponential periods, and the `ω`/F1 seam.

## Approach
- Separate the motivic period block `{π, ζ(odd)}` from the Stieltjes block `{γ_n}` in the DSS reduction.
- Treat `γ_n` and regularization constants such as `log(2π)` and Glaisher-type values as archimedean regularization data on the exponential/non-period side.
- Use the Fresan-Jossen exponential-motives home as the candidate category: irregular singularities plus rapid-decay cohomology, containing Nori motives but also Euler-Gamma/Stieltjes-type periods.
- Rephrase the missing F1 lift as an exponential-motivic Frobenius on the wild/irregular archimedean place.

## Log
- 2026-06-19 - Created from Professor's extraction ticket. This is a pipeline home for the parent-corpus frame: DSS is not only a motivic-period problem; the Stieltjes constants live on the exponential-period side, sharpening `ω`/F1 from "multiplicative Frobenius" to "exponential-motivic / irregular-wild Frobenius."
