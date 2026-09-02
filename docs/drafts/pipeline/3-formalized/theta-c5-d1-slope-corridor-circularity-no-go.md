# Theta C5--D1 slope corridor circularity no-go

- **Stage:** 3-formalized
- **RH chain:** corridor → TCD `D1` → theta incidence → Weil positivity → RH.
- **Result:** For every actual source point `u>0`, corridor membership is exactly `(C5 slope > 0) ∧ (native D1 > 0)`.
- **Proof:** `R₇=A²D1+LΩ′`; `A>0`, hence `LΩ′<R₇ ↔ 0<A²D1 ↔ 0<D1`.
- **Verdict:** `CIRCULAR`; corridor supplies no independent TCD reduction.
- **Positive survivor:** exact pointwise/global classification. Any shared producer must control a source invariant not equivalent to native D1.
- **Lean:** `ThetaCuspExactCompletedC5D1SlopeCorridorCircularityNoGo`; targeted build passed; axioms only `propext`, `Classical.choice`, `Quot.sound`.

