# F2 — bounded Cauchy reflection throughout the strip

- **Stage:** 5-failed
- **Rejected:** A bounded conjugate-linear family on unweighted logarithmic Haar `L²`, defined at every `0<Re s<1/2`, satisfying `R_s A_s=A_(s♯)J` for actual normalized Cauchy averaging.
- **Obstruction [K]:** Source compatibility forces the literal correction, without a multiplier assumption. Its positive frequency order at `s=1/8+i` excludes boundedness. No resonance assumption is needed.
- **Positive survivor [K]:** Exact order `1/2−2 Re s`; bounded compatible realization iff `Re s≥1/4`; uniqueness and exact attained norm. The constructed operator exchanges actual PM core columns and is an antiunitary involution on the critical line.
- **Paper and Lean:** [Gamma order and norm](../3-formalized/f2-cauchy-reflection-order.md); [actual source factorization and core reflection](../3-formalized/f2-cauchy-compatible-reflection.md). Both final plain Lean checks passed; printed endpoints use only standard axioms.
- **Scope:** This excludes this fixed-Haar source-compatible family. It does not exclude a weighted Lewis-space transfer intertwiner. Whether one source window already forces the same law is [open here](../1-in-progress/f2-local-cauchy-range-density.md).
