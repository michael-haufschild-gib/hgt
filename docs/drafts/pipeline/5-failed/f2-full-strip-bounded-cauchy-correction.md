# F2 — bounded Cauchy correction throughout the strip

- **Stage:** 5-failed
- **Rejected:** The literal arithmetic Cauchy correction defines bounded multiplication on unweighted logarithmic Haar `L²` for every `0<Re s<1/2`.
- **Obstruction [K]:** At `s=1/8+i`, its exact positive frequency order excludes boundedness. No resonance assumption is needed.
- **Positive survivor [K]:** Exact order `1/2−2 Re s`; bounded realization iff `Re s≥1/4`; both directions bounded iff `Re s=1/4`. The bounded operator is constructed, with norm attained at `t=2 Im s`.
- **Paper and Lean:** [Complete proof and audited declarations](../3-formalized/f2-cauchy-reflection-order.md). Final plain Lean check passed; all ten printed endpoints use only standard axioms.
- **Scope:** This retires this fixed-Haar multiplier candidate. It does not exclude a weighted Lewis-space intertwiner. Whether compatibility with the actual averaging operator forces the same boundary is [open here](../1-in-progress/f2-cauchy-compatible-reflection.md).
