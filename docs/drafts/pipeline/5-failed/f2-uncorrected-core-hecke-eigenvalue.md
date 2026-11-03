# Uncorrected Hecke eigenvalue on the PM core

- **Stage:** 5-failed
- **Claim rejected:** Raw four-branch Hecke acts on every resonant PM core with the completed-period eigenvalue `1+2·2^(−2s)`.
- **Exact obstruction:** At `a=1`, every upper resonance has nonzero defect `c(1−4q)`, where `q=2^(−2s)` and `c=2ζ(2s−1)/(2s−1)`. This includes the critical line.
- **Strong positive survivor:** The complete boundary correction is `−2qζ(2s)+c(1−4q)`; completed periods retain their source Hecke law, and actual core coefficients retain the induced Mellin transport.
- **New insight:** Boundary subtraction changes the Hecke equation; source period transport and core coefficient transport must retain this correction.
- **Paper and Lean:** Exact correction and nonvanishing are [formalized and individually audited](../3-formalized/f2-hecke-scattering-boundary-correction.md). The [actual finite-core signed-form limit](../3-formalized/f2-weil-form-as-core-packet-limit.md) is also audited. Corrected F2 remains active.
