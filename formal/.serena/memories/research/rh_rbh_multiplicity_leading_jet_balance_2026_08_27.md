# RBH multiplicity-leading fixed-aperture balance (2026-08-27)

Formalized `formal/GaloisForLFunctions/RHTower/ReflectedBiHeatMultiplicityLeadingJetBalance.lean`, wired umbrella.

For each actual `rho : XiDivisorSupport`, with exact multiplicity `m`, common leading coefficient `A_rho=(1/2) Lambda^(m)(rho)` is nonzero. At aperture 2:
`|L_rho|=|A_rho| 2^((Re rho-1)/2)` and `|R_rho|=|A_rho| 2^(-Re rho/2)`.
Thus top-jet norms are equal iff `Re rho=1/2`; universal equality over Xi support is exactly RH. This removes multiplicity and unknown coefficient from RBH receiver. Remaining producer is source-first derivation of fixed-aperture equality.

Direct Lean passed; targeted build 11454/11454; axioms only propext/Classical.choice/Quot.sound. Stage-3 card `docs/drafts/pipeline/3-formalized/reflected-bi-heat-multiplicity-leading-jet-balance.md`.