# Theta Hawking backreaction generator endpoint (2026-08-23)

Implemented `formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBackreactionGeneratorEndpoint.lean`; imported by `formal/GaloisForLFunctions/RHTower.lean`.

Primary physics source checked: P. Kumar, I. A. Reyes, J. Wintergerst, *Relativistic dynamics of moving mirrors in CFT2: quantum backreaction and black holes*, arXiv:2310.03483 / Phys. Rev. D 109, 065010 (2024). Its integrated anomalous ray-tracing equation is
`sqrt(f') - (q/2) f''/f' - P_+ = A`, equivalently for `y=log sqrt(f')`,
`exp(y) - q y' - P_+ = A`.

Exact bridge:
- `sourceLogDeriv = (log k)'`.
- positive-ray background velocity `v0=q*thetaCuspLogDecaySlope=-q k'/k > 0` for `q,x>0`.
- rapidity linearization `B eta = v0 eta - q eta' = -q(eta'+(k'/k)eta)`.
- full-density dressing `U eta=k eta` gives `U B U^-1=-i q D`, `D=-i ∂`.
- constant mirror-momentum forcing becomes the literal source/cokernel vector `k`.
- canonical undressed rapidity response is `thetaTwoEndedSourceSolution alpha / k`; it solves the anomaly pencil pointwise for every `alpha`.
- `XiC alpha=0` iff this past-ended response also equals the future-tail response (`ThetaCuspHawkingBackreactionResonance alpha`).
- at resonance, dressed response is the unique element in the closed shifted Hedenmalm derivative domain.
- RH iff all such two-ended anomaly resonance frequencies have zero imaginary part.

Key theorems:
- `thetaCuspHawkingAnomalyLinearization_conjugacy`
- `xiC_eq_zero_iff_thetaCuspHawkingBackreactionResonance`
- `xiC_eq_zero_iff_existsUnique_closedHawkingBackreactionMode`
- `riemannHypothesis_iff_thetaCuspHawkingBackreactionResonances_real`

Verification:
- `lake env lean GaloisForLFunctions/RHTower/ThetaCuspHawkingBackreactionGeneratorEndpoint.lean` passes.
- axiom audit: only `propext`, `Classical.choice`, `Quot.sound`.
- no `sorry`, `admit`, `axiom`, `opaque`, or `unsafe`.

Hostile boundary:
- full-line background is signed. Only x>0 is a future-oriented mirror branch; x<0 is a time-reversed/bifurcate partner coordinate, not one future-directed worldline.
- Kumar–Reyes–Wintergerst explicitly retain radiation-reaction runaway pathology. The theorem is a genuine anomaly generator/resonance identification, but not a proof that physical backreaction is passive/no-runaway.
- remaining open core: derive partner sewing/admissibility or causal passivity from quantum backreaction itself. Do not assume it; that would be RH in disguise.

Prior endpoint: `mem:research/theta_cusp_hawking_partner_instability_endpoint_2026_08_23`.
