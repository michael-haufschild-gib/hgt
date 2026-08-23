# Theta-cusp Hawking backreaction passivity endpoint (2026-08-23)

New Lean module: `formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBackreactionPassivityEndpoint.lean`; imported by `formal/GaloisForLFunctions/RHTower.lean` after generator endpoint.

## Exact new closure
For a literal two-ended anomaly resonance `alpha`, define compact divisor mode `g_alpha = Q F_alpha` and normalized closed physical state `u_alpha = (i alpha)^-1 g_alpha`. Since `F_alpha = -alpha U_alpha` and density-dressed rapidity response is `i U_alpha`, quantile pullback of `u_alpha` is a.e. exactly the physical response. This closes prior gap between conformal-anomaly response and compact Green/Krein mode.

The same state obeys fixed compact Green eigenrelation `K u_alpha = -alpha^-1 u_alpha`.

Define positive physical energy `E_phys = normSq((i alpha)^-1) thetaRootEnergy(alpha)` and boundary port dissipation `J = Re <R2 u_alpha,u_alpha>`. Proved:
- `J = ||in||^2 - ||out||^2`
- `J = 2 thetaSource.mass Im(alpha) E_phys`
- `E_phys > 0`
- `J >= 0 iff Im(alpha) >= 0`
- `J >= 0 iff ||out|| <= ||in||`.

Xi evenness gives reflected resonance `-alpha`. Therefore restricted passivity on every two-ended anomaly resonance forces both `Im(alpha)>=0` and `-Im(alpha)>=0`; hence all resonance frequencies real. Formal endpoint:
`riemannHypothesis_iff_thetaCuspHawkingBackreactionResonancePassive`.

## Literature/physical audit
Jaekel–Reynaud, arXiv:quant-ph/0101080: perfect mirror anomaly/radiation-reaction law has runaways. Causal stability/passivity requires partially transmitting high-frequency-transparent mirror and applies to full mirror+radiation impedance, not radiation susceptibility alone. Butera arXiv:2306.03813 and Wu–Lee arXiv:quant-ph/0501127 support nonlocal dissipation/noise and FDT in microscopic/open-system treatments.

Do not claim passivity is proved by perfect-mirror anomaly. Remaining producer: construct causal high-frequency-transparent mirror/material dilation from theta source and prove its physical impedance induces restricted port passivity above without assuming RH.

## Verification
- `lake env lean GaloisForLFunctions/RHTower/ThetaCuspHawkingBackreactionPassivityEndpoint.lean`: clean.
- Axiom audit for physical/compact representation, dissipation law, and RH endpoint: only `propext`, `Classical.choice`, `Quot.sound`.
- No `sorry`, `admit`, `axiom`, `opaque`, `unsafe` in new file.
- Repository-wide `scripts/formal_tools.py lint` currently fails only on 13 unrelated pre-existing umbrella reachability errors; new module is reachable and produced no lint finding.
