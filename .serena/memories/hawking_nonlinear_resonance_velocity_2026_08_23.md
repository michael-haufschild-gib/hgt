# Exact nonlinear Hawking resonance velocity endpoint (2026-08-23)

Created `formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingNonlinearResonanceVelocityEndpoint.lean` and wired import into `RHTower.lean`; added current-route row to `docs/reports/endpoints.md`.

## Mathematical result
For
[
F_a(\tau,z)=\int_\mathbb R e^{-izx-i\tau k_a(x)}(-i k_a(x))\,dx,
\quad k_a(x)=e^{ax}\Theta(x),
]
the module proves joint complex `C¹` regularity for `|a|<1`, using one local Schwartz majorant for carrier and both partials. At zero coupling:
[
F_a(0,z)=-i\,\Xi_C(z+ia).
]
Define
[
M_2(a,z)=\int e^{-izx}k_a(x)^2\,dx.
]
Exact joint derivative partials are
[
\partial_\tau F_a(0,w)=-M_2(a,w),\qquad
\partial_z F_a(0,w)=-i\Xi_C'(w+ia).
]
Every simple Xi zero `alpha=w+ia` has local exact nonlinear resonance branch `gamma` with
[
\gamma'(0)=i\,M_2(a,w)/\Xi_C'(\alpha).
]
Flagship theorem `thetaCuspHawkingNonlinearResonanceVelocity_classification` is exhaustive and closed: every point is nonresonant, derivative-degenerate, or admits exact branch/velocity. Component laws:
[
\Re\gamma'(0)=-\Im(M_2/\Xi_C'),\quad
\Im\gamma'(0)=\Re(M_2/\Xi_C').
]

## Interpretation
This advances prior divisor persistence to an actual source-faithful first-coupling motion law. It does not prove a sign or RH. Sharp open producer is theta-specific sign/nonvanishing of `Re(M₂/XiC′)`, or a multiple-zero divisor-centroid extension. Central sector velocity is generally purely imaginary, not stationary, so do not claim real-sheet retention at `a=0`.

## Verification
Direct target check passed:
`lake env lean GaloisForLFunctions/RHTower/ThetaCuspHawkingNonlinearResonanceVelocityEndpoint.lean`.
Only this module's olean was emitted for axiom inspection. All 10 new public theorems depend only on `[propext, Classical.choice, Quot.sound]`. No umbrella/full build, no git. Scratch files removed.

## Literature audit
No direct theta/Xi moving-mirror resonance-velocity result found. General inverse-Wronskian derivative pattern is consistent with QNM excitation literature, but theta-specific numerator and formal joint eikonal branch are local research; novelty remains unverified.