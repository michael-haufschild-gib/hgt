# Theta-cusp Hawking tilted-mirror optical theorem endpoint (2026-08-23)

Added `formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingTiltedMirrorOpticalTheoremEndpoint.lean` and umbrella import.

Unconditional result: for each real tilt `a` with `|a| < 1`, `k_a(x)=exp(a*x) thetaCuspFullSource(x)` is real Schwartz data and admits an explicit open safe-coupling interval of strictly increasing/timelike ray-tracing maps. Its real-frequency Born numerator is exactly `2 i u v XiC(u+v+a i)`.

Exact normalized shell law:
`E_a(w)=w^4 normSq(XiC(w+a i))/(48*pi^2)`.

Plancherel for the tilted source second derivative and Schwarz reality/evenness give:
`integral_(0,inf) w^4 normSq(XiC(w+a i)) dw = pi * integral_R |k_a''|^2 dx`.
Hence total right Born pair energy equals `(1/(48*pi))*integral_R |k_a''|^2`, the quadratic Davies--Fulling Schwarzian backreaction energy of the same tilted mirror.

Also proved exact equivalence `RiemannHypothesis ↔ ThetaCuspHawkingTiltedMirrorsDarkFree`, where dark-free means every nonzero real tilt has no real zero of the de-embedded pair carrier.

Hostile audit: generic timelikeness/optical theorem cannot prove dark-free. Positive Schwartz sources can have off-real Fourier--Laplace zeros while obeying same physical kinematics and energy balance. Open core is theta-specific reflected-pair (`k_a,k_-a`) no-dark-mode rigidity; CCR/KMS/QEI/passivity alone are insufficient.

Verification: direct `lake env lean` passed; target forbidden-token scan clean; axiom audit for main theorems reports only `[propext, Classical.choice, Quot.sound]`.