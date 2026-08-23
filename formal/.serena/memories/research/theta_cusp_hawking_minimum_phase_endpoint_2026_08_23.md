# Theta-cusp Hawking minimum-phase endpoint (2026-08-23)

New Lean module: `formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingMinimumPhaseEndpoint.lean`; imported by `formal/GaloisForLFunctions/RHTower.lean`.

## Result

Use causal coordinate `p=-i z` for normalized theta-cusp moving-mirror Born form factor `thetaCuspFourierLaplace(i p)=XiC(i p)`. Each backreaction resonance `alpha` maps to literal causal zero `b=-i alpha`; `Re b=Im alpha`.

For `Im alpha>0`, elementary half-plane inner factor `B_alpha(p)=(p-b)/(p+conj b)` has on physical boundary `p=-i x`:

- exact global phase `polePhase (Re alpha) (Im alpha) x`;
- modulus `1` for every real `x`, hence multiplying theta Born form factor preserves its full particle-number intensity;
- Wigner–Smith phase slope `2 Im(alpha)/(Im(alpha)^2+(x-Re(alpha))^2)>0`;
- at `x=0`, additional clock `2 Im(alpha)/normSq(alpha)>0`.

The bare normalized theta-Born form factor has central derivative zero by XiC evenness. Define `ThetaCuspHawkingMinimumPhaseClockRigid` as zero additional central all-pass clock on every upper causal resonance. Proved `riemannHypothesis_iff_thetaCuspHawkingMinimumPhaseClockRigid` using functional-equation partner `-alpha`.

## Scientific verdict

This is a genuine route-specific observable endpoint/no-go, not a proof producer. Hawking intensity/KMS/passivity cannot detect right-half-plane Blaschke factors. Exact missing datum is source-derived phase/minimum-phase calibration. Open producer: derive central clock rigidity (or stronger canonical minimum-phase factorization) from causal high-frequency-transparent theta mirror/material dynamics without assuming zero-freeness.

## Verification

- `lake env lean GaloisForLFunctions/RHTower/ThetaCuspHawkingMinimumPhaseEndpoint.lean`: clean.
- Target module build succeeded.
- `#print axioms` on six core/capstone theorems: only `propext`, `Classical.choice`, `Quot.sound`.
- No `sorry`, `admit`, `axiom`, `opaque`, `unsafe` in new file.
- `scripts/formal_tools.py lint` still fails only unrelated pre-existing umbrella-reachability errors; new module is reachable.
- Umbrella direct Lean check is blocked by missing unrelated `AnharmonicChebyshevCubicDescentCriterion.olean`; no full build run.