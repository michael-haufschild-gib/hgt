# Theta-cusp Hawking tilted backreaction gauge endpoint (2026-08-23)

New module: `formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingTiltedBackreactionGaugeEndpoint.lean`.

Mathematical delta:
- `z(a,w)=w+a i` is both tilted-mirror Born spectral point and base theta backreaction resonance coordinate.
- Reflected source `k_{-a}` removes the imaginary shift from the anomaly connection: its real-frequency pencil at `w` equals the base pencil at `w+a i`.
- Density tilt cancels on undressing, so rapidity response is gauge invariant.
- Exact optical/backreaction weld: `XiC(w+a i)=0` iff the reflected tilted anomaly response is two-ended.
- Define horizon-relative charge `c_a(r)=c_lab(r)-a`. For every tilted dark mode, `c_a=0`.
- Laboratory port dissipation splits into relative dissipation plus modular work; at a dark mode it is exactly `2*M*a*E`.
- Therefore co-moving/KMS passivity is automatically saturated and cannot exclude off-line zeros.
- New RH endpoint: `ThetaCuspHawkingTiltedResonanceCentralizerRigid`, absence of nonzero-tilt source-coupled two-ended zero modes. Proved equivalent to RH.

Hostile qualification:
- Do not claim full KMS algebra has trivial centralizer; generic KMS centralizers contain stationary/conserved observables.
- Needed producer is strict mixing/triviality only in coefficient-faithful source-coupled one-particle resonance sector.
- Charged/independent conjugate sectors remain a known loophole; generic KMS/passivity does not prove endpoint.

Validation:
- Direct Lean passed.
- Forbidden-token scan clean.
- `#print axioms` for gauge, weld, charge/work, and RH endpoint: only `propext`, `Classical.choice`, `Quot.sound`.
- Umbrella import added at `formal/GaloisForLFunctions/RHTower.lean`.

Primary-physics grounding:
- Hawking flux for charged/rotating horizons naturally includes chemical-potential/horizon-generator shifts; use as analogy only, not identification.
- Next task: derive source-faithful resonance-sector mixing from an actual Hawking KMS/scattering dilation, or prove it impossible.