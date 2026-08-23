# Hawking KMS/Wigner centralizer separation endpoint (2026-08-23)

Created `formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingKMSWignerCentralizerSeparationEndpoint.lean`.

Core results:
- `thetaCuspHawkingTiltedDarkMode_KMSCommutatorIntensity_eq_zero`: every Hermitian finite-KMS commutator reporter vanishes at a tilted dark mode because reflected-horizon relative gap is zero.
- `thetaCuspHawkingTiltedDarkMode_KMSDissipativeIntensity_eq_zero`: energy-weighted finite-KMS dissipation vanishes for every amplitude and inverse temperature.
- `thetaCuspHawkingBackreactionPortDissipation_eq_wignerSmithClockZero`: for every upper resonance,
  `port = thetaSource.mass * normSq(alpha) * physicalEnergy * centralWignerClock`.
- `thetaCuspHawkingTiltedDarkMode_KMSZero_wignerSmith_portWork_pos`: positive-tilt dark mode has zero co-moving KMS dissipation but strictly positive Wigner delay and lab port work.

Interpretation: generic KMS/FDT or Krein passivity cannot force resonance-centralizer rigidity. Co-moving zero gap erases dissipative visibility while lab-frame phase/work defect survives. Remaining RH producer must be theta-specific lab-frame phase/Krein crossing Ward law controlling positive Wigner defect.

Critical hostile findings:
- Raw full theta mirror cannot equal canonical Cayley S-matrix: `no_fullThetaMirror_eq_canonicalCayley_at_all_balanced_frequencies` (nonzero even second jet vs Cayley oddness).
- Full nonlinear all-sector mixing is unconditional; it does not prove RH.
- Moving-mirror FDT literature supports noise/dissipation relation but does not determine all-pass phase: arXiv:1602.02526, arXiv:2306.03813.
- Krein theory says instability requires opposite-signature collision, but generic signature alone does not remove zero-gap centralizers (arXiv:1212.2951).

Verification:
- direct target Lean check passed;
- target-only Lake build passed;
- all five new theorem declarations depend only on `propext`, `Classical.choice`, `Quot.sound`;
- scratch files removed;
- no git used.

Integration:
- import added to `formal/GaloisForLFunctions/RHTower.lean`;
- route row added to `docs/reports/endpoints.md`.

Next strongest candidate: derive exact first-background-coupling velocity of a simple zero of the nonlinear susceptibility. Expected paper formula for branch `gamma(t)` through `alpha=w+ia`:
`gamma'(0) = i * M2(a,w) / XiC'(alpha)`,
where `M2(a,w)=∫ exp(-iwx) (thetaCuspTiltedSource a x)^2 dx`.
Its imaginary part is the concrete sheet-orientation coordinate. Use `HTGeometry.ParametricSpectralBranch` or prove a conditional branch-velocity identity without rebuilding joint holomorphy.