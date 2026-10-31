# Formal corpus placement

Root [AGENTS.md](../AGENTS.md) and [CLAUDE.md](../CLAUDE.md) govern workflow, search, proof
integrity, comments, and compilation. This guide adds placement only; it does not override them.

## Choose the mathematical owner

Paths below are relative to `formal/GaloisForLFunctions/`. Prefer an existing programme and
its topic subfolder; RH relevance alone does not make `RHTower/` the owner.

| Folder | Contents |
|---|---|
| `RHTower/` | RH/Xi/Weil/Li criteria, explicit formulas, CCM and CHMD infrastructure not owned by a programme below; use topic subfolders |
| `RHTower/Heat/` | New heat-flow, Gaussian transport, heat-zero persistence/counting, collision and energy modules |
| `RHTower/WD/` | New route WD Ward caps, directed source-current estimates and arithmetic collision/extinction arguments |
| `HTGeometry/` | Reusable hypertranscendence, differential algebra, constraint/value-relation geometry and analytic infrastructure; use topic subfolders |
| `HeckeKreinToeplitz/Index/` | Kernel column spaces, finite negative index, isotropic subspaces and rank laws |
| `BiarithmeticGeometry/Affine/` | Rational affine representations, translation unipotence and polynomial coefficients |
| `AdelicKreinGeometry/Haar/` | Haar successors, affine period defects and polynomial corrections |
| `HilbertMetric/` | Source-independent Hilbert/finite-metric, Gaussian-kernel and feature-volume laws |
| `SelbergClass/` | General Selberg-class L-functions, twists and continuation |
| `Hurwitz/`, `U0/`, `Bottcher/` | Their respective theorem programmes |
| `BiScaleUncertainty/` | Log-grid/scale uncertainty, source correlations, packets and observation laws |
| `arithmetic-positivity-theory/` | Exact-source spectral positivity; factorial/Bernoulli test families and mixed-energy estimates |
| `BezoutValuationIncidence/` | Finite-horizon divisor rows, valuation/coprimality incidence and signed sieve energies |
| `TransHorizonIncidenceMechanics/` | Sieve observations beyond cutoff, Fermi traces, damping and receiver transfer |
| `SmoothBernoulliPoleCalibration/` | Higher-order Bernoulli elimination, smooth tapers and even-pole calibration |
| `ArithmeticCriticalityTheory/` | Arithmetic jump operators, ground states, Doob transforms and criticality |
| `ArithmeticIncidencePositivity/` | Prime ratio/product conductances, reflected crossings and shared-surplus allocation |
| `SignChangingScrewGauge/` | Sign-changing collars, screw resonance and gauge compensation |
| `SignedArithmeticEnergyIncidence/` | Signed-form allocation, balance/frustration, completions and adverse-profile laws |
| `ArithmeticContinuationAndCriticalEnergy/` | Damping/parameter continuation, signed work and horizon-uniform energy budgets |
| `ArithmeticCompensationTheory/` | Same-source compensation, prime-comb horizon laws, correctors and origin/tail costs |
| `ScaleSignedIncidenceCriticality/` | Observable resolution limits, sign blindness and cofinal criticality |
| `SquareRootThreshold/` | Zero visibility, aperture/height resolution and square-root/zero-width thresholds |
| `DilutionCrystallizationPincer/` | Dilution, crystal visibility and incommensurability bounds |
| `ArithmeticCastelnuovoSeveri/` | Scaling-surface intersection theory, Hodge index, effectivity and finite-field calibration |
| `ReverseTwistedArcPoleCompression/` | Pole-compression and twisted-arc receiver bridges |
| `goldbach/`, `twin-prime/` | Additive prime-pair problems and their arithmetic bridges |
| `RHProofLab/` | Existing Euler-product/positivity-selector modules; not a general scratch directory |

## File layout

- Research leaves belong inside the owning folder, not directly under `GaloisForLFunctions/`.
  Package-root files are umbrellas, `Core.lean`, and cross-area aggregators.
- Follow the existing import graph. Most programmes use a sibling `<Programme>.lean` umbrella;
  `arithmetic-positivity-theory/` uses `ArithmeticPositivityTheory.lean`;
  `goldbach/` and `twin-prime/` use their own `Main.lean`.
  `MainTheorems.lean` is the cross-area aggregator.
- Put reusable lemmas with their mathematical owner; import them from applications rather than
  copying them or creating a new programme for one bridge.
- Programme folders are not a list of live proof routes. RH status belongs in
  [frontier](../docs/reports/rh-current-frontier-map.md) and
  [killed mechanisms](../docs/reports/rh-killed-routes.md); research notes/gaps belong in
  [pipeline cards](../docs/drafts/pipeline/), not Lean comments.
- Put new heat and WD modules in the subfolders above. Historical modules retain their
  current paths until separately migrated; update imports and umbrella entries when moving a file.
- `QuantumAlg/`, `PNTPlus/`, `QECLean/` are read-only vendors. Consult their `PROVENANCE.md`;
  keep project-owned extensions outside them, and use upstream resyncs for vendor changes.
- Keep `formal/AGENTS.md` and `formal/CLAUDE.md` identical.
