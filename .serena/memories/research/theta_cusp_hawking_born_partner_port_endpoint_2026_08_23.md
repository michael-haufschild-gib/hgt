# Theta-cusp Hawking Born/partner-port endpoint — 2026-08-23

## Result
Extended `formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBogoliubovBornEndpoint.lean` with a source-specific two-channel endpoint and corrected prior overclaim.

New exact laws:
- `thetaCuspHawkingPortIntensityDifference_eq_flux`: incoming positive-norm port intensity minus outgoing partner-port intensity equals oriented theta Green flux.
- `thetaCuspHawkingPortIntensities_eq_iff`: partner ports balance iff centered dark frequency is real.
- `thetaCuspHawkingBornDark_port_imbalance_of_nonreal`: hypothetical nonreal Xi zero is simultaneously dark for prescribed-trajectory Born amplitude and imbalanced for compact-source Green ports. Therefore Born zero and trapped theta mode are not automatically one dynamical Hawking channel.
- `ThetaCuspHawkingBornPortConsistent` and `riemannHypothesis_iff_thetaCuspHawkingBornPortConsistent`: RH iff every nonkinematic Born-dark frequency has balanced theta partner ports.

Top module prose now explicitly says source Green identity does not identify a Born zero with moving-mirror QFT normal mode. Missing physical producer is a source-derived Ward/backreaction law identifying prescribed-trajectory Born channel with the theta two-port Green channel.

## Hostile audit
- Ideal exponential-peeling holonomy cannot equal theta Born kernel up to separable gauges: thermal mixed phase curvature is constant/nonzero; theta kernel carries Xi-dependent curvature and zeros.
- KMS/intensity passivity is phase-blind.
- Scalar Hawking canonical relation on real frequencies cannot simply be evaluated at complex Xi zeros.
- Black-hole laser complex modes need trapping/opposite norm; Born transition zeros are not dynamical eigenfrequencies.
- Canonical bosonic completion of an arbitrary Born beta imposes no zero-location constraint. Backreaction/zero-to-pole transmutation is essential.
- “Dark-but-amplifying” becomes honest only after same-channel identification; without it, circular/false.

## Literature
Primary references audited:
- Coutant–Parentani, arXiv:0912.2755: complex bound modes, opposite norm/trapping.
- Coutant–Parentani–Finazzi, arXiv:1108.1821: Bogoliubov phases matter for correlations/laser interference.
- Kumar–Reyes–Wintergerst, arXiv:2310.03483: prescribed trajectories omit quantum backreaction; dynamical mirror backreaction changes horizon endpoint.
- Obadia–Parentani, arXiv:gr-qc/0103061: moving-mirror Bogoliubov scattering structure.

## Verification
- `lake env lean GaloisForLFunctions/RHTower/ThetaCuspHawkingBogoliubovBornEndpoint.lean`: pass.
- Scratch `#print axioms` for port law, mismatch no-go, capstone: only `[propext, Classical.choice, Quot.sound]`.
- Serena diagnostics: none.
- `git diff --check`: pass.
- Target module forbidden declaration scan: clean.
- Global `scripts/formal_tools.py lint` fails only unrelated concurrent unreachable modules: `DeningerDynSysIntegralLift`, `XiReflectionChargeTruePrimeFiniteCountertermEscape`, `JacobiWeylAlternative`, `WeakTwoLocalPauliPerturbationGrowthLaw`.
- Module remains untracked; umbrella import exists in dirty `formal/GaloisForLFunctions/RHTower.lean`.
