# Hawking mass-dilation order blindness no-go (2026-08-24)

Created `formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingMassDilationOrderBlindnessNoGo.lean` and added its import to `formal/GaloisForLFunctions/RHTower.lean`.

Core exact result: for the genuine tilted theta ray `p_M(u)=M p(u/M)`, the complete Davies--Fulling numerator is invariant at comoving frequencies, the Bogoliubov beta coefficient has mass weight `M`, coupling onset order is invariant, and Schwarzian flux has universal weight `M^-2`. Exact Schwarzschild shell duration is `M^3`, hence terminal shell load is proportional to `M_n=2^-n` and is summable for every onset order.

This falsifies the physical weld in `ThetaCuspHawkingEvaporationSingularityOrderSelectionEndpoint.lean`: analytic coupling order `m` is not a mass scaling dimension, so replacing intensity by `kappa^(2m)` double-counts mass dilation. Updated that module header to `[FALSIFIED PHYSICAL WELD]`; its conditional reporter algebra remains valid.

Key theorems:
- `thetaCuspHawkingMassDilatedFullMirrorAmplitude_comoving`
- `thetaCuspHawkingMassDilatedFullMirrorBogoliubovBeta_comoving`
- `thetaCuspHawkingMassDilation_preserves_fullMirrorCouplingOnsetOrder`
- `thetaCuspHawkingMassDilatedSchwarzian_comoving`
- `summable_thetaCuspHawkingMassDilationDyadicShellLoad`
- `thetaCuspHawkingMassDilationFiniteLoad_doesNotForceOrderOne`

Positive survivor: any RH-bearing Hawking producer must break self-similar mass dilation coefficient-faithfully (mass-dependent greybody mixing, horizon memory/nonlocal semiclassical backreaction, or genuine singularity boundary condition). Late/passive Schwarzschild recoil and self-similar evaporation are order-blind.

Verification: direct targeted Lean compile passed; all initial 22 public theorems plus the later exact all-jet ray covariance theorem were checked with `#print axioms` (the changed Schwarzian capstone and final no-go were rechecked) and depend only on `propext`, `Classical.choice`, `Quot.sound`. Global lint reported only six pre-existing unreachable HTGeometry modules. Temporary scratch files and generated oleans removed. No git commands used.