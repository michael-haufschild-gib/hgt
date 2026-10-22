# Route-P Gamma-sewn Stokes complex half-plane current

- **ID:** `P-G66`
- **Stage:** `1-in-progress`
- **Type:** complex source-current continuation / exact vertical phase
- **Status:** `[CORPUS-NEW] [PAPER-PROVED] [LEAN DIRECT GREEN] [EXACT MODULE BUILD GREEN] [UMBRELLA-WIRED] [FINAL AUDIT PENDING] [NOT RH]`
- **Parent:** `hedenmalm-theta-route-p-gamma-sewn-stokes-positive-chamber.md`
- **Lean target:**
  `formal/GaloisForLFunctions/RHTower/GammaSewnMobiusApertureStokesComplexHalfPlaneCurrent.lean`

## Goal

Restore complex spectral parameter after P-G65 without losing source control or importing zeta
continuation/divisor data.

## Conjecture P-G66.A: Kummer phase is source-isometric

Multiplication by

```text
exp(-it deningerFreq(m))
```

has modulus one and preserves every height seminorm exactly.

**Verdict: proved and formalized.**

## Conjecture P-G66.B: real Stokes plus phase gives complex Euler current

On each prime-power axis, real Euler coefficient at `sigma` times Kummer phase equals coefficient
at `sigma+it`. Therefore, for every `sigma>0`, physical sewn dual after positive-chamber Stokes and
vertical phase equals complex von Mangoldt current. Same two-step seminorm bound holds.

**Verdict: proved and formalized.**

## New knowledge

Euler current exists source-natively throughout `Re(s)>0`. No zeta analytic continuation, Xi
divisor, or RH premise is used. Divergence below/at `Re(s)=1` belongs to scalar total-mass reader,
not current itself.

## Lean realization

Headline declarations:

- `norm_gammaSewnMobiusApertureStokesKummerPhaseMultiplier`;
- `deningerHeightSeminorm_gammaSewnMobiusApertureStokesKummerPhaseOperator`;
- `primePowerFluxTerm_ofReal_add_imaginary`;
- `gammaSewnMobiusApertureStokesDualFeaturePairing_phase_positiveChamber_eq_complexEuler`;
- `norm_gammaSewnMobiusApertureStokesComplexEulerDualPairing_le`.

## Gates

- [x] norm-one Kummer phase
- [x] exact complex coefficient transport
- [x] complex Euler current on `Re(s)>0`
- [x] continuous two-height-step dual bound
- [x] permanent direct Lean check
- [x] exact module build
- [x] umbrella import wired
- [ ] full umbrella build, lint, and axiom audit
- [ ] positivity-preserving completed singular extension
- [ ] RH capstone

## Honest boundary

P-G66 continues current only on rapid tests. It does not define constant-one scalarization,
completed prime--Gamma passive current, Xi-pole landing, or RH.

