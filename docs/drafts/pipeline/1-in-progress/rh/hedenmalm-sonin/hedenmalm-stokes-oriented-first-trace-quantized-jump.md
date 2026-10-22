# Hedenmalm--Stokes oriented first-trace quantized jump

- **Label:** `P-G143`
- **Stage:** 1-in-progress
- **Type:** THEOREM / ORIENTED RESIDUE CLASSIFICATION / POLAR CANCELLATION WALL
- **Parents:** `P-G139`, `P-G141`, `P-G142`,
  `HedenmalmThetaPhysicalEndpointPrimeHardyGreenScaling`,
  `PrimeArchPolarSeamRemoval`
- **Lean:**
  `formal/GaloisForLFunctions/RHTower/Hedenmalm/HedenmalmStokesOrientedFirstTraceQuantizedJump.lean`
- **Status:** `[PROVED IN LEAN] [QUANTIZED JUMP] [NOT RH]`

## Result

Let

```text
j_p(t) = 8 t log(p) p^(-1-2|t|),
J(t)   = sum_p j_p(t).
```

Lean proves every fixed fibre is ordinarily summable, including `t=0`, where `j_p(0)=0` for every
prime. The moving-horizon connection itself is

```text
connection_t(L)=t exp(-(1/2+|t|)L),
```

so `j_p` is the signed connection paired with the unsigned stable Hardy channel. P-G141's positive
covariant first trace is exactly `t*j_p(t)` primewise and `t*J(t)` globally.

The total current is reflection-odd and faithful:

```text
J(-t)=-J(t),
J(t)=0 iff t=0,
lim_(t->0+) J(t)=4,
lim_(t->0-) J(t)=-4,
J(0)=0.
```

Thus fibrewise `ell^1` admission does not commute with neutral-depth limit. Orientation before
squaring is a quantized pole residue, not a continuous vector which source symmetry can force to
zero.

Define completed and counter currents on same stable ray:

```text
C(t)=8t Re(completedPrimeGammaFlux(1+2|t|)),
K(t)=8t Re(higherValuation(1+2|t|)-logDeriv(archFactor)(1+2|t|)).
```

For `t!=0`, Lean proves exact decomposition `C(t)=J(t)+K(t)`. Analytic removal of completed polar
seam gives

```text
lim_(t->0+) C(t)=0,
lim_(t->0+) K(t)=-4,
lim_(t->0-) K(t)=4,
C is continuous at 0.
```

Polar/Gamma source therefore supplies exact opposite quantized jump. No asymptotic estimate or
PNT input is used: coefficient `4` follows from already formal residue-one prime logarithmic
Dirichlet current and completed Xi seam analyticity.

## Heavy conjecture loop

### C0 -- reflection-orbit conservation

**Conjecture.** Odd moving-horizon amplitude cancels on each reflected zero orbit and forces
neutrality.

**Failure.** P-G33 already classifies every constant two-copy incidence. Symmetric channel kills
every fibre, including off-line fibres; nonsymmetric channel retains RH-equivalent obstruction.
Orbit cancellation is tautological, not producer.

### C1 -- oriented linear Ward current

**Conjecture.** Remove one depth factor from P-G141 energy. Result should retain sign and remain
summable off wall.

**Verdict: PROVED, STRONGER.** Prime family is summable on every fibre, including wall. Total is
faithful and reflection-odd. But wall passage has quantized jump `+4/-4`; naive continuous Ward
vanishing is false.

### C2 -- completed prime--Gamma cancellation

**Conjecture.** Archimedean/polar source should cancel valuation-one residue before scalarization.

**Verdict: PROVED EXACTLY.** Countercurrent has opposite one-sided charge; completed current is
continuous at neutral wall. This is source-native cancellation, not fitted subtraction.

### C3 -- completed continuity forces neutrality

**Conjecture.** Once polar completion removes jump, continuity may select `t=0`.

**Failure.** Continuity is an identity for abstract signed depth and holds on all nearby off-wall
fibres. It regularizes orientation but supplies no zero away from wall. Global vanishing of `J` is
still exactly RH in Lean.

## Universal interpretation

P-G141 and P-G142 are two quotients of one oriented residue class:

```text
oriented valuation-one residue J
  -- multiply by signed depth --> positive finite energy tJ (orientation erased)
  -- add polar countercurrent --> continuous completed current C (positivity erased)
```

This explains simultaneous stalls. Scalarization and polar completion each remove singularity by
discarding one structure required by RH. Missing producer must act on finite regular remainder
after canonical `+4/-4` cancellation and retain a source coorientation; another reflection sum,
depth factor, scalar counterterm, or continuity theorem cannot advance Route P.

## Positive survivor

Construct source-native signed comparison for completed regular current on actual Xi copies, before
any square, proving its right-half dissipativity (P-G139) or equivalent zero. Universal polar
residue is now fully discharged; new law must control finite prime--Gamma remainder, not principal
part.

## Verification

- direct `lake env lean` module check: passed
- exact module build: passed (`12812/12812`)
- `#print axioms` headline audit: only `propext`, `Classical.choice`, `Quot.sound`
- targeted forbidden-declaration scan: clean
- umbrella import: wired; umbrella build pending

## Gates

- [x] conjecture frozen from P-G141/P-G142 survivor
- [x] reflection-orbit version killed against P-G33
- [x] coefficient-faithful signed connection identity
- [x] fibrewise summability and global faithfulness
- [x] quantized one-sided limits and discontinuity
- [x] exact polar/Gamma countercurrent and completed continuity
- [x] exact module build and axiom audit
- [ ] umbrella build
- [ ] unconditional completed regular-current sign/vanishing
- [ ] RH

## Log

- 2026-08-13 -- opened after P-G142 isolated oriented pre-square Ward law.
- 2026-08-13 -- C0 killed by existing P-G33 reflection-incidence trichotomy.
- 2026-08-13 -- C1--C3 formalized; residue jump and polar cancellation closed without RH.
