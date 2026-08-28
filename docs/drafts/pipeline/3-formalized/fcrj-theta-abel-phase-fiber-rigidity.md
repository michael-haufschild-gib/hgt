# FCRJ theta--Abel phase-fiber rigidity

- **ID:** `fcrj-theta-abel-phase-fiber-rigidity`
- **Stage:** 3 — formalized in Lean 4
- **Source route:** CCM-FU / FCRJ physical theta--Abel aperture
- **Theorem status:** Lean-proved

## Claim

Distinct complex theta--Abel aperture profiles are coefficient-faithful in `L²` on every interval
of positive length. Consequently, a finite maximal discrete-phase fiber cannot cancel unless every
coefficient in that fiber is zero. The countable dominant-layer survival theorem therefore needs
no phase-injectivity hypothesis.

## Gates

- [x] Exact paper statement and proof
- [x] Strongest positive survivor extracted
- [x] Direct Lean check and axiom audit
- [x] Targeted module build
- [ ] Publication-ready exposition

## Exact theorem

For pairwise distinct `z_i` and `A > 0`, every coordinate `j` admits `C_j > 0` such that

```text
|x_j|² <= C_j integral_0^A |sum_i x_i exp(-z_i u)|² du.          (1)
```

In particular,

```text
sum_i x_i [u |-> exp(-z_i u)] = 0 in L²([0,A])  ==>  x_i = 0.    (2)
```

Apply `(2)` to any finite fiber of the sampled phase map
`i |-> exp(z_i) / exp(beta)`. Even if several distinct exponents have the same sampled phase,
their continuous aperture profiles remain independent. Hence every fiber containing a nonzero
theta--Abel coefficient has nonzero aggregate `L²` vector.

Combining this fact with countable `L²` dominant-layer survival gives: if the literal mode vectors
are norm-summable, the rightmost real part `beta` is attained by a finite strictly isolated layer,
the dominant exponents are distinct, and one corresponding source coefficient is nonzero, then
the physical half-density-scaled response does not tend to zero whenever `-1/2 < beta < 0`.

## Proof

Reindex the finite family as unit confluent slots and apply interval Gram observability for plain
exponentials. If the `L²` sum is zero, its squared norm and therefore its aperture energy vanish;
`(1)` forces each coefficient to vanish. Restriction to a finite sampled-phase fiber preserves
distinctness. A selected nonzero theta--Abel coefficient is nonzero because the source coefficient,
log-window multiplier, restored `(z+1)/z` factor, and aperture profile are all nonzero. The resulting
nonzero fiber is exactly the premise required by countable dominant-layer survival.

## Lean certificate

- Module:
  `formal/GaloisForLFunctions/RHTower/XiPhysicalPrimeApertureThetaAbelPhaseFiberRigidity.lean`
- Umbrella:
  `formal/GaloisForLFunctions/RHTower.lean`
- Direct check: PASS
- Targeted build: PASS
- Axiom audit: `[propext, Classical.choice, Quot.sound]`
- Capstones:
  `plainExponentialApertureL2_relation_coefficients_zero`,
  `finiteExponentialVectorFiberCoefficient_thetaAbel_ne_zero`,
  `not_tendsto_xiPhysicalThetaAbelCountableL2PhysicalScale_zero_of_distinctModes`

## No-go closure

Discrete phase collision is not an escape mechanism. Under distinct dominant exponents, exactly two
analytic escapes remain:

1. actual zero-mode aperture vectors fail `ell¹(L²)` norm summability;
2. no finite strictly isolated rightmost real part is attained.

## Novelty audit

Finite exponential independence and interval Gram observability are classical. Corpus and targeted
primary-literature audit found no exact synthesis connecting continuous theta--Abel aperture
profiles, collisions of sampled phases, countable dominant-layer survival, and physical
half-density nondecay. Candidate-new content is restricted to that route-specific synthesis and
the exact two-escape classification, not abstract exponential independence.

## Verification log

- 2026-08-27: direct `lake env lean` check passed.
- 2026-08-27: scratch `#print axioms` audit passed with standard axioms only.
- 2026-08-27: targeted module build passed.
