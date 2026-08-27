# FCRJ theta--Abel smooth-probe summability

- **ID:** `fcrj-theta-abel-smooth-probe-summability`
- **Stage:** 2 — fully proven on paper
- **Source route:** CCM-FU / FCRJ physical theta--Abel aperture
- **Theorem status:** Lean-proved

## Claim

A fixed squared smooth compact-aperture Laplace probe makes the complete multiplicity-weighted
right-Xi theta--Abel packet norm-summable in physical aperture `L²`. A suitable probe exists from
the already-proved dense-residual profile set. Thus norm nonsummability is no longer an escape:
every nonempty finite strictly isolated rightmost layer forces physical half-density nondecay.

## Gates

- [x] Exact paper statement and proof
- [x] Strongest positive survivor extracted
- [x] Direct Lean check and axiom audit
- [x] Targeted module build
- [ ] Publication-ready exposition

## Exact theorem

Let `rho` range over actual Xi-divisor support with `Re rho > 1/2`, retaining divisor
multiplicity `m(rho)`, and set

```text
w_rho = rho - 1/2,
z_rho = rho - 1,
lambda_f(rho) = m(rho) (Laplace(f)(w_rho))².                     (1)
```

For every nonempty smooth support window, a dense residual set of fixed profiles has
`Laplace(f)(w_rho) != 0` at every right-Xi point. One integration by parts followed by squaring,
together with multiplicity-exact Xi inverse-square summability, gives

```text
sum_rho |lambda_f(rho)| < infinity.                              (2)
```

Actual Xi geometry supplies uniform bounds

```text
|exp(c z_rho)-1| <= 2,
|(z_rho+1)/z_rho| <= 2,
||u |-> exp(-z_rho u)||_L2([0,A]) <= K_A.                       (3)
```

The second bound uses the unconditional Xi height gap `1 < |Im rho|`; the third uses
`-1/2 < Re z_rho < 0`. Hence the literal mode vectors satisfy

```text
sum_rho ||lambda_f(rho) (exp(c z_rho)-1)(z_rho+1)/z_rho
               [u |-> exp(-z_rho u)]||_L2 < infinity.           (4)
```

If a nonempty finite set `D` is a strictly isolated rightmost layer,

```text
Re z_rho = beta       for rho in D,
Re z_rho < beta       for rho outside D,                        (5)
```

then Lean constructs a fixed smooth `f` for which

```text
exp((beta+1/2)n) N_n(f) does not tend to 0 in L².                (6)
```

No phase-injectivity, coefficient-nonvanishing, summability, or wall premise is required: support
injectivity, profile genericity, `(2)--(4)`, and `-1/2 < beta < 0` are all discharged internally.

## Proof

Restrict centered inverse-square Xi summability to right divisor support. Squared smooth Laplace
decay bounds `lambda_f` by its multiplicity-weighted inverse-square majorant, proving `(2)`.
Critical-strip geometry bounds the moving-window multiplier. The source-derived Xi height gap
bounds the restored theta--Abel factor, while compact-aperture `L²` embedding bounds every
exponential profile. Their product proves `(4)`. Dense-residual profile nonvanishing supplies an
actual fixed probe. Distinct support points give distinct `z_rho`; Loop 74 removes sampled-phase
collisions, and Loop 73 yields `(6)`.

## Lean certificate

- Module:
  `formal/GaloisForLFunctions/RHTower/XiPhysicalPrimeApertureThetaAbelSmoothProbeSummability.lean`
- Umbrella:
  `formal/GaloisForLFunctions/RHTower.lean`
- Direct check: PASS
- Targeted build: PASS
- Axiom audit: `[propext, Classical.choice, Quot.sound]`
- Capstones:
  `xiRightSupportSmoothProbeCoefficient_summable`,
  `xiRightSupportSmoothProbeThetaAbelModeVector_norm_summable`,
  `exists_smoothProbe_not_tendsto_xiRightSupportThetaAbelPhysicalScale_zero`

## No-go closure

Failure of `ell¹(L²)` summability is not intrinsic to the right-Xi packet; a single fixed smooth
probe repairs it without deleting any right-Xi support point. After Loops 73--75, sole surviving
analytic escape is that positive transverse real parts have no nonempty finite strictly isolated
maximum.

## Novelty audit

Smooth explicit-formula weights, Laplace-transform decay by integration by parts, Xi zero-density
summability, and compactly supported convolution squares are classical. Targeted corpus and primary-
literature audit found no exact synthesis of multiplicity-weighted squared smooth Laplace probing,
the restored theta--Abel coefficient, physical aperture `L²`, phase-fiber rigidity, and the resulting
one-escape classification. Candidate-new content is restricted to `(3)--(6)` as this route-specific
synthesis, not the classical ingredients.

## Verification log

- 2026-08-27: direct `lake env lean` check passed.
- 2026-08-27: scratch axiom audit passed with standard axioms only.
- 2026-08-27: targeted module build passed.
