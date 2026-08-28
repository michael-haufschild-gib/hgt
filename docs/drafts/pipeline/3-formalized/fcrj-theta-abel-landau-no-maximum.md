# FCRJ theta--Abel Landau rigidity without a maximum

- **ID:** `fcrj-theta-abel-landau-no-maximum`
- **Stage:** 3 — formalized in Lean 4
- **Source route:** CCM-FU / FCRJ physical theta--Abel aperture
- **Theorem status:** Lean-proved

## Claim

Finite dominant-layer asymptotics are unnecessary. After one fixed generic squared smooth probe,
the exact physical log-window multiplier, restored theta--Abel factor, and compact aperture Laplace
amplitude form a coefficient-generic Xi Landau system. If any Xi divisor lies strictly right of the
critical line, its complete log-sampled scalar carrier is cofinally unbounded below. Equivalently,
RH holds exactly when one generic physical theta--Abel probe has an eventual lower bound.

## Gates

- [x] Exact paper statement and proof
- [x] Strongest positive survivor extracted
- [x] Direct Lean check and axiom audit
- [x] Targeted module build
- [ ] Publication-ready exposition

## Exact theorem

For every multiplicity-exact right-Xi copy `q`, write

```text
w_q = rho_q - 1/2,
z_q = rho_q - 1,
b_f,A,c(q)
  = Laplace(f)(w_q)^2 (exp(c z_q)-1) ((z_q+1)/z_q) A_A(z_q),
A_A(z) = (1-exp(-A z))/z.                                      (1)
```

Here `A_A(z)` is the scalar integral of the physical aperture exponential. Actual Xi geometry gives

```text
-1/2 < Re z_q < 0,
1 < |Im z_q| <= |z_q|.                                         (2)
```

For `A,c>0` every factor in `(1)` is nonzero on a generic fixed profile. Moreover,

```text
|exp(c z_q)-1| <= 2,
|(z_q+1)/z_q| <= 2,
|A_A(z_q)| <= 1+exp(A/2),                                      (3)
```

and squared smooth Laplace decay supplies

```text
|Laplace(f)(w_q)^2| <= C_f / |w_q|^2.                          (4)
```

The coefficients respect conjugation and are constant on multiplicity fibres. Thus `(1)--(4)`
instantiate `XiRightCoefficientSystem`. Define the real log-sampled carrier

```text
H_f,A,c(n) = Re [2 sum_q b_f,A,c(q) n^(rho_q-1/2)].             (5)
```

The coefficient-generic pole-tomography theorem gives, without any maximum or isolation premise,

```text
Nonempty(right-Xi copies)
  ==> for every B and N, some n>=N has H_f,A,c(n)<B.             (6)
```

Consequently `H_f,A,c` cannot tend to zero. Since RH makes the right-copy type empty and failure of
RH makes it nonempty, Lean proves the closed criterion

```text
RH <-> exists generic smooth f, exists C,N,
        for every n>=N, 0 <= H_f,A,c(n)+C.                      (7)
```

## Proof

Reflection of the rectangular amplitude transfers its known nonvanishing from the open right
half-plane to `Re z<0`. The Xi ordinate gap bounds both denominator-bearing factors uniformly.
Multiplying these bounds by the corpus inverse-square smooth-profile estimate proves the coefficient
system majorant. Conjugation and multiplicity-fibre invariance follow factorwise. The existing
coefficient-generic Xi Landau theorem then proves `(6)` by pole tomography at every actual right-Xi
support point; its argument uses the transverse supremum only as an abscissa and never requires it
to be attained. Empty right support under RH gives the forward implication of `(7)`; `(6)` gives
the reverse implication.

## Lean certificate

- Module:
  `formal/GaloisForLFunctions/RHTower/XiPhysicalPrimeApertureThetaAbelLandauNoMaximum.lean`
- Umbrella:
  `formal/GaloisForLFunctions/RHTower.lean`
- Direct check: PASS
- Targeted build: PASS
- Axiom audit: `[propext, Classical.choice, Quot.sound]`
- Capstones:
  `xiPhysicalThetaAbelCoefficientSystem`,
  `xiPhysicalThetaAbelLandauResponse_cofinally_unbounded_below`,
  `not_tendsto_xiPhysicalThetaAbelLandauResponse_zero`,
  `riemannHypothesis_iff_exists_smoothProbe_eventually_lowerBound_physicalThetaAbelLandau`

## No-go closure

Failure of the positive transverse supremum to be attained is not an escape. Neither finite
rightmost support, strict isolation, phase injectivity, nor a dominant-layer limit appears in
`(6)--(7)`. Loops 73--76 now close every divisor-side infinite-tail loophole identified after the
theta--Abel rate wall. Surviving RH burden is source-side: identify or compare the actual centered
theta--Abel prime response with `(5)` strongly enough that the sought RH-scale source bound supplies
its eventual lower bound. This result does not assert that bridge.

## Novelty audit

Classical ingredients are Landau's theorem for nonnegative Dirichlet coefficients, smooth explicit
formulae, compact Laplace windows, and reciprocal-square zero summability. Targeted corpus and
primary-literature searches found no exact synthesis of a generic squared smooth probe with the
physical theta--Abel multiplier, restored factor, compact aperture moment, multiplicity-exact Xi
pole tomography, and the maximum-free criterion `(7)`. Candidate-new content is restricted to
`(1)--(7)` as this coefficient-exact route synthesis; Landau's theorem and smooth explicit formulae
are not claimed new.

Primary comparison points:

- Hardy--Riesz, *The General Theory of Dirichlet's Series* (classical positive-coefficient boundary
  singularity theorem).
- B. Maurizi, *Extending Landau's Theorem on Dirichlet Series with Non-Negative Coefficients*,
  arXiv:1009.0228.
- E. P. Balanzario, D. E. Cardenas Romero, R. Chacon Serna,
  *A smooth version of Landau's explicit formula*, arXiv:2311.04347.

## Verification log

- 2026-08-27: direct `lake env lean` check passed.
- 2026-08-27: targeted module build passed.
- 2026-08-27: scratch axiom audit passed with standard axioms only.
