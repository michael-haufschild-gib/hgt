# FCRJ theta--Abel energy Weil source weld

- **ID:** `fcrj-theta-abel-energy-weil-source`
- **Stage:** 2 — fully proven on paper
- **Source route:** CCM-FU / FCRJ physical theta--Abel aperture
- **Theorem status:** Lean-proved

## Claim

The restored physical theta--Abel scalar has an exact pole cancellation that turns it into an
entire nonvanishing mode amplitude. Squaring this mode produces an inverse-square Xi coefficient
system and an entire self-sharp two-edge Weil family. Its full Weil value differs from the
maximum-free Landau carrier by an aperture-uniform absolutely summable remainder. Consequently,
false RH forces both the Weil values and normalized continued prime--archimedean source contours
cofinally below every real level. One fixed unit physical family is an unconditional closed RH
criterion.

## Gates

- [x] Exact paper statement and proof
- [x] Strongest positive survivor extracted
- [x] Direct Lean check and axiom audit
- [x] Targeted module build
- [ ] Publication-ready exposition

## Exact theorem

Write

```text
A_d(u) = (1-exp(-d u))/u,
P_L,A,c(w) = A_L(w) (w+1/2) A_c(1/2-w) A_A(w-1/2).            (1)
```

Every `A_d` is entire after its removable value at zero is installed. For a right-Xi copy set
`w=rho-1/2` and `z=rho-1`. Then Lean proves the exact physical identity

```text
P_L,A,c(w)
 = A_L(w) (exp(cz)-1) ((z+1)/z) A_A(z).                         (2)
```

Thus the apparent restored-factor pole is cancelled before any estimate. If `L,A,c>0`, `(2)` is
nonzero at every right-Xi copy. Actual strip and height geometry gives

```text
|P_L,A,c(± i alpha_q)|
 <= C_L,A / |alpha_q|,
C_L,A = 4(1+exp A)(1+exp(|L|/2)).                               (3)
```

Define the energy coefficient and bilateral Xi test

```text
b(q) = P_L,A,c(rho_q-1/2)^2,
F_a(s) = exp(a i s)P_L,A,c(i s)+exp(-a i s)P_L,A,c(-i s).       (4)
```

The function `F_a` is entire, even, Schwarz-symmetric, self-sharp, and square-summable on the full
multiplicity-exact Xi divisor. Its square has the sign-selected dominant edge

```text
D_a(w) = P(w)^2 exp(2aw),                  Re w>0,
       = P(-w)^2 exp(-2aw),                Re w<0,
       = 0,                                Re w=0.               (5)
```

For every `a>=0`, pointwise and after summation,

```text
|F_a(alpha_q)^2-D_a(i alpha_q)|
 <= 4 C_L,A^2 / |alpha_q|^2,                                  (6)

|Weil(F_a,F_a)-sum_q D_a(i alpha_q)|
 <= 4 C_L,A^2 sum_q |alpha_q|^-2.                              (7)
```

At `a=log(n)/2`, full-divisor reflection folds `(5)` exactly to

```text
sum_q D_(log n/2)(i alpha_q)
 = Re-embedded [2 sum_(right q) b(q)n^(rho_q-1/2)].             (8)
```

The maximum-free coefficient-generic Landau theorem and `(7)--(8)` imply

```text
not RH ==> for every B,N, some n>=N has
  Re Weil(F_(log n/2),F_(log n/2)) < B.                         (9)
```

Hence the following unit-parameter statement is closed and premise-free:

```text
RH <-> for every n with 1<log(n)/2,
  0 <= Re Weil(F^unit_(log n/2),F^unit_(log n/2)).              (10)
```

Finally, for every finite Xi packet there is an admissible rectangle on which the exact continued
prime--archimedean source contour of `F_a^2` equals its enclosed multiplicity sum. Cofinal rectangle
exhaustion and square summability give

```text
(2 pi i)^-1 contour(F_a^2 * continued-source) -> Weil(F_a,F_a). (11)
```

Combining `(9)` and `(11)` yields the source-side survivor

```text
not RH ==> for every B,N, some n>=N and an admissible rectangle have
  Re [(2 pi i)^-1 contour(F_(log n/2)^2 * continued-source)] < B. (12)
```

## Proof

Identity `(2)` follows from `w=z+1/2` and
`z A_c(-z)=exp(cz)-1`; clearing the actual nonzero `z` verifies the restored-factor cancellation.
Entirety follows by composition and multiplication of removable rectangular amplitudes. Their
conjugation laws give Schwarz symmetry; bilateral reflection gives evenness and self-sharpness.
The critical strip, the unconditional Xi ordinate gap, and elementary exponential bounds prove
`(3)`. Expanding the square in `(4)` leaves one growing edge plus a cross term and a decaying edge.
For `a>=0` the latter exponential has norm at most one on the selected half-strip, proving `(6)`;
inverse-square Xi summability proves `(7)`. Reflection pairs left and right copies exactly, and the
complex-power logarithm identity proves `(8)`. Landau oscillation survives the fixed bound `(7)`,
giving `(9)--(10)`. The corpus finite Guinand--Weil rectangle law and cofinal summation prove
`(11)--(12)`.

## Lean certificate

- Module:
  `formal/GaloisForLFunctions/RHTower/XiPhysicalPrimeApertureThetaAbelEnergyWeilSource.lean`
- Umbrella:
  `formal/GaloisForLFunctions/RHTower.lean`
- Direct check: PASS
- Targeted build: PASS
- Axiom audit: `[propext, Classical.choice, Quot.sound]`
- Capstones:
  `xiPhysicalThetaAbelEntireModeAmplitude_eq_physical`,
  `norm_xiWeilPolarization_physicalThetaAbelEnergy_sub_dominant_le`,
  `riemannHypothesis_iff_unitPhysicalThetaAbelEnergy_logSample_weil_nonneg`,
  `exists_admissible_physicalThetaAbelEnergySourceContour_approximates_weil`,
  `not_riemannHypothesis_implies_physicalThetaAbelEnergy_sourceContour_cofinally_unbounded_below`

## No-go closure

The restored theta--Abel factor does not create a meromorphic-test obstruction: its physical
log-window factor cancels the pole exactly, and the resulting detector is entire. The passage from
the right-divisor Landau carrier to a full self-sharp Weil value loses only one fixed summable
constant, not an aperture-dependent error. The passage from that Weil value to the corpus's
continued prime--archimedean source is cofinal and exact at every finite rectangle.

Remaining RH-bearing burden is narrower: prove an unconditional lower bound for this explicit
continued source-contour family, or identify its prime part with a manifestly nonnegative FCRJ
energy after controlling the archimedean and boundary terms. This result does not assert that sign.

## Novelty audit

Classical ingredients are Weil positivity, Guinand--Weil explicit formulae, compactly supported
Laplace/Fourier windows, Landau oscillation, and reciprocal-square zero summability. Corpus and
primary-literature searches through 2026-08-27 found no exact synthesis of the pole-cancelled
physical theta--Abel amplitude `(1)--(2)`, its squared noncensoring Xi coefficient, the uniform
two-edge remainder `(6)--(7)`, maximum-free Landau transfer `(9)`, and cofinal exact source-contour
divergence `(12)`. Candidate-new content is restricted to that route-specific synthesis.

Primary comparison points:

- A. Weil, explicit-formula positivity criterion, as summarized in modern compact-window work.
- A. Connes, C. Consani, M. Marcolli, *The Weil proof and the geometry of the adeles class space*,
  arXiv:math/0703392.
- M. Chuk, *Weil positivity in compact windows: certified two-sided bounds and a Landau--Widom
  decay law*, arXiv:2608.24827.
- E. P. Balanzario, D. E. Cardenas Romero, R. Chacon Serna,
  *A smooth version of Landau's explicit formula*, arXiv:2311.04347.

## Verification log

- 2026-08-27: corpus conjecture search completed before construction.
- 2026-08-27: targeted primary-literature audit completed.
- 2026-08-27: direct `lake env lean` check passed.
- 2026-08-27: scratch axiom audit passed with standard axioms only.
- 2026-08-27: targeted module build passed.
