# FCRJ theta--Abel energy prime/archimedean residue separation

- **ID:** `fcrj-theta-abel-energy-prime-arch-residue`
- **Stage:** 2 — fully proven on paper
- **Source route:** CCM-FU / FCRJ physical theta--Abel aperture
- **Theorem status:** Lean-proved

## Claim

The completed archimedean channel of the exact physical theta--Abel energy source is not an
uncontrolled contour tail. On every source-domain rectangle crossing `z=-i/2`, its normalized
contour is exactly one explicit nonnegative square. For positive physical parameters it is
strictly positive. Consequently all unresolved sign burden in the completed source contour lies
in the continued prime-flux channel.

## Gates

- [x] Exact paper statement and proof
- [x] Strongest positive survivor extracted
- [x] Direct Lean check and axiom audit
- [x] Targeted module build
- [ ] Publication-ready exposition

## Exact theorem

Write

```text
F_a(z)=the Loop-77 physical theta--Abel energy two-edge transform,
s(z)=1/2+i z,
P(z)=infinitePrimeFlux(s(z)),
G(z)=logDeriv(archFactor)(s(z)),
S(z)=continuedPrimeArchSourceRelativeTrace(z).
```

Lean first proves the unconditional pointwise source decomposition

```text
F_a(z)^2 S(z)=F_a(z)^2[-i P(z)]+F_a(z)^2[i G(z)].              (1)
```

The completed arch factor has, in the source half-plane `Im z<1/2`, the factorization

```text
archFactor(s(z))=(z+i/2) H(z),                                 (2)
```

where `H` is analytic and nowhere zero. If a positively oriented rectangle satisfies

```text
z1.re<0<z2.re,
z1.im < -1/2 < z2.im < 1/2,                                   (3)
```

then the local weighted argument principle gives

```text
contour F_a(z)^2[i G(z)] dz = 2 pi i F_a(-i/2)^2.              (4)
```

The physical detector evaluates exactly as

```text
F_a(-i/2)=e^(a/2) 2(1-e^(-L/2)) c A.                           (5)
```

Therefore the normalized archimedean contour is

```text
(2 pi i)^-1 contour F_a(z)^2[i G(z)] dz
  =[e^(a/2) 2(1-e^(-L/2)) c A]^2 >=0,                          (6)
```

and is strictly positive when `L,A,c>0`.

## Proof

Identity `(1)` is the defining continued prime--archimedean decomposition. Factorization `(2)`
extracts the unique zero `s=1` of the completed arch factor; positivity of `Re s(z)` on
`Im z<1/2` makes its Gamma cofactor analytic and nonzero. The local weighted rectangle argument
principle then proves `(4)` for the entire weight `F_a^2`.

At `z=-i/2`, the positive edge has mode coordinate `i z=1/2`, while the reflected edge has
coordinate `-1/2`. The latter vanishes because the physical entire amplitude contains the exact
factor `w+1/2`. At `w=1/2`, both remaining aperture amplitudes land at their removable value zero,
giving factors `c` and `A`, while the log window is
`A_L(1/2)=2(1-e^{-L/2})`. This proves `(5)--(6)`.

## Lean certificate

- Module:
  `formal/GaloisForLFunctions/RHTower/XiPhysicalPrimeApertureThetaAbelEnergyPrimeArchResidue.lean`
- Umbrella:
  `formal/GaloisForLFunctions/RHTower.lean`
- Direct check: PASS
- Targeted build: PASS
- Axiom audit: `[propext, Classical.choice, Quot.sound]`
- Capstones:
  `physicalThetaAbelEnergy_sourceIntegrand_eq_prime_add_arch`,
  `rectIntegral_physicalThetaAbelEnergy_mul_archSource_eq`,
  `xiPhysicalThetaAbelEnergyNormalizedArchSourceContour_eq_explicit`,
  `xiPhysicalThetaAbelEnergyNormalizedArchSourceContour_re_nonneg`,
  `xiPhysicalThetaAbelEnergyNormalizedArchSourceContour_re_pos`

## No-go closure

Gamma growth and archimedean boundary tails cannot obstruct this physical source family on a
pole-crossing source rectangle. The entire arch channel is one explicit positive residue, not an
estimate or asymptotic remainder. Any negative completed-source contour must be carried by the
continued prime-flux term in `(1)` with magnitude exceeding `(6)`.

Remaining RH-bearing burden: formalize a cofinal pole-crossing rectangle family and prove an
eventual lower floor for its direct continued prime-flux contour after adding the explicit square
`(6)`. This is a prime-only source problem; no Gamma estimate remains.

## Novelty audit

Weighted argument principles, the completed arch-factor zero at `s=1`, and prime/archimedean
explicit-formula splitting are classical. Corpus and primary-literature searches through
2026-08-27 found no exact evaluation `(5)--(6)` for the pole-cancelled physical theta--Abel energy
detector or its use to remove the entire archimedean sign burden from this source criterion.
Candidate-new content is restricted to that route-specific synthesis and exact positive residue.

Primary comparison points:

- Classical Guinand--Weil weighted explicit formula and argument principle.
- A. Connes, C. Consani, M. Marcolli, *The Weil proof and the geometry of the adeles class space*,
  arXiv:math/0703392.
- A. Groskin, *A finite Guinand--Weil dictionary and archimedean tail order for the truncated Weil
  quadratic form*, arXiv:2607.02828.

## Verification log

- 2026-08-27: corpus conjecture search completed before construction.
- 2026-08-27: targeted primary-literature audit completed.
- 2026-08-27: direct `lake env lean` check passed.
- 2026-08-27: scratch and built-module axiom audits passed with standard axioms only.
- 2026-08-27: targeted module build passed.
- 2026-08-27: formal lint reports only pre-existing unrelated unreachable Sieve modules; new
  module is reachable from `GaloisForLFunctions.RHTower`.
