# Route P primitive Gamma--Julia physical Stokes stable specialization

- **ID:** `route-p-primitive-gamma-julia-physical-stokes-stable-specialization`
- **Stage:** 3-formalized / needs audit
- **Type:** `[POSITIVE SURVIVOR] [THEOREM] [P-G105J]`
- **Parent:** `route-p-primitive-gamma-julia-stokes-aperture-residue-transport.md`
- **Lean:**
  `formal/GaloisForLFunctions/RHTower/RoutePPrimitiveGammaJuliaPhysicalStokesStableSpecialization.lean`

## Goal

Lift P-G105I trace-level prime/polar cancellation into a forced physical specialization of
P-G105G signed bivariate pencil and prove finite stability near aperture wall.

## Conjecturing loop

### Conjecture 1 — polar channel needs an independently chosen normalization

**Falsified.** Exact first coefficient forces ratio

```text
r(d)=-polarCountercurrent(d)/firstTraceCurrent(d).
```

Prime and polar one-sided residues are `4` and `-4`; therefore `r(d)->1` from right. No free scalar
remains.

### Conjecture 2 — forced pivot ratio may have wrong sign for P-G105G stability

**Falsified near wall.** Since `r(d)->1`, it is strictly positive throughout some punctured right
neighborhood. For upper-half-plane `u`, both

```text
z=64u,  w=r(d)u
```

lie in upper half-plane.

### Conjecture 3 — aperture congruence may destroy positive source spectrum

**Falsified.** P-G105I scale diagonal is real Hermitian. Congruence of P-G105G positive
prime-log-conjugated Gram remains positive semidefinite for every finite packet.

### Conjecture 4 — physical specialization loses exact completed trace

**Falsified.** Factor `64` removes child coefficient `1/64`; channel generator trace is
`(1-r(d))` times child trace. At all-prime level,

```text
(1-r(d)) firstTraceCurrent(d)=completedPrimeGammaCurrent(d)
```

exactly. Finite generators have same formula with finite transported child trace.

## Paper proof

Tendsto division applied to `-polar -> 4` and `prime -> 4` gives `r->1`; openness of positive
half-line gives eventual positivity. Aperture diagonal congruence preserves positive semidefiniteness.
P-G105G spectral factor theorem then applies to `z=64u`, `w=ru`: positive `r` and `Im u>0` put both
channels in product upper half-plane, so every determinant factor is nonzero.

Direct channel trace is

```text
tr(diag(64,r)B)=1-r.
```

Kronecker trace law and P-G105I finite trace identity give finite formula. Definition of `r` plus
exact completed-current decomposition gives all-prime completed trace. `QED`

## Novelty and anti-theatre audit

Result identifies physical Stokes specialization rather than merely asserting compatibility.
Wall balance `r->1`, child scale `64`, finite PSD congruence, P-G105G stability, and completed first
coefficient are one exact chain. Apparent scalar renormalization is shadow of projective channel
balance.

Still no cofinal determinant. Finite packets may approach all-prime source in several topologies;
P-G105J proves stability for each and exact first trace, not locally uniform determinant
convergence or Xi divisor identity.

## Formal status

Lean proves unconditionally:

- positivity of literal first-trace current for `d>0`;
- pivot ratio tends one and is eventually positive;
- exact completed linear trace identity;
- Hermitian aperture diagonal and PSD actual transported Gram;
- physical pencil equals `I+u` times explicit generator;
- exact finite generator trace;
- physical finite stability whenever ratio positive;
- eventual finite stability near wall for every packet;
- premise-free P-G105J capstone.

Direct Lean and target-only module build pass. Axiom audit reports only `propext`,
`Classical.choice`, and `Quot.sound`. Forbidden scan and `git diff --check` pass. Module is wired;
no umbrella build was run.

## Refined open core

Construct cofinal operator/determinant for physical generators. Need trace-norm or determinant-class
control uniform on compact `u` sets, including regular positive-depth bulk, and show finite first
traces converge to completed current. Then prove limiting divisor is completed Xi without fitting.

## Higher universal principle

Polar completion is projective balancing. Child and pivot residues fix a ratio, not two independent
weights. Their equal wall magnitude forces balanced channel `r=1`, erasing divergent linear term
while anti-Pick quadratic interaction survives and enforces stability. This simultaneously explains
four-unit cancellation and why scalar one-channel models failed.

## Log

- 2026-08-16 — P-G105J forced physical channel ratio, exact generator trace, and near-wall finite
  stability paper-proved and formalized.
