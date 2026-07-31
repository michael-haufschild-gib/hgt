# Suzuki full jump kernel is an exact Loewner growth-versus-deficit gap

- **ID:** `suzuki-jump-kernel-loewner-growth-gap`
- **Stage:** 2-fully-proven
- **Type:** THEOREM / EXACT RH-FRONTIER REDUCTION / NEW CONJECTURE
- **Scientific status:** `[PROVED HERE] [NOVELTY UNVERIFIED] [NOT AN RH PROOF]`
- **Parent:** `../../3-formalized/new_scientific_knowledge/suzuki-even-carleman-pole-carrier.md`
- **Input:** `suzuki-screw-cesaro-curvature-recurrence.md`

## Actual frontier after curvature recurrence

Curvature-centered screw recurrence now supplies, unconditionally, arbitrarily large apertures
whose far-negative dyadic shift pairs satisfy mandatory central Herglotz residue sign.  Central
shift existence is closed.  Remaining theorem is full Pick positivity of actual sewn sheet jump.

Fix real form shifts

```text
alpha<beta<0.                                           (1)
```

Let `W_lambda` be odd phase-one characteristic and `R_lambda` normalized right triangle.  Define
reflection-odd source response

```text
q_lambda(z)
 =Odd_z[R_lambda(z)/W_lambda(z)].                       (2)
```

Let `M_0` be zero-shift Xi multiplier.  Existing sewn carrier is `m_ext=-C_odd/P`.

## Theorem A: actual quotient is source affine extrapolation `[PROVED]`

Away from real characteristic divisor,

```text
m_ext(z)
 =-M_0(z)+[beta q_alpha(z)-alpha q_beta(z)]/(beta-alpha). (3)
```

### Proof

Sewn characteristic and right triangle are

```text
P=(beta-alpha)W_alpha W_beta,
J_R=beta W_beta R_alpha-alpha W_alpha R_beta.           (4)
```

Odd carrier is

```text
C_odd=M_0P-Odd_z[J_R].                                  (5)
```

Since `W_alpha,W_beta` are odd, `P` is even.  Division by `P` commutes with odd reflection, and

```text
J_R/P
 =[beta R_alpha/W_alpha-alpha R_beta/W_beta]/(beta-alpha). (6)
```

Taking odd parts in `(6)` and substituting into `-C_odd/P` proves `(3)`.  Exact one-sided centered
coordinate `eta(lambda)=-i lambda/2` contributes one common nonzero factor to `alpha,beta`, which
cancels from `(4)--(6)`.

## Theorem B: full Pick kernel has same affine law `[PROVED]`

For any spectral function `f`, put

```text
K_f(z,w)=[f(z)-conj(f(w))]/[z-conj(w)].                 (7)
```

Real linearity of `(7)` and `(3)` give

```text
K_jump
 =-K_0+[beta H_alpha-alpha H_beta]/(beta-alpha),        (8)
H_lambda=K_(q_lambda),
K_0=K_(M_0).                                           (9)
```

This is exact two-variable identity, not central or diagonal approximation.

## Theorem C: Loewner growth gap `[PROVED]`

Evaluate Hermitian kernels on arbitrary finite upper-half-plane nodes and coefficient vector `v`:

```text
H_alpha(v)=v* H_alpha v,
H_beta(v)=v* H_beta v,
T(v)=v* K_0 v.                                         (10)
```

These values are real.  From `(8)` and `beta-alpha>0`, direct algebra gives

```text
v* K_jump v>=0
iff
(-alpha)[H_beta(v)-H_alpha(v)]
 >=(beta-alpha)[T(v)-H_alpha(v)].                       (11)
```

Thus full jump positivity is equivalent to one Loewner growth-versus-deficit inequality:

```text
(-alpha)(H_beta-H_alpha)
 >=_Loewner (beta-alpha)(K_0-H_alpha).                  (12)
```

Equation `(12)` is matrix analogue of central scalar chord-mass gap.  Its two sides have exact
meaning:

- `H_beta-H_alpha`: prime--Gamma source-kernel growth when moving shift toward spectral floor;
- `K_0-H_alpha`: deficit from far source kernel to global Xi multiplier kernel;
- `-alpha`: extrapolation lever arm;
- `beta-alpha`: observed source separation.

Since `(1)` implies

```text
theta=-alpha/(beta-alpha)>1,                            (13)
```

sewn source is genuine extrapolation past nearer source, not convex averaging.

## New conjecture: `SUZUKI-LOEWNER-GROWTH`

`[CONJECTURE]` At one large aperture selected by curvature-centered screw recurrence, there is a
sufficiently negative finite dyadic pair `alpha=-2L`, `beta=-L` for which `(12)` holds on every
finite upper-half-plane node set.

For dyadic pair, `(12)` simplifies without scale factors to

```text
2[H_(-L)-H_(-2L)] >=_Loewner K_0-H_(-2L).              (14)
```

This is current source theorem whose proof would close RH through existing pole tomography.

## Corrected square producer: `SUZUKI-HOLONOMY-COMPENSATED-BIANCHI-SQUARE`

The first prime--Gamma-only version is `[FALSIFIED]`: direct Neumann comparison cancels from the
central residue but leaves a full-frequency projective-characteristic holonomy.  Exact survivor is
proved in `suzuki-full-frequency-neumann-holonomy-survivor.md`.

`[CONJECTURE / PROOF MECHANISM]` Exact resolvent identity

```text
R_beta-R_alpha=(beta-alpha)R_beta R_alpha              (15)
```

and reflected Euler--Gamma triangle maps, coupled to the explicit Neumann holonomy kernel
`K_(N_(alpha,beta))`, admit a common-gauge factorization

```text
K_(m_EG)+K_(N_(alpha,beta))
 =B_(alpha,beta)^* B_(alpha,beta).                     (16)
```

Here `B_(alpha,beta)` must be built before Xi-divisor identification from actual restricted-Weil
resolvents, prime-power endpoint atoms, Gamma completion, and the centered projective tangent
forced by finite shift.  Equation `(16)` is falsifiable: one finite node/coefficient vector with
negative left side kills proposed factorization.

This is Bianchi-type because four channels—global multiplier, far source, near source, and
Neumann projective holonomy—must close as one exact resolvent square.  Pairwise positivity is
insufficient.

## Scientific-method attack

1. Write `q_lambda` from actual source quotient in one common characteristic gauge.
2. Polarize resolvent identity `(15)` before taking quotient; retain cross terms rather than
   estimating them.
3. Separate only the universal Neumann central pole; retain its exact projective holonomy
   `alpha*beta*sin(az)/(2z(beta-alpha))*(W_alpha'(0)/W_alpha-W_beta'(0)/W_beta)`.
4. Pair prime-power atoms with reflected Gamma completion and centered projective tangent; test
   whether the coupled four-channel defect is square `(16)`.
5. Hostile-test `(14)` first on every finite spectral truncation symbolically.  No decimal tests.
6. If one sign reverses, retire square producer but retain exact equivalence `(12)` and seek a
   signed/Krein factorization.

## Falsifiers

- Central residue sign is only one asymptotic vector of `(12)` and cannot prove matrix law.
- `H_beta-H_alpha` need not be positive from abstract self-adjointness; quotient normalization can
  reverse Loewner order.
- Canonical finite Donoghue kernel has wrong divisor and cannot substitute for `H_lambda`.
- Characteristic zeros require cross-multiplied Gram form; quotient identity is used only off that
  real divisor.
- Functional-equation--Schwarz orbit insertion must violate `(12)` or `(16)`; otherwise argument
  is circular.
- A scalar or diagonal-only proof does not control off-diagonal finite node forms.
- Central Neumann cancellation cannot be promoted to full frequency; the exact holonomy term is
  mandatory.

## RH consequence if conjecture is proved

```text
curvature recurrence selects aperture and dyadic pair
 -> SUZUKI-LOEWNER-GROWTH `(12)`
 -> full jump Pick kernel `(8)` is positive
 -> m_ext has no nonreal poles
 -> existing Xi-pole tomography excludes nonreal Xi zeros
 -> RH.                                                 (17)
```

Unproved arrow is exactly `(12)`.  No claim of RH is made here.

## Novelty audit

Suzuki 2023/2026 supply screw transform, restricted operator, deficiency sources, and real-zero
finite characteristic functions.  Corpus supplied admissible two-shift sewing and jump carrier.
Targeted primary-source search found no affine Pick-kernel decomposition `(8)`, Loewner gap
equivalence `(11)--(12)`, or three-channel square conjecture `(16)`.  Priority remains unverified.

## Formal status

`formal/GaloisForLFunctions/RHTower/SuzukiJumpKernelLoewnerGap.lean` proves `(3)`, `(8)`, `(11)`,
and strict extrapolation `(13)` unconditionally.  It connects directly to actual one-sided
centered Suzuki quotient.  `SuzukiFullFrequencyNeumannHolonomy.lean` proves the algebraic and Pick
kernel correction required by the stronger producer.  Source inequality `(12)` and compensated
square `(16)` remain conjectural.
