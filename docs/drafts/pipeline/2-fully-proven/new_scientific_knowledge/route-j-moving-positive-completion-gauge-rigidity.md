# Route J moving positive-completion gauge rigidity

- **ID:** `route-j-moving-positive-completion-gauge-rigidity`
- **Stage:** 2-fully-proven
- **Type:** THEOREM / CLASS NO-GO / POSITIVE SURVIVOR
- **Scientific status:** `[PAPER-PROVED] [NEW INTERNAL SYNTHESIS] [EXTERNAL NOVELTY UNVERIFIED] [NOT RH]`
- **Parent:** `../../1-in-progress/route-j-principal-relative-julia-current.md`, `J-SF6`
- **Prior boundary:** `route-h-finite-theta-core-divisor-charge-rigidity.md` closes fixed
  meromorphic gauges. This card treats genuinely moving positive-source gauges; no local
  convergence, fixed order, or normal-family hypothesis is imposed.

## Frontier question

Let

```text
z_n = xiCTaylorAnisotropicCenteredPoint sigma n,
x_n = xiTaylorAnisotropicHorizontalStep sigma n.
```

For every superaccurate finite Xi Taylor schedule, its logarithmic current has exact divisor
charge

```text
x_n Im(P_n'(z_n)/P_n(z_n)) -> m,
m = analyticOrderAt(xi,sigma).toNat.                         (J.60)
```

A fixed analytic unit cannot screen `(J.60)`, but that does not address a source gauge which
changes with `n`. The live Route-J conjecture was that increasing theta, Julia, Gamma, or
co-Poisson source depth might create such a moving gauge while retaining positivity.

## Positive-completion class

For a nonnegative density `h` on `(0,infinity)`, define

```text
G_h(z)  = integral h(t)(1-exp(i t z)) dt,
G'_h(z) = integral h(t)(-i t exp(i t z)) dt.                 (J.61)
```

Suppose a one-sided source transform `F` and its spectral derivative `D` obey the exact
integration-by-parts connections

```text
G_h(z)  = -i z F,
G'_h(z) = -i(F+zD).                                         (J.62)
```

The density, transform, and depth may all depend on `n`. Required hypotheses are only:

1. `h_n(t)>=0` for `t>0`;
2. both integrals in `(J.61)` are absolutely integrable at `z_n`;
3. `(J.62)` holds at `z_n`;
4. `F_n(z_n)!=0`.

No common density, bounded depth, locally convergent family, fixed meromorphic order, or
uniform moment bound is assumed.

## Theorem — arbitrary moving positive completions have zero divisor charge

Assume `sigma.re<1/2`. For every family satisfying `(J.61)`--`(J.62)`,

```text
|Im(D_n/F_n)| <= 2/Im(z_n),                                 (J.63)
x_n Im(D_n/F_n) -> 0.                                       (J.64)
```

Consequently every superaccurate Taylor schedule satisfies

```text
x_n [Im(P_n'/P_n)-Im(D_n/F_n)] -> m.                        (J.65)
```

Thus such a moving gauge screens the Taylor charge exactly if and only if `m=0`, equivalently
`xi(sigma)!=0`. At every hypothetical Xi zero it preserves the full positive integer
multiplicity.

### Proof

For `y=Im z>0`, positivity of `h` gives the pointwise half-plane contraction

```text
||G'_h(z)|| <= Re G_h(z)/y <= ||G_h(z)||/y.                  (J.66)
```

Use `(J.62)`. Since `||z||>=y`, the triangle inequality applied to

```text
zD = i G'_h-F
```

gives

```text
||D|| <= 2||F||/y.                                          (J.67)
```

After division by the nonzero `F`,

```text
|Im(D/F)| <= ||D/F|| <= 2/y,
```

which proves `(J.63)`.

The centered anisotropic mesh has

```text
Im(z_n) -> eta = 1/2-sigma.re > 0,
x_n -> 0.
```

Hence eventually `Im(z_n)>eta/2`, and `(J.63)` yields

```text
|x_n Im(D_n/F_n)| <= |x_n| 4/eta -> 0.
```

This proves `(J.64)`. Subtract `(J.64)` from the exact Taylor charge law `(J.60)` to obtain
`(J.65)`. Uniqueness of limits shows that screening is equivalent to `m=0`; the completed-Xi
order theorem identifies this with `xi(sigma)!=0`.

## Literal theta-packet corollary

Let `L_n>=0` and `N_n>0` be arbitrary at every mesh point. Set

```text
F_n = criticalLogPhaseTailPacketValue L_n N_n z_n,
D_n = criticalLogPhaseTailPacketDerivative L_n N_n z_n.
```

The exact translated-density integration-by-parts identities instantiate `(J.62)` with

```text
h_n(t) =
  -criticalLogPhaseTranslatedDensityProfileDerivative L_n N_n t > 0.
```

Strict right-half-plane completion proves `F_n!=0`. Therefore `(J.64)`--`(J.65)` hold for
arbitrary simultaneous phase-lag and depth schedules. Increasing Prouhet/Haar/theta depth, even
non-normally and with no convergent gauge family, cannot screen one unit of Xi divisor charge
while this positive-completion structure is retained.

## Why this is not fixed-gauge repackaging

The fixed-gauge law has one meromorphic germ `G` and computes its charge from one integer local
order. Here `h_n`, `F_n`, and `D_n` may change independently with `n`; there need not be a
limiting germ or eventually fixed divisor. The no-go comes from a uniform half-plane contraction,
not meromorphic-order quantization. It eliminates a class left explicitly open by the fixed-gauge
theorem.

## Hostile conjecture audit

### J6-M1 — grow positive source depth at the mesh rate

**Conjecture.** Let `N_n` or `L_n` grow fast enough that the moving theta gauge supplies the
`1/x_n` logarithmic derivative needed to cancel `(J.60)`.

**Attack.** `(J.63)` is independent of `N_n`, `L_n`, total mass, moments, and family convergence.
Since `Im(z_n)` stays bounded below, every such logarithmic derivative is uniformly bounded.

**Verdict.** Falsified class-completely.

### J6-M2 — rescale positive density amplitudes singularly

**Conjecture.** Multiply `h_n` by an unbounded positive scalar.

**Attack.** Both `F_n` and `D_n` scale by the same scalar. Their logarithmic derivative and
`(J.63)` are unchanged.

**Verdict.** Falsified exactly.

### J6-M3 — use a target-selected positive density

**Conjecture.** Choose `h_n` from the target fibre rather than a fixed source rule.

**Attack.** The proof permits arbitrary `h_n` pointwise. Target dependence does not evade the
ceiling while positivity and `(J.62)` survive. Such selection is still theatre as provenance,
but the analytic no-go does not need that objection.

**Verdict.** Falsified even before the source-only audit.

## Strongest positive survivor

Any moving gauge which screens a zero of multiplicity `m` must carry

```text
x_n Im(D_n/F_n) -> m>0.                                    (J.68)
```

It must therefore leave the positive-completion/Herglotz cone: a nonnegative one-sided source
cannot supply the required mesh-scale phase velocity. The surviving transgression must introduce
an indefinite signed density, a singular boundary term invalidating `(J.62)`, or a genuinely
relation-valued channel without a scalar logarithmic derivative.

This survivor matches the updated biaxial source law. Arbitrarily increasing positive depth is
still regular at the divisor-charge scale; the missing channel must be singular in structure,
not merely large in its source index.

## Novelty boundary

The positive-real/Herglotz derivative contraction and logarithmic-derivative algebra are classical
parent facts. No novelty is claimed for them. Searches of primary literature on Herglotz-
Nevanlinna families, Xi logarithmic derivatives, theta Laplace transforms, and normal-family
gauges found no statement combining:

1. arbitrary depth-varying positive one-sided completions;
2. the explicit anisotropic Xi Taylor mesh;
3. exact multiplicity charge; and
4. class-complete impossibility of moving-gauge screening.

The scientific delta is this source-specific uniformity and its exact screening classification.
External priority remains unverified.

## Lean target

Formalize unconditionally:

1. pointwise normalized-current bound `(J.63)`;
2. arbitrary moving-family zero-charge law `(J.64)`;
3. exact Taylor-transfer limit `(J.65)`;
4. screening iff `xi(sigma)!=0`;
5. literal arbitrary-`L_n`, arbitrary-`N_n>0` theta-packet corollary.

No new axiom, computation, zero hypothesis, RH hypothesis, or fixed-family assumption is allowed.

## Signed extension — linear cancellation conditioning is necessary

The positive theorem leaves real signed densities. Their exact source singularity can be measured
without assuming a limiting gauge.

For real `h`, define absolute completion mass

```text
V_h(z) = Re integral_0^infinity |h(t)|(1-exp(i t z)) dt >= 0.           (J.69)
```

Whenever the signed derivative and absolute completion are integrable, the same pointwise kernel
inequality gives

```text
||G'_h(z)|| <= V_h(z)/Im z.                                             (J.70)
```

Whenever `G_h(z)!=0`, define the intrinsic cancellation condition number

```text
kappa_h(z) = V_h(z)/||G_h(z)||.                                        (J.71)
```

This is a literal source cancellation condition number. Positive `h` has `kappa<=1`; a signed
density can have large `kappa` only when its positive and negative completion vectors nearly
cancel. From `(J.62)`, `(J.70)`, and `(J.71)`,

```text
|Im(D/F)| <= (kappa_h(z)+1)/Im z.                                       (J.72)
```

Now assume `xi(sigma)=0`, put

```text
m   = analyticOrderAt(xi,sigma).toNat > 0,
eta = 1/2-sigma.re > 0,
```

and suppose the signed moving gauge screens the finite-Taylor charge. Exact charge subtraction
forces

```text
x_n Im(D_n/F_n) -> m.
```

Eventually the left side exceeds `m/2` and `Im z_n>eta/2`. Combining this with `(J.72)` gives

```text
m eta/4 < x_n(kappa_(h_n)(z_n)+1).
```

The explicit mesh inequality `x_n<2/(n+1)` therefore yields the sharp necessary growth

```text
(m eta/8)(n+1) < kappa_(h_n)(z_n)+1                     eventually.   (J.73)
```

Thus a signed scalar transgression cannot screen through bounded, slowly growing, or merely
non-normal conditioning. It must arrange at least linear positive/negative cancellation in the
literal completion norm. This is an unconditional no-go rate, not an RH-equivalent estimate:
under a hypothetical divisor it classifies every successfully screening signed density.

The remaining scalar-density survivor is now a linearly ill-conditioned signed source whose
boundary terms still satisfy the exact integration-by-parts connection. Relation-valued channels
remain outside this scalar condition-number theorem.

### Non-theatre check

`(J.73)` is not the definition of screening rewritten. Screening controls the signed logarithmic
phase current. `kappa_(h_n)(z_n)` is the exact, independently source-visible ratio comparing the positive absolute
completion `(J.69)` with the signed completion before logarithmic division. The proof converts a
divisor-current requirement into a quantitative cancellation law on the source measure itself.

### Additional Lean target

Formalize:

1. signed derivative variation bound `(J.70)`;
2. exact condition-number logarithmic-current bound `(J.72)`;
3. exact transfer of screening to gauge charge;
4. eventual linear lower bound `(J.73)`.
