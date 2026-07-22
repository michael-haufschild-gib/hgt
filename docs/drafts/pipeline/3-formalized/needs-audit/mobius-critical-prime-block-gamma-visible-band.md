# Möbius critical prime-block Gamma-visible resonance band

- **ID:** `mobius-critical-prime-block-gamma-visible-band`
- **Stage:** 3-formalized
- **Type:** THEOREM / INTEGRATED NO-GO / POSITIVE SURVIVOR
- **Scientific status:** `[PROVED HERE] [FINITE CORE FORMALIZED] [NOVELTY UNVERIFIED]`
  `[NOT AN RH PROOF]`
- **Lean:**
  `formal/GaloisForLFunctions/RHTower/MobiusCriticalPrimeBlockGammaBand.lean`
- **Parent:** `mobius-critical-prime-block-resonance-wall.md`

## Statement

For

```text
W_Y={p prime:Y/3<p<=Y},
B_Y(t)=product_(p in W_Y)(1-p^(-1/2)exp(-it log p)),
I_Y=[pi/logY,4pi/(3logY)],
```

every `Y>=27` and every `t in I_Y` satisfy

```text
|B_Y(t)|^2 >= (1+Y^(-1/2))^(#W_Y).                       (GB1)
```

Thus resonance occupies an interval of exact width

```text
|I_Y|=pi/(3logY),                                        (GB2)
```

not a single Fourier point.  If `w:R->R` is nonnegative and continuous at zero with `w(0)>0`,
then

```text
integral_R w(t)|B_Y(t)|^2 dt -> infinity.                (GB3)
```

In particular every fixed positive Gamma height density sees unbounded terminal-block energy.
Pointwise resonance cannot disappear as a measure-zero spike after Gamma--Hankel localization.

## Finite band proof

For `p in W_Y`, the parent theorem gives

```text
(2/3)logY <= logp <= logY.                               (GB4)
```

For `t in I_Y`, multiplication of positive endpoints yields

```text
2pi/3 <= t logp <= 4pi/3.                               (GB5)
```

Cosine is at most `-1/2` on this full chamber.  The exact local identity

```text
|1-p^(-1/2)exp(-it logp)|^2
 =1+p^(-1)-2p^(-1/2)cos(t logp)
 >=1+p^(-1/2)
 >=1+Y^(-1/2)                                           (GB6)
```

multiplies over `W_Y` and proves `(GB1)`.

## Integrated divergence

The bands `I_Y` shrink to zero.  Continuity and positivity of `w` provide `Y_0` such that

```text
w(t)>=w(0)/2 for t in I_Y, Y>=Y_0.                       (GB7)
```

Therefore `(GB1)`--`(GB2)` give

```text
integral_R w(t)|B_Y(t)|^2dt
 >= w(0)pi/[6logY] (1+Y^(-1/2))^(#W_Y).                 (GB8)
```

The existing Chebyshev window budget gives `#W_Y >> Y/logY`.  Also
`log(1+Y^(-1/2))>=1/(2sqrtY)` for large `Y`.  Taking logarithms in `(GB8)` leaves

```text
c sqrtY/logY - loglogY + O(1) -> infinity,               (GB9)
```

which proves `(GB3)` without zero data, RH, or computation.

## Consequence for Möbius--Laplace source proofs

The Gamma--Hankel identity turns a fixed positive height density into a positive quadratic norm.
The parent card excluded uniform multiplier/operator norms using a synchronized point witness.
`(GB3)` is stronger for the actual proposed source mechanism: even the weighted `L2` energy of the
terminal block applied to the constant input diverges.  Therefore Gamma damping cannot be applied
before terminal-prime cancellation and then expected to regularize the Euler cascade.

This does not bound the naturally truncated additive Möbius transform.  A viable proof may still
cancel several prime blocks against each other before norming, or use a cutoff-dependent signed
projection that removes the entire moving band.

## Hostile audit

1. **Single-point artifact.** Removed by the explicit interval `I_Y`.
2. **Gamma density decay.** The band tends to zero, where every standard Gamma density is positive.
3. **Shrinking width.** Polynomial width `1/logY` is overwhelmed by exponential height
   `exp(c sqrtY/logY)`.
4. **Operator norm versus source vector.** `(GB3)` is a direct integrated-energy lower bound for
   the constant input, not only an essential-supremum statement.
5. **Natural integer truncation.** Not addressed.  Terminal Euler blocks generate multiplicative
   subset apertures, so no claim is made about `sum_(n<=N)mu(n)exp(-nx)`.

## Lean certificate

Lean proves:

- `cos_le_neg_half_of_two_pi_div_three_le_of_le_four_pi_div_three`;
- `mobiusCriticalPrimeWindow_cos_le_neg_half_on_gammaBand`;
- `mobiusCriticalPrimeBlock_norm_sq_lower_on_gammaBand`;
- `mobiusCriticalPrimeGammaBand_width`;
- `integral_weight_mul_mobiusCriticalPrimeBlock_norm_sq_lower_on_gammaBand`;
- `exists_local_half_floor_of_continuousAt_of_pos`;
- `exists_semilocalGammaFloor_on_mobiusCriticalPrimeGammaBand`;
- `exists_semilocalGamma_mobiusCriticalPrimeBlock_energy_lower`.

Direct `lake env lean` verification passes without diagnostics.  The exact weighted band-integral
lower bound `(GB8)` is formalized for any continuous weight with a declared positive band floor.
The actual normalized semilocal Gamma density is proved positive at zero, its eventual band floor
is constructed, and `(GB8)` is specialized to that density.  Only the final elementary asymptotic
divergence step `(GB9)` remains paper-level.

## Literature boundary

Targeted searches covered partial Euler products in the critical strip, finite-Euler-product
resonance, and Gamma-weighted Dirichlet-polynomial norms.  No source located the explicit shrinking
band `(GB1)` or its fixed-Gamma integrated divergence `(GB3)`.  The ingredients are elementary,
and absence of a search match is not a priority claim; status remains `NOVELTY UNVERIFIED`.

## No-go closure

- **Killed mechanism:** Gamma damping of terminal Euler blocks before signed cross-block
  cancellation.
- **Strongest positive survivor:** resonance is a Gamma-visible band of width `Theta(1/logY)` and
  integrated size at least `exp(c sqrtY/logY)/logY`.
- **Required replacement:** cancel/project the moving band before any fixed positive norm.

## Gates

- [x] paper proof of finite resonance band
- [x] paper proof of integrated divergence for every locally positive weight
- [x] finite cosine, block, width, generic weighted-integral, and actual Gamma-floor bounds
  formalized in Lean
- [x] targeted corpus and literature search
- [ ] formalize final asymptotic divergence
- [ ] construct a signed cross-block cancellation theorem
- [ ] RH

## Log

- 2026-07-22 — Upgraded point resonance to positive-width band and proved fixed-Gamma integrated
  divergence; finite core formalized without computation.
