# Gamma damping crosses the prime-log half-weight only through nonadditive covariance

- **ID:** `gamma-damped-stationary-prime-log-covariance-law`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper), `[BRIDGE]`
- **Scientific status:** `[PROVED] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Parents:** the archimedean Gamma characteristic, the Euler-log prime-power Herglotz carrier,
  and positive-definite kernel theory
- **Statement:** A canonical diagonally damped Gamma covariance is positive and has exactly enough
  exponential diagonal decay to cross the prime-log half-weight.  Its distinct prime-power
  channels have strictly positive cross terms, however, so its Gram energy cannot equal the
  additive Euler logarithmic derivative.  A successful construction must retain and renormalize
  this covariance rather than identify it with the source trace directly.

## Setup

Let

```text
phi(t)=(cosh t)^(-1/2)
```

be the characteristic function of the normalized archimedean cyclic Gamma measure `mu_infinity`.
For `t>=0`, put

```text
d(t)=sqrt(phi(2t)),
K_Gamma(t,u)=d(t)d(u)phi(t-u).                            (1)
```

## Positive Gamma-sewn covariance

For every finite family `t_1,...,t_n` and complex coefficients `c_1,...,c_n`,

```text
sum_(i,j) conjugate(c_i)c_j K_Gamma(t_i,t_j)
 =int |sum_i c_i d(t_i) exp(i t_i s)|^2 dmu_infinity(s)
 >=0.                                                     (2)
```

Thus `K_Gamma` is positive semidefinite.  This is diagonal congruence of the stationary positive
kernel `phi(t-u)`; it is not the indefinite sum-frequency kernel `phi(t+u)`.

Its diagonal is

```text
K_Gamma(t,t)=phi(2t).                                     (3)
```

For `t>=0`,

```text
exp(-t)<=phi(2t)<=sqrt(2)exp(-t),                         (4)
```

because

```text
exp(2t)/2<=cosh(2t)<=exp(2t).
```

Hence the diagonal supplies exactly one full exponential power.

## Crossing the Cauchy-feature half-weight

At an exponent-one prime-log atom `t=log p`, the Cauchy-feature energy after transport by the
critical half-weight `b=1/2` is proportional to

```text
1/(1+(log p)^2).
```

The prime carrier alone therefore diverges.  Multiplication by the Gamma diagonal gives

```text
phi(2 log p)/(1+(log p)^2)
 <=sqrt(2)/(p(1+(log p)^2)).                              (5)
```

The series on the right converges.  Grouping primes with `exp(m)<=p<exp(m+1)` bounds the `m`-th
block by a constant times `1/m^2`.  Higher prime powers are even smaller.  Therefore the sewn
positive covariance has a well-defined critical-half-weight Cauchy feature even though the prime
facet alone does not.

This proves that the half-weight wall is not an impossibility theorem for every positive sewing;
it is specifically a wall for uncoupled positive prime transport.

## Exact additivity obstruction

For all real `t,u`, every factor in `(1)` is strictly positive.  In particular,

```text
K_Gamma(t,u)>0.                                           (6)
```

For two distinct prime-power atoms with positive amplitudes `a,b`,

```text
||a g_t+b g_u||^2
 =a^2 K_Gamma(t,t)+b^2 K_Gamma(u,u)
   +2ab K_Gamma(t,u),                                    (7)
```

and the last term is strictly positive.

The Euler logarithm and its log-position derivative are additive over prime powers:

```text
log zeta(1+s)=sum_(p,k) exp(-s k log p)/(k p^k),
-zeta'(1+s)/zeta(1+s)=sum_(p,k) log p exp(-s k log p)/p^k. (8)
```

There are no pairwise prime-power terms in `(8)`.  Consequently the coherent Gram energy `(7)`
cannot be identified with the additive source trace.  Orthogonal direct-sum channels restore
additivity but discard the Gamma covariance if they are scalarized separately. The positive
resolution is instead channel-resolved synthesis: use the damped Gamma modes as the columns of one
operator `T`. Then `T^*T` retains every cross covariance in its off-diagonal matrix entries, while
`Tr(T^*T)` reads only the additive diagonal column energy. The theorem is recorded in
`ccm-gamma-damped-cauchy-frame-trace-law.md`.

## Consequence for the countable Gram route

The canonical kernel `(1)` is the first positive source object found in this route that genuinely
crosses the prime-log half-weight.  It does not prove the finite-degree Xi Gram identity.  Instead
it fixes the shape of the missing operation:

```text
Gamma-damped stationary prime covariance
  + resolved prime-channel synthesis before trace
  + exact arithmetic identification of the Gram diagonal
  -> completed principal-relative Gram.                  (9)
```

The prime channels cannot be collapsed to a coherent scalar sum before forming the Gram, because
every cross entry in `(6)` is nonzero. They must remain resolved inside an operator-valued or
relative carrier, matching the principal-shell/Sonin and Gauss-paired quantized-differential
constructions already present in the pipeline.

## Scientific classification

Characteristic-function positivity, diagonal kernel congruence, and the elementary exponential
bounds are standard.  The result is a route bridge, not new scientific knowledge.

## Gates

- [x] canonical positive Gamma-sewn covariance constructed
- [x] exact exponential diagonal decay proved
- [x] critical half-weight Cauchy summability proved
- [x] strict nonadditive cross terms isolated
- [x] construct the channel-resolved Hilbert--Schmidt Gram whose trace is additive
- [ ] identify its diagonal with the exact completed arithmetic source
- [ ] identify the completed finite-degree Gram with the Xi Hankel block
- [ ] RH

## Source-selection caveat

The formula `d(t)=sqrt(phi(2t))` is canonical once one asks to use the diagonal of the Gamma
sum-frequency kernel, but the current Hardy--Titchmarsh square does not select this diagonal
congruence.  It selects multiplication by the exact local symbol and its Euler Gram.  Therefore
`K_Gamma` is a legitimate source-built candidate kernel, not yet the proved compression of the
semilocal trace operator.  A promotion theorem must derive `(1)` from the Gauss-paired local ratios,
Sonin projection, or conductor graph; merely observing that `(1)` uses only `phi` and prime-log
coordinates would not satisfy the source-selection gate.

## Lean progress

`SoninSemilocalTwoPlaceAssociation.lean` now formalizes the exact kernel, strict positivity of every
entry, its diagonal identity, and the exponential upper bound:

```text
semilocalArchimedeanDampedCovarianceKernel
semilocalArchimedeanDampedCovarianceKernel_pos
semilocalArchimedeanDampedCovarianceKernel_self
semilocalArchimedeanCharacteristic_two_mul_le_sqrtTwo_mul_exp_neg
```

The full finite-matrix positive-definiteness statement still uses the classical Gamma Fourier
integral on paper; that spectral-measure identity is not yet represented in the Lean module.

`GammaDampedPrimeLogCauchyDomain.lean` now formalizes the complete finite-packet domain statement.
For arbitrary finite packet data it proves

```text
sum_p phi(2 log p)
  * |sum_j c_j/(z_j-log p)|^2<infinity.
```

For distinct upper-half-plane nodes, the capstone combines this with the prime-only theorem to give
the exact critical carrier transition: the Gamma-damped packet is always summable, while the
undamped critical-half-weight packet is summable exactly when `c=0`. The proof formalizes the
Cauchy-condensation majorant `sum_n 1/(n(log n)^2)<infinity`. This closes the full finite Cauchy-core
domain gate; it does not close the source-selection or relative-trace identity gates.

## Lean certification — 2026-08-19 (stage 2 → 3)

New module: `formal/GaloisForLFunctions/RHTower/SoninSemilocalDampedCovariancePositivity.lean`,
wired into `GaloisForLFunctions.RHTower`; axiom-clean (`propext`, `Classical.choice`, `Quot.sound`
only).  It closes the gap this card recorded ("the full finite-matrix positive-definiteness
statement still uses the classical Gamma Fourier integral on paper").

| Card statement | Lean name |
|---|---|
| `(1)` the sewn kernel | `RHTower.semilocalArchimedeanDampedCovarianceKernel` (pre-existing) |
| `(2)` **positive semidefiniteness of `K_Γ`**, finite-matrix form | `RHTower.semilocalArchimedeanDampedCovarianceKernel_posSemidef` |
| the spectral input: `φ` is a characteristic function | `RHTower.charFun_gammaCyclicMeasure`, `RHTower.positiveDefiniteOnReal_semilocalArchimedeanCharacteristic` |
| `(3)` diagonal identity `K_Γ(t,t) = φ(2t)` | `RHTower.semilocalArchimedeanDampedCovarianceKernel_self` (pre-existing) |
| `(4)` `e^{-t} ≤ φ(2t) ≤ √2 e^{-t}` for `t ≥ 0` | `RHTower.exp_neg_le_semilocalArchimedeanCharacteristic_two_mul` (new lower half) and `RHTower.semilocalArchimedeanCharacteristic_two_mul_le_sqrtTwo_mul_exp_neg` (pre-existing) |
| `(5)` prime-log form `φ(2 log p) ≤ √2/p` | `RHTower.semilocalArchimedeanCharacteristic_two_mul_log_le` |
| `(5)` critical-half-weight Cauchy summability | `RHTower.summable_gammaDampedPrimeLogCauchyPacketEnergy`, `RHTower.gammaDampedPrimeLogCauchyPacket_critical_carrierTransition` (pre-existing) |
| `(6)`,`(7)` strict positivity of every cross entry and the exact additivity obstruction | `RHTower.semilocalArchimedeanDampedCovarianceKernel_pos` (pre-existing), `RHTower.semilocalArchimedeanDampedCovariance_gram_strict_superadditive` |

Reuse note: no new Gamma–Fourier work was needed.  The corpus already owned the archimedean cyclic
spectral probability measure `HTGeometry.gammaCyclicMeasure` with
`∫ e^{ihy} dν = (cosh h)^{-1/2}`, and the universal Bochner Gram law
`GaloisForLFunctions.HTGeometry.positiveDefiniteOnReal_charFun`.  The sewn kernel is their diagonal
congruence, so PSD follows by absorbing the real damping into the coefficients.

Still open on this card, and correctly so, are the RH-facing gates: identifying the Gram diagonal
with the exact completed arithmetic source, identifying the completed finite-degree Gram with the
Xi Hankel block, and RH itself.  Those are open problems, not proved statements.
