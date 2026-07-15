# The prime-seam damping aperture law

- **ID:** `prime-seam-damping-aperture-law`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / BRIDGE / NOT NEW SCIENTIFIC KNOWLEDGE
- **Source:** `PrimeClockShaleDiagonal.lean`, `XiPrimeSeamCoherenceCollapse.lean`,
  `XiPrimeSeamReflectionEnergy.lean`, and `GammaDampedPrimeLogCauchyDomain.lean`
- **Statement:** `[PROVED HERE]` The exact power damping needed to make the reflected prime seam
  square-summable is the horizontal reflection charge
  `|2*sigma-1|`. Consequently any family of source estimates with arbitrarily small positive
  power loss forces that charge to vanish, whereas every fixed positive loss sees only a strip.

## Goal

Interpolate sharply between two already formalized endpoints:

- the undamped prime-clock reflection energy is summable only on the critical line;
- the canonical reciprocal-prime/Gamma-damped logarithmic seam is summable at every point of the
  open critical strip.

The interpolation determines exactly what the damping erased. It gives a positive source-side
target: recover the seam with arbitrarily small power loss. This is not itself a proof of RH and
does not infer a source estimate from zero-divisor information.

## Gates

- [x] 0 -> 1 in-progress: exact weighted series and source use are explicit.
- [x] 1 -> 2 fully-proven: complete comparison proof below; no open mathematical dependency.
- [ ] 2 -> 3 formalized: formalize the real-power threshold and the cofinal-loss RH consumer.
- [ ] 3 -> 4 publication-ready: the theorem is a direct prime-series comparison and is classified
  as bridge infrastructure rather than new scientific knowledge.

## Reflected seam and damping aperture

For `sigma, theta in R` with `theta >= 0` and a rational prime `p`, put

```text
A_p(sigma) = p^(-sigma) - p^(-(1-sigma)),
C_p(sigma) = log(p) A_p(sigma).
```

The first is the real amplitude underlying `primeClockReflectionEnergy`. The second has exactly the
norm of `orbitwiseNatPrimeSeamCharge p rho` whenever `Re(rho)=sigma`: the two complex terms have the
same phase `p^(i Im(rho))`.

Define the power-damped square energies

```text
E_amp(theta,sigma) = sum_p p^(-theta) |A_p(sigma)|^2,
E_log(theta,sigma) = sum_p p^(-theta) |C_p(sigma)|^2.
```

### Damping-aperture theorem `[PROVED HERE]`

For every real `sigma` and every `theta >= 0`, writing

```text
delta = |sigma-1/2|,
```

one has

```text
E_amp(theta,sigma) < infinity
  iff delta=0 or theta>2*delta,

E_log(theta,sigma) < infinity
  iff delta=0 or theta>2*delta.                 (1)
```

Equivalently, for either energy,

```text
inf {theta>0 : E(theta,sigma)<infinity}
  = 2|sigma-1/2|
  = |2*sigma-1|.                                (2)
```

Thus the summability aperture is exactly the horizontal FE--Schwarz reflection charge.

### Proof

At `sigma=1/2`, both seams vanish prime by prime, so both series are zero for every `theta`.

Suppose `delta>0`. Reflection `sigma |-> 1-sigma` changes the sign of `A_p` and preserves its
absolute value, so it is enough to take `sigma=1/2-delta`. Then

```text
A_p(sigma)
  = p^(-1/2+delta) (1-p^(-2delta))
```

and hence

```text
p^(-theta)|A_p(sigma)|^2
  = p^(-1-(theta-2delta)) (1-p^(-2delta))^2.     (3)
```

For every prime `p>=2`,

```text
0 < (1-2^(-2delta))^2
    <= (1-p^(-2delta))^2
    <= 1.                                       (4)
```

Therefore the amplitude series has the same convergence behavior as

```text
sum_p p^(-s),   s=1+theta-2delta.
```

The prime power series converges for `s>1`. For `s<=1`, each term is at least `1/p`, and Euler's
prime harmonic divergence applies. This proves the first equivalence in `(1)`.

For the logarithmic seam, multiply `(3)` by `(log p)^2`. If `s>1`, choose
`epsilon=(s-1)/2>0`; the elementary eventual bound `(log x)^2 <= x^epsilon` compares the tail with
`sum_n n^(-(1+epsilon))`. If `s<=1`, `log p >= log 2>0` gives a positive constant multiple of the
already divergent prime harmonic series. This proves the second equivalence. The infimum statement
`(2)` follows immediately. QED

## Exact consequences for the RH corpus

### Fixed damping gives only a band

For any fixed `theta>0`, summability of the weighted seam forces exactly

```text
|Re(rho)-1/2| < theta/2,                         (5)
```

unless the point is already on the critical line. In particular, `theta=1` accepts every point in
the open strip `0<Re(rho)<1`. This explains structurally why the inverse-prime factor supplied by
the canonical Gamma diagonal in `GammaDampedPrimeLogCauchyDomain.lean` repairs the Hilbert domain
but cannot orient Xi zeros.

No fixed positive damping exponent can prove RH from this summability assertion alone: it leaves an
open horizontal band of undetected off-line points.

### Cofinal vanishing loss kills the horizontal charge

Let `rho` be any point. If

```text
for every epsilon>0,
  sum_p p^(-epsilon) |orbitwiseNatPrimeSeamCharge p rho|^2 < infinity,
```

then `(1)` gives

```text
|2 Re(rho)-1| < epsilon
```

for every `epsilon>0`. Hence `Re(rho)=1/2`, and every prime seam charge vanishes termwise.

Applied to all Xi divisor fibres, this gives the non-circular implication

```text
arbitrarily-small-loss prime-seam summability on every Xi fibre
  -> all horizontal charges vanish
  -> xiHurwitzOrientationEnergy=0
  -> RH.                                         (6)
```

The last two arrows already exist in Lean. The new first arrow is the exact threshold calculation;
the source production of its premise remains open.

### Relation to prime coherence

`XiPrimeSeamCoherenceCollapse.lean` already proves a stronger conclusion from a different input:
if all prime seam charges on an open-strip fibre have one common value, cofinal decay forces that
common value to be zero. Thus no separate common-charge normalization remains in the coherence
route.

The present theorem supplies a second positive interface that does not assume pairwise coherence:
it is enough to place the individual seam in every positively damped prime Hilbert space. In source
terms, a successful argument must either

1. remove the Gamma inverse-prime loss completely;
2. produce estimates for a family of losses `theta -> 0+`; or
3. build a relative trace whose cancellation has the same effect.

Any theorem that stops at one fixed `theta>0` is a strip theorem, not an RH theorem.

## Corpus placement and formalization surface

The endpoint `theta=0` is `summable_primeClockReflectionEnergy_iff` in
`PrimeClockShaleDiagonal.lean`. The open-strip endpoint `theta=1` for the logarithmic Xi seam is
provided by `XiPrimeSeamPairAsymptotics.lean` and identified as a reflection second difference in
`XiPrimeSeamReflectionEnergy.lean`. `GammaDampedPrimeLogCauchyDomain.lean` supplies the analytic
meaning of that inverse-prime loss on the regular Cauchy core.

A direct Lean module should expose:

```text
summable_weightedPrimeClockReflectionEnergy_iff
summable_weightedNatPrimeSeamCharge_norm_sq_iff
primeSeamDampingAperture_eq_abs_two_mul_sub_one
riemannHypothesis_of_allPositivePrimeSeamDamping
```

The proof should reuse the existing prime-harmonic divergence and logarithmic prime-power
summability lemmas. No new zero-set axiom, density statement, or limiting measure is needed.

## Status

- `[PROVED]` The exact damping threshold is `|2*sigma-1|`.
- `[PROVED]` Reciprocal-prime damping is orientation-blind on the whole open critical strip.
- `[PROVED]` Arbitrarily-small-loss seam summability forces the charge to vanish.
- `[OPEN SOURCE INTERFACE]` Derive the all-positive-loss estimates from an Euler--Gamma value
  relation, rather than assuming them on Xi zero fibres.
- `[ROUTE FILTER]` Reject every fixed-power Hilbert-domain repair as a proposed RH closure unless
  it also contains a mechanism that sends the power loss to zero.

## Log

- 2026-07-15 — exact interpolation theorem proved on paper and connected to the prime-clock,
  Gamma-damped Cauchy, prime-coherence, and Xi--Hurwitz orientation surfaces.
