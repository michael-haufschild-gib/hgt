# Exact critical renewal law for the Möbius–Laplace transform

## Status

Stage 3 — formalized in Lean 4.

## Claim

For `x>0`, the dilation series converges absolutely and

`sum_{k>=1} mobiusDiscreteLaplaceTransform(k*x) = exp(-x)`.

Consequently, for

`F(y) = exp(-y/2) * mobiusDiscreteLaplaceTransform(exp(-y))`,

one has the exact critical renewal equation

`sum_{k>=1} k^(-1/2) F(y-log k) = exp(-y/2) * exp(-exp(-y))`.

## Scientific delta

`[CORPUS]` No exact dilation identity or critical log-coordinate renewal law for the concrete
Möbius–Laplace transform was found. Existing Lambert inversion modules concern different weighted
Euler/functional carriers.

`[LITERATURE]` The first identity is a classical Lambert-series consequence of
`sum_{d|n} mu(d) = [n=1]`. The critical-coordinate formulation and its use as a diagnosis of the
Mellin wall were not found as explicit statements, but novelty is limited to synthesis and
normalization. Expected classification: `[NEW TO CORPUS] [CLASSICAL CONSEQUENCE]`.

## Dependency-closed proof obligations

1. Prove absolute summability of the positive-integer double series using
   `nk >= n+k-1` and two geometric series.
2. Apply Tonelli/Fubini and regroup by `m=nk`.
3. Use the divisor identity `sum_{n|m} mu(n)=[m=1]`.
4. Rewrite at `x=exp(-y)`; verify
   `k^(-1/2) exp(-(y-log k)/2)=exp(-y/2)` exactly.

## Frontier interpretation

Fourier/Mellin diagonalization of the critical renewal operator has symbol
`zeta(1/2+i*t)`. Thus ordinary bounded-inverse or coercivity arguments are impossible: the operator
has the same critical zero obstruction as RH. Any source proof must exploit the distinguished
causal Möbius solution, not positivity or a global lower bound for the renewal operator.

## Hostile tests

- Absolute rearrangement must be explicit; conditional double-series manipulation is forbidden.
- Identity alone gives a weighted sum of dilates, not pointwise half-decay.
- Any proposed coercive inverse on all bounded functions is killed by critical-line oscillatory
  modes and must be rejected rather than patched.

## Dependency-closed proof

For positive integers `k,n`, define

`a_x(k,n)=mu(n) exp(-knx)`.

Since `kn >= k+n-1`,

`|a_x(k,n)| <= exp(x) exp(-kx) exp(-nx)`.

The right side is a product of two convergent geometric series, so the double series is absolutely
summable. Its `k`-row is exactly `mobiusDiscreteLaplaceTransform(kx)`. Regrouping by `m=kn` is now
legitimate and gives coefficient `sum_{n|m} mu(n)`, equal to `1` at `m=1` and `0` otherwise. Hence
the total is `exp(-x)`.

For the critical law, substitute `x=exp(-y)` and multiply by `exp(-y/2)`. For every `k>=1`,

`k^(-1/2) F(y-log k) = exp(-y/2) Phi(k exp(-y))`.

Termwise equality preserves absolute summability, and the dilation identity gives the stated
renewal equation.

## Classification

`[PAPER-PROVED] [NEW TO CORPUS] [CLASSICAL CONSEQUENCE]`. The critical normalization is a useful
new connector, but the theorem does not supply half-decay or RH.

## Failed successor audit

- **Global renewal coercivity:** rejected. Mellin/Fourier symbol at critical normalization is
  `zeta(1/2+i*t)`, so any lower bound on the full ambient function space collides with critical
  zeros and with the non-absolutely summable weights.
- **Translation-hull compactness of the actual profile:** rejected as a source conjecture. Point
  evaluation on a compact translation hull already gives boundedness of the critical profile,
  hence simply repackages the missing half-decay.
- **Last open core:** prove cancellation for the distinguished causal Möbius solution from an
  independent arithmetic mechanism. Renewal identity alone contains no contraction or positivity
  capable of producing it.

## Lean formalization

- `summable_mobiusLaplaceLambertPair`
- `tsum_pnat_mobiusDiscreteLaplaceTransform_dilate`
- `summable_pnat_mobiusDiscreteLaplaceTransform_dilate`
- `mobiusLaplaceCriticalRenewalWeight_eq_rpow`
- `summable_mobiusLaplaceCriticalRenewal`
- `tsum_mobiusLaplaceCriticalRenewal`
- Targeted verification:
  `lake env lean GaloisForLFunctions/RHTower/MobiusLaplaceCriterionFrontier.lean`
