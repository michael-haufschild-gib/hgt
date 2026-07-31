# Suzuki critical aperture quarter-shift current

- **ID:** `suzuki-critical-aperture-quarter-shift-current`
- **Stage:** 2 — fully proved on paper
- **Type:** SOURCE THEOREM + REPRESENTATION CHANGE
- **Status:** `[PAPER-PROVED] [LEAN-PROVED CORE] [SOURCE-PURE] [NO RH PREMISE] [NOVELTY UNVERIFIED]`
- **Parent:** `suzuki-rooted-midpoint-compound-gram.md`
- **Statement:** pairing critical Gamma-conormal boundary with true-aperture dyadic innovation
  converts nonsummable rooted coordinate into exact quarter-shift geometric resolvent and an
  absolutely convergent prime current.

## Corpus frontier

`VonMangoldtGammaConormalEulerBoundary.lean` already defines finite current

```text
sum_(p,e in S) conj(G_(-1/2,t)(p,e)) I_(h,a)(p,e),       (Q1)
```

where `G` is uniquely renormalized Gamma--Euler height boundary and `I` cubically normalized true
aperture innovation.  It proves neither depth completion nor critical prime completion.  Existing
critical-root theorem proves `G_(-1/2,t)` is not an `ell^2` vector.  Existing affine-Cauchy theorem
and new hostile audit prove canonical triple-log division still leaves divergent mass.  Thus actual
frontier is topology of `(Q1)`: whether source innovation pairs with distributional critical
boundary before any square is formed.

## Theorem `SUZUKI-CRITICAL-APERTURE-QUARTER-SHIFT-CURRENT`

For prime `p`, put `L=log p`,

```text
q=exp(-L)=1/p,
r=exp(-(h*a/2)L),
g=exp(-L/4),
theta=exp(i*t*L/2),
C=(h*sqrt(h))^-1 * q/(1+q) * (1-r)^2.                (Q2)
```

For `h>0`, `a>0`, exact critical depth atom is

```text
conj(G_(-1/2,t)(p,e)) I_(h,a)(p,e)
  = C*sqrt(L)*(g*theta)*(g*theta*r^2)^e.              (Q3)
```

Therefore

```text
sum_(e>=0) conj(G_(-1/2,t)(p,e)) I_(h,a)(p,e)
  = C*sqrt(L)*(g*theta)/(1-g*theta*r^2).              (Q4)
```

and sum of norms of right side over primes converges.  Consequently finite currents `(Q1)` have
canonical exhaustion-independent cofinal value at critical displacement although critical boundary
alone has no Hilbert vector.

## Derivation and hostile audit

At depth `e`, valuation is `n=p^(e+1)` and `log n=(e+1)L`.  Critical density in existing Gamma
feature is

```text
L/n * exp((1/2)log n)=L*exp(-(e+1)L/2).
```

Its positive square root is `sqrt(L)g^(e+1)`; conjugated height phase is `theta^(e+1)`.  Existing
innovation definition is exactly `C(r^2)^e`.  Multiplication proves `(Q3)`.  Since
`|g*theta*r^2|=exp(-(1/4+h*a)L)<1`, geometric summation proves `(Q4)`.

For prime completion, `q/(1+q)=1/(p+1)`, `0<(1-r)^2<1`, and denominator is uniformly separated
from zero because `p>=2`.  Thus closed current is bounded by a fixed `h`-dependent multiple of

```text
sqrt(log p) / p^(5/4).
```

Using `log p <= 4 p^(1/4)` gives domination by a constant times `p^(-9/8)`, hence absolute
convergence even after enlarging prime sum to all natural numbers.

Hostile checks:

- Critical sign is forced by `u=-1/2`; changing it breaks `g=p^-1/4`.
- Conjugation fixes positive phase `theta`; wrong phase does not affect convergence but falsifies
  exact current.
- Cubic normalization is scalar in depth and does not alter ratio.
- Transverse factor `q/(1+q)=1/(p+1)` supplies full extra inverse prime.  Omitting it returns
  divergent scale.
- Existing quarter-prime calibration concerns exterior height; it does not state `(Q3)--(Q4)` or
  critical cofinal current.  Corpus search found only finite definition `(Q1)`.

Verdict: exact depth law and convergence proof `SURVIVE PRELIMINARY ATTACK`; novelty remains
unverified.  Suzuki's 2022 source has `Lambda(n)/sqrt(n)` and 2026 finite-interval construction is
unconditional, but source audit found no true-aperture quarter-shift current.

## Scientific consequence

Critical obstruction is not repaired by more logarithmic filters or by standalone Hilbert
completion.  Correct source category is rigged pairing

```text
critical Gamma boundary (distributional) x aperture innovation (trace class) -> scalar current.
```

The transverse disk factor moves prime scale from `p^-1/4` amplitude to `p^-5/4` current.  This is
the first corpus-derived power-scale cancellation mechanism surviving critical no-go.

New RH-bearing frontier: insert exact current `(Q4)`, with calibrated exterior phase and midpoint
Lorentz debt `d^2`, into global-local compound Bezoutian.  Remaining theorem is sign/Schur
completion of this fixed current, not existence of `L_M` and not cofinal convergence.

## Formalization gate

- [x] Prove actual-source atom identity `(Q3)` in Lean.
- [x] Prove per-prime depth `Summable` and exact `tsum` `(Q4)`.
- [ ] Prove absolute prime summability and define cofinal current.
- [ ] Rewire active compound conjecture to critical current topology.

Lean core:
`formal/GaloisForLFunctions/RHTower/SuzukiCriticalApertureQuarterShiftCurrent.lean`, especially
`suzukiCriticalApertureBoundaryAtom_succ`,
`norm_suzukiCriticalApertureDepthRatio_lt_one`, and
`tsum_suzukiCriticalApertureBoundaryAtom_eq_resolvent`.

## Literature state

- Suzuki 2022 screw source: https://arxiv.org/abs/2206.03682
- Suzuki 2026 finite interval construction: https://arxiv.org/abs/2606.09096
- `[LOCAL-RESEARCH]`: finite current and source coordinates are corpus definitions.
- `[BRIDGE]`: geometric series and p-series convergence are parent analysis; possible novelty is
  exact source-specific quarter-shift pairing and its RH representation consequence.

## Log

- 2026-07-22 — conjectured after canonical affine-Cauchy repair was formally falsified; exact
  source expansion derived and hostile-audited.
