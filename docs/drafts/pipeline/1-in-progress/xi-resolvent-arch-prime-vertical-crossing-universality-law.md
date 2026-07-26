# Xi resolvent arch-prime vertical crossing universality law

Status: **Stage 3 — formalized in Lean**

## Discovery

Whole-corpus theorem-posting closure joined:

- `XiResolventArchPrimeSplit`: at every real Euler point `s=1/2+x`, `x>1/2`, the normalized Xi
  current lies strictly below its pole-plus-Gamma benchmark, with a positive gap at least the
  prime-2 atom; and
- `XiWardInteriorSourceBudgetDivergence`: on the vertical line through the same Euler point, the
  real Xi logarithmic current tends to `+∞`.

No exact benchmark-crossing theorem occurs in either module or in the corpus research index.

## Universal law

For `x>1/2`, define

`J_x(t) = Re logDeriv(xi)(1/2+x+it) / x`

and let `A_x` be the normalized pole-plus-real-Gamma expression at height zero.  Then:

1. `J_x(0) < A_x`, with gap at least
   `log(2) · 2^(-(1/2+x)) / x > 0`;
2. `J_x(t) → +∞` as `t→+∞`; and therefore
3. there exists `t_x>0` with `J_x(t_x)=A_x`.

Thus every strict-right Euler ray has a forced positive-height archimedean benchmark crossing: the
prime current creates the initial negative displacement, while vertical Gamma growth forces exact
recrossing.

## Dependency-closed paper proof

1. `xiResolventMoment_zero_eq_logDeriv` identifies `J_x(0)` with the real zeroth resolvent moment.
2. `re_xiResolventMoment_zero_add_primeTwo_le_arch` gives
   `J_x(0) + log(2)·2^(-(1/2+x))/x ≤ A_x`.
3. Every factor in the prime-2 term is positive for `x>1/2`; hence `J_x(0)<A_x`.
4. `re_logDeriv_xi_vertical_tendsto_atTop` gives divergence of the unnormalized current; division
   by positive `x` preserves divergence.
5. Choose `T>0` with `A_x<J_x(T)`.
6. On `0≤t≤T`, `Re(1/2+x+it)>1`, so `xi_ne_zero_of_one_le_re` excludes poles of `logDeriv xi`.
7. Entire analyticity of `xi` implies continuity of its logarithmic derivative on this zero-free
   segment.
8. Intermediate value theorem gives `t_x∈(0,T)` with `J_x(t_x)=A_x`.

No RH assumption or computation enters.

## Formal targets

- `xiNormalizedVerticalEulerCurrent`
- `xiEulerArchimedeanBenchmark`
- `xiNormalizedVerticalEulerCurrent_zero_lt_benchmark`
- `xiNormalizedVerticalEulerCurrent_tendsto_atTop`
- `exists_pos_xiNormalizedVerticalEulerCurrent_eq_archimedeanBenchmark`
- `xi_resolvent_archPrime_verticalCrossingUniversality`

## Novelty audit

Post-proof searches covered `Riemann xi logarithmic derivative + vertical line + archimedean
benchmark crossing`, `prime-Gamma decomposition + vertical crossing`, and `zeta logarithmic
derivative + prime-2 gap`.  Results treated off-critical-line arguments, omega theorems for
`ζ'/ζ`, generic Xi product formulae, or bounds on logarithmic derivatives.  None stated the
height-zero prime gap together with forced recrossing of the same pole-plus-Gamma benchmark.
Representative adjacent sources:

- [The argument of the Riemann Xi-function off the critical line](https://arxiv.org/abs/0904.1051)
- [Omega Theorems for Logarithmic Derivatives of Zeta and L-functions Near the 1-line](https://arxiv.org/abs/2404.17250)
- [Bounding the log-derivative of the zeta-function](https://doi.org/10.1007/s00209-021-02820-9)
- [Riemann xi-function, Encyclopedia of Mathematics](https://encyclopediaofmath.org/wiki/Riemann_xi-function)

No exact collision found in this scoped audit. **[NOVELTY UNVERIFIED]**

## Lean formalization

Formal source:
`formal/GaloisForLFunctions/RHTower/XiResolventArchPrimeVerticalCrossingUniversalityLaw.lean`.

Verified with:

`lake env lean GaloisForLFunctions/RHTower/XiResolventArchPrimeVerticalCrossingUniversalityLaw.lean`

Umbrella:
`formal/GaloisForLFunctions/RHTower.lean`.
