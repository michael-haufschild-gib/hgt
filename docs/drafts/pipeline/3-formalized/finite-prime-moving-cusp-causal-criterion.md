# Finite-prime moving-cusp form of the causal theta criterion

- **ID:** L-PSRC-SQB-MOVING-CUSP
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean; an RH-equivalent finite-source criterion, not an RH proof)
- **Routes:** L, PSRC, SQB
- **Statement:** The causal Möbius–theta boundary observation can be read, to superpolynomial accuracy, from the canonical atom split of one finite prime-deleted theta source at a cusp point moving with the observation scale.

## The finite source and its directed cusp port

Let `k=thetaCuspFullSource`, and let `P_Y` be the product of all primes
`p<=Y`. The finite Euler-deleted source is

```text
k_Y(x) = product_(p<=Y) (1-p^(-1/2) T_(log p)) k(x)
       = sum_(d|P_Y) mu(d)/sqrt(d) * k(x+log d).
```

The **directed positive-ray atom port** at `x=-log N` retains the terms
whose shifted arguments are positive:

```text
B_Y(N) = sum_(d|P_Y, d>N) mu(d)/sqrt(d) * k(log(d/N)).       (1)
```

The direction and the arithmetic atom labels are part of this
observation. The unsplit scalar value `k_Y(-log N)` also includes the
terms `d<=N` and is not (1).

Set `Y_N=N log N` for integers `N>=3`. Then, for every `A>0`,

```text
B_Y_N(N) = B(N) + O_A(N^(-A)),
B(t) = sum_(n>t) mu(n)/sqrt(n) * k(log(n/t)).                (2)
```

Consequently the [causal Möbius--theta criterion](causal-mobius-theta-boundary-criterion.md)
has the entirely finite moving-cusp form

```text
RH  <->  for every epsilon>0, B_Y_N(N)=O_epsilon(N^epsilon). (3)
```

The observation in (3) uses a finite prime set for each `N`; the
prime horizon and cusp position move together. No limit of finite
Green operators or prime-deleted source transforms is assumed.

## Proof

The finite product expansion is the squarefree Möbius identity.
Every integer missing from (1) but present in `B(N)` has a prime
factor larger than `Y_N`, hence is larger than `Y_N`. The explicit
Gaussian theta atom formula used in the causal criterion gives, for
`u>=1`, constants `C,c>0` with

```text
|k(log u)| + |k'(log u)| <= C (1+u)^C exp(-c u^2).          (4)
```

For example, insert
`k(log u)=sqrt(u)*sum_(m>=1) g(m*u)`, where
`g(v)=(4*pi^2*v^4-6*pi*v^2)exp(-pi*v^2)`, and differentiate the
absolutely convergent series. A Gaussian-tail integral bounds the
missing integers by

```text
|B(N)-B_Y_N(N)|
 <= sum_(n>Y_N) n^(-1/2)|k(log(n/N))|
 <= C sqrt(N) (1+log N)^C exp(-c' (log N)^2),              (5)
```

after adjusting positive constants. The last expression is
`O_A(N^(-A))` for every fixed `A`.

The criterion quoted above is stated for all real `t>=1`. It suffices
to check integers. For `N<=t<N+1`, the defining sum has the same
indices as `B(N)`. Differentiating each summand and using (4) shows

```text
|dB(t)/dt| <= (1/t) sum_(n>t) n^(-1/2)
                         |k'(log(n/t))| = O(N^(-1/2)).      (6)
```

The estimate follows by comparison with the integrable Gaussian
profile after `n=t u`. At `t=N+1`, the excluded single term has size
at most `k(0)/sqrt(N+1)`. Thus

```text
sup_(N<=t<=N+1) |B(t)-B(N)| = O(N^(-1/2)).                  (7)
```

Equations (2) and (7) transfer the subpower condition in the causal
criterion to (3), in both directions.

## Quantitative off-line witness

Suppose `rho` is a zeta zero with `1/2<Re rho<1`, and set
`v=Re rho-1/2>0`. The causal criterion proves that the Mellin
transform of `B` has a pole at `w=rho-1/2`, with order equal to the
zero multiplicity. Hence for every `0<delta<v`,

```text
limsup_(N->infinity) N^(-v+delta) * |B_Y_N(N)| = infinity. (8)
```

Indeed, a bound `B_Y_N(N)=O(N^(v-delta))` would give the same bound
for `B(t)` by (2) and (7). Its Mellin integral would then be
holomorphic on `Re w>v-delta`, contradicting that pole. This identifies
the horizontal distance of a hypothetical off-line zero as a forced
power-growth exponent of a finite, source-labelled moving-cusp port.
It does not bound that port from above.

## What this changes

The [prime-deletion mode theorem](sqb-prime-deletion-causal-mode-escape.md)
shows that fixed-cusp local convergence loses a nonzero negative-cusp
radiation trace. Equations (1)--(3) and (8) identify an RH-sensitive
**moving** boundary port of the same finite deletion family. Any
proposed SQB or L source estimate can now be tested on the finite,
labelled port (1).
The mathematical producer still missing is a bound on its signed
cross-prime sum. The Gaussian truncation in (5) pays only for primes
beyond the moving horizon; it gives no cancellation among retained
Möbius coefficients. No computations or Lean builds were used.

## Lean formalization (2026-09-27)

The card and the whole criterion it rests on are now formalized unconditionally, in three modules
(all declarations axiom-clean `[propext, Classical.choice, Quot.sound]`, built with
`lake build --old`, warning-free, wired into `RHTower`).

**The causal criterion itself** (previously paper-only on
`theta/causal-mobius-theta-boundary-criterion.md`):

`formal/GaloisForLFunctions/RHTower/CausalThetaHalfLaplace.lean`

| Ingredient | Declaration |
|---|---|
| `K(w) = ∫_0^∞ k(u)e^{wu}du` and its tails are entire (as Mellin transforms) | `thetaHalfLaplace`, `thetaHalfLaplaceTail`, `thetaHalfLaplaceTail_eq_mellin`, `differentiable_thetaHalfLaplaceTail` |
| uniform tail bound used for the entire correction series | `norm_thetaHalfLaplaceTail_le` |
| reflection `K(w) + K(−w) = Ξ(iw)` | `thetaHalfLaplace_add_neg` |
| `k' ≤ 0` on the positive ray, `∫_0^∞ k' = −k(0)` | `deriv_thetaCuspFullSource_nonpos`, `integral_Ioi_deriv_thetaCuspFullSource` |
| integration by parts `wK(−w) = ∫_0^∞ (−k')(1 − e^{−wu})` and **(5)** `Re(wK(−w)) > 0` | `mul_thetaHalfLaplace_neg`, `re_mul_thetaHalfLaplace_neg_pos` |
| `K(ρ − 1/2) ≠ 0` at every zero with `1/2 < Re ρ < 1` | `thetaHalfLaplace_ne_zero_of_riemannZeta_eq_zero` |

`formal/GaloisForLFunctions/RHTower/CausalMobiusThetaTail.lean`

| Ingredient | Declaration |
|---|---|
| `B(t) = ∑_{n>t} μ(n)n^{−1/2}k(log(n/t))`, absolute convergence, measurability | `causalMobiusThetaTail`, `exists_abs_causalMobiusThetaTerm_le`, `measurable_causalMobiusThetaTail` |
| `F(w) = ∫_1^∞ B(t)t^{−w−1}dt`, analytic on `Re w > a` under `B = O(t^a)` | `causalTailMellin`, `differentiableAt_causalTailMellin` |
| the entire correction `H(w) = ∑ μ(n)n^{−w−1/2}∫_{log n}^∞ k(u)e^{wu}du` | `causalTailCorrection`, `differentiable_causalTailCorrection` |
| **(3)** `F(w) + H(w) = K(w)/ζ(w+1/2)` on `Re w > 1/2` (Fubini + substitution `u = log n − x`) | `causalTailMellin_add_correction`, `integral_causalLogIntegrand` |
| growth `O(t^a)` excludes zeros with `1/2 + a < Re ρ < 1` (identity theorem with `(s−1)ζ(s)`) | `causalMobiusThetaTail_growth_excludes_zero` |
| **(6)** Abel summation against Littlewood's Mertens bound | `tsum_sub_mul_eq_abel`, `causalMobiusThetaTail_subpower_of_riemannHypothesis` |
| **(2)** `RH ⟺ ∀ε>0, B(t) = O_ε(t^ε)` | `riemannHypothesis_iff_causalMobiusThetaTail_subpower` |

**This card:** `formal/GaloisForLFunctions/RHTower/CausalMobiusThetaMovingCusp.lean`

| Card item | Declaration |
|---|---|
| finite product expansion = squarefree Möbius identity | `thetaPrimeDeletion_eq_sum_divisors` (corpus `thetaPrimeDeletion` is the operator product) |
| **(1)** directed port `B_Y(N)`, `Y_N = ⌊N log N⌋`; the unsplit value also carries `d ≤ N` | `finitePrimeCausalPort`, `movingCuspHorizon`, `movingCuspPort`, `thetaPrimeDeletion_neg_log_eq_add_port` |
| missing integers have a prime factor above the horizon | `lt_of_causalMobiusThetaTerm_ne_zero_of_notMem_divisors`, `abs_causalMobiusThetaTail_sub_port_le` |
| **(4)** `\|k(log u)\| + \|k'(log u)\| ≤ C(1+u)^C e^{−cu²}` for `u ≥ 1` | `exists_abs_iteratedDeriv_thetaCuspFullSource_le_gaussian`, `exists_thetaCuspFullSource_log_gaussian_bound` |
| **(5)** `\|B(N) − B_{Y_N}(N)\| ≤ C√N(1+log N)^C e^{−c'(log N)²}` | `exists_tsum_missing_le_gaussian`, `exists_abs_causalTail_sub_movingCuspPort_le_gaussian` |
| **(2)** `B_{Y_N}(N) = B(N) + O_A(N^{−A})` for every `A` | `exists_abs_movingCuspPort_sub_le` |
| **(7)** `sup_{N≤t≤N+1}\|B(t) − B(N)\| = O(N^{−1/2})` (MVT on `k`, jump term at `N+1`) | `exists_abs_causalMobiusThetaTail_sub_le_unitInterval` |
| **(3)** `RH ⟺ ∀ε>0, B_{Y_N}(N) = O_ε(N^ε)` | `riemannHypothesis_iff_movingCuspPort_subpower` |
| **(8)** off-line zero ⇒ `limsup N^{−v+δ}\|B_{Y_N}(N)\| = ∞` for `0<δ<v` | `not_eventually_movingCuspPort_le_of_riemannZeta_eq_zero`, `frequently_lt_abs_movingCuspPort_of_riemannZeta_eq_zero` |

The Lean route for (8) uses the growth-exclusion form of the criterion (a bound `O(t^{v−δ})` on
`B` continues the boundary identity past `ρ − 1/2`, forcing `K(ρ − 1/2) = 0`), which is the
content of "the Mellin transform has a pole at `ρ − 1/2`" that the card uses.

## Gates
- [x] 1 → 2: complete paper proof
- [x] 2 → 3: every statement formalized, unconditional, axiom-clean

- 2026-09-27 — causal criterion and moving-cusp card formalized; moved to 3-formalized.
