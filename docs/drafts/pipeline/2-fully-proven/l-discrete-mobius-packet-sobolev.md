# Route L: all-order discrete Möbius packet identity

- **ID:** L-DISCRETE-MOBIUS-PACKET-SOBOLEV
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** Literal finite Möbius coefficients and the corpus Gamma--Hankel packet expansion
- **Lean status:** Cubic source-packet identity, its positive energy square sum, and its exact Route L source identification are formalized in `MobiusReciprocalDiscretePacketBridge`; general `J`, finite horizon, and two-sided critical source aperture remain paper-level

## Theorem

Fix an integer `J≥1`, real `delta≥0`, and cutoff `N≥1`. For `1≤n≤N`, put

```text
q_n = (n-1)/(n+1),
b_k = sum_(1≤n≤N) mu(n)/(n+1)^(1+delta) * q_n^k,
Delta_2^m b_k = sum_(h=0)^m (-1)^h binom(m,h) b_(k+2h).
```

The finite order-`J+delta` Route L source energy is

```text
B_(J+delta,delta)(N)
  = sum_(1≤m,n≤N) mu(m)mu(n) (mn)^(J-1)/(m+n)^(2J-1+delta)
  = 2^(delta-2J+3) * sum_(k≥0)
      binom(2J-2+delta+k,k) * (Delta_2^(J-1) b_k)^2.        (1)
```

Every summand on the right is nonnegative. In particular, the cubic hard target of Route L has the exact representation

```text
B_(3+delta,delta)(N) = 2^(delta-3) * sum_(k≥0)
    binom(4+delta+k,k) * (b_k-2b_(k+2)+b_(k+4))^2.         (2)
```

Thus the outstanding cutoff-uniform cubic energy estimate is **exactly** a weighted discrete second-difference estimate for the *literal* order-one Möbius packets. Formula (2) is an identity, not that estimate. The already formalized Gamma--Hankel bounded-return and order-transfer theorems imply RH if its right-hand side has a cutoff-independent bound along an unbounded sequence of `N` for arbitrarily small positive `delta`.

## Proof

Write `r=2J-1+delta` and `a_J(n)=mu(n)n^(J-1)`. The corpus theorem `RHTower.MobiusRenewalPacketEnergy.finiteGammaHankelEnergy_packetExpansion` applies to the shifted coefficient vector `a_J(n+1)` and yields

```text
B_(J+delta,delta)(N)
  = 2^r * sum_(k≥0) binom(r+k-1,k) * c_(J,k)^2,
c_(J,k) = sum_(1≤n≤N) mu(n)n^(J-1)/(n+1)^r * q_n^k.      (3)
```

The generic theorem has a factor `Gamma(r)` on each side, so it cancels because `r>0`. Its finite source sums justify the binomial-series interchange. The exact algebraic identity

```text
1-q_n^2 = 4n/(n+1)^2
```

gives

```text
c_(J,k) = 4^(-(J-1)) * sum_(1≤n≤N)
  mu(n)/(n+1)^(1+delta) * q_n^k * (1-q_n^2)^(J-1)
        = 4^(-(J-1)) * Delta_2^(J-1) b_k.                 (4)
```

The second equality is the ordinary finite binomial theorem and interchange of two finite sums. Substituting (4) in (3) gives the constant `2^r/4^(2J-2)=2^(delta-2J+3)`, proving (1). Setting `J=3` proves (2). For a one-atom check, `N=1` gives `b_0=2^(-1-delta)` and `b_k=0` for `k>0`; (2) equals `2^(-5-delta)`, the direct `(m,n)=(1,1)` kernel value.

The [Lean module](../../../../formal/GaloisForLFunctions/RHTower/MobiusReciprocalDiscretePacketBridge.lean) proves the exact cubic packet identity as `cubic_sourcePacket_eq_stepTwoDifference`, combines it with the generic positive expansion as `cubicGammaHankelEnergy_eq_stepTwoDifference`, identifies the same literal finite source as `cubicGammaHankelEnergy_eq_routeL`, and cancels the nonzero Gamma factor in `routeLCubicEnergy_eq_packetSecondDifference`. The module is wired into `RHTower.lean` and passed targeted `lake --old build GaloisForLFunctions.RHTower.MobiusReciprocalDiscretePacketBridge`. No RH estimate is asserted by these identities.

## Unconditional finite packet horizon (paper proof)

For the cubic case and `0≤delta≤1`, write `c_k=(b_k-2b_(k+2)+b_(k+4))/16`, so (3) is `B_(3+delta,delta)(N)=2^(5+delta)sum_k binom(4+delta+k,k)c_k²`. Uniformly in `N≥1`,

```text
|c_k| ≤ (3/2) exp(-2k/(N+1)),
binom(4+delta+k,k) ≤ binom(k+5,5) ≤ (k+5)^5/120.        (5)
```

Indeed `0≤q_n=1-2/(n+1)≤exp(-2/(n+1))`, and the absolute coefficient sum is bounded by `sum_(n≥1)n^(-3)≤1+integral_1^infinity x^(-3)dx=3/2`. The binomial bound follows by comparing the positive factors in its finite product, since `5+delta≤6`. Splitting the exponential into two equal factors, for every `K≥0`,

```text
0 ≤ 2^(5+delta) sum_(k≥K) binom(4+delta+k,k)c_k²
  ≤ C (N+1)^6 exp(-2K/(N+1))                         (6)
```

with an absolute constant `C`. For the last step, bound `sum_(k≥0)(k+5)^5 exp(-2k/(N+1))` by `5^5+integral_0^infinity (x+6)^5 exp(-2x/(N+1))dx`, which is `O((N+1)^6)` for `N+1≥2`. Thus for every requested `P>0`, the choice

```text
K_P(N)=ceil(((P+6)/2)*(N+1)*log(N+1))
```

makes the omitted positive tail `O_P((N+1)^(-P))`, uniformly in `0≤delta≤1`. A cutoff-uniform cubic energy bound is therefore equivalent to the same bound for the **finite** packet range `0≤k<K_P(N)`; the hard arithmetic lies below an `O(N log N)` packet horizon. This horizon theorem is still open in Lean.

## Source-index aperture at the cubic threshold (paper proof)

The finite horizon can also be narrowed in the *source* index. Fix any `A` with `0<A≤4`, and take a threshold `k_A` large enough for the estimates below. For `0≤delta≤1`, `N≥1`, and `k≥k_A`, put

```text
L_k=floor(A*k/log k),
a_delta=(5+delta)/(4+2delta),
U_k=ceil(k^a_delta),
c_k^mid=sum_(L_k<n≤min(N,U_k)) mu(n)n²/(n+1)^(5+delta) q_n^k.
```

For `k<k_A`, set `c_k^mid=c_k`. There is a constant `C_A` independent of `N` and `0≤delta≤1` such that

```text
sum_(k≥0) binom(4+delta+k,k) |c_k-c_k^mid|² ≤ C_A.        (7)
```

Indeed the binomial weight `w_k` obeys `w_k≤e^5 k^(4+delta)` for `k≥1`: its finite product is `prod_(j=1)^k(1+(4+delta)/j)`, and `log(1+x)≤x`, `sum_(j=1)^k 1/j≤1+log k`. For the low-index portion, put `R=L_k+2` and `t=2k/R`. Since `n²/(n+1)^(5+delta)≤(n+1)^(-3-delta)` and `q_n^k≤exp(-2k/(n+1))`, its absolute value is at most `sum_(m=2)^(L_k+1) m^(-3-delta)exp(-2k/m)`. Choose `k_A` so large that `R≤k/2`. The summand is then increasing up to `R`, uniformly in `delta≤1`, and comparison with its integral gives

```text
|c_k^low| ≤ int_0^R x^(-3-delta) exp(-2k/x) dx
          = (2k)^(-2-delta) int_t^infinity u^(1+delta) exp(-u) du
          ≤ C (2k)^(-2-delta) t^(1+delta) exp(-t).      (7-low)
```

The last inequality is uniform for `t≥1`, `0≤delta≤1`: write `u=t+v` and use `(t+v)^(1+delta)≤t^(1+delta)(1+v)^2`. Since `R≤A*k/log k+2`, enlarging `k_A` if necessary gives `t≥(2/A)log k-1` and `t≤C_A log k`. Thus `|c_k^low|≤C_A k^(-2-delta-2/A)(log k)^(1+delta)`. Its weighted square is at most `C_A k^(-delta-4/A)(log k)^4`, which is summable uniformly in `delta` when `A<4`.

The **critical lower endpoint `A=4`** also works by using (7a). Set `L=floor(4k/log k)` and `H=floor(L/2)`, with `k` large enough that `L≤k/2`. The portion `n≤H` obeys the preceding absolute argument with an effective aperture `<4` (for example `H+2≤3k/log k` eventually), so its weighted square sum converges. On the remaining interval `H<n≤L`, the real kernel `g_k(x)` defined below is increasing: for `2≤x≤L≤k/2`,

```text
g_k'(x)/g_k(x)
  = 2/x-(5+delta)/(x+1)+2k/(x²-1)
  ≥ -4/x+2k/x² ≥ 0.
```

For `H≤x≤L`, slow variation gives `E(x)≤C E(L)`: indeed `0≤log L-log x≤log 3`, and the difference of their cube roots is at most `(log 3)^(1/3)`. Finite Abel summation on `(H,L]`, (7a), monotonicity of `g_k`, and `x≤L` therefore give

```text
|sum_(H<n≤min(N,L)) mu(n)g_k(n)|
  ≤ C E(L) L g_k(L)
  ≤ C E(L) k^(-5/2-delta) (log k)^(2+delta).     (7-low-end)
```

For `N<L`, replace `L` by `min(N,L)` in Abel summation; its boundary and variation are still bounded by `L g_k(L)`. The last inequality uses `L≈4k/log k` and `exp(-2k/(L+1))≤C k^(-1/2)`. After squaring and multiplying by `w_k`, the upper-half bound is `C k^(-1-delta)(log k)^(4+2delta) E(L)^2`. Its series converges uniformly in `0≤delta≤1`, because `log L≥(log k)/2` eventually and therefore `E(L)^2≤exp(-c (log k)^(1/3))`; logarithmic powers are integrable against this decay in the measure `dk/k`. This proves the low-edge part of (7) at `A=4` as well. The critical constant `4` is where the absolute estimate alone becomes harmonic at `delta=0`.

The critical high-index edge uses the already proved Mertens saving in `DeningerMertensSummatory`: after absorbing finitely many initial values into the constant,

```text
|M(x)| ≤ C_M x E(x),
M(x)=sum_(n≤x) mu(n),
E(x)=exp(-(log x)^(1/3)/108),                  x≥1.        (7a)
```

For real `x≥U_k≥k≥k_A`, let `g_k(x)=x²(x+1)^(-5-delta)((x-1)/(x+1))^k`. We have `0≤g_k(x)≤x^(-3-delta)`. Differentiating its two positive factors gives the uniform bound

```text
|g_k'(x)| ≤ 8x^(-4-delta)+2k x^(-5-delta)
          ≤ 10x^(-4-delta).                              (7b)
```

For `N>U_k`, finite Abel summation of `sum_(U_k<n≤N) mu(n)g_k(n)` has boundary terms `M(N)g_k(N)-M(U_k)g_k(U_k)` and integral `-int_(U_k)^N M(x)g_k'(x)dx`. Since `E` is decreasing on `[1,infinity)`, (7a)--(7b) bound these uniformly by

```text
|c_k^high| ≤ C_H E(U_k) U_k^(-2-delta)
            ≤ C_H E(k) k^(-a_delta*(2+delta)),            (7c)
```

with an absolute `C_H`; when `N≤U_k`, the high portion is zero. The definition of `a_delta` gives `a_delta(4+2delta)=5+delta`, so (7c) and the binomial bound imply

```text
w_k |c_k^high|² ≤ e^5 C_H² k^(-1) E(k)².               (7d)
```

The series on the right converges: after `u=log x`, its integral comparison is a constant times `int_(log k_A)^infinity exp(-2u^(1/3)/108)du<infinity`. The square of the sum of the low and high portions is at most twice the sum of their squares, proving (7). The exponent `a_delta` is the exact threshold where an *absolute-value* high-index estimate has harmonic `k^(-1)` energy; the unconditional Mertens saving supplies the missing summability at this threshold. If one uses only absolute values, `U_k=ceil(k^(a_delta+epsilon))` for any fixed `epsilon>0` also gives (7), with a constant depending on `epsilon`.

By the triangle inequality in weighted `ℓ²`, the full cubic packet norm is bounded along any sequence of cutoffs if and only if the middle norm is bounded there, up to the fixed error norm `sqrt(C_A)`. Taking the sharp choice `A=4` and combining (7) with the finite packet horizon above gives a **finite source-and-packet wedge** criterion: for any fixed `P>0`, the Route L RH receiver is supplied by a cutoff-independent bound along unbounded `N` for

```text
sum_(k_4≤k<K_P(N)) w_k
  |sum_(floor(4k/log k)<n≤min(N,ceil(k^a_delta)))
       mu(n)n²/(n+1)^(5+delta) q_n^k|².                   (8)
```

The finitely many `k<k_4` have a uniform absolute bound, and the full tail beyond `K_P(N)` is `O_P(N^(-P))`. Conversely, a bounded full energy bounds (8). Thus the unresolved cancellation is confined to the literal Möbius coefficients inside this **two-sided critical wedge**; neither edge can cause failure. Both critical endpoint proofs use the proved Mertens rate and remain paper-level; the full-to-middle equivalence follows from the already formalized exact cubic packet identity once (7) is formalized.

## Open arithmetic producer

The identity isolates the exact sequence to control: the step-two second difference of `b_k`, with weight growing like `k^(4+delta)`. The source-index aperture further shows that only `4k/log k≲n≲k^a_delta` can carry the missing arithmetic gain. The corpus proves adjacent-order recurrences and sign laws for `b_k` in `MobiusPacketDifferenceSign`, but no cutoff-uniform weighted square bound for that wedge. The next conjecture must exploit the actual Möbius signs across its source indices and packets; the edge estimates do not supply that gain.
