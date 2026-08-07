# Suzuki--Mangoldt macroscopic prime-block surplus

- **Stage:** 3 — formalized in Lean 4
- **Formalized companion:** `./suzuki-mangoldt-macroscopic-prime-block-surplus-formalized.md`
- **Status:** Stage 2 — dependency-closed paper proof
- **Labels:** `[NEW]` `[SUZUKI]` `[SOURCE-SPECIFIC]` `[UNCONDITIONAL]`
- **Stage 1 card:** `docs/drafts/pipeline/1-in-progress/suzuki-mangoldt-macroscopic-prime-block-surplus.md`
- **Open core advanced:** `SUZUKI-APEX-BLOCK-TRANSPORT`

## 1. Universal right-flank law

For `beta >= 0`, `L>0`, define

```text
R_{beta,L}(d) = exp(beta d) (1-d/L),       0 <= d <= L.
```

### Theorem 1 (subcritical tilted-tent antitonicity)

If `beta L < 1`, then `R_{beta,L}` is strictly decreasing on `[0,L]`.  More strongly, for
`0<=r<=L` and every real `C`,

```text
(∀ d in [r,L], R_{beta,L}(d)<=C)  iff  R_{beta,L}(r)<=C.
```

Thus `R_{beta,L}(r)` is the exact least uniform ceiling on the tail.  Consequently
`0<d<=L` implies `R_{beta,L}(d)<1`.

### Proof

Direct differentiation gives

```text
R'_{beta,L}(d)
 = exp(beta d) [beta(1-d/L)-1/L]
 = exp(beta d)/L [beta(L-d)-1].
```

For `0<=d<=L`, nonnegativity of `beta` gives
`beta(L-d)<=beta L<1`.  Since `exp(beta d)/L>0`, the derivative is strictly negative.
The mean-value theorem proves strict antitonicity.  A tail ceiling must dominate the value at its
left endpoint; conversely strict antitonicity makes that endpoint value a ceiling.  Finally
`R_{beta,L}(0)=1`.  QED.

This law is universal: no arithmetic object occurs.

## 2. Width-five aligned Suzuki law

Put

```text
L5    = log 5,
a5(n) = log(5n)/2,
tau(m)= 2 log m,
A_n(t)= exp(t/4) C_{L5,a5(n)}(t/2),
q5    = sqrt(2) (1-log(2)/log(5)).
```

Here `C_{L,a}` is the rectangular two-edge autocorrelation already formalized in the Suzuki lane.

### Lemma 2 (exact aligned sampling)

For integers `n,m>=5`,

```text
A_n(tau(m)) = sqrt(m) max(0, log 5 - |log(m/n)|).
```

In particular `A_n(tau(n))=sqrt(n)log 5`.

### Proof

On positive lag the channel is the sum of the fixed tent and the moving tent.  At
`t=2log m` with `m>=5`, the fixed tent is
`2exp(t/4)max(0,log 5-log m)=0`.  Since

```text
2a5(n)-log 5 = log n,
exp(tau(m)/4)=exp(log(m)/2)=sqrt(m),
```

the moving tent gives the displayed identity.  Taking `m=n` gives the apex value.  QED.

### Lemma 3 (uniform fivefold right-flank contraction)

For `n>=5` and every integer `m` with `2n<m<=5n`,

```text
A_n(tau(m)) <= q5 A_n(tau(n)),       0<q5<1.
```

### Proof

Set `d=log(m/n)`.  Positivity and monotonicity of logarithm give
`log 2<d<=log 5`.  Lemma 2 and
`sqrt(m)=sqrt(n)exp(d/2)` yield

```text
A_n(tau(m))/A_n(tau(n)) = R_{1/2,log 5}(d).
```

The identity also holds at the support endpoint, where both right-side expressions vanish.
The certified inequalities `log 5<2` and `0<log 5` give
`(1/2)log 5<1`; Theorem 1 makes the ratio at most its value at `log 2`, namely `q5`.
Because `0<log 2<log 5`, strict antitonicity gives `q5<1`; positivity is immediate.  QED.

## 3. Symbolic Chebyshev mass floor

Let

```text
P_n = {p prime : 2n<p<=5n}.
```

### Lemma 4 (macroscopic log-Haar mass)

For every natural `n` satisfying `exp(20)<=n`,

```text
sum_(p in P_n) 2log(p)/p >= 1/10.
```

### Proof

Write `N=n` as a real number.  Formalized Chebyshev bounds give

```text
theta(5N)-theta(2N)
 >= (5N-1)log 2-log(5N+2)-2sqrt(5N)log(5N)-(2N)log 4
 =  (N-1)log 2-log(5N+2)-2sqrt(5N)log(5N).                 (1)
```

We prove a completely symbolic lower bound for the right side.

The function `log x/sqrt x` is antitone on `[exp 2,infinity)`.  From `N>=exp 20`,

```text
log(5N)/sqrt(5N) <= 20/exp 10 < 1/50.                    (2)
```

The final strict inequality is exact: `exp 1>2`, hence
`exp 10=(exp 1)^10>2^10=1024>1000`.  Multiplying (2) by `2(5N)` gives

```text
2sqrt(5N)log(5N) <= N/5.                                 (3)
```

Also `5N+2<=6N`.  Applying `log x<=2sqrt x`, using `sqrt 6<3`, and using
`sqrt N>=exp 10>1000`, gives

```text
log(5N+2) <= 2sqrt(5N+2) <= 6sqrt N <= N/100.            (4)
```

Finally the certified bounds `1/2<log 2<1` and `N>20` imply

```text
(N-1)log 2 - N/5 - N/100
 >= (N-1)/2 - 21N/100
 = 29N/100-1/2
 >= N/4.                                                  (5)
```

Equations (1)--(5) show

```text
sum_(p in P_n) log p = theta(5N)-theta(2N) >= N/4.
```

For every `p in P_n`, `p<=5N`; therefore

```text
2log(p)/p >= (2/(5N))log p.
```

Summing gives at least `(2/(5N))(N/4)=1/10`.  QED.

No numerical sample, prime table, prime-gap hypothesis, PNT remainder, or RH statement is used.

## 4. Macroscopic source surplus

Define

```text
S5(n)=sum_(p in P_n) (2log(p)/p) [A_n(tau(n))-A_n(tau(p))].
```

### Theorem 5 (fivefold macroscopic Suzuki--Mangoldt block law)

For every natural `n` with `exp(20)<=n`,

```text
S5(n) >= ((1-q5)/10) sqrt(n) log 5 > 0.
```

Moreover `S5` is unbounded: for every real `B`, some natural `n>=exp(20)` satisfies
`B<S5(n)`.

### Proof

Lemma 3 gives, term by term,

```text
A_n(tau(n))-A_n(tau(p)) >= (1-q5)A_n(tau(n)).
```

All prime weights are positive.  Summing, applying Lemma 4, and then Lemma 2 gives

```text
S5(n)
 >= (sum_(p in P_n)2log(p)/p)(1-q5)A_n(tau(n))
 >= (1/10)(1-q5)sqrt(n)log 5.
```

Every factor in the last expression is strictly positive.  QED.

For unboundedness, put `c5=(1-q5)log(5)/10>0`.  Given `B`, Archimedean growth supplies a natural
number

```text
n > max(exp(20), (max(B,0)/c5)^2).
```

Then `B<c5 sqrt(n)<=S5(n)`.  QED.

## 5. What this resolves and what remains

Theorem 5 resolves the source-scaling frontier exposed by the width-`log 2` theorem.  Existing
single-flank surplus is `Omega(n^(-1/2))`; the new actual-prime block is `Omega(sqrt n)` and
unbounded, matching the scale of a fixed-width target overlap at an aligned moving apex.  The
right-flank coefficient is also sharp on the full continuous tail.  Thus the apex-block program is
not killed by scale: a concrete unconditional source block of the necessary order exists.

It does **not** yet prove RH or capacity-one target domination.  Remaining exact question is whether
this explicit block coefficient, possibly combined with unused fixed/Gamma target mass, dominates
the sharp future/past overlap for every aperture.  That comparison is the next frontier theorem.
