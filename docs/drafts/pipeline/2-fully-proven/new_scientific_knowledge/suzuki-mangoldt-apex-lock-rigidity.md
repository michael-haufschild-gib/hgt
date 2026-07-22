# Suzuki Mangoldt apex-lock rigidity

- **Stage:** 2 — fully proved on paper
- **Type:** source-specific rigidity / positive no-go survivor
- **Status:** `[PAPER-PROVED] [NOVELTY UNVERIFIED]`
- **Computation used:** no
- **RH used:** no
- **Parent:** `suzuki-mangoldt-log-haar-bicausal-transport.md`
- **Failed route:**
  `../../5-failed/suzuki-pointwise-turning-seam-cell-transport.md`

## Exact claim

Put

```text
L_2 = log 2,
a_n = (1/2) log(2n),
tau_n = 2 log n,
A_n(t) = exp(t/4) R_(L_2,a_n)(t/2).
```

For every integer `n>=4`, `tau_n` is the unique maximizer of `A_n` on the positive lag axis:

```text
t>0 and A_n(tau_n)<=A_n(t)  iff  t=tau_n.              (1)
```

Consequently every set `S subset (0,infinity)` on which
`A_n(tau_n)<=A_n(t)` holds pointwise has Lebesgue measure zero.  If `Lambda(n)>0`, then the source
atom at this null superlevel has strictly positive log-Haar mass

```text
w_n=2 Lambda(n)/n>0.                                    (2)
```

Thus no positive-volume, capacity-one, pointwise value-dominating cell can pay the apex atom.  In
particular this obstruction occurs cofinally at `n=2^k`, `k>=2`.

## Complete proof

For `0<L<2`, split the positive channel into fixed and moving pieces

```text
F_L(t)=2 exp(t/4) max(0,L-t/2),
M_(L,a)(t)=exp(t/4) max(0,L-|t/2-(2a-L)|).
```

On positive lags with `L<=a`, the four-tent autocorrelation identity gives

```text
A_(L,a)(t)=F_L(t)+M_(L,a)(t).                            (3)
```

Let `c=4a-2L`.  The moving tent is centered at `c`, and

```text
M_(L,a)(c)=exp(c/4)L.                                    (4)
```

It has a strict global maximum there.  For `t<c`, its tent height is at most `L` while
`exp(t/4)<exp(c/4)`.  For `t>c`, write `x=(t-c)/4>0`.  If the tent is nonzero, its height is
`L-2x`.  Since `L<2`,

```text
L-2x < L(1-x) < L exp(-x),
```

where the last inequality is strict exponential convexity.  Multiplication by
`exp(t/4)=exp(c/4)exp(x)` proves `M_(L,a)(t)<M_(L,a)(c)`.  If the tent vanishes, strictness follows
from `(4)` and `L>0`.

The identical argument with `c=0` proves

```text
0<t  =>  F_L(t)<2L.                                     (5)
```

Now specialize to `L=L_2` and `a=a_n`.  Elementary logarithm laws give

```text
0<L_2<2,
c=4a_n-2L_2=2log n=tau_n.                               (6)
```

For `n>=4`, monotonicity of logarithm gives

```text
a_n >= (3/2)L_2,
exp(c/4)>=2.                                             (7)
```

The fixed piece is supported in `t<2L_2`; the moving piece is supported in
`t>4a_n-4L_2`.  First inequality in `(7)` makes these positive supports disjoint.  Therefore at
each positive `t`, at most one summand in `(3)` is nonzero.  Equations `(4)`, `(5)`, and second
inequality in `(7)` show that every fixed-piece value is strictly below moving apex value, while
moving-piece equality occurs only at `c`.  This proves `(1)`.

Any pointwise dominating set is therefore contained in singleton `{tau_n}`, hence is Lebesgue
null.  Under `Lambda(n)>0`, `(2)` follows because `n>0`.  Prime powers have
`Lambda(p^k)=log p>0`; powers of two with `k>=2` give an unbounded family.  This closes all proof
obligations.

## Hostile audit

- The theorem does **not** disprove aggregate or block transport.  Several low-valued atoms may
  contribute surplus that pays one apex atom.
- It does disprove every seam construction assigning each atom its own positive-volume subset of
  its pointwise value-dominating superlevel, even if the subset is non-interval and selected
  adaptively.
- Generic fact that strict maximizer has null equality set is standard.  Scientific content here
  is exact source lock `a_n=(1/2)log(2n)`, which places actual Mangoldt atom at unique Suzuki apex on
  a cofinal prime-power family.
- Corpus, Suzuki 2026, and Groskin 2026 audits found rectangular autocorrelation, Weil transport,
  and finite tail order, but no matching apex-lock/source-cell obstruction.  External priority is
  not certified.

## Frontier consequence

Per-atom pointwise seam transport is retired.  Exact successor is
`SUZUKI-APEX-BLOCK-TRANSPORT`: construct source-canonical disjoint blocks containing apex and flank
atoms and prove aggregate sample mass is paid by aggregate completed-kernel mass.  Any valid proof
must expose a nonnegative block surplus; it cannot decompose into independently dominated atomic
cells.
