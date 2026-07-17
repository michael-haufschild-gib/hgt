# Dumitrescu--Wolf tangent phases wrap infinitely often

- **ID:** dumitrescu-wolf-tangent-phase-wrap-obstruction
- **Stage:** 2-fully-proven / needs-audit
- **Type:** THEOREM (paper)
- **Source:** C. Dumitrescu and M. Wolf, *The Disproof of the Riemann Hypothesis*, arXiv:2102.08313v3, Lemma 2 and Appendix
- **Statement:** Under the paper's RH setup, the two Riccati sequences used to quantize the vertical zero contribution cannot converge to `+infinity` and `-infinity`; whenever their recurrences stay defined, each is a tangent of a divergent phase with vanishing increments and therefore has a subsequence tending to zero.

## Goal

Audit the endpoint claim that turns the vertical zero integral into an integer
multiple of `pi`.  This is a route discriminator, not an RH result.

## Gates

- [x] 0 -> 1 in-progress: the claimed quantization was reduced to the two explicit Riccati recurrences
- [x] 1 -> 2 fully-proven: the recurrence was solved as a tangent phase and the asserted limits were contradicted, `[PROVED HERE]`
- [ ] 2 -> 3 formalized: no Lean theorem; formalizing a failed disproof is not source-bearing for RH-false
- [ ] 3 -> 4 publication-ready

## Theorem

Fix `1/2 < alpha < beta < 1` and `T > 0`, and put

```text
A = (alpha-1/2)(beta-1/2),    c = beta-alpha > 0.
```

Let `gamma_k` be the positive ordinates of the nontrivial zeta zeros, with
multiplicity, under the paper's RH assumption.  Define

```text
h_-(k) = c (gamma_k-T)/(A+(gamma_k-T)^2),
h_+(k) = -c (T+gamma_k)/(A+(T+gamma_k)^2).
```

For all sufficiently large `k`, `h_-(k)>0`, while `h_+(k)<0` for every
`k`.  Moreover,

```text
h_-(k) -> 0,                 h_+(k) -> 0,
sum_k arctan(h_-(k)) = +infinity,
sum_k arctan(h_+(k)) = -infinity.
```

Consider the recurrences appearing in the paper,

```text
f(k+1) = (f(k)+h_-(k))/(1-f(k)h_-(k)),    f(1)=0,
g(k+1) = (g(k)+h_+(k))/(1-g(k)h_+(k)),    g(1)=0.
```

If a denominator vanishes, the corresponding recurrence is not defined.  If
no denominator vanishes, then neither `f(k)->+infinity` nor
`g(k)->-infinity`.  In fact, each sequence has a subsequence tending to
zero.

## Proof `[PROVED HERE]`

The Riemann--von Mangoldt counting law gives

```text
N(X) = (X/(2 pi)) log(X/(2 pi)) - X/(2 pi) + O(log X).
```

Partial summation therefore gives

```text
sum_(0<gamma_k<=X) 1/gamma_k -> +infinity.
```

For large `k`, `gamma_k>2T` and

```text
h_-(k)  asymptotic to  c/gamma_k,
-h_+(k) asymptotic to  c/gamma_k.
```

Both magnitudes tend to zero, and `arctan x` is comparable to `x` near
zero.  The two asserted divergences follow.

The tangent addition identity solves the recurrences exactly.  As long as
all denominators are nonzero,

```text
f(N) = tan(sum_(k<N) arctan(h_-(k))),
g(N) = tan(sum_(k<N) arctan(h_+(k))).
```

It remains to use an elementary phase-wrap lemma.  If `u_k>0`, `u_k->0`,
and `sum u_k=+infinity`, let `N_m` be the first index at which the partial
sum reaches `m pi`.  Minimality gives

```text
0 <= sum_(k<=N_m) u_k - m pi < u_(N_m),
```

so the tangent of that partial sum tends to zero.  Applying this to the
eventually positive increments `arctan(h_-(k))` supplies a subsequence of
`f` tending to zero.  Applying the same argument to
`-arctan(h_+(k))` supplies a subsequence of `g` tending to zero.  Hence the
limits asserted in Lemma 2 of the preprint are impossible.

If a recurrence denominator does vanish, its claimed globally defined
sequence already fails.  Thus the conclusion holds in both cases.

## Consequence for the proposed disproof

The paper separates the paired vertical zero phase into a `T-gamma_k`
channel and a `T+gamma_k` channel and assigns them endpoint phases `pi/2`
and `-pi/2`.  The theorem shows that neither endpoint exists.  The two
channels must instead remain paired: their leading `1/gamma_k` tails cancel,
leaving a convergent but non-quantized phase whose `gamma_k` near `T` form a
moving boundary layer.  No integer-multiple-of-`pi` conclusion follows.

There is a second, independent scaling gap.  The paper bounds the denominator
tail by `epsilon_2=1/T^2`; restoring the omitted numerator
`2(s-1/2)` and integrating over an edge of length `2T` yields only an `O(1)`
bound, not `o(1)`.  A smaller tail tolerance could repair that estimate, but
cannot repair the false phase limits above.

## Status

The recurrence obstruction is complete.  Bibliographic provenance and the
precise current-version comparison remain subject to the repository's
external audit, so this card remains in `needs-audit`.

