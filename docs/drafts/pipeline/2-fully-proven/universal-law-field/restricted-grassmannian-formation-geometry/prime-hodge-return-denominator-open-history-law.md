# Prime--Hodge return denominator and open-history law

- **ID:** ULF-PHRD-001
- **Stage:** 2-fully-proven
- **Type:** unconditional pre-divisor fusion and no-finite-closure theorem
- **Parents:** ULF-CCRHD-001, ULF-PHSF-001, P-G202
- **Status:** `[PROVED HERE] [UNCONDITIONAL] [NOT RH] [NOVELTY UNVERIFIED]`
- **Purpose:** extract the first-return arithmetic hidden in the integral--nuclear defect `T`,
  explain the independently occurring four-leg completion, and prove that the exact history cannot
  belong to any finite closed unitary recurrence.

## 1. Higher-law interpretation

The source defect has two incompatible but exact readings.  Its first moment admits a finite
topological shadow: denominator four and winding numerator seven.  Its full history has a
power-law tail and therefore admits no finite rational-inner closure.  Thus four-leg positivity is
the smallest closed observer of `T`, not the lifted history itself:

```text
open prime-pair formation history --coarse first moment--> four-leg degree-7 observer,
open prime-pair formation history --retain all grades-----> necessarily noncompact completion.
```

This is a theorem about the pre-divisor source.  It neither supplies nor assumes a Xi divisor.

## 2. Exact first-exit law and mean

For `n>=0`, recall

```text
m_n = 105/((2n+3)(2n+5)(2n+7)),
w_n = m_n-m_(n+1)
    = 630/((2n+3)(2n+5)(2n+7)(2n+9)).               (PHRD.1)
```

By `ULF-CCRHD-001` and `ULF-PHSF-001`, `w_n` is both the time-`n` exit energy of the oriented
prime-pair colligation and the history-`n` marginal of `T`.  Put `p_(n+1)=w_n`.

**Theorem PHRD-A.** The exit law is a probability distribution with exact mean

```text
sum_(n>=0) (n+1)w_n = sum_(n>=0)m_n = 7/4.           (PHRD.2)
```

**Proof.** Finite summation by parts gives

```text
sum_(n=0)^N (n+1)(m_n-m_(n+1))
  = sum_(n=0)^N m_n-(N+1)m_(N+1).
```

The last term tends to zero.  With `a_n=1/(2n+3)`, direct subtraction gives

```text
m_n=(105/8)(a_n-2a_(n+1)+a_(n+2)).
```

Therefore

```text
sum_(n=0)^N m_n
  =(105/8)(a_0-a_1-a_(N+1)+a_(N+2))
  ->(105/8)(1/3-1/5)=7/4.
```

The already proved telescope `sum w_n=1` supplies total probability one. QED.

## 3. Finite return quantization forces denominator four

Use monitored subspace recurrence in the sense of Bourgain--Grünbaum--Velázquez--Wilkening.
For a unitary `U`, finite-dimensional absorbing subspace `V` of dimension `d`, projection `P`, and
first-return amplitudes

```text
A_n=P U ((I-P)U)^(n-1) P,                            (PHRD.3)
```

the Haar-averaged first-return probability at time `n` is

```text
p_n=(1/d)||A_n||_F^2.                                (PHRD.4)
```

Their Theorem 3.2 states that recurrence with finite expected return is equivalent to a rational
inner matrix Schur function, and then

```text
sum_(n>=1)n p_n=K/d,                                 (PHRD.5)
```

where `K` is the positive winding degree of the determinant of the first-return function.  See
[Quantum recurrence of a subspace and operator-valued Schur functions](https://arxiv.org/abs/1302.7286).

**Theorem PHRD-B.** Any such finite-dimensional recurrent unitary whose averaged mean equals the
source mean `7/4` satisfies

```text
4 divides d, 7 divides K.
```

The minimal pair is `(d,K)=(4,7)`, and it occurs.

**Proof.** Equation `(PHRD.5)` and `K/d=7/4` give `4K=7d`; coprimality of `4` and `7` gives the
divisibilities.  For existence, let

```text
V=span(e_1,e_2,e_3,e_4),  W=span(f_2,f_3,f_4),
Ue_1=e_1,
Ue_j=f_j, Uf_j=e_j  (j=2,3,4).
```

This is a unitary on `V directSum W`.  Its first-return function on `V` is

```text
Ahat(z)=diag(z,z^2,z^2,z^2).                         (PHRD.6)
```

Thus `p_1=1/4`, `p_2=3/4`, its mean is `7/4`, and `det Ahat(z)=z^7`. QED.

This explicit realization is a coarse model only.  It does not realize the individual source
weights in `(PHRD.1)`.

## 4. Exact source history forbids every finite closed recurrence

**Theorem PHRD-C.** No finite-dimensional monitored unitary system has Haar-averaged first-return
law

```text
p_n=w_(n-1)  (n>=1).                                 (PHRD.7)
```

**Proof.** Suppose `(PHRD.7)` holds on a `d`-dimensional absorbing subspace.  The positive return
operator

```text
R=sum_(n>=1) A_n* A_n
```

satisfies `R<=I`.  Since `sum p_n=1`, `(PHRD.4)` gives `Tr R=d`; hence the positive finite matrix
`I-R` has trace zero and is zero.  Every state is recurrent.  Equation `(PHRD.2)` gives finite
averaged expected return, so Theorem 3.2 of the cited paper makes the first-return function
rational inner and analytic on a neighborhood of the closed disk.

Choose `r>1` inside that neighborhood.  Cauchy's estimate on `|z|=r` gives constants `C>0` such
that

```text
p_n=(1/d)||A_n||_F^2 <= C r^(-2n).                   (PHRD.8)
```

But for every `n>=1`,

```text
w_(n-1)=630/((2n+1)(2n+3)(2n+5)(2n+7))
       >=2/(3n^4),                                   (PHRD.9)
```

because the four denominator factors are at most `3n,5n,7n,9n`.  No exponential upper bound
`(PHRD.8)` can dominate `(PHRD.9)` for all large `n`. Contradiction. QED.

## 5. Cross-organ consequence

`RoutePPrimitiveBurnolDeningerFourLegHodgeCompletion` independently proves that phase-stable
positive matrix completion needs four legs: upper, line-reflected upper, lower, and
conjugate-lower.  Theorem PHRD-B independently makes dimension four the smallest finite return
observer compatible with the source mean, with determinant degree seven.  Theorem PHRD-C proves
that this agreement cannot be upgraded to an exact finite recurrence model.

Hence the same source unit has:

```text
closed observer projection: minimal four polarizations, degree numerator 7;
open lifted history:        infinitely many grades with n^(-4) exit tail.
```

This is a route-independent prediction: any exact completion retaining all `w_n` must be
infinite-dimensional/noncompact, history-renormalizing, or genuinely open/relative.  A finite
four-leg Schur colligation can reproduce only coarse moments.

## 6. Audit boundary

- `[LITERATURE]` Rational-inner characterization and `K/d` return quantization come from the cited
  theorem.
- `[CORPUS]` `m_n,w_n,T`, exact exit ownership, four-leg Hodge completion, and the functional-
  equation quartet are prior certified inputs.
- `[PROVED HERE]` Exact mean `7/4`, denominator-four/minimal-degree-seven law, explicit minimal
  coarse realization, and impossibility of finite closed realization of the full history.
- `[NOT PROVED]` The four Hodge legs are not yet identified with a canonical absorbing subspace;
  no arithmetic relative determinant of degree seven has been constructed; no off-line quartet
  degree-additivity or completion invariance is asserted here.
- **Lean status:** paper proof only.  No Lean file was written or built during the current
  corpus/literature research phase.

