# Prime-only physical transition of the Möbius–theta causal tail

- **ID:** L-PSRC-PRIMORIAL
- **Stage:** 2-fully-proven (paper theorem; Lean formalization open)
- **Type:** THEOREM (paper)
- **Routes:** L, PSRC
- **Statement:** The exact theta observation of the physical Möbius residue source has a uniformly bounded prime-only innovation and localizes to signed joint history across genuine new-prime transitions.

## Goal

The [causal boundary criterion](causal-mobius-theta-boundary-criterion.md)
reduces RH to subpower growth of a signed theta observation. Its existing
physical decomposition uses `lcm(1,...,l)` and retains prime-power clock
jumps. The literal source contains only squarefree Möbius periods. The
result below replaces that clock with the primorial while preserving the
physical Hilbert measure and the exact theta observation. It identifies
the remaining signed producer more precisely; it does not bound it.

## Prime-only innovation [PROVED HERE]

Use physical cells `r>=1` with weight `w_r=1/[r*(r+1)]` and Hilbert
space `H=ell²(w)`. Let

```text
f_d(r)={r/d},
C_N(r)=sum_(d<=N) mu(d)*f_d(r),
R_l=product_(p prime, p<=l) p,  R_0=R_1=1,
F_l={H sequences periodic modulo R_l},
Pi_l=orthogonal projection onto F_l.
```

Define the source's primorial innovation and predictable part by

```text
I_N^sf=sum_(d<=N) mu(d)*(f_d-Pi_(d-1)f_d),
P_N^sf=sum_(d<=N) mu(d)*Pi_(d-1)f_d,
C_N=I_N^sf+P_N^sf.                                (1)
```

If `mu(d)!=0` and `d` is composite, then `d` is squarefree and every
prime factor of `d` is less than `d`; hence `d|R_(d-1)` and
`f_d∈F_(d-1)`. The `d=1` term is zero. Therefore

```text
I_N^sf=sum_(p<=N, p prime) mu(p)*(f_p-Pi_(p-1)f_p). (2)
```

For prime `p`, the increment in (2) lies in `F_p` and is orthogonal
to `F_(p-1)`. These increments are mutually orthogonal. To bound one,
compare `f_p` with the `R_(p-1)`-periodic predictor
`r↦f_p(1+((r-1) mod R_(p-1)))`. The two agree through cell
`R_(p-1)` and lie in `[0,1]`; later physical cells have total mass
`1/[R_(p-1)+1]`. Orthogonal projection is the least-squares
predictor, so

```text
||I_N^sf||_H²
 =sum_(p<=N) ||f_p-Pi_(p-1)f_p||_H²
 <=sum_(p<=N) 1/[R_(p-1)+1] <2.                 (3)
```

For the `k`-th prime, `R_(p_k-1)=prod_(i<k)p_i>=2^(k-1)`; the
geometric series bounds the final sum. Since `|C_N(r)|<=N` and each
prime innovation lies in `[-1,1]`, also

```text
||P_N^sf||_H<=N+sqrt(2),
|P_N^sf(r)|<=2*N,
P_N^sf∈F_N.                                    (4)
```

The last claim follows termwise from `Pi_(d-1)f_d∈F_(d-1)⊂F_N`.
Thus composite squarefree atoms enter the predictable history
without creating a new clock digit; true innovations occur only when
a new prime appears.

## Theta-wavelet transition [PROVED HERE]

Let `q_N^flat` be the exact smooth-gauge theta test constructed in the
causal criterion. Its paper-proved properties are

```text
B(N)=<C_N,q_N^flat>_H+e_N,  e_N=O(N^(-5/2)),
sup_N ||q_N^flat||_H<infinity.                       (5)
```

For every `A>0`, its short-period and long-period estimates read

```text
||Pi_Q q_N^flat||_H
 <=C_A*sqrt(Q/N)*[N^(-2)+(Q/N)^A]         (Q<=N),
sum_r w_r*|q_N^flat(r)-Pi_Q q_N^flat(r)|
 <=C*N^(3/2)/Q²                              (Q>=N). (6)
```

Here `Pi_Q` means physical projection onto sequences periodic modulo
`Q`; it agrees with `Pi_l` when `Q=R_l`. Fix `0<delta<1`. Take `l_-`
maximal with `R_(l_-)<=N^(1-delta)` and `l_+` minimal with
`R_(l_+)>=N^(5/4+delta)`.
They exist for all sufficiently large `N`: `R_1=1`, while one prime
in each dyadic interval (Bertrand) makes `R_N` grow faster than every
fixed power of `N`.

Equations (3)--(6) prove

```text
B(N)=<(Pi_(l_+)-Pi_(l_-))P_N^sf,q_N^flat>_H+O_delta(1)
    =sum_(l_-<p<=l_+, p prime)
       <(Pi_p-Pi_(p-1))P_N^sf,q_N^flat>_H+O_delta(1). (7)
```

Indeed the innovation contribution in (5) is at most
`sqrt(2)*sup_N||q_N^flat||_H`. For the lower endpoint,
self-adjointness of `Pi_(l_-)`, (4), and the first estimate in (6)
bound the pairing by

```text
(N+sqrt(2))*C_A*sqrt(R_(l_-)/N)
  *[N^(-2)+(R_(l_-)/N)^A]=O_delta(1)
```

for `A>1/delta`. For the upper endpoint, the second estimate in (6)
and `|P_N^sf(r)|<=2*N` give

```text
|<(1-Pi_(l_+))P_N^sf,q_N^flat>_H|
 <=2*C*N^(5/2)/R_(l_+)²=O_delta(N^(-2*delta)).
```

The middle difference telescopes over primes because `R_l` changes
only at primes. This proves (7) without an energy estimate for
individual layers.

## Consequence and remaining producer

Subpower growth of the prime-only covariance in (7), for every fixed
`delta>0`, is equivalent to the original causal criterion and hence
to RH. The point of (7) is its **source description**: the hard term
is joint old-prime/composite predictable history observed by the
completed-theta wavelet at genuine new-prime transitions. Higher
prime-power clock layers in the lcm filtration were refinements of the
physical observation, not arrivals of squarefree source atoms.
No signed estimate for the middle term is proved here.

Existing Lean anchors: `EulerDeletionResidueMartingale.lean` (physical
measure and periodic projection), `EulerDeletionResidueFourierCoefficient.lean`
(signed sawtooth Fourier coefficient), `EulerDeletionPrimePowerClockSupport.lean`
(old lcm clock), and the `Sieve` primorial-divisibility lemmas returned
by corpus deep search. Equations (1)--(7) remain paper-level; no Lean
build or computation was run for this card.
