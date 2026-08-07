# Sharp geometric-bracket minimax and Suzuki--Mangoldt absolute block-surplus law

- **ID:** `suzuki-mangoldt-uniform-dyadic-block-surplus`
- **Stage:** 3 — formalized in Lean 4
- **Formalized companion:** `./suzuki-mangoldt-uniform-dyadic-block-surplus-formalized.md`
- **Status:** unconditional; Lean formalization completed in the paired Stage 3 card
- **Novelty:** corpus-new exact universal law and sharp Suzuki specialization; external priority not certified
- **Scope:** source side of `SUZUKI-APEX-BLOCK-TRANSPORT`

## Setup

For integers `n,m>=2`, put

```text
A_n(m)=A_(log 2, log(2n)/2)(2 log m)
      =sqrt(m) max(0, log 2-|log(m/n)|),
w_m=2 Lambda(m)/m.
```

The exact sample identity was already formalized in the ray-isolation card. This card proves the
stronger support, block-mass, and uniform-surplus consequences below.

## Theorem 1: exact open-annulus support

For every `n,m>=2`,

```text
A_n(m)>0  iff  n<2m and m<2n.                           (1)
```

**Proof.** Since `sqrt(m)>0`, positivity is equivalent to
`|log(m/n)|<log 2`. Strict monotonicity of the real logarithm converts this to
`1/2<m/n<2`, which is exactly `(1)`. QED.

## Theorem 2: cross-prime three-atom dilution

For every `n>=4`, there are primes `p,q` satisfying

```text
n/2<p<n<q<2n.                                           (2)
```

Both flank samples are positive by `(1)`. Their Mangoldt masses obey

```text
w_n<=w_p,                 w_n<2w_q.                     (3)
```

Consequently

```text
5w_n<2(w_n+w_p+w_q),                                    (4)
```

so the apex carries strictly less than two fifths of block mass. Moreover,

```text
w_n A_n(n)+w_p A_n(p)+w_q A_n(q)
  <(w_n+w_p+w_q)A_n(n).                                 (5)
```

**Proof.** Apply Bertrand at `floor(n/2)` and at `n`; primality excludes equality at the even
endpoints, giving `(2)`. On `[exp(1),infinity)`, `log(x)/x` is antitone. Since `p>=3`,
`p<n`, and `Lambda(n)<=log n`, this gives `w_n<=w_p`. From `n<q<2n` and strict logarithmic
monotonicity, `log n/n<2 log q/q`, giving `w_n<2w_q`. This proves `(3)--(4)`.
The aligned apex is the unique positive-lag maximum, while `p,q` differ from `n`; multiplying both
strict sample deficits by the positive prime masses proves `(5)`. QED.

## Theorem 3: sharp universal tilted-tent minimax law

For `L>0`, `beta>=0`, and `0<=d<=L`, define

```text
F(d)=exp(-beta*d)(1-d/L),
G(d)=exp(beta*(L-d))d/L,
alpha=1/(1+exp(beta*L)),
C_(beta,L)=exp(-beta*alpha*L)(1-alpha).
```

Then

```text
min(F(d),G(d)) <= C_(beta,L),                              (6)
max_[0,L] min(F,G) = C_(beta,L),                           (7)
F(d)=G(d) iff d=alpha*L,                                   (8)
0<C_(beta,L)<1.                                            (9)
```

**Proof.** The balance identity `alpha*exp(beta*L)=1-alpha` makes both profiles equal to
`C_(beta,L)` at `d=alpha*L` and proves the reverse direction in `(8)` after cancellation of a
positive exponential. The derivative

```text
G'(d)=exp(beta*(L-d))/L * (1-beta*d)
```

is positive up to balance because
`beta*alpha*L=(beta*L)/(1+exp(beta*L))<1`; use `x+1<=exp(x)`. Thus for
`d<=alpha*L`, `min(F,G)<=G(d)<=G(alpha*L)`. For `d>=alpha*L`, both factors in `F` are no larger
than their balance values, so `min(F,G)<=F(d)<=F(alpha*L)`. Attainment proves exactness `(7)`.
The balance lies in `(0,1)`; exponential positivity and its nonpositive exponent prove `(9)`.
QED.

## Theorem 4: sharp dyadic Suzuki contraction

For every `n>=2`, there is a dyadic prime power `m` such that

```text
n<2m,  m<=2n,  m!=n,
w_m>=log(2)/n>0,
A_n(m)<=C_* A_n(n),                                      (10)
C_*=exp(-(sqrt(2)-1)log(2)/2)(2-sqrt(2)),
0<C_*<sqrt(2)/2<1.                                       (11)
```

**Proof.** Let `k=floor(log_2 n)`, `ell=2^k`, `h=2^(k+1)`, and
`d=log(n/ell)`. Then `ell<=n<h=2ell` and `d in [0,log 2]`. The exact normalized samples are

```text
A_n(ell)/A_n(n)=F_(1/2,log 2)(d),
A_n(h)/A_n(n)=G_(1/2,log 2)(d).
```

Apply Theorem 3 and choose the endpoint realizing the lower profile. At `n=ell`, the profiles are
one and zero, so the selected endpoint is `h!=n`. Since `exp(log(2)/2)=sqrt(2)`, the general
balance is `sqrt(2)-1` and gives the displayed closed form for `C_*`. Its exponential factor is
strictly below one and `2-sqrt(2)<sqrt(2)/2`, proving `(11)`. Both endpoints are nontrivial powers
of two, so `Lambda(m)=log 2`; since `m<=2n`,

```text
w_m=2log(2)/m >= log(2)/n.
```
QED.

## Theorem 5: absolute prime-gap-free source surplus

Define

```text
S_n(m)=w_m(A_n(n)-A_n(m)).
```

The sharp dyadic witness from Theorem 4 satisfies

```text
0<(1-C_*)(log(2))^2/sqrt(n)
 <=(1-C_*)w_m A_n(n)<=S_n(m).                            (12)
```

This is a source-derived absolute surplus: its lower bound contains neither prime gaps nor
`Lambda(n)`, and is not defined from the RH-bearing target deficit.

**Proof.** Multiply `(10)` by `w_m` and rearrange. Then use
`w_m>=log(2)/n` and `A_n(n)=sqrt(n)log(2)`. QED.

For the cofinal dyadic apex family `n=2^k`, `k>=1`, one may take the successor
`m=2^(k+1)`. Its sample is exactly zero and hence

```text
S_(2^k)(2^(k+1))=w_(2^(k+1)) A_(2^k)(2^k)>0.            (13)
```

This exact boundary identity is also formalized directly.

## Frontier effect

The source side of the apex-block problem is no longer an existence problem and no longer depends
on prime gaps: `(12)` supplies an actual positive Mangoldt flank surplus with an absolute lower
bound at every aligned apex. The exact law `(6)--(9)` is independent of Suzuki and applies to every
positive-width geometric bracket with nonnegative exponential tilt.
At dyadic apices the useful flank is the adjacent same-ray boundary atom with zero sample, so the
earlier ray-isolation result excludes only **positive-sample** same-ray flanks, not boundary
dilution.

The remaining open connector is target-side and quantitative: construct pairwise capacity-one
continuum blocks whose completed-kernel excess dominates the explicit lower bound `(12)`, while
retaining unused mass for the Gamma charge. No such target domination is claimed here.

## Proof dependencies

- exact aligned sample formula and unique-apex theorem from the formal Suzuki corpus;
- Bertrand's theorem;
- `Lambda(n)<=log n`;
- monotonicity of `log(x)/x` on `[exp(1),infinity)`;
- elementary dyadic floor-log inequalities;
- elementary real exponential calculus for the sharp minimax law.

No RH statement, log-Haar capacity assumption, numerical experiment, or unproved positivity
premise is used.
