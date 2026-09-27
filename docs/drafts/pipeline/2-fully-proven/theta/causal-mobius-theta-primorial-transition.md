# Prime-only physical transition of the Möbius–theta causal tail

- **ID:** L-PSRC-PRIMORIAL
- **Stage:** 2-fully-proven (paper theorem; Lean formalization open)
- **Type:** THEOREM (paper)
- **Routes:** L, PSRC
- **Statement:** The exact theta observation has a uniformly bounded prime-only physical innovation. On a uniform primorial cycle its arithmetic layers factor into smooth and rough cofactors; completed-theta reflection makes all non-largest-prime layers superpolynomially small in total, leaving the signed largest-prime current.

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

## Uniform-cycle reinterpretation [PROVED HERE]

The physical measure makes conditional projections of a period `d`
respond to a prime `p` even when `p` does not divide `d`. This is a
property of the measure, not of the arithmetic source. There is an exact
way to remove it without changing the theta observation. Put `M=R_N`,
and let `U_l` be uniform conditional averaging on the finite cyclic
group `Z/MZ` onto functions of the residue modulo `R_l`. Every nonzero
Möbius atom `f_d` with `d<=N` is `M`-periodic, so `U_N C_N=C_N`.

For a function of period `d`, `U_l f_d` depends only on the residue
modulo `gcd(d,R_l)`: an `R_l`-coset runs uniformly through the residue
classes of `d` sharing that gcd. Consequently, for prime `p`,

```text
(U_p-U_(p-1))f_d=0                if p does not divide d.       (8)
```

For this uniform-cycle argument, use the unflattened exact theta test
`q_N` from the causal criterion. Put
`a_N(r)=w_r*q_N(r)=[g(r/N)-g((r+1)/N)]/sqrt(N)` for `r>=1`, and
extend it by the same difference formula at `r=0`. Since `g(0)=0`,
`a_N(0)=-g(1/N)/sqrt(N)` and `sum_(r>=0)a_N(r)=0` exactly.
Extend `C_N` by `C_N(0)=0`, so this extra cell leaves the original
pairing unchanged. Periodize the absolutely summable observer by

```text
Q_N(a)=M*sum_(r>=0, r=a mod M) a_N(r),  a in Z/MZ.
```

With normalized uniform inner product `⟨u,v⟩_M=M^(-1)*sum_a u(a)v(a)`,
periodicity gives the **exact** identity

```text
⟨C_N,q_N⟩_H=⟨C_N,Q_N⟩_M.                              (9)
```

The constant layer has zero pairing because the extended observer
has exact mean zero. Telescoping uniform projections, using (8),
and writing `d=p*m` therefore gives

```text
B(N) = -sum_(p<=N, p prime) ⟨(U_p-U_(p-1))f_p,Q_N⟩_M
       -sum_(p*m<=N, p prime, m>=2, p does not divide m)
          mu(m)*⟨(U_p-U_(p-1))f_(p*m),Q_N⟩_M
       +e_N.                                           (10)
```

Here `e_N=O(N^(-5/2))` is the exact remainder in the unflattened
source identity of the causal criterion.
Equation (10) is a source-faithful prime--cofactor decomposition with
**no nonincident prime layers**. It gives a different interpretation of
the physical predictable drift: its nonincident response is measure
bias; the arithmetic response is entirely prime incidence. The
cofactor signs in the second sum remain essential and unbounded by
this identity.

The uniform carrier does not provide a free Hilbert bound. Its
periodized observer has norm that can grow with `M`; replacing the
physical measure removes incidence bias but loses the bounded-test
property in (5). A proof route must exploit signed prime--cofactor
structure in (10), or find a dual norm that controls this exact
observer, without taking absolute values of the cofactor sum.

### Exact smooth/rough factorization [PROVED HERE]

Uniform averaging permits a stronger explicit formula. Write `V_g`
for uniform averaging modulo a divisor `g` of `M`, so `U_l=V_(R_l)`.
For `g|d`, average `f_d` over any residue class `r mod g`. That class visits
`r mod g, (r mod g)+g, ..., (r mod g)+(d/g-1)*g` modulo `d`, so

```text
V_g f_d(r)=[(r mod g)+(d-g)/2]/d.                 (11)
```

For each squarefree `d` divisible by `p`, factor it uniquely as
`d=p*a*b`, where all prime factors of `a` are `<p` and all prime
factors of `b` are `>p`. Write the centered sawtooth

```text
psi_p(j)=[(j mod p)-(p-1)/2]/p.
```

Equation (11), first with `g=p*a` and then with `g=a`, gives the
factorization

```text
(U_p-U_(p-1))f_(p*a*b)(r)=psi_p(floor(r/a))/b. (12)
```

Set `H_p(X)=sum_(b<=X, every prime factor of b > p) mu(b)/b`,
including `b=1`. Möbius multiplicativity now yields an exact
formula for the entire prime layer:

```text
(U_p-U_(p-1))C_N(r)
 =-sum_(a|R_(p-1), p*a<=N)
      mu(a)*H_p(N/(p*a))*psi_p(floor(r/a)).      (13)
```

The rough-side coefficient has the unconditional absolute bound
`|H_p(X)|<=sum_(b<=X)1/b<=1+log X`. Thus the unresolved arithmetic
growth is organized as a **signed old-prime smooth-divisor sum**
against a centered new-prime sawtooth, with only a logarithmic
rough-cofactor weight. Substituting (13) into (9)--(10) gives the
literal theta observation as this smooth/rough prime-current sum,
up to `O(N^(-3/2))`. This is a candidate source law to attack;
the absolute bound on `H_p` does not control the remaining signed
sum over `a` and `p`.

### Largest-prime reduction [PROVED HERE; paper]

The actual theta atom gives more than generic smooth-wavelet decay.
Recall `a_N(r)=[g(r/N)-g((r+1)/N)]/sqrt(N)` and set

```text
A_N(a,p)=sum_(r>=0) a_N(r)*psi_p(floor(r/a)),
G(x)=sum_(m>=1)g(m*x),  x>0.
```

Abel summation on the integer cells is exact. The centered sawtooth
changes only at `r=j*a`, where its jump is `1/p-1_(p|j)`.
Because `g(r/N)` tends rapidly to zero and `g(0)=0`, the extended
`r=0` cell removes the boundary term:

```text
A_N(a,p)=1/sqrt(N)*[
   (1/p)*sum_(j>=1)g(j*a/N)
   -sum_(k>=1)g(k*p*a/N)].                     (14)
```

The exact completed-theta reflection used in the causal criterion is
`G(1/x)=x*G(x)` for every `x>0`. Applying it at `x=N/a` and
`x=N/(p*a)` turns (14) into the **source-specific duality**

```text
A_N(a,p)=sqrt(N)/(p*a)*[G(N/a)-G(N/(p*a))]. (15)
```

For `x>=1`, the explicit Gaussian polynomial defining `g` gives
`|G(x)|<=C*exp(-c*x^2)` after absorbing polynomial factors into
the exponential. Since `p*a<=N`, put `x=N/(p*a)>=1`; then

```text
|A_N(a,p)|<=C*N^(-1/2)*exp(-c*x^2).          (15a)
```

In a non-largest-prime term `d=p*a*b` from (12), `b>1` has every
prime factor larger than `p`. Hence `x=N/(p*a)>=b>p`.
Equation (15a) suppresses that term by a Gaussian in the **later
prime**, before using its Möbius sign. To sum all these bounds,
split at `P=log N/(4*log log N)` for sufficiently large `N`.
For `p<=P`, every `a|R_(p-1)` satisfies
`a<=R_(p-1)<=p^p<=N^(1/4)`; hence
`x=N/(p*a)>=N^(1/2)` for large `N`. For `p>P` and `b>1`,
`x>=b>p>P`, so `x^2` grows faster than `log N`.
There are at most `N*log_2 N` triples `(p,a,b)` with
`p*a*b<=N`. Thus the Gaussian sum of **all** `b>1` terms in
(10) is `O_A(N^(-A))` for every fixed `A>0`, even after taking
absolute values. The same argument shows that all `b=1` terms
with `p<=P` are superpolynomially small.

Consequently the exact causal observation has the
**largest-prime normal form**

```text
B(N)=-sum_(p<=N, p prime)
       sum_(a|R_(p-1), p*a<=N)
         mu(a)*sum_(r>=0) a_N(r)*psi_p(floor(r/a))
     +e_N+O_A(N^(-A))  (every fixed A>0).              (16)
```

Each squarefree modulus `p*a` appears once, at its largest prime.
All earlier-prime projections of that same atom have negligible
combined theta observation. The same low-`p` estimate allows the
sum in (16) to be restricted to `p>P`. The signed largest-prime sum
still has the full RH difficulty; the new gain is exact
theta-reflection control of every earlier prime layer.

There is an important whole-chain check. In (15), the first term
`G(N/a)` is itself superpolynomially small after summing all
`p*a<=N`: for `p<=P`, `N/a>=N^(3/4)`, while for `p>P`,
`N/a>=p>P`. The second term satisfies
`sqrt(N)/(p*a)*G(N/(p*a))=(p*a)^(-1/2)*k(log(N/(p*a)))`.
Since `mu(p*a)=-mu(a)`, the largest-prime current in (16) is,
up to `O_A(N^(-A))`, the negative finite Möbius--theta head
over `2<=d<=N`. This identifies its arithmetic content exactly:
the new decomposition removes nonterminal geometric layers but does
not generate the missing cancellation of the finite head.

The remaining current is exactly a **sieve dilation defect**. Let
`X=N/p`, `Q=R_(p-1)`, and define the truncated wheel count

```text
S_(p,X)(r)=sum_(a|Q, a<=X) mu(a)*floor(r/a),
M_(p,X)=sum_(a|Q, a<=X) mu(a).
```

Since `j mod p=j-p*floor(j/p)` and
`floor(floor(r/a)/p)=floor(r/(a*p))`,

```text
sum_(a|Q, a<=X) mu(a)*psi_p(floor(r/a))
 =S_(p,X)(r)/p-S_(p,X)(floor(r/p))
   -(p-1)/(2*p)*M_(p,X).                         (17)
```

The last term has **zero** theta observation because
`sum_(r>=0)a_N(r)=0` exactly. Hence RH now asks for a
subpower bound on the **wavelet observation of the complete
cross-prime scale defect**
`S_(p,N/p)(r)/p-S_(p,N/p)(floor(r/p))`, summed over primes.
The truncated wheel count itself is signed; only its untruncated
version is a positive sifted count. Equation (17) does not provide
the needed bound, but identifies a specific renormalization defect
on which a new source law could act.

## Consequence and remaining producer

Subpower growth of the prime-only covariance in (7), for every fixed
`delta>0`, is equivalent to the original causal criterion and hence
to RH. The stronger uniform-cycle result (16)--(17) identifies the
same hard observation, up to a power-saving error, as the signed
largest-prime current or equivalently the wavelet-tested cross-prime
sieve dilation defect, with the explicit remainder `e_N`.
Higher prime-power clock layers in the lcm
filtration were refinements of the physical observation, not arrivals
of squarefree source atoms. No signed subpower estimate for the
largest-prime current is proved here.

Existing Lean anchors: `EulerDeletionResidueMartingale.lean` (physical
measure and periodic projection), `EulerDeletionResidueFourierCoefficient.lean`
(signed sawtooth Fourier coefficient), `EulerDeletionPrimePowerClockSupport.lean`
(old lcm clock), and the `Sieve` primorial-divisibility lemmas returned
by corpus deep search. Equations (1)--(17) remain paper-level; no Lean
build or computation was run for this card.
