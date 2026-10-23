# Reflected Type I cancellation with marks on the predecessor

- **ID:** goldbach-predecessor-mark-type-i
- **Stage:** 2-fully-proven (classical paper deduction; Lean pending)
- **Type:** THEOREM; no scientific novelty claimed
- **Source:** [Transverse-mark attempt](../1-in-progress/goldbach-transverse-mark-correlation.md).

## Statement

Let T tend to infinity through even integers and write L=log T. Fix K≥1,
C≥0, 0≤θ<1 and 0≤u<(1−θ)/2. For 1≤i≤K put

    a_i=1/10+i/(10(K+1)),
    P_i={p prime: exp(L^a_i)<p≤exp(2L^a_i), p∤T−1},
    V_i=Σ_(p∈P_i)1/p,
    W_T(v)=∏_i [ω_i(v)2^(1−ω_i(v))/V_i]  (v≥1),
    Z=exp(L^(24/100)).

Here ω_i counts distinct prime divisors from P_i, and R_Z(v) indicates
that every prime divisor of positive v exceeds Z. For arbitrary complex
coefficients |α_d|≤L^C, define

    U_q(t)=Σ_(d≤T^u, R_Z(d)=1) α_d
           Σ_(1≤dk≤t, k odd) R_Z(k) μ(T−dk) W_T(T−dk−1)
                                      1_(q|T−dk).

The endpoints satisfy 0≤t≤T−2,
so the mark's argument is positive. Then, for every fixed A>0,

    Σ_(q≤T^θ, q odd squarefree, (q,T)=1)
      max_(0≤t≤T−2)|U_q(t)| ≪_(A,K,C,u,θ) T L^−A.             (P1)

The pools are punctured at T−1, not T. Root moduli may share pool primes.
The mark no longer vanishes merely because T−dk is a large prime.
This assertion supplies no primality restriction on the long variable k.

## Inputs

Use the maximal Möbius Bombieri–Vinogradov theorem and prime reciprocal
Mertens already checked on the [retained-modulus Type I card](goldbach-retained-modulus-type-i.md).
That card proves the required uniform coprimality extension: for fixed
δ>0, C_0 and B, uniformly in R≤H^C_0,

    Σ_(m≤H^(1/2−δ), (m,R)=1) max_(c,m)=1 max_(v≤H)
      |Σ_(h≤v, h≡c mod m, (h,R)=1) μ(h)| ≪ H(log H)^−B.       (BV)

It also proves ordinary and primitive affine divisor moments. In the
uses below the slope is T^o(1), the intercept is O(T), and the interval
has length comparable to T divided by the slope. For fixed j the bound
is that length times O((log T)^(2^j−1)). The gcd of slope and intercept
must be one; each application below checks this explicitly.

Mertens gives V_i=log 2+o(1). Puncturing at T−1 removes at most
O(L exp(−L^(1/10))) reciprocal mass. Thus W_T is bounded uniformly in T.

## Proof

### 1. Errors before progression reduction

Choose J=ceil(c_A log L), with c_A sufficiently large depending also on
the fixed parameters. Three reductions are needed.

First discard (d,T)>1. Such a d has a prime p>Z dividing T and dk.
Summing the root multiplicity before discarding q costs τ(T−dk).
Grouping x=dk costs at most L^C τ(x). The divisor-moment argument on
the retained-modulus card therefore bounds this error by

    O(T L^(C+4)/Z).                                           (1)

Second replace R_Z(k), for odd k, by

    S_J(k)=Σ_(r|k, r squarefree, p|r⇒2<p≤Z, ω(r)≤J) μ(r).

Since d is Z-rough, Bonferroni's error has the same small-prime count
at k and dk. Its root-averaged contribution is at most

    O(T L^(C+3)) [4Σ_(2<p≤Z)1/p]^(J+1)/(J+1)!.                (2)

This includes roots sharing primes with T in the intermediate error
bound: for the divisors r in Bonferroni, extract g=(r,T), then use
the primitive affine moment at intercept T/g and slope r/g.
All such r are T^o(1). Since Σ_(p≤Z)1/p=O(log L), choosing c_A
large enough makes (2) smaller than any requested fixed power of L.

Third expand the mark. The same finite Taylor formula as on that card gives

    W_T(v)=Σ_(a|v)c_a+E(v),  |E(v)|≤Σ_(a|v)e_a,  e_a≥0,
    Σ_a e_a τ(a)/a ≪_K C_K^J/J!.                             (3)

The support consists of odd squarefree a with (a,T−1)=1 and a=T^o(1).
For c_a, each band contributes between 1 and J primes. Its coefficient
with s primes is s(−1/2)^(s−1)/V_i. Hence |c_a|≪_K1, because
s2^(1−s)≤1 for every positive integer s. Error divisors have at most
K(J+1) prime factors. These assertions follow from the explicit finite
expansion, not a probabilistic approximation of the mark.

After the roughness truncation, summing d and using |S_J(k)|≤τ(k)
costs at most L^C τ(x)^2 at x=dk. Including q costs τ(T−x). Thus
the mark-error sum is at most

    L^C Σ_a e_a Σ_(1≤ah≤T−2) τ(T−1−ah)^2 τ(ah+1).             (4)

Both affine sequences are primitive. The first uses (a,T−1)=1;
the second has constant term one. Cauchy–Schwarz with their fourth
and second divisor moments gives an inner bound O((T/a)L^9).
For the increasing sequence, reverse h in its finite interval to use
the decreasing affine-moment formulation; the new intercept is 1
modulo a and is O(T). Equations (3)–(4) give

    O_K(T L^(C+9) C_K^J/J!).                                 (5)

All three errors are bounded over the full admissible interval, so
maximal endpoints introduce no extra factor. Fix c_A to pay these
errors before choosing the precision B in (BV).

### 2. Exact progression and automatic coprimalities

Fix retained a,q,r and put k=rj, g=(r,T), r'=r/g. We have (d,T)=1
after (1), and g,r' are coprime because r is squarefree. On a nonempty
support,

    q | T−drj,       a | T−drj−1.

Since (q,T)=1, necessarily (q,dr)=1. Also (a,qg)=1: the integer
T−drj is divisible by qg, while it is one modulo a. Finally (a,dr)=1.
Indeed a and d are already disjoint by their prime ranges. If a prime
divided a and r, the mark congruence would force it to divide T−1,
contrary to the definition of the pools.

Set T−drj=qgh. The progression becomes exactly

    T/g−dr'j=qh,
    h ≡ (T/g)q^−1 mod dr',
    h ≡ (qg)^−1 mod a.                                      (6)

The CRT modulus is therefore

    m=a d r',                                                (7)

not dr' and not lcm(a,q). Its residue is reduced: (dr',T/g)=1,
and the second residue is a unit modulo a. We also have (m,2qg)=1.
All d,r,a,q,g are odd, so j is odd exactly when h is odd.
Squarefreeness of qg gives

    μ(qgh)=μ(qg)μ(h)1_((h,qg)=1).

Consequently the sum over j is a Möbius sum in one reduced class
modulo m, with (h,R)=1 for R=2qg, on an interval inside
1≤h≤H=T/(qg). Its moving endpoints cost twice the maximum in (BV).

### 3. Aggregate marks into the BV modulus

Applying BV separately for every a would lose the reciprocal factor
needed to sum the marks. Instead sum a,d,r' together for fixed q,g.

For a given modulus m, its Z-rough part is exactly d. Its remaining
part ar' is squarefree and has at most (K+1)J prime factors. Each
factorization into a and r' is determined by a subset of those primes.
Thus the multiplicity is at most

    2^((K+1)J) = O(L^D_0)                                   (8)

for a fixed D_0 depending on c_A,K. The bound |c_a|≪_K1 and
|α_d|≤L^C add only another fixed power of L. Different factorizations
can give different residues in (6); the maximum over reduced residues
in (BV) handles each of them. No common-residue assertion is used.

Now m≤T^(u+o(1)) and H≥T^(1−θ−o(1)). The strict inequality
2u+θ<1 supplies a fixed δ>0 for which m≤H^(1/2−δ) for all large T.
Also R≤H^C_0 for a fixed C_0 depending on θ. Hence, for fixed q,g,
the whole retained sum is

    O_B(L^(C+D_0) T/(qg) L^−B).                              (9)

Summing g over divisors of rad(T) costs at most 1+log T, since these
are distinct positive integers at most T. Summing 1/q costs another
1+log T. Choose B>A+C+D_0+2. Equations (1), (2), (5) and (9)
prove (P1).

## Audit and scope

- Mark roots and Möbius roots now impose different residue classes.
  Their CRT modulus and its multiplicity are both retained.
- The new puncture (a,T−1)=1 is essential to the primitive mark-error
  moment and to (a,r)=1. Puncturing only at T would not justify either.
- Root moduli sharing pool primes are allowed; incompatible chosen
  divisors a contribute zero. No unconditional (q,P_i)=1 is imposed.
- The final BV precision is chosen after the truncation order, so the
  polylogarithmic multiplicity in (8) causes no circular parameter choice.
- The resulting support permits prime complements, but (P1) estimates
  an unrestricted long variable. It does not bound the balanced Type II
  form or prove that a marked Goldbach representation exists.

**Verdict: BRIDGE.** This is a classical BV deduction, not a claim of
new scientific knowledge. The exact maximal Möbius-BV Lean dependency
remains unavailable in the previously inspected corpus. No new analytic
assumption or unproved interface has been inserted into Lean.

- [x] Complete paper deduction and arithmetic/error audit.
- [ ] Exact unconditional Lean dependency closure and theorem.
- [ ] Balanced signed estimate on the same predecessor-mark support.

## Log

- 2026-10-23 — Derived the predecessor-mark reduction directly. Retained
  CRT modulus a d r/g and paid its multiple representations by the finite
  truncation order. The balanced signed correlation remains unresolved.
