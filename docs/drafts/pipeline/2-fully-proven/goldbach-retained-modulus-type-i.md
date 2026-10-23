# Reflected Type I sums with shared marking primes retained

- **ID:** goldbach-retained-modulus-type-i
- **Stage:** 2-fully-proven (classical paper deduction; Lean pending)
- **Type:** THEOREM (paper; classical consequence, not a novelty claim)
- **Source:** [Goldbach programme](../1-in-progress/goldbach-unconditional-2026-10-23.md), Cycle 8.
- **Statement:** A reflected marked Type I estimate averaged over polynomial
  root moduli, including moduli sharing marking primes.

## Exact statement T1

Let T tend to infinity through even positive integers, L=log T, and fix
an integer K≥1. Put a_i=1/10+i/(10(K+1)) for 1≤i≤K. Let P_i be the primes
in (exp(L^a_i),exp(2L^a_i)] not dividing T, and let V_i=Σ_(p∈P_i)1/p.
Define

    ω_i(n)=#{p∈P_i:p|n},
    W_T(n)=∏_i [2^(1−ω_i(n))ω_i(n)/V_i],
    Z=exp(L^(24/100)).

R_Z(n) is one if every prime factor of positive n exceeds Z, and zero
otherwise. For arbitrary complex coefficients |α_d|≤L, set, for 0≤t<T,

    T_q(t)=Σ_(d≤T^(1/5), R_Z(d)=1) α_d
           Σ_(1≤dk≤t, k odd) R_Z(k) μ(T−dk)W_T(T−dk)1_(q|T−dk).

**[PROVED HERE, on paper]:** for every fixed A>0,

    Σ_(q≤T^(51/100), q odd squarefree, (q,T)=1)
      max_(0≤t<T)|T_q(t)| ≪_(A,K) T L^−A.

No condition requires q to avoid the marking primes. Shifted arguments
are positive. The estimate is uniform in T and the allowed coefficients.

## Classical inputs and their exact scope

Möbius Bombieri–Vinogradov, including the maximum over endpoints, is
Proposition 3, p. 115, of Murty–Vatwani,
[A remark on a conjecture of Chowla](https://mrammurty-ai.github.io/chowla.pdf),
J. Ramanujan Math. Soc. 33 (2018), 111–123. It cites Siebert–Wolke,
Math. Z. 122 (1971), Corollary 1. The primary PDF's statement and
bibliography were read. It covers every residue class; only reduced
classes are used below. For each B there is C_B such that the sum of
maximal Möbius progression sums over moduli at most
x^(1/2)/(log x)^C_B is O_B(x/(log x)^B).

The other analytic input is prime reciprocal Mertens:
Σ_(p≤x)1/p=log log x+constant+o(1). It gives V_i=log 2+o(1), uniformly
after puncturing: removed mass is at most L exp(−L^(1/10)). It also
gives Σ_(2<p≤Z)1/p=O(log L). The bands are disjoint and lie below Z
for sufficiently large T. Constants may be ineffective.

No LWW energy theorem or target-dependent zero-free hypothesis is
used in this proof.

## Paper proof

### 1. Uniform coprimality extension of Möbius BV

For fixed C, δ, B>0, uniformly in positive integers R≤H^C,

    Σ_(m≤H^(1/2−δ), (m,R)=1) max_(c,m)=1 max_(v≤H)
      |Σ_(n≤v, n≡c mod m, (n,R)=1) μ(n)| ≪_(C,δ,B) H(log H)^−B.    (1)

Let s_R(v) indicate integers whose prime factors divide R. Prime-power
Euler factors give the exact convolution
μ(n)1_((n,R)=1)=(μ*s_R)(n). Fix 0<η<min(1,2δ) and split the convolution
variable v at H^η. For short v, invert v modulo m and use classical
BV at H/v. The modulus range has a fixed power margin. Summing costs
at most Σ_(v≤H^η)1/v≤1+log H; request one extra logarithm of precision.

For each fixed σ>0,

    Σ_v s_R(v)/v^σ = ∏_(p|R)(1−p^−σ)^−1 = H^o(1),                (2)

uniformly for R≤H^C. Split primes at (log H)^(1/2). The logarithm
of the small-prime product is O_σ((log H)^(1/2)); the larger-prime
part is O_(C,σ)((log H)^(1−σ/2)), hence o(log H). Consequently the
reciprocal tail beyond H^η is at most H^(−η/2+o(1)), using σ=1/2,
and there are at most H^(1/4+o(1)) R-smooth integers up to H, using
σ=1/4. The trivial progression count H/(vm)+1 bounds the long part by

    H(1+log H)H^(−η/2+o(1)) + H^(1/2−δ)H^(1/4+o(1)).

Both terms save a fixed power. This proves (1), including both maxima.

### 2. Divisor moments for the errors

For every fixed integer j≥1,

    Σ_(h≤H)τ(h)^j ≪_j H(1+log H)^(2^j−1).                       (3)

The prime-power inequality (e+1)^j≤binom(e+2^j−1,2^j−1) gives
τ^j≤τ_(2^j). One proof of that inequality maps a j-tuple of
exponents in {0,...,e} to the counts of its 2^j membership profiles
at levels 1,...,e; the counts recover each exponent. Summing the
ordered factorizations defining τ_(2^j), with one factor last,
proves (3).

The same bound holds for τ(U−bh)^j on 1≤h<U/b, with H=U/b, if
(U,b)=1 and b≤U^(1/2^j). Among 2^j factors of U−bh omit a largest
one. The remaining product v≤U^(1−1/2^j)≤H is coprime to b. Its h
lie in one class modulo v, with count at most H/v+1≤2H/v. Sum
τ_(2^j−1)(v)/v to obtain the bound. This proves all affine moments
below; no shifted-divisor asymptotic is assumed.

### 3. Discard d sharing the target

Since 0≤2^(1−ω)ω≤1 for integers ω≥0, W_T is bounded in terms of K.
Sum absolute errors over q before dropping its root condition; the
multiplicity is at most τ(T−dk). Group n=dk and use
Σ_(d|n)|α_d|≤Lτ(n). If (d,T)>1, some prime p>Z divides n and T.
Write U=T/p and n=pv. Since τ(pv)≤2τ(v), Cauchy–Schwarz and (3) give

    L Σ_(p|T,p>Z) Σ_(1≤v<U) τ(pv)τ(p(U−v))
      ≪ L^4 Σ_(p|T,p>Z) T/p ≪ T L^5/Z.                         (4)

This is negligible at every fixed logarithmic precision. Henceforth
(d,T)=1. The estimate includes q multiplicity; an unweighted pair
count would not suffice.

### 4. Roughness truncation with root multiplicity

Let J=ceil(C_A log L), increasing C_A below as necessary. On odd k
replace R_Z(k) by the alternating divisor sum S_J(k) over squarefree
r|k with primes 2<p≤Z and ω(r)≤J. Finite Bonferroni gives

    |R_Z(k)−S_J(k)|≤binom(ω_((2,Z])(k),J+1).

As d is Z-rough, this prime count equals that for n=dk. The total
root-averaged error is therefore at most a constant times

    L Σ_(r squarefree, ω(r)=J+1, p|r⇒2<p≤Z)
        Σ_(1≤n<T,r|n)τ(n)τ(T−n).                                (5)

Put g=(r,T), r'=r/g, U=T/g, n=rh. Squarefreeness gives (r',U)=1.
Also

    τ(n)τ(T−n)≤τ(r)τ(g)τ(h)τ(U−r'h),  τ(r)τ(g)≤4^(J+1).

Every r in (5) is at most Z^(J+1)=T^o(1). The affine j=2 bound
applies, including when r shares primes with T. Cauchy–Schwarz makes
the inner sum at most 4^(J+1)(T/r)O(L^3). Thus (5) is at most

    O(TL^4) [4Σ_(2<p≤Z)1/p]^(J+1)/(J+1)!.

Since the prime reciprocal sum is O(log L), choose C_A large enough
to obtain O_A(TL^−A). Maximal endpoints cost nothing here: these
nonnegative errors are bounded over all 1≤n<T.

### 5. Mark expansion and weighted remainder

For f(ω)=ω2^(1−ω), Taylor's theorem for ωx^(ω−1) at x=1 gives

    f(ω)=Σ_(s=1..J)s(−1/2)^(s−1)binom(ω,s) + remainder,
    |remainder|≤(J+1)2^−J binom(ω,J+1).                         (6)

At ω=0 both sides are zero; if ω≤J the remainder is zero. Apply
(6) in each band and divide by V_i. Disjoint bands give

    W_T(N)=Σ_(a|N)c_a+E(N),  |E(N)|≤Σ_(a|N)e_a,  e_a≥0,        (7)
    Σ_a |c_a|τ(a)/a≪_K1,
    Σ_a e_a τ(a)/a≪_K C_K^J/J!.                               (8)

Every a is odd, squarefree, coprime to T and at most T^o(1).
For completeness, in one band the divisor factor τ(a)=2^s makes
the absolute degree-s coefficient 2s/V_i. Its reciprocal sum is
at most 2sV_i^(s−1)/s!, whose sum is 2e^V_i. The weighted
reciprocal remainder is at most 2V_i^J/J!. Telescope the product
error, bounding an exact factor by 1/V_i and a truncated factor
by its absolute divisor expansion. These bounds prove (8).

After roughness truncation, |S_J(k)|≤τ(k)≤τ(dk). Including d and q
multiplicities, the error from (7) is at most

    L Σ_a e_a τ(a) Σ_(1≤h<T/a)τ(h)τ(T−ah)^2.

The affine argument is primitive because (a,T)=1. Cauchy–Schwarz,
(3) and its affine form at j=2,4 bound the inner sum by
(T/a)O(L^9). The total is O_K(TL^10 C_K^J/J!), negligible at every
fixed requested precision. Both truncations are paid in their actual
order.

### 6. Exact reflected progression

Fix retained a,q,r and write

    l=lcm(a,q),  g=(r,T),  r'=r/g,  m=d r'.

Joint root conditions give l|T−drj with j odd. Since (l,T)=1,
a nonempty progression has (l,dr)=1. Also (d,g)=1 because d is
rough and g has primes below Z. Hence g|T−drj, (g,l)=1, and

    T−drj=lgh,  so  T/g−mj=lh.                                 (9)

Squarefreeness gives (r',T)=1; the earlier discard gives (d,T)=1.
Thus (m,T/g)=(m,lg)=1. Equation (9) gives exactly the reduced class

    h≡(T/g)l^−1 mod m.

As T is even and d,r,l,g are odd, j is odd exactly when h is odd.
Also lg is squarefree, so

    μ(lgh)=μ(lg)μ(h)1_((h,lg)=1).

Apply (1) with R=2lg. The original cutoff 1≤drj≤t<T is an interval
inside 1≤h≤H=T/(lg). It is a difference of two initial segments;
its moving lower endpoint costs two, not a short-interval theorem.

Take T large enough that every retained a,r≤T^(1/100). Then

    l≤T^(52/100), g≤T^(1/100), H≥T^(47/100), m≤T^(21/100),
    21/100 < (47/100)(1/2−1/20),  R≤H^2.

For fixed a,q,g, (d,r')↦m is injective: r' is precisely the
small-prime part of m and d its Z-rough part. Thus (1) pays the full
sum over d,r with these fixed a,q,g and coefficient cost at most L.
The resulting bound is O_B(L·T/(lg)·L^−B).

### 7. Shared marking primes are summable

For any positive a and Q≥1, the totient divisor identity gives

    Σ_(q≤Q)1/lcm(a,q)
      = (1/a)Σ_(q≤Q)gcd(a,q)/q
      = (1/a)Σ_(e|a,e≤Q)φ(e)Σ_(j≤Q/e)1/(ej)
      ≤ τ(a)(1+log Q)/a.                                     (10)

No coprimality of a,q was used. Sum step 6 over g|rad(T), using
Σ_(g|rad(T))1/g≤1+log T, then over q by (10), then over a by (8).
The result is O_(B,K)(T L^(3−B)). Take B>A+3 and add (4) and the
two truncation errors. This proves T1.

## Hostile audit and larger classical range

- Target common factors are paid before declaring the progression
  reduced. Factors g remain in (9), its length H and coprimality R.
- Shared marking primes replace aq by lcm(a,q). Their full cost τ(a)
  already occurs in the coefficient norms.
- Affine divisor moments become primitive only after gcd extraction;
  their τ(g) cost has been retained.
- Cutoff maxima and root multiplicities appear in every error bound.
  BV's modulus is dr/g; its length is T/(lg).
- No primality condition is imposed on the long variable k. This
  proves neither a signed Type II estimate nor Goldbach.

The same proof gives d≤T^u and q≤T^θ for every fixed 0≤θ<1 and
0≤u<(1−θ)/2, with |α_d|≤L^C for fixed C. Choose a fixed margin in
that strict inequality and then make the subpower a,r smaller than
the required powers. The restriction R is at most H^C' for a fixed
C' depending on θ. All error estimates remain valid. The line
2u+θ=1 is the limit of this BV substitution, not an impossibility
theorem for other methods or endpoint refinements.

## Novelty and formal dependency audit

This is a classical Möbius-BV consequence with divisor expansions
and lcm bookkeeping. **No new scientific knowledge is claimed.**
The fixed-shift proof lead is now
[the sibling root-average card](twin-prime-mark-preserving-root-average.md).
The varying-target gcd extraction also appears in Guo's
[Type I discussion](https://raw.githubusercontent.com/aster2024/openai-math-followups/main/mobius-goldbach-shift/source/main.tex).
The explicit shared-root sum (10) and target-uniform error accounting
identify the requirements of this programme. Failure to locate an
identical statement is not evidence of novelty.

Paper inputs are classical Möbius BV and prime reciprocal Mertens;
the additional bounds used here are proved above. Formal dependency
closure is not established. The local search has not supplied a
checked maximal Möbius-BV theorem. It must not be inserted as a new
Lean premise.

## Relevance and status

This removes the shared-label restriction from the Type I part of
a reflected root-average argument. The signed Type II estimate and
signed removal of marks remain separate open inputs. The final
prime-correlation theorem and Goldbach are unproved.

- [x] Exact statement and adversarial checks.
- [x] Paper proof and novelty audit; classical consequence only.
- [ ] Exact unconditional Lean theorem and dependency audit.
- [ ] Signed Type II estimate and mark-removal transfer.

## Log

- 2026-10-23 — Opened the lcm(a,q) transfer with reflected target and
  shared marking primes retained.
- 2026-10-23 — Closed the paper argument, including root-averaged
  truncation errors, target gcd extraction, and range 2u+θ<1.
  Exact analytic Lean closure and both signed prime-sum inputs remain open.
