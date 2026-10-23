# Removing squarefreeness from the reflected bilinear problem

- **ID:** goldbach-squarefree-bilinear-transfer
- **Stage:** 2-fully-proven (paper deduction; Lean pending)
- **Type:** BRIDGE; no scientific novelty claimed
- **Parent:** [Predecessor-mark correlation](../1-in-progress/goldbach-transverse-mark-correlation.md).

## Exact unconditional comparison

Fix integers T≥2 and R≥1. Let I,J be finite sets of positive integers,
and Q a finite set of positive root moduli. Let w be any complex weight
on {1,...,T−1}, and put A_w=max_(1≤x<T)|w(x)|. For a function f on
positive integers define the actual bilinear seminorm

    N_f = sup_(|α_m|≤1, |β_n|≤1)
          Σ_(q∈Q) max_(0≤t<T)
          |Σ_(m∈I,n∈J, mn≤t) α_m β_n
                       f(T−mn) w(T−mn) 1_(q|T−mn)|.          (1)

The maximum ranges over integer t. The same α and β occur for every
q and t. In particular, (1) does not permit coefficients to be chosen
separately for each root modulus. It is finite; the coefficient domain
is a finite product of closed unit discs and all displayed functions
are continuous.

Write H_X=Σ_(1≤j≤X)1/j and

    C_R(T)=Σ_(1≤d≤R)|μ(d)| τ(gcd(T,d²)).

Then the following numerical inequality is unconditional:

    N_μ ≤ C_R(T) N_λ + sqrt(8) A_w T H_T^(15/2)/sqrt(R),       (2)
    C_R(T) ≤ R H_R².                                         (3)

For Q={1}, H_T^(15/2) in (2) can be replaced by H_T^(3/2).
There is no bound on N_λ among the premises. It is the actual
Liouville seminorm appearing on the right, not an assumed analytic
interface. In the Goldbach application, incorporate the fixed fractional
cutoff and W_T(x−1) into w, setting w(1)=0.

## 1. Congruence masks separate without depending on q

For a positive k and a row index m, put g=gcd(m,k). The congruence
mn≡T mod k is empty unless g|T. When g|T, let h=k/g. Then
(m/g,h)=1 and the congruence is equivalent to

    n ≡ a_g(m) mod h,
    a_g(m)=(T/g)(m/g)^−1 mod h.                              (4)

Use a_g(m)=0 outside its designated row class. For h=1 the sole
residue and sole character are zero and one, respectively. Finite
additive-character orthogonality now gives the exact expansion

    1_(mn≡T mod k)
      = Σ_(g|gcd(T,k)) (1/h) Σ_(0≤r<h) u_(g,r)(m)v_(g,r)(n), (5)

where

    u_(g,r)(m)=1_(gcd(m,k)=g) exp(2πi r a_g(m)/h),
    v_(g,r)(n)=exp(−2πi r n/h).

Both factors have modulus at most one. The sum of absolute scalar
coefficients in (5) is exactly τ(gcd(T,k)). Importantly, none of these
factors depends on the root modulus q or endpoint t from (1).

For any f, multiplying α by u_(g,r) and β by v_(g,r) preserves the
coefficient unit discs. The triangle inequality, first for each
endpoint and then for the common root sum, therefore proves

    N_(f(x)1_(k|x)) ≤ τ(gcd(T,k)) N_f.                        (6)

The notation means multiplication of the argument x=T−mn. It does
not alter Q or replace a common coefficient family by q-dependent
ones. If (T,k)=1, the factor in (6) is exactly one.

## 2. The square-divisor tail has a uniform second moment

For positive x define

    D_R(x)=#{d>R: d²|x}.

For every integer X≥1,

    Σ_(1≤x≤X) D_R(x)² ≤ 8X/R.                               (7)

To prove this, expand the square and count multiples of
lcm(d²,e²)=lcm(d,e)². The resulting bound is

    X Σ_(d,e>R) 1/lcm(d,e)².

Write d=ga,e=gb with (a,b)=1. Dropping this coprimality only enlarges
the nonnegative series, so its value is at most

    Σ_(g≥1) g^−2 (Σ_(a>R/g) a^−2)².                         (8)

For g≤R, the inner sum is at most 2g/R. This follows from
Σ_(a>y)a^−2≤1/floor(y)≤2/y for y≥1, by integral comparison.
This part of (8) is at most 4/R. For g>R, the inner sum is at most
Σ_(a≥1)a^−2≤2, while Σ_(g>R)g^−2≤1/R. This contributes at most
another 4/R, proving (7). All exchanges concern nonnegative series.

## 3. Pay squarefreeness removal after taking the root sum

The exact squarefree expansion is

    μ(x)=λ(x) μ(x)²
        =λ(x) Σ_(d²|x) μ(d),

and hence

    |μ(x)−λ(x)Σ_(d≤R,d²|x)μ(d)| ≤ D_R(x).                   (9)

For fixed x=T−mn, the number of row-column pairs is at most τ(T−x).
The number of retained root moduli dividing x is at most τ(x).
Taking absolute errors over the entire interval before maximizing
endpoints therefore bounds the error in (1) by

    A_w Σ_(1≤x<T) τ(T−x)τ(x)D_R(x).                         (10)

The ordinary divisor moments needed here have the elementary bounds

    Σ_(n≤T) τ(n)^4 ≤ T H_T^15,
    Σ_(n≤T) τ(n)^2 ≤ T H_T^3.                               (11)

For completeness, (e+1)^j≤binom(e+2^j−1,2^j−1): map a j-tuple
of exponents in {0,...,e} to the counts of its 2^j membership profiles
at levels 1,...,e. These counts recover every exponent. Prime-power
multiplication gives τ(n)^j≤τ_(2^j)(n). Summing the ordered
factorizations defining τ_(2^j), leaving the last factor free, gives
T H_T^(2^j−1). This proves (11), without an affine-divisor hypothesis.

Cauchy–Schwarz applied to the two fourth moments gives

    Σ_(1≤x<T) τ(T−x)²τ(x)² ≤ T H_T^15.

A second application, using (7), bounds (10) by the error in (2).
For Q={1}, omit τ(x) in (10) and use the second moment in (11),
giving the smaller exponent 3/2. These errors are uniform in the
row and column sets, their aspect ratio, the endpoints and Q.

The retained sum in (9) contributes at most
Σ_(d≤R)|μ(d)|N_(λ(x)1_(d²|x)). Apply (6) with k=d² to obtain
the main term C_R(T)N_λ. This proves (2).

Finally τ(gcd(T,d²))≤τ(d²)≤τ_3(d). The second inequality follows
at a prime power p^e from 2e+1≤(e+1)(e+2)/2. Counting ordered
triples and leaving their last member free gives
Σ_(d≤R)τ_3(d)≤R H_R². This proves (3).

## Consequence for the active proof attempt

Choose R=ceil((log T)^(2A+17)). For bounded A_w, the error in (2)
is O_A(T(log T)^−A−1), and C_R(T) costs only a fixed logarithmic
power. Consequently a proof of every fixed logarithmic saving for
the actual Liouville seminorm would supply the corresponding Möbius
saving. The required larger precision is fixed in terms of A.

This identifies squarefreeness as a controlled transfer, rather than
an additional signed-correlation conjecture. It does **not** prove
the Liouville estimate. The unresolved expression is still the
coefficient-weighted covariance of the affine signs on predecessor-
mark support. The full common-coefficient root sum in (1) must be
retained in any subsequent argument.

## Audit

- The approximation is at the bilinear-sum level, before squaring a
  covariance; no uncontrolled square of a truncated mark occurs.
- The error includes both factorization and root multiplicities.
- A congruence mask is not removed at unit cost for nonunit targets;
  the exact τ(gcd(T,k)) cost is retained.
- The mask coefficients are independent of q, so (6) respects the
  placement of the supremum outside the root average.
- No linear Möbius progression theorem is applied to a quadratic
  Liouville sequence, and no prime-pair existence is inferred.
- These are classical finite-character and divisor-moment deductions.
  No external novelty claim is made. Lean dependency closure and the
  actual signed estimate are separate unfinished work.

## Log

- 2026-10-23 — Derived (2)–(3), including the second-moment tail and
  the q-independent separation of nonunit congruence masks. The
  Möbius balanced problem now reduces quantitatively to the same
  Liouville bilinear seminorm. No Liouville cancellation claimed.
