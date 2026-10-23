# Primality-compatible marks on the predecessor of a Goldbach summand

- **ID:** goldbach-transverse-mark-correlation
- **Stage:** 1-in-progress
- **Type:** CONJECTURE; direct analytic proof attempt
- **Source:** Goldbach programme, cycles 7–10; user direction to prioritize original proof work.

## Exact change of arithmetic support

Existing divisor marks W(n) vanish when n is a large prime. Replace them by
W(n−1). This weight can be positive when n itself is prime. It is therefore
possible to seek a prime pair on its support without subsequently removing
the marks. This is a change of proof target, not a claim that cancellation
survives the change.

Let T be even, n=T−p, and let the disjoint small-prime pools avoid T−1.
Use the same nonnegative bounded mark W as the previous Type I card, now
evaluated at n−1. The eventual target is a negative Liouville first moment
on the support where p is prime and n is below the cube of its least prime
factor. That would detect a genuine prime complement. No signed estimate
is assumed in a Lean statement.

A negative Möbius first moment on that support would also suffice:
the possible composites have two prime factors counted with multiplicity,
so their Möbius values are zero or positive. The Type I theorem below is
for μ. Its assembly therefore requires the μ version of the balanced
estimate; a λ estimate alone is not being substituted for it.

## Immediate analytic target

Derive the root-averaged Type I estimate with W(T−dk−1) in place of
W(T−dk), keeping all root congruences. Then attack the balanced Type II
form directly. The Type I derivation is useful only with the new support;
it must not be mistaken for control of the balanced form.

For bounded α,β, the balanced expression is

`B_T = Σ_(m≈M,n≈N) α_m β_n μ(T−mn) W(T−mn−1)`.

The λ version is also examined below to test the proposed multiplicative
mechanism. The μ version is required for the proved Type I input.

All cutoffs must restrict T−mn to a fixed positive fraction of T.
M,N are positive powers of T. Any claim of a logarithmic saving must
control the actual centered covariance after Cauchy, including its diagonal.

## First proof obligations

1. Derive the exact congruences and effective modulus for the Type I sum.
2. Prove and quantify the mark-expansion and truncation errors on this support.
3. In Type II, retain the affine intercepts after expanding marks. Determine
   whether the inherited multiplicative argument still applies; do not
   silently treat an affine Liouville value as multiplicative.
4. Prove a signed estimate for the resulting covariance, or record the exact
   failed inference and pursue a different argument. A new name for that
   covariance is not progress toward its estimate.

## Type I: paper deduction completed

The exact theorem and full proof are on the
[predecessor-mark Type I card](../2-fully-proven/goldbach-predecessor-mark-type-i.md).
It holds for d≤T^u and root moduli q≤T^θ throughout 2u+θ<1, with
arbitrary fixed logarithmic precision and roots sharing pool primes allowed.

After the roughness divisor r is introduced, put g=(r,T), r'=r/g and
T−drj=qgh. The two residue conditions on h are

    h≡(T/g)q^−1 mod dr',     h≡(qg)^−1 mod a.

Puncturing the pools at T−1 makes (a,r)=1 on nonempty support.
The effective modulus is a d r', and the length is T/(qg).
The key summation step is to aggregate a,d,r' into that modulus before
using Möbius BV. A modulus has at most 2^((K+1)J) admissible
factorizations, where J=O(log log T), so the multiplicity is only a
fixed power of log T. Applying BV separately for each a would not pay
the mark sum. Both truncation errors, including their root multiplicities,
are proved on the linked card.

This is a classical paper consequence, not new scientific knowledge.
Its maximal Möbius-BV Lean dependency remains open. It is not a signed
prime-correlation estimate.

## Direct attack on the balanced term

Take m and n in dyadic intervals containing at most M and N integers,
with MN comparable to T and M,N≥T^ε. Fix f∈{μ,λ} and write

    F(m,n)=1_(T/4≤T−mn≤T/2) f(T−mn) W_T(T−mn−1),
    C(n₁,n₂)=Σ_m F(m,n₁)F(m,n₂).

For |α_m|,|β_n|≤1, Cauchy–Schwarz gives exactly

    |Σ_(m,n) α_m β_n F(m,n)|²
       ≤ M Σ_(n₁,n₂) β_n₁ conjugate(β_n₂) C(n₁,n₂)
       ≤ M Σ_(n₁,n₂)|C(n₁,n₂)|.                              (11)

The first expression on the right is real and nonnegative; no signed
covariance is discarded before the displayed inequality. Both choices
of f obey it, since their absolute values are at most one.

### What can be bounded directly

The mark is uniformly bounded, say by C_K. The diagonal satisfies
Σ_n C(n,n)≤C_K² MN. More generally the contribution of
|n₁−n₂|≤H to the last sum in (11) is at most

    C_K² M N(2H+1).                                          (12)

Its contribution to the bound for |B_T| is at most
C_K M sqrt(N(2H+1)). Taking H=floor(N L^(−2A−2)) pays this region
at precision T L^−A, since N≥T^ε. Thus the diagonal and very nearby
slopes are not the missing term. For the remaining pairs, the absolute
bound |C|≤C_K²M gives only O(T), with no logarithmic saving.

### Exact arithmetic after two marks

For a retained pair of divisor marks a₁,a₂, the congruences are

    n_i m ≡ T−1 mod a_i   (i=1,2).

Because (a_i,T−1)=1, a nonempty progression forces (n_i,a_i)=1.
The CRT compatibility condition is exactly

    gcd(a₁,a₂) | n₁−n₂.                                     (13)

Indeed the residues for m are (T−1)n_i^−1 modulo a_i; cancel the
three units modulo gcd(a₁,a₂). When (13) holds, the full modulus is
D=lcm(a₁,a₂). Write m=m₀+Dv and A_i=T−n_i m₀. For f=λ the signs become

    λ(A₁−Dn₁v) λ(A₂−Dn₂v),       A_i≡1 mod a_i,               (14)

and their affine determinant is

    A₁(−Dn₂)−A₂(−Dn₁)=DT(n₁−n₂).                            (15)

Thus shared marks constrain the difference of slopes but do not
divide the corresponding signed arguments. Pulling out λ(D) or λ(a_i)
would be an invalid use of complete multiplicativity. The old common-
cofactor proof does not transfer to (14).

Combining the signs by multiplicativity instead gives

    λ((A₁−Dn₁v)(A₂−Dn₂v)).

This is a reducible quadratic with discriminant D²T²(n₁−n₂)².
The Type I theorem concerns one linear Möbius progression and gives
no estimate for this quadratic sign. Replacing it by its absolute
value recovers only the unsuccessful O(T) bound above.

For f=μ, put L_i(v)=A_i−Dn_i v. The exact expression is

    μ(L₁(v))μ(L₂(v))
      =μ(L₁(v))² μ(L₂(v))² λ(L₁(v)L₂(v)).

The two squarefreeness indicators must remain. Removing them from a
signed sum would be another unsupported step; the λ calculation does
not prove a μ estimate.

### Precise next target, not an assumed input

For every fixed ε,A,K>0, prove for the actual F above with f=μ that

    Σ_(n₁,n₂, |n₁−n₂|>N L^(−2A−2)) |C(n₁,n₂)|
        ≪_(ε,A,K) M N² L^−2A.                               (16)

Together with (11)–(12), this would give the balanced estimate at
root modulus one. It is a sufficient stronger target, not a theorem
or a reformulation claiming equivalence with Goldbach. A proof could
also retain the β-weighted signs in (11), avoiding the stronger
absolute-value demand in (16). No estimate for either version has
been proved here. Even that root-one estimate would still need a
root-averaged extension and a complete prime-detecting argument.

## Status and research audit

- Type I: complete paper deduction; Lean analytic closure missing.
- Type II: the diagonal/near-slope bound and exact CRT reduction are
  established above. The signed off-diagonal estimate is **[OPEN CORE]**.
- The route remains active. Only the attempted transfer of the old
  multiplicativity step has failed; no impossibility theorem is claimed.
- No new scientific knowledge or Goldbach proof is claimed. The work
  removes a support defect and reaches an actual unproved signed sum;
  adding more names or detector identities would not estimate it.
- Next work must attack the far-slope signed average in (11) or (16).
  Source auditing is not a substitute for that argument.
