# Signed determinant sum when the modulus consumes the marks

- **ID:** twin-prime-consumed-mark-determinant
- **Stage:** 1-in-progress
- **Type:** CONJECTURE / BRIDGE
- **Source:** [partial-layer deduction](../2-fully-proven/twin-prime-partially-consumed-mark-energy.md)
- **Statement:** Obtain every fixed logarithmic saving for the
  fully consumed contribution while retaining both Möbius factors.

## Exact candidate

Use the fixed bands, `rho=1/2`, `omega`, `V_i`, `W_X`,
`Z=exp((log X)^(24/100))`, and actual Type II coefficients of
the source card. For fixed `delta,C>0`, the lengths satisfy
`MN` comparable to `X`, `M,N>=X^delta`; the Vaughan cutoffs
are `U=V=X^(1/10)`, and `|v|<=X^C`.

For odd squarefree `q`, put

`C_q(t)=mu(q)W_X(q) sum_(h>=1,gcd(q,h)=1)
  mu(h) rho^omega(h)
  sum_(mn+2=qh, X<mn<=t) alpha_m beta_n`.

The proposed estimate is: for every `A>0`, some fixed `K`
and fixed distinct band exponents in `(1/10,1/5)` give

`sum_(q<=X^(51/100),q odd squarefree)
  sup_(X<=t<=2X) |C_q(t)| << X/(log X)^A`.

All constants are uniform in the stated blocks and frequencies.
The choice of `K` precedes `X`. This is the empty-free-group
layer of the exact expansion, not the entire marked root sum.
Layers with a positive but insufficient number of free groups
also remain open.

**[OPEN CORE]** Cancellation must survive the root-modulus
absolute values with the actual arithmetic coefficients. A
positive cofactor energy without marking groups cannot supply
the required saving.

## Exact determinant representation

For the empty free subset, the aggregation coefficient is

`mu(k)rho^(omega(k)-K) prod_i(omega_i(q)/V_i)`, `q|k`.

Write `k=qh`. If `gcd(q,h)>1`, `mu(k)=0`. Otherwise,
squarefreeness of `q` and multiplicativity give exactly

`mu(k)rho^(omega(k)-K) prod_i(omega_i(q)/V_i)
 =mu(q)W_X(q) mu(h)rho^omega(h)`.

Thus the candidate is exactly `T_(q,empty)` on the source card.
Dualizing the absolute values introduces arbitrary unit-modulus
weights `epsilon_q` and individual endpoints `t_q`. The resulting
sum is over

`m n-q h=-2`,

with coefficient

`epsilon_q mu(q)W_X(q) mu(h)rho^omega(h)
 mu(m)R_Z(m)m^(iv) c_V(n)R_Z(n)n^(iv)`,

and the retained restriction `gcd(q,h)=1`. The factor `mu(q)`
may be absorbed in `epsilon_q`; neither `mu(m)` nor `mu(h)`
may be discarded. Since all variables are odd on the support,
the determinant equation implies `gcd(m,h)=gcd(q,n)=1`.
It does not imply `gcd(q,h)=1`.

The representation exposes a four-variable determinant problem
with arithmetic coefficients in every variable. It does not
turn those coefficients into smooth functions or separate a
coupled Fourier coefficient without cost.

## Attack against the parent theories

1. [Bettin--Chandee, Corollary 1](https://arxiv.org/abs/1502.00769)
   estimates determinant representations with arbitrary coefficients
   in two variables and smooth weights in the other two. Its
   derivative bounds involve a smoothness parameter `eta`, with
   an `eta^(3/2)` loss in the error. The actual coefficients above
   have not been shown to satisfy that interface. Arbitrary
   Fourier expansion does not give the required frequency
   localization or coefficient norm. Corollary 1 and Theorem 1
   were checked in the primary PDF, pages 2--4.
2. The purported stronger bilinear Kloosterman estimate
   [Dong--Robles--Zeindler, arXiv:2601.00292](https://arxiv.org/abs/2601.00292)
   was withdrawn on 5 January 2026. The withdrawal notice identifies
   a missing squared amplification factor, which removes the
   claimed improvement. It is not an available input.
3. [Guo, almost-prime-pairs reduction, Theorems 1.4--1.5](https://github.com/aster2024/openai-math-followups/blob/main/almost-prime-pairs-reduction/paper.pdf)
   states counterexamples to transfers based only on specified
   one-point, affine-correlation, character, and Type I estimates.
   The model sequences explicitly fail complete multiplicativity.
   Statements and scope were checked, not the full constructions.
   These results do not refute the candidate for the actual Möbius
   coefficients. They do rule out claiming that the listed generic
   numerical estimates alone finish the transfer.
4. The corpus search `determinant shifted convolution four
   coefficients Mobius bilinear Kloosterman` located exact
   convolution identities, Kloosterman kernel definitions, and
   conditional energy criteria, but no matched cancellation
   theorem. The existing finite modulus-energy certificate is
   not such an arithmetic theorem.

**Verdict: BRIDGE.** Exact remaining signed problem; no proof or
scientific novelty claimed. It does not assume twin primes, but
neither does its formulation establish a new cancellation mechanism.

## Why the unsigned empty-label energy cannot work

There is a direct lower-bound diagnostic for the actual coefficients
at `v=0`. Set `M=N=T`, `X=T^2`, use the blocks `(T,2T]`, and put

`f(s)=sum_(mn=s) mu(m)R_Z(m)c_V(n)R_Z(n)`

on these blocks. For distinct primes `p,r` in `(T,sqrt(2)T]`,
the only admissible factorizations of `pr` are `(p,r)` and `(r,p)`.
For sufficiently large `T`, both primes exceed `Z,U,V`, and hence

`f(pr)=-log r-log p=-log(pr)`.

Unique factorization makes these products distinct for distinct
unordered pairs. The prime number theorem on this fixed-ratio
interval gives at least `c T/log T` eligible primes. Therefore

`sum_(X<s<=2X)|f(s)|^2 >= c' X`.

Thus the proposed empty-label bound `E_0<<X/(log X)^D` fails
for every `D>0`. This does not refute the signed candidate:
`mu(qh)` is absent from this nonnegative energy. It identifies
precisely why that sign must remain in a replacement argument.
This lower-bound deduction is now
[formalized and axiom-audited](../3-formalized/twin-prime-semiprime-energy-lower-bound.md).

For formalization, use the slightly more uniform statement with
arbitrary natural cutoffs `z,V<=T` in the coefficient `f` and
energy over `T^2<s<=2T^2`. The same proof works: take the first
prime in `(T,6T/5]` and the second in `(6T/5,7T/5]`. Their
product is at most `42T^2/25<2T^2`, and unique factorization is
injective on this Cartesian product because the intervals are
disjoint. Each interval contains `>>T/log T` primes by PNT.
The original cutoffs eventually lie below `T`, so this stronger
cutoff-uniform lower bound implies the displayed diagnostic.
The unconditional PNT is available in `PNTPlus/Consequences.lean`;
its exact statement and vendoring provenance were inspected. The
formal proof uses `chebyshev_asymptotic` below. No conditional PNT
interface is needed.

The logarithmically weighted form gives a cleaner precise bound.
Let `P=(T,6T/5]` and `R=(6T/5,7T/5]`, restricted to primes,
and let `Theta_P,Theta_R` be their sums of `log p`. The corpus's
`chebyshev_asymptotic` gives `Theta_P/T -> 1/5` and
`Theta_R/T -> 1/5`. Eventually each mass is at least `T/10`.
Injectivity of `(p,r) -> pr` on `P x R` and
`(log p+log r)^2>=4 log p log r` give

`sum_(T^2<s<=2T^2)|f(s)|^2
 >=4 Theta_P Theta_R >=T^2/25`.

This holds uniformly for all natural cutoffs `z,V<=T`, once `T`
is large. It avoids any cardinality estimate or division by `log T`.
The exact semiprime coefficient, full lower bound, and failure of
`o(T^2)` for every cutoff family are certified in
`twin-prime/SemiprimeEnergy.lean`. The leaf and capstone axiom audits
passed with only standard foundational axioms. This closes the
[unsigned shortcut](../5-failed/twin-prime-unsigned-empty-label-energy.md),
while the signed candidate remains open.

## Formalization leads and obligations

The pinned source
[`plasma-ai/erdos-408`, commit `5b02bf9ab59fd813af8f19c604ba70254fced08d`](https://github.com/plasma-ai/erdos-408/tree/5b02bf9ab59fd813af8f19c604ba70254fced08d)
contains `Erdos408.OneSided.eventually_detMoment` and a position-model
formalization of the shift-1 method. `OneSidedTypeII` exposes
character--Mellin and integer-kernel inputs, discharged for its
own application. Its README's toolchain is Lean 4.35.0; this
workspace uses 4.32.2. Relevant source statements were read;
the external project has not been compiled or axiom-audited here.
Neither a shift-2 extension nor an open analytic premise has
been imported into the twin-prime Lean namespace.

- [x] Exact signed endpoint and determinant representation.
- [x] Parent-theory and current-source interface attack.
- [ ] Prove cancellation with the actual two Möbius factors.
- [ ] Close the other layers with too few free groups.
- [ ] Unconditional Lean proof of the analytic statement.
- [x] Formalize and axiom-audit the positive empty-label energy lower bound.

## Log

- 2026-10-23 — Isolated the fully consumed contribution after the
  partial-layer aggregation. Checked the smoothness limitation of
  the classical determinant theorem and excluded a withdrawn
  proposed improvement. Retained the exact arithmetic signs and
  individual endpoints. Twin-prime infinitude remains unproved.
- 2026-10-23 — Completed the cutoff-uniform positive energy theorem
  and its Lean audit. This rules out the unsigned shortcut without
  removing the signed cancellation obligation.
