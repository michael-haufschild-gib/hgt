# Quantitative Möbius correlation for slowly growing determinant-four frames

- **ID:** twin-prime-polylogarithmic-affine-cancellation
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper deduction) / BRIDGE; not Lean-certified
- **Source:** [fixed-determinant target](../1-in-progress/twin-prime-fixed-determinant-uniformity.md)
  and [residue-matching boundary](../3-formalized/twin-prime-residue-matching-boundary.md).
- **Statement:** Actual Möbius affine correlations have a logarithmic saving, uniformly in a small positive power of the logarithm of the sample length; paper deduction from the cited source argument.

## Exact paper result

There are absolute `kappa,c,C>0` and `T0` such that for every
integer `T>=T0` and every reduced primitive frame `(a,b;c1,d)` with

`a,c1>=1`, `0<=b<a`, `0<=d<c1`,
`gcd(a,b)=gcd(c1,d)=1`, `|ad-bc1|=4`,
`a,c1 <= (log T)^kappa`,

one has

`|sum_(1<=t<=T) mu(at+b)mu(c1t+d)| <= C T/(log T)^c`.

The constants and threshold must be independent of the frame.
The proof below tracks the constants in an existing paper argument,
then pays the squarefree projection and cofactor aggregation. It is
weaker than polynomial slope uniformity. The mixed and long-cofactor
terms and positive twin-prime mass remain open. This is not a
redefinition of the main goal and is not an assumed Lean input.

## Uniform Liouville estimate: complete parameter audit

The [ordinary two-point manuscript](https://github.com/openai/math/blob/main/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/final.pdf)
states a quantitative Liouville theorem only for fixed forms and
qualitative Möbius cancellation. Its stated fixed-form theorem is
not being invoked with growing coefficients. Instead the following
argument checks the modulus dependence in its Part I proof, §§2--9.
The source PDF hash is
`ccb6f339a7505db7ab158dae4b739164ed8dda32be4012b0310198dd32f5c70a`.

Fix `h=4` and an arbitrary residue `b mod l`. Put

`F(X)=(1/X) sum_(1<=n<=X,n==b mod l) lambda(n)lambda(n+4)`.

Let `A,W` be the absolute choices in the source, `delta=1/200`,
`gamma=delta/(6W)`, `L=(log X)^(1/A)`, `J=floor(gamma log L)`,
`eta=exp(-J)`, and `K=exp(4J)`. Test moduli `l<=L^(gamma/100)`.

1. **Prime supplies.** All centered primes exceed `exp(L^0.995)`,
   hence eventually exceed `4l`, uniformly on this range. Their
   supply lower bounds therefore lose no primes to the modulus.
   Padding upper moments only decrease when primes are excluded.
2. **Finite-law comparison.** In Lemma 3.1 the modulus occurs in
   the bit-decoding error and the CRT product. Both displayed
   bounds hold uniformly already for `l<=exp L`; the tested
   range is much smaller. The circuit depth and size do not
   change with the numerical residue representative.
3. **Centering.** The source's split into at most `l` residue
   classes costs explicitly `l`, so its error is bounded by
   `C_4 l 2^J eta^(-1) L^(-1/20)`. The proved paper improvement
   retaining the coupled residue could remove this factor, but
   is not needed for this small-modulus test.
4. **Padding anti-concentration.** Removing primes dividing `4l`
   changes the characteristic-function exponent by at most
   `(16/5) sum_(p|4l) 1/p`. The elementary harmonic bound makes
   the resulting constant at most `C_4 l^4`. Thus the relevant
   deletion cost becomes at most `C_4 l^4 2^J/K`.
5. **Other deletion costs.** The positive second moment is bounded
   by the full prime product; its upper bound can be independent
   of the removed prime divisors of `l`. The residue comparison
   must still be applied with its uniform threshold above.
6. **Graph moment, §§5--7.** The only modulus test in each edge
   is a zero-one factor. In the product residue law it depends
   on the independent `l` coordinate, not the centered prime
   coordinates. Thus it is unchanged during the singleton
   integrations in Lemma 5.5. It is discarded in all positive
   exceptional-word majorants and in the final padding sum.
   The prohibited-word event uses prime divisibility only.
   Its reciprocal counts, the rank estimate, singleton
   elimination and forest code depend on `h=4`, the prime
   supply bounds and the displayed word lengths, not on `l`.
   Their constants and thresholds are consequently uniform
   once the preceding prime-supply bounds hold. The numerical
   word count and scalar expansions in §5.2 have absolute
   coefficient mass `exp(O(L^5))`; progression tests add no
   gates depending on the number of residue classes. The
   uniform finite-law comparison from item 2 applies to them.
   Hence Theorem 5.4 has its same absolute `C2` and a threshold
   independent of every `l<=L^(gamma/100)`.
7. **Spectral transfer, §§8.1--8.3.** Lemma 8.1 is a finite
   matrix identity and inequality, with no modulus parameter.
   The row bounds discard the progression indicator; padding
   mass at a retained departure is at most `K`. The degree
   projection uses only `sum V_i<=2WJ`. Proposition 8.3 thus
   has the same `C3=3 max(2,2 sqrt(8),e C2)`, independently of
   `l`. The test-vector norm in (8.9) uses the uniform truncated
   weight comparison from item 2, with `S>=1`. The exceptional
   blocks cost `e^(-2 floor L)` times a fixed power of `L`.
   In (8.13), every displacement is at most `4 exp(100L+1)`;
   `M=ceil(exp(103L))`, `T_j>=exp(L^A)`, and the row envelope
   is a fixed power of `L`. The boundary error is therefore
   `O(exp(-L))` with a uniform threshold. No modulus-dependent
   constant or threshold remains in this last transfer.

Here are further details for items 1--5, to fix the quantitative
meaning of every dependence. The prime number theorem used is
only for the fixed modulus five. For `l<=L^(gamma/100)`, none
of the centered primes divides `4l` once `L` is large; their
smallest size is `exp(L^0.995)>4l`. All positive upper moments
over padding primes are bounded by the full prime set, uniformly
in removed divisors. These prove the retained mass bound and
the degree and rare-site deletions without using an `l`-dependent
version of the prime number theorem.

In Lemma 3.1, `B=ceil(L^15)` bits per residue coordinate give
decoding error at most `2^(1-B)(l+sum p)<=exp(3L)2^(-B)`.
Every marginal involving at most `t` bits uses a CRT modulus
at most `l exp(tL)`. On an interval of length at least
`exp(L^A/2)` its variation error is at most
`exp(2tL-L^A/2)`. Both estimates already hold for `l<=exp L`.
The number of bits is at most `exp(2L)` and the decoded circuit
size at most `exp(L^17)`, regardless of the residue representative.
The source's Fourier correction and bounded-independence theorem
then give the stated comparison with a uniform threshold.

For centering, the residue indicator's additive Fourier coefficients
have total absolute value one. Thus Lemma 4.4 has a constant
depending only on `h=4`, before the split into at most `l`
shift classes. The two dyadic pieces cost an absolute factor.
No primitive-residue restriction is needed.

For padding, start with the full fixed-modulus-five prime set
and its absolute error in (4.12). Removing primes dividing `4l`
changes the characteristic-function exponent by at most
`(16/5) sum_(p|4l) 1/p <= (16/5)(1+log(4l))`.
The constant in (4.13), and hence in Lemma 4.5, is therefore
at most `C l^(16/5)<=C l^4`. The positive second moment used
for rare sites is bounded by
`prod_(p<=exp L)(1+24/p) prod_i(4 V_i^2+V_i)`,
independently of `l`. The state expansions in the deletion
transfer have the same circuit bounds as before and use the
uniform finite-law comparison just proved.

Combining these facts with the source's final assembly gives
the explicit uniform inequality

```text
|F(X)| <= C [eta + l eta^(-1) 2^J L^(-1/20)
             + 2^J (l^4/K + L^(-100) + exp(-2WJ))
             + (K/eta)(C3/sqrt(W))^J
             + exp(-L^0.9) + X^(-1)].
```

Choose the absolute constants in the source's order: first `A`,
then its absolute graph constants, then `W>=10` with
`e^5 C3/sqrt(W)<=e^(-1)`. All remaining thresholds now depend
only on these fixed constants. Since `J=floor(gamma log L)`,
`eta<=e L^(-gamma)`. The centering exponent is at most
`gamma/100+(1+log 2)gamma-1/20 < -gamma/2`.
The padding exponent is
`4gamma/100-(4-log 2)gamma < -gamma/2`.
The spectral term is at most `exp(-J)`; the other terms are
smaller than a constant times `L^(-gamma/2)` for sufficiently
large `L`. This proves, uniformly at every real cutoff,

`|F(X)| <= C L^(-gamma/2)`.

Put

`kappa0=gamma/(100A)`, `c0=gamma/(2A)=50 kappa0`.

This establishes the ambient-normalized actual Liouville bound
on paper for every modulus `l<=(log X)^kappa0`, every residue,
and every cutoff. It does not assert arbitrary-row relative centering; the matching
counterexample is therefore respected.

## Quantitative Möbius transfer

For positive `n`, the exact identity is

`mu(n)=lambda(n) sum_(d^2|n) mu(d)`.

Use asymmetric truncations `R=floor((log T)^(kappa0/10))` and
`R^2`. In a primitive affine progression `at+b`, a square divisor
`d^2` either shares a prime with `a` and never occurs, or selects
one residue of `t mod d^2`. Summing the omitted square divisors
therefore costs at most

`O(T/R + sqrt(aT+a))`.

After truncating the first row, its divisor sum has modulus at most
`R`. Truncating the second at `R^2` consequently costs at most

`O(T/R + R sqrt(c1T+c1))`.

For the retained pair `(d1,d2)`, CRT gives either no samples or
one residue modulo `q=lcm(d1^2,d2^2)<=R^6`. Multiplicativity
turns the Liouville product into the physical fixed-shift product
at `u=ac1 t+min(c1b,ad)`, with a constant sign `lambda(ac1)`.
The retained restriction is one progression modulo `ac1 q`.
If `ac1<=(log T)^(kappa0/100)`, then

`ac1 q <= (log T)^(61 kappa0/100) <= (log u_max)^kappa0`.

There are at most `R^3` retained square-divisor pairs. Even the
crude termwise use of the ambient Liouville estimate costs only

`O(T (log T)^(kappa0/100+3kappa0/10-c0))`.

The lower endpoint lies below `ac1`, so each retained progression
loses at most one initial term; the total endpoint cost is at most
`R^3`. The square-divisor errors above are
`O(T/(log T)^(kappa0/10))` plus negligible square-root errors.
Thus constants `kappa=kappa0/200`, `c=kappa0/20` suffice
for the exact result. The square-root terms tend to zero faster
than any fixed negative logarithmic power after division by `T`,
uniformly in the stated slopes. Floors in `R` change only an
absolute constant once `T` is large. No qualitative Möbius input is being
silently treated as a quantitative one.

## Consequence for the actual RH-language cofactor row

Let

`U_Z(n)=sum_(dm=n,2<=m<=Z) mu(d) log m`.

There are absolute `kappa1,c1,C>0` such that, for all sufficiently
large integer `X` and every `2<=Z<=(log X)^kappa1`,

`|sum_(2<=n<=X,n odd) U_Z(n)U_Z(n+2)| <= C X/(log X)^c1`.

Take `kappa1=kappa/2`, `c1=c/2`. Expand the two finite divisor
sums. On the odd carrier the cofactors `m,k` are odd and at
least three, and `md+2=ke` forces `gcd(m,k)=1`. The canonical
parametrization in the source card is

`d=2kt+b`, `e=2mt+d0`, `0<=t<=floor((X-mb)/(2mk))`,

with `0<b<2k`, `0<d0<2m`, primitive rows and determinant four.
For `m,k<=Z`, the parameter horizon is at least `X/(4mk)`
once `X` is large, uniformly on this logarithmic cutoff range.
Its logarithm is comparable to `log X`, and `2Z` lies below
its `kappa` power. Apply the preceding affine estimate to
`1<=t<=T` and add the single `t=0` endpoint. Summing absolute
logarithmic cofactor weights bounds the full expression by

`C X (log X)^(-c) (sum_(m<=Z) log(m)/m)^2
 + C (sum_(m<=Z) log m)^2`.

This is at most
`C X (log Z)^4/(log X)^c + C Z^2(log Z)^2`.
For `Z<=(log X)^kappa1`, both terms are
`O(X/(log X)^(c/2))`, uniformly in `Z`.

The already certified damping-removal bound at
`epsilon_X=(1+log(X+2))^(-6)` transfers this estimate to the
corresponding damped truncated row, since `Z^2<=X` eventually
and its normalized deformation error is `O(1/log X)`.
This controls only the `UU` corner at logarithmic cutoffs.
It neither pays the polynomial cutoff target nor the mixed
and long-cofactor terms needed for positive prime-pair mass.

## Attack, parent comparison and Lean gap

- The original fixed-form theorem alone does not justify any growing
  coefficient range; its modulus-dependent constants must be replaced
  by the explicit bounds above throughout its proof.
- The two truncations are unequal deliberately: bounding both at `R`
  and then using the pointwise bound `R` leaves an unpaid error.
- Keeping `l` polynomial in `L` avoids the matching regime where
  the slopes dominate all available rough shifts. This does not
  settle the larger polynomial-in-`T` conjecture.
- The checked [Tao--Teräväinen source, Theorem 3.1 and Remarks 3.2](https://arxiv.org/pdf/2512.01739v2)
  gives logarithmic savings uniformly in logarithmically growing
  affine coefficients outside a controlled exceptional set of scales.
  The every-cutoff conclusion here uses the later ordinary-correlation
  manuscript's graph argument, not a removal of that exceptional set
  from Tao--Teräväinen's theorem. The small growing-modulus extension
  is a constant audit of that existing argument, followed by elementary
  square-divisor truncation. **Verdict: BRIDGE**, no new scientific
  mechanism or worldwide novelty claim.

The corpus searches for ordinary correlations, short exponential
sums and bounded independence did not locate unconditional Lean
versions of the analytic and Boolean-circuit inputs used here.
The surfaced averaged-Chowla interface takes the cancellation
statement as a premise; it cannot supply it. The certified plain
Möbius window estimate has neither the additive-frequency bound
nor the prescribed quantitative rate required in this proof.

**Lean gap:** formalize the actual short exponential-sum theorem,
the finite-law comparison including bounded independence, and the
graph moment argument before using the resulting correlation
bound in Lean. No declaration, typeclass, structure field or
imported assumption standing in for one of these inputs has been
introduced. This card records a paper deduction from proved
external results and their inspected arguments, not a Lean proof.
The larger polynomial-slope target and twin-prime infinitude
remain unproved.

## Gates

- [x] Exact actual-row candidate and parameter normalization.
- [x] Explicit square-divisor and endpoint costs on paper.
- [x] Complete modulus-uniformity audit of Part I, §§2--9.
- [x] Exact cited-parent comparison and BRIDGE verdict.
- [x] Complete paper deduction, including squarefree projection and cofactor aggregation.
- [ ] Unconditional Lean certificate of every analytic input.

## Log

- 2026-10-23 — Opened this actual-row test after certifying the
  arbitrary-row matching obstruction. The original polynomial
  target and twin-prime infinitude remain unproved.
- 2026-10-23 — Finished the modulus audit through graph moments
  and overlapping-block transfer. Retained explicit `l` and `l^4`
  losses, paid both square-divisor truncations and the affine
  endpoints, and derived logarithmic-cutoff cancellation for
  the actual nonunit cofactor row. Paper stage only; analytic
  inputs are not yet Lean-certified. No new-science claim.
