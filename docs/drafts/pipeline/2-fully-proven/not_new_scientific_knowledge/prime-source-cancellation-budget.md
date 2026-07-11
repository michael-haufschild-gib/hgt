# Prime-source cancellation budget for finite differential-translation handles

- **ID:** `prime-source-cancellation-budget`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) — `[PROVED HERE] [BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Statement:** A nonzero real-shift differential-translation filter with `N` scalar operator
  coordinates can cancel at most `N-1` nonzero prime coefficients of an ordinary Dirichlet source.
  With arbitrary complex shifts, the number of cancelled primes `p<=x` is `O(log x)`.  Thus every
  finite handle leaves all but finitely many prime sources exposed in the real-shift case and a
  relative-density-one set exposed in the complex-shift case.

## General setup

Let

`F(s)=sum_(n>=1) b_n n^(-s)`

be an ordinary Dirichlet series with finite abscissa of absolute convergence.  Let `P_0` be the
finite exceptional set of primes at which `b_p=0`.  Choose distinct shifts `h_1,...,h_m` and
nonzero polynomials

`P_j(D)=sum_(k=0)^(d_j) c_(j,k)D^k`, `c_(j,d_j)!=0`.

Put

`L=sum_(j=1)^m P_j(D)T_(h_j)`,

where `D=d/ds` and `T_h f(s)=f(s+h)`.  Define the scalar operator dimension

`N(L)=sum_(j=1)^m (d_j+1)`.

On a common right half-plane, termwise translation and differentiation give

`L F(s)=sum_(n>=1) b_n E_L(log n)n^(-s)`,

where

`E_L(x)=sum_(j=1)^m P_j(-x)exp(-h_j x)`.                 (1)

Distinct exponential modes make `E_L` nonzero whenever `L` is nonzero.

## Real-shift cancellation law `[PROVED HERE]`

Assume `h_1,...,h_m` are real.  Then `E_L` has at most `N(L)-1` distinct real zeros.  Consequently

`#{p prime : b_p!=0 and coefficient_p(LF)=0} <= N(L)-1`. (2)

Equivalently, cancelling `q` distinct nonzero prime sources requires

`N(L)>=q+1`.                                               (3)

### Zero-budget lemma

For distinct real numbers `h_j`, the `N=sum_j(d_j+1)` functions

`x^k exp(-h_j x)`, `1<=j<=m`, `0<=k<=d_j`,

form an extended complete Chebyshev system on every real interval.  Hence every nonzero member of
their span has at most `N-1` distinct real zeros.

A direct induction avoids importing the terminology.  For one exponent the assertion is the
ordinary polynomial zero bound.  For several exponents, choose the last block and apply

`(d/dx+h_m)^(d_m+1)`.

Multiplication by `exp(h_m x)` turns each first-order factor `d/dx+h_m` into ordinary
differentiation, so repeated Rolle reduces the number of distinct zeros by at most `d_m+1`.  The
operator kills the last block.  On every other block it maps

`Q(x)exp(-h_jx)`

to another polynomial of the same degree times `exp(-h_jx)`, with nonzero leading multiplier
`(h_m-h_j)^(d_m+1)`.  The resulting exponential polynomial is therefore nonzero and belongs to a
system of dimension `N-(d_m+1)`.  Induction gives at most

`N-(d_m+1)-1`

zeros after applying the operator, hence at most `N-1` before it.  This proves the lemma and (2).

## Complex-shift cancellation law `[PROVED HERE]`

For arbitrary distinct complex `h_j`, the function `E_L` in (1) is an entire exponential
polynomial of exponential type up to a polynomial factor.  Choose `z_0` with `E_L(z_0)!=0`.
On the disk `|z-z_0|<=R`,

`log max |E_L(z)|=O_L(R)+O_L(log R)=O_L(R)`.

Jensen's formula therefore bounds the number of zeros in that disk by `O_L(R)`.  In particular,

`#{x in [0,X] : E_L(x)=0}=O_L(X)`.

Taking `X=log x` gives

`#{p<=x : b_p!=0 and coefficient_p(LF)=0}=O_L(log x)`.   (4)

Since `pi(x)` grows faster than `log x`, the surviving primes have relative density one among all
primes whenever `P_0` has relative prime density zero; in particular this holds when `P_0` is
finite.

## Hypertranscendence consequence `[PROVED HERE]`

If `b_p!=0` for all but finitely many primes, then every nonzero finite differential-translation
filter `L` leaves infinitely many nonzero prime coefficients.  Hence `LF` belongs to the
Ostrowski--Reich class `D` and is hypertranscendental over `C(s)`.  The conclusion holds for
arbitrary complex shifts and arbitrary finite derivative orders.

The cancellation estimates are stronger than this binary HT conclusion.  For real shifts, a
finite handle cannot erase more prime atoms than its coordinate dimension minus one.  For complex
shifts, it cannot even reduce the source to a zero-density prime set.

## Completed-carrier transfer `[PROVED HERE]`

Let `u` be meromorphic and suppose a fixed differential-translation operator `A` exposes

`A u = r+F`,

where `r` is DA, translations preserve the DA field, and `F` has nonzero coefficients at all but
finitely many primes.  If a nonzero finite operator `L` made `Lu` DA, then

`A(Lu)-Lr=L F`

would be DA because constant-coefficient differential-translation operators commute.  The HT
consequence above contradicts this.  Therefore every nonzero `Lu` is HT.  Moreover the residual
source `LF` obeys the exact cancellation budgets (2) and (4).

## Riemann xi specialization

For `u=xi'/xi`, the formalized even-shift source stripper is

`A=T_2-1`

and

`A u-r=sum_(n>=2) Lambda(n)(1-n^(-2))n^(-s)`,

with rational

`r(s)=1/(s+2)+1/(s+1)-1/(s-1)`.

At every prime `p`, the exposed coefficient is `log(p)(1-p^(-2))!=0`.  Hence:

1. every nonzero finite differential-translation filter of `xi'/xi`, with arbitrary complex
   shifts, is HT;
2. if all shifts are real and the filter has coordinate dimension `N`, at most `N-1` exposed
   prime coefficients can vanish;
3. for arbitrary complex shifts, only `O_L(log x)` exposed primes `p<=x` can vanish.

Thus no fixed finite differential-difference representation of the completed logarithmic carrier
can compress its arithmetic source into a finite, sparse, holonomic, or DA residual.  Any proposed
Li, explicit-formula, spectral-trace, canonical-system, Connes, or Nyman--Beurling implementation
that requires that exact compression is impossible.  The full named routes remain untouched when
they retain genuinely infinite-dimensional prime input.

## Candidate significance

The exact real-shift inequality is a finite-resource conservation law:

> one erased prime source costs at least one independent differential-translation coordinate.

It converts qualitative hypertranscendence into a sharp complexity budget and is insensitive to
differential order versus shift count: only their total coordinate dimension matters.  The complex
law gives a second regime in which oscillatory shifts permit infinitely many cancellations but
only logarithmically many up to height `x`, leaving relative prime density one.

## Novelty verdict

`[NOVELTY VERDICT: FAIL]`.  No exact prime-source budget statement was located in the searched
corpus, but both estimates are direct specializations of classical parent theorems.  The real law
is precisely the extended-Chebyshev zero bound for real exponential monomials evaluated at prime
logarithms.  The complex law is Jensen's exponential-type zero count followed by the prime number
theorem.  A specialist can derive both immediately after writing the filtered prime coefficient.
The route consequence is useful and quantitative, but it does not clear the routine-parent gate.

## Gates

- [x] Complete paper proof of the coefficient transform.
- [x] Complete real-shift zero budget by repeated Rolle/extended Chebyshev systems.
- [x] Complete complex-shift logarithmic cancellation bound by Jensen.
- [x] Unconditional xi specialization from the formalized source identity.
- [x] Search exact literature on prime-sampled exponential-polynomial cancellation budgets.
- [x] Apply the severe routine-parent novelty test: classical Chebyshev/Jensen ingredients force
  bridge status even though the exact prime-source wording was absent.
- [x] Determine that the quantitative route consequence is stronger than the qualitative
  differential-translation orbit freeness.
- [ ] Formalize only if the complete analytic statement, not merely a finite combinatorial shadow,
  can be represented unconditionally in Lean.

## Primary parents

1. Extended complete Chebyshev systems generated by real exponential monomials.
2. Jensen zero counting for entire functions of exponential type.
3. Chebyshev/PNT prime-density estimates.
4. Ostrowski--Reich class-`D` hypertranscendence.
5. The completed-logarithmic-derivative source stripper for `xi'/xi`.

## Log

- 2026-07-11 -- Isolated from the full differential-translation orbit proof.  Replaced the binary
  assertion that infinitely many primes survive by a sharp real-shift `N-1` cancellation budget
  and an arbitrary-complex `O(log x)` cancellation law.
- 2026-07-11 -- Parent audit failed novelty: the two regimes are direct extended-Chebyshev and
  Jensen/PNT consequences.  Filed the complete theorem as a stage-2 quantitative bridge.
