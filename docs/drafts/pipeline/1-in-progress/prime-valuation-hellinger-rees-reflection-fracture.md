# Prime-valuation Hellinger--Rees reflection fracture

- **ID:** `prime-valuation-hellinger-rees-reflection-fracture`
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper) / SINGULAR THIRD-COMPLETION MECHANISM
- **Scientific status:** `[PAPER-PROVED CORE] [NOVELTY PROVISIONAL] [NOT RH]`
  `[CRITICAL NORMAL-CONE CROSSOVER PAPER-PROVED]`
  `[SOURCE-REFLECTION MODERATION OPEN]`
- **Parents:**
  - `../2-fully-proven/prime-valuation-kakutani-polar-third-completion.md`;
  - `../2-fully-proven/prime-valuation-conditioning-normalization-amplification-no-go.md`;
  - `source-effective-polar-kummer-conormal-purity.md`;
  - `deninger-mertens-adiabatic-exponential-corner.md`;
  - `global-wold-volume-gamma-bimoderate-completion.md`.
- **Statement:** Finite-prime Hellinger overlap between the critical Wold valuation sector and a
  coherent radial twist has exactly three Rees faces.  Critical twist stays in the bulk, negative
  twist reaches the source-normal boundary with universal half-density order, and positive twist
  is flat beyond every power of the source-normal scale.  Functional-equation reflection exchanges
  the last two faces.

## Goal

The Kakutani selector proves only that every nonzero coherent radial twist leaves the critical
product-measure sector.  It does not say how the twist meets the singular source-normal boundary.
The normalization-amplification theorem then rules out an ordinary strong limit of conditioned
states.

This card retains the vanishing source scale instead of normalizing it away.  It computes the exact
Rees order of every coherent radial sector and turns the RH-facing source theorem into a moderation
statement for one independently calibrated reflection operator.

## Setup

For a rational prime \(p\), let
\[
 \mu_{p,0}(k)=(1-p^{-1})p^{-k},\qquad k\geq0.
\]
For \(-\tfrac12<c<\tfrac12\), put
\[
 \mu_{p,c}(k)
 =
 (1-p^{-(1-2c)})p^{-(1-2c)k}.
\]
The local Hellinger affinity is
\[
 H_p(c)
 =
 \sum_{k\geq0}\sqrt{\mu_{p,0}(k)\mu_{p,c}(k)}
 =
 \frac{\sqrt{(1-p^{-1})(1-p^{-(1-2c)})}}
 {1-p^{-(1-c)}}.                                         \tag{1}
\]

For \(x\geq2\), define
\[
 {\cal H}_x(c)=\prod_{p\leq x}H_p(c),\qquad
 a_x=\prod_{p\leq x}(1-p^{-1}).                          \tag{2}
\]
The scale \(a_x\) is the exact mass of the finite-prime vacuum event and is the vanishing
coefficient used by the BV/Wold source-normal blow-up.  Its half-density scale is \(a_x^{1/2}\).

## Theorem: exact Hellinger--Rees trichotomy

`[PROVED HERE]`

For \(-\tfrac12<c<\tfrac12\):

1. If \(c=0\), then
   \[
    {\cal H}_x(0)=1.                                      \tag{3}
   \]
2. If \(c<0\), then
   \[
    \frac{{\cal H}_x(c)}{a_x^{1/2}}
    \longrightarrow
    C_-(c)
    :=
    \prod_p
    \frac{\sqrt{1-p^{-(1-2c)}}}{1-p^{-(1-c)}}
    \in(0,\infty).                                       \tag{4}
   \]
3. If \(0<c<\tfrac12\), then
   \[
    \log {\cal H}_x(c)
    =
    -\frac{x^{2c}}{4c\log x}(1+o(1)),                    \tag{5}
   \]
   and consequently, for every \(N>0\),
   \[
    \frac{{\cal H}_x(c)}{a_x^N}\longrightarrow0.         \tag{6}
   \]

Equivalently, the extended Rees order
\[
 \operatorname{ord}_{\rm src}(c)
 =
 \lim_{x\to\infty}
 \frac{\log{\cal H}_x(c)}{\log a_x}
\]
exists and equals
\[
 \boxed{
 \operatorname{ord}_{\rm src}(c)=
 \begin{cases}
  \tfrac12,&c<0,\\
  0,&c=0,\\
  +\infty,&c>0.
 \end{cases}}                                             \tag{7}
\]

### Proof

Equation `(3)` follows by substituting \(c=0\) into `(1)`.

Assume \(c<0\).  Dividing `(1)` by \((1-p^{-1})^{1/2}\) gives
\[
 \frac{H_p(c)}{(1-p^{-1})^{1/2}}
 =
 \frac{\sqrt{1-p^{-(1-2c)}}}{1-p^{-(1-c)}}.              \tag{8}
\]
Both prime series
\[
 \sum_p p^{-(1-2c)},\qquad
 \sum_p p^{-(1-c)}
\]
converge because their exponents exceed one.  Hence the product on the right of `(4)` converges
absolutely to a finite positive number.  Multiplying `(8)` over \(p\leq x\) proves `(4)`.

Now assume \(0<c<\tfrac12\), and write
\[
 \alpha=1-2c,\qquad \beta=1-c.
\]
Then \(0<\alpha<\beta<1\).  Taking logarithms in `(1)` and using
\(\log(1-u)=-u+O(u^2)\) gives
\[
 \log H_p(c)
 =
 -\frac12p^{-\alpha}
 +p^{-\beta}
 -\frac12p^{-1}
 O(p^{-2\alpha}+p^{-2\beta}+p^{-2}).                    \tag{9}
\]
Every exponent in the remainder is strictly larger than \(\alpha\).  Prime-number-theorem
partial summation gives, for \(0<\gamma<1\),
\[
 \sum_{p\leq x}p^{-\gamma}
 =
 \frac{x^{1-\gamma}}{(1-\gamma)\log x}(1+o(1)).          \tag{10}
\]
The \(\alpha\)-term in `(9)` therefore dominates all other terms.  Since
\(1-\alpha=2c\), summation proves `(5)`.

Mertens' product theorem gives
\[
 \log a_x=-\log\log x+O(1).
\]
The magnitude \(x^{2c}/\log x\) dominates every multiple of \(\log\log x\), so `(5)` implies
`(6)`.  Equations `(3)`--`(6)` give `(7)`.

## Theorem: universal critical normal-cone crossover

The fixed-\(c\) trichotomy has a nontrivial transition layer of width \(1/\log x\).  Define
\[
 \Phi(u)
 =
 \frac12\int_0^1\frac{(e^{ut}-1)^2}{t}\,dt,
 \qquad u\in\mathbb R.                                  \tag{7a}
\]
The integrand extends continuously by zero at \(t=0\).

`[PROVED HERE]` For every fixed real \(u\), put \(c_x=u/\log x\).  Then
\[
 \boxed{
 {\cal H}_x(c_x)\longrightarrow e^{-\Phi(u)}.
 }                                                       \tag{7b}
\]

Thus the singular third completion has a canonical real normal coordinate
\[
 u=c\log x,                                             \tag{7c}
\]
and its Hellinger comparison does not jump directly from bulk to the two off-line Rees faces.
It passes through the universal positive profile \(e^{-\Phi(u)}\).

### Proof

For \(p\leq x\), write
\[
 q=p^{-1},\qquad t_p=\frac{\log p}{\log x}.
\]
Substitution of \(c_x\) into `(1)` gives
\[
 \log H_p(c_x)
 =
 \frac12\log(1-q)
 +\frac12\log(1-qe^{2ut_p})
 -\log(1-qe^{ut_p}).                                    \tag{7d}
\]
Taylor expansion in \(q\), with the finitely many small primes separated, yields
\[
 \log H_p(c_x)
 =
 -\frac{(e^{ut_p}-1)^2}{2p}+R_{p,x}.                    \tag{7e}
\]
For fixed \(u\), the remainders are dominated by \(C_u p^{-2}\).  For every fixed prime,
\(R_{p,x}\to0\) because \(c_x\to0\).  Dominated convergence over the primes therefore gives
\[
 \sum_{p\leq x}R_{p,x}\longrightarrow0.                 \tag{7f}
\]

For every fixed integer \(n\geq1\), prime-number-theorem partial summation gives
\[
 \frac1{(\log x)^n}\sum_{p\leq x}\frac{(\log p)^n}{p}
 \longrightarrow\frac1n.                                \tag{7g}
\]
The uniformly absolutely convergent expansion
\[
 (e^{ut}-1)^2
 =
 \sum_{n\geq2}\frac{(2^n-2)u^n}{n!}t^n                 \tag{7h}
\]
and the bound \(t^n\leq t^2\) on \([0,1]\) allow the limit to pass through the series.  Hence
\[
 \sum_{p\leq x}\frac{(e^{ut_p}-1)^2}{p}
 \longrightarrow
 \sum_{n\geq2}\frac{(2^n-2)u^n}{n!\,n}
 =
 \int_0^1\frac{(e^{ut}-1)^2}{t}\,dt.                    \tag{7i}
\]
Summing `(7e)` and using `(7f)`--`(7i)` proves `(7b)`.

## Geometry of the crossover

The profile has the following exact consequences.

1. \(\Phi(0)=0\), while \(\Phi(u)>0\) for \(u\ne0\).
2. Its critical quadratic metric is
   \[
    \Phi(u)=\frac{u^2}{4}+O(u^3),\qquad
    \Phi''(0)=\frac12.                                   \tag{7j}
   \]
3. Reflection has a strict orientation:
   \[
    \Phi(u)-\Phi(-u)
    =
    2\int_0^1
      \frac{\sinh(ut)(\cosh(ut)-1)}{t}\,dt,              \tag{7k}
   \]
   which has the sign of \(u\).
4. For \(v\to+\infty\),
   \[
    \Phi(-v)
    =
    \frac12(\log v+\gamma-\log2)+o(1),                  \tag{7l}
   \]
   while
   \[
    \Phi(v)
    =
    \frac{e^{2v}}{4v}(1+o(1)).                           \tag{7m}
   \]

Equation `(7l)` follows after \(y=vt\) from
\[
 \int_0^v\frac{(1-e^{-y})^2}{y}\,dy
 =
 \log v+\gamma-\log2+2E_1(v)-E_1(2v).
\]
Equation `(7m)` is endpoint Laplace asymptotics; the \(e^{2vt}\) term dominates the
\(e^{vt}\) and constant terms.  The two ends of one profile have the same leading forms as the
half-normal logarithmic scale and the rapid exponential scale of `(4)`--`(6)` after
\(u=c\log x\) is substituted.  The crossover theorem itself is for fixed \(u\); no uniform
interchange of \(x\to\infty\) and \(u\to\pm\infty\) is asserted.  The fixed-\(c\) endpoint laws
remain the independent theorems `(4)`--`(6)`.

Mertens' theorem also identifies the normal coordinate with the exact Wold scale:
\[
 u=c\log x
 =
 e^{-\gamma}\frac{c}{a_x}(1+o(1)).                       \tag{7m'}
\]

There is also an exact source-metric identity.  Differentiating the local affinity at the critical
sector gives
\[
 -\left.\frac{d^2}{dc^2}\log H_p(c)\right|_{c=0}
 =
 (\log p)^2\frac{p^{-1}}{(1-p^{-1})^2}.                  \tag{7n}
\]
If
\[
 d_p^2=\frac{p^{-1}}{(1+p^{-1})^2}
\]
is the already formalized squarefree Fisher/WKB capacity, then
\[
 -\left.\frac{d^2}{dc^2}\log H_p(c)\right|_{c=0}
 =
 (\log p)^2
 \left(\frac{1+p^{-1}}{1-p^{-1}}\right)^2 d_p^2.         \tag{7o}
\]
Consequently
\[
 -\frac1{(\log x)^2}
 \left.\frac{d^2}{dc^2}\log{\cal H}_x(c)\right|_{c=0}
 \longrightarrow\frac12,                                \tag{7p}
\]
in agreement with `(7j)`.

Equations `(7n)`--`(7o)` give the first exact metric comparison between the prime-valuation
Hellinger fracture and the squarefree Fisher/WKB seam.  The correction factor tends to one at
large primes but is retained exactly.  This supplies a source-derived critical tangent
calibration; it does not yet prove global order-zero reflection on Xi conormals.

## Reflection fracture

For a centered divisor character
\[
 \chi_\rho(p)=p^{1/2-\rho},
\]
the radial exponent is
\[
 c_\rho=\tfrac12-\operatorname{Re}\rho.
\]
Functional-equation reflection sends \(\rho\) to \(1-\rho\) and therefore sends \(c_\rho\) to
\(-c_\rho\).  An off-line pair consequently has Rees orders
\[
 \{\operatorname{ord}_{\rm src}(c_\rho),
   \operatorname{ord}_{\rm src}(-c_\rho)\}
 =
 \{\tfrac12,+\infty\}.                                   \tag{11}
\]
Only a critical-line character has equal finite order on both reflected faces:
\[
 \operatorname{ord}_{\rm src}(c)
 =
 \operatorname{ord}_{\rm src}(-c)
 <\infty
 \quad\Longleftrightarrow\quad c=0.                      \tag{12}
\]

The interpretation is exact:

```text
critical character:
  remains in the critical bulk sector;

strict-right character:
  reaches the vacuum normal cone at exactly its canonical
  half-density scale sqrt(a_x);

reflected strict-left character:
  is exponentially flat beyond every finite Rees grade.
```

This is information lost by both earlier completions.  Scalar adelic \(L^2\) erases every point
fibre.  Normalized boundary conditioning erases the vanishing scale and is not strongly Cauchy.
The Hellinger--Rees object retains bulk, half-normal boundary, and the infinitely flat face
simultaneously.

## RH-bearing source conjecture

> **[CONJECTURE -- SOURCE-CALIBRATED REES-MODERATE REFLECTION.]**
> The completed ordinary-prime Euler--Gamma/co-Poisson source constructs, before divisor
> specialization, a presentation-independent reflection involution on its prime-valuation
> half-density conormal pro-object.  Relative to the exact Wold/BV source scale \(a_x^{1/2}\), both
> the involution and its inverse have Rees order zero.  Its distinguished conormal section is
> nonzero on the top multiplicity jet of every nontrivial \(\Xi\)-divisor fibre.

“Rees order zero” may be stated on finite-prime representatives \(R_x\) as
\[
 \log\|R_x\|+\log\|R_x^{-1}\|
 =
 o(|\log a_x|),                                          \tag{13}
\]
after the Hermitian scale is fixed by the source differential determinant character.  Uniform
boundedness is sufficient but not required.

If the conjecture holds and \(\Xi(\rho)=0\), the involution identifies the \(\rho\) and
\(1-\rho\) top conormal jets without changing their Rees order.  Equation `(12)` forces
\(c_\rho=0\), hence
\[
 \operatorname{Re}\rho=\tfrac12.
\]
Thus the conjecture implies RH.

The conjecture is narrower than “every Xi conormal is normal in the critical GNS sector.”  It does
not require an ordinary strong limit of normalized states.  It asks for moderate transport of the
unnormalized half-density/Rees object, exactly the structure that survives the
normalization-amplification no-go.

An equivalent sufficient determinant formulation is useful.  For a reflected semisimple pair,
the finite-prime Hellinger determinant is
\[
 {\cal D}_x(c)={\cal H}_x(c){\cal H}_x(-c).
\]
If \(c\ne0\), equations `(4)` and `(6)` make \({\cal D}_x(c)\) flat beyond every power of \(a_x\).
If \(c=0\), it is identically one.  Therefore it is enough to prove that the source-produced
determinant of every finite-multiplicity reflected Xi conormal orbit has finite Rees order and that
the comparison with \({\cal D}_x\) is strict.  This is the determinant/integral-class form of
`(13)`: a finite analytic multiplicity may not be sent into the all-orders-flat radical.

This formulation does not follow from abstract self-duality.  A two-chart enhanced object can
place \(c\) and \(-c\) in opposite filtrations and let reflection exchange the charts.  Such an
object carries off-line pairs without contradiction.  The load-bearing claim is source-calibrated
strictness of the determinant comparison, not existence of a reflected pairing.

## Candidate source producer

The current strongest producer is the residue-corrected determinant differential character
proposed in `source-effective-polar-kummer-conormal-purity.md`:

```text
regular holonomy:       polarized Wold--Gamma det_2 cocycle;
singular curvature:     BV/renormalized first-trace class;
integral class:         ordinary-prime Wold index;
Hermitian calibration:  strict Kummer--Arakelov real regulator;
distinguished section:  completed Euler--Gamma/co-Poisson source.
```

Its new required output is not total-variation convergence.  It is the sub-Rees condition `(13)`.
This separates the precise source problem from the already false normalized-Cauchy estimate.

## Hostile audit

1. **Functional equation alone is insufficient.**  A projective reflection can be rescaled by an
   arbitrary nonzero scalar.  Equation `(13)` is meaningful only after an independent Hermitian
   calibration; the source-conormal projective topology does not provide one.
2. **Reflection may reverse filtration.**  A Hausdorff two-chart completion can retain the
   half-normal and infinitely flat members separately and swap them.  Bare self-duality therefore
   does not imply `(13)` or finite determinant grade.
3. **No ordinary state limit is asserted.**  The conditioned boundary states stay at maximal total
   variation distance from their weak atomic limit.
4. **Flat terms are not silently deleted.**  The \(+\infty\) face is retained as an enhanced
   Stokes/flat component.  The conjecture says source reflection is moderate across it; declaring
   it zero would violate conormal faithfulness.
5. **Generalized-prime countermodels are not excluded by vocabulary.**  They falsify the mechanism
   unless they fail the literal ordinary-prime Wold index, residue-corrected Gamma/BV differential
   character, or source-calibrated moderation `(13)`.
6. **Multiplicity is not silently discharged.**  Equations `(3)`--`(12)` classify the semisimple
   prime character.  Polynomial valuation-depth jets preserve Kakutani measure class, but their
   exact Hellinger--Rees order has not been proved here.  The source comparison must establish the
   top multiplicity jet separately.
7. **The conjecture remains RH-bearing.**  No current corpus theorem proves `(13)`.  It must not be
   inferred from scalar FE, finite CP maps, \(\det_2\) alone, or hypertranscendence alone.

## Literature boundary

Parent mathematics includes Kakutani's product-measure theorem, Hellinger affinity, Mertens'
product theorem, prime-number-theorem partial summation, Rees filtrations, and Stokes moderation.
Targeted searches located these parents but not the three-face asymptotic `(3)`--`(7)` for the
ordinary-prime geometric valuation sectors, the critical crossover `(7a)`--`(7p)`, nor their
functional-equation reflection use.  Searches also checked prime-factor Poisson models,
mod-Poisson convergence, local asymptotic normality, and Hellinger geometry of product models.
Those are conceptual parents for a critical scaling profile but no located source states the
specific ordinary-prime geometric-sector limit `(7b)` or its two Rees endpoint laws.

The exact asymptotic theorem is elementary once `(1)` is written, so novelty is provisional and
restricted to the source-specific Hellinger--Rees interpretation and reflection fracture.  The RH
mechanism is candidate-new only if source-calibrated moderation `(13)` can be constructed from the
residue-corrected Euler--Gamma/BV differential character rather than assumed.

Primary parents:

- Shizuo Kakutani, *On equivalence of infinite product measures*, Annals of Mathematics 49
  (1948), 214--224.
- Daniel Allcock and Jeffrey D. Vaaler, *A Banach space determined by the Weil height*,
  https://arxiv.org/abs/0808.1038.
- Daniel S. Freed, *Determinant Line Bundles Revisited*,
  https://arxiv.org/abs/dg-ga/9505002.
- Sylvie Paycha and Steven Rosenberg, *Curvature on determinant bundles and first Chern forms*,
  https://arxiv.org/abs/math/0009172.
- Simon Scott, *Relative Zeta Determinants and the Quillen Metric*,
  https://arxiv.org/abs/math/9910148.

## Gates

- [x] 0 \(\to\) 1: source scale, exact invariant, RH consumer, and falsifiers stated
- [x] exact local Hellinger affinity inherited from the proved Kakutani card
- [x] negative-slope half-density asymptotic paper-proved
- [x] positive-slope super-Rees-flat asymptotic paper-proved
- [x] critical \(c=u/\log x\) normal-cone crossover paper-proved
- [x] crossover orientation and both endpoint asymptotics paper-proved
- [x] exact valuation-Hellinger/squarefree-Fisher metric comparison paper-proved
- [x] reflection fracture and exact selector paper-proved
- [x] normalization-amplification no-go incorporated
- [x] preliminary corpus and literature noncollision search
- [ ] independent analytic-number-theory audit of `(5)`
- [ ] independent operator-algebra/Rees audit of interpretation `(7)`--`(13)`
- [ ] construct source-calibrated finite-prime reflection representatives
- [ ] prove sub-Rees condition `(13)` from the residue-corrected determinant character
- [ ] prove multiplicity-faithful Xi conormal comparison
- [ ] dependency-closed RH proof
- [ ] unconditional Lean formalization

## Log

- 2026-07-29 — Centered Ward replication and ordinary normalized-state convergence were killed by
  existing codiagonal and normalization-amplification theorems.  Retaining the vanishing Wold/BV
  scale exposed the Hellinger--Rees trichotomy `(3)`--`(7)`.  Froze source-calibrated
  Rees-moderate reflection as the new RH-bearing theorem.
