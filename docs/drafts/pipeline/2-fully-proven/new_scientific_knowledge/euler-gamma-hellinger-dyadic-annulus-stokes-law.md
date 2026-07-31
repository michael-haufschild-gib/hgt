# Euler--Gamma--Hellinger dyadic annulus and cofinal-confluence fracture

- **ID:** `euler-gamma-hellinger-dyadic-annulus-stokes-law`
- **Stage:** 2-fully-proven
- **Type:** EXACT SOURCE-CURRENT BRIDGE / IRREGULAR-BOUNDARY DIAGNOSTIC
- **Scientific status:** `[PAPER-PROVED] [CORPUS-NEW BRIDGE]`
  `[EXTERNAL NOVELTY UNVERIFIED] [NOT RH] [NO COMPUTATION]`
- **Parents:**
  - `gamma-factorial-hilbert-hankel-source-normal-bridge.md`;
  - `../not_new_scientific_knowledge/prime-tail-copoisson-essential-boundary-bockstein.md`;
  - `prime-wold-accelerated-type-modular-drift-law.md`;
  - `../../1-in-progress/reflected-character-singular-splitting-bockstein-law.md`;
  - `../../../4-publication-ready/riemann-divisor-prime-transfer-spectrum/main.tex`.

## Result

The finite Wold--Hellinger reflection cost and the Euler--Gamma/co-Poisson quadrant current are
not parallel constructions.  The logarithm of the squared Hellinger sewing multiplier is exactly
the mass of a dyadic annulus cut from that same quadrant current.

This identifies the essential sewing germ before any zero is selected.  It also exposes a new
fracture:

```text
finite spectral confluence:
  the source annulus vanishes cubically;

fixed-displacement cofinal boundary:
  its accelerated Stokes valuation is linear in displacement.
```

Thus neither an ordinary Taylor/Rees completion nor a pure tropical completion retains the whole
source object.  The missing completion must remember spectral confluence and cofinal exponential
valuation simultaneously.

## 1. Finite Euler and Hellinger objects

For \(x\geq2\), put
\[
 Z_x(s)=\prod_{p\leq x}(1-p^{-s})^{-1},
 \qquad
 P_x(s)=\log Z_x(s)
       =\sum_{p\leq x}\sum_{k\geq1}{p^{-ks}\over k},
\tag{1}
\]
where the series identity is used for \(\Re s>0\).

Let
\[
 H_x(c)
 =
 \prod_{p\leq x}
 { (1-p^{-1})(1-p^{-(1-2c)})\over
   (1-p^{-(1-c)})^2},
 \qquad |c|<\frac12,
\tag{2}
\]
be the squared Hellinger affinity between the critical prime-valuation law and radial drift
\(c\).  Its reflected squared sewing multiplier is
\[
 S_x(c)={H_x(-c)\over H_x(c)}.
\tag{3}
\]

The finite Euler factorization is
\[
 H_x(c)
 =
 {Z_x(1-c)^2\over Z_x(1)Z_x(1-2c)}.
\tag{4}
\]
Consequently
\[
\boxed{
\begin{aligned}
 L_x(c)
 &:=
 \log S_x(c)\\
 &=
 P_x(1-2c)-P_x(1+2c)
 -2P_x(1-c)+2P_x(1+c)\\
 &=
 2\sum_{p\leq x}\sum_{k\geq1}{p^{-k}\over k}
 \left[
  \sinh(2ck\log p)-2\sinh(ck\log p)
 \right].
\end{aligned}}
\tag{5}
\]

### Proof

Equation `(4)` follows by multiplying the local factors in `(2)`.  Taking the ratio at
\(-c\) and \(c\), then taking logarithms, gives the second line of `(5)`.  Expanding each finite
Euler logarithm by `(1)` and using
\[
 e^u-e^{-u}=2\sinh u
\]
gives the final line. `QED`

For \(c>0\), every summand in the final line is positive because
\[
 \sinh(2u)-2\sinh u
 =
 2\sinh u(\cosh u-1)>0
 \qquad(u>0).
\tag{6}
\]
Thus \(L_x\) is odd and has the sign of \(c\).

## 2. Literal Euler--Gamma quadrant annulus

Let \(\mu_{E,x}\) be the locally finite measure on
\(Q=[0,\infty)^2\) obtained from the ordinary prime-power interval segments
\[
 \sigma_{p^k}(t)=(t,k\log p-t),
 \qquad 0\leq t\leq k\log p,
\tag{7}
\]
with weight \(1/k=\Lambda(p^k)/\log(p^k)\), restricted to \(p\leq x\):
\[
 \int_QF\,d\mu_{E,x}
 =
 \sum_{p\leq x}\sum_{k\geq1}{1\over k}
 \int_0^{k\log p}
 F(t,k\log p-t)\,dt.
\tag{8}
\]
Its two-variable Laplace transform is
\[
 {\cal H}_x(z,w)
 =
 \int_Qe^{-zt-wu}\,d\mu_{E,x}
 =
 {P_x(z)-P_x(w)\over w-z},
\tag{9}
\]
with the removable diagonal value.

`[PAPER-PROVED] [HELLINGER_DYADIC_QUADRANT_ANNULUS]`

For every \(|c|<1/2\),
\[
\boxed{\qquad
 L_x(c)
 =
 4c\left[
 {\cal H}_x(1-2c,1+2c)
 -
 {\cal H}_x(1-c,1+c)
 \right].
\qquad}
\tag{10}
\]
Equivalently,
\[
\boxed{\qquad
 L_x(c)
 =
 \int_Q
 4c\,e^{-(t+u)}
 \left[
  \cosh(2c(t-u))-\cosh(c(t-u))
 \right]
 d\mu_{E,x}(t,u).
\qquad}
\tag{11}
\]

### Proof

Equation `(9)` gives
\[
\begin{aligned}
 P_x(1-2c)-P_x(1+2c)
 &=4c\,{\cal H}_x(1-2c,1+2c),\\
 P_x(1-c)-P_x(1+c)
 &=2c\,{\cal H}_x(1-c,1+c).
\end{aligned}
\]
Substitution in `(5)` proves `(10)`.

The measure \(\mu_{E,x}\) is invariant under \((t,u)\mapsto(u,t)\).  Hence the integral of
\(e^{ac(t-u)}\) equals the integral of \(\cosh(ac(t-u))\).  Applying this to the two terms in
`(10)` proves `(11)`. `QED`

For \(c>0\), the measure in `(11)` is nonnegative.  The essential Hellinger sewing cost is
therefore not an unspecified fast multiplier: it is the exponential of a source-defined positive
dyadic annulus of the already constructed Euler--Gamma quadrant measure.  Positivity here is a
construction fact, not a critical-line selector.

## 3. Exact confluence order

`[PAPER-PROVED] [CUBIC_CONFLUENCE_OF_THE_ESSENTIAL_ANNULUS]`

At every finite prime cutoff,
\[
 L_x(0)=L_x'(0)=L_x''(0)=0
\tag{12}
\]
and
\[
\boxed{\qquad
 L_x'''(0)
 =
 -12P_x'''(1)
 =
 12\sum_{p\leq x}\sum_{k\geq1}
 k^2(\log p)^3p^{-k}
 >0.
\qquad}
\tag{13}
\]

### Proof

Oddness gives \(L_x(0)=L_x''(0)=0\).  Differentiating `(5)` once at zero gives zero because
the linear terms cancel:
\[
 2(2k\log p)-4(k\log p)=0.
\]
Three derivatives give
\[
 2\left[(2k\log p)^3-2(k\log p)^3\right]
 =12(k\log p)^3.
\]
Multiplication by \(p^{-k}/k\) proves the series in `(13)`.  Differentiating `(1)` three times
gives the identity with \(-12P_x'''(1)\). `QED`

More generally, centering at \(s\) gives
\[
\begin{aligned}
 L_{x,s}(c)
 &:=
 P_x(s-2c)-P_x(s+2c)
 -2P_x(s-c)+2P_x(s+c),\\
 L_{x,s}'''(0)&=-12P_x'''(s).
\end{aligned}
\tag{14}
\]
The cubic is the first member of an exact all-orders law.  For \(n\geq0\),
\[
\boxed{
 L_{x,s}^{(n)}(0)
 =
 \begin{cases}
  -2(2^n-2)P_x^{(n)}(s),&n\ \text{odd},\\
  0,&n\ \text{even}.
 \end{cases}}
\tag{15}
\]
The \(n=1\) case vanishes because \(2^1-2=0\); every odd order \(n\geq3\) is nonzero on the
positive real Euler face.

On \(\Re s>1\), put \(n=m+1\).  The already formalized Euler--Gamma divided-log jet weld
identifies
\[
 {1\over n}P^{(n)}(s)
\]
with the order-\(m\) Gamma factorial/co-Poisson confluence current.  Hence, for odd \(n\),
\[
\boxed{\qquad
 L_s^{(n)}(0)
 =
 -2n(2^n-2)\times
 \left(\text{order-}(n-1)\text{ Euler--Gamma confluence current}\right).
\qquad}
\tag{16}
\]
For \(n=3\), the forced coefficient is \(-36\).  No normalization is fitted.

For odd \(n\), differentiating
\(P_x(s-ac)-P_x(s+ac)\) at zero gives \(-2a^nP_x^{(n)}(s)\); for even \(n\) it gives zero.
Apply this first with \(a=2\), then subtract twice the case \(a=1\).  This proves `(15)`;
`(16)` is the Euler--Gamma jet weld with \(m=n-1\).

## 4. Shrinking-window profile

`[PAPER-PROVED] [ORIENTED_HELLINGER_DYADIC_CRITICAL_PROFILE]`

For fixed \(t\in\mathbb R\),
\[
\boxed{\qquad
 L_x\!\left({t\over\log x}\right)
 \longrightarrow
 \Psi(t)
 :=
 2\int_0^1
 {\sinh(2tu)-2\sinh(tu)\over u}\,du.
\qquad}
\tag{17}
\]
The integrand is extended continuously by zero at \(u=0\).  The profile \(\Psi\) is odd, entire,
has the sign of \(t\), and
\[
 \Psi(t)={2\over3}t^3+O(t^5).
\tag{18}
\]

### Proof

For the \(k=1\) part of `(5)`, use the prime Mertens finite measures
\[
 \nu_x
 =
 {1\over\log x}
 \sum_{p\leq x}{\log p\over p}
 \delta_{\log p/\log x}.
\tag{19}
\]
Mertens' first theorem gives \(\nu_x\Rightarrow du\) on \([0,1]\).  Since
\[
 u\longmapsto
 {\sinh(2tu)-2\sinh(tu)\over u}
\]
is continuous at zero, the \(k=1\) contribution tends to `(17)`.

For \(k\geq2\), the Taylor remainder bound
\[
 |\sinh(2v)-2\sinh v|
 \leq C_t|v|^3e^{2|v|}
\tag{20}
\]
and \(v=tk\log p/\log x\) give, for all sufficiently large \(x\), a majorant proportional to
\[
 {1\over(\log x)^3}
 k^2(\log p)^3p^{-3k/4}.
\tag{21}
\]
The double series in `(21)` is summable for \(k\geq2\), so this contribution tends to zero.
Dominated convergence proves `(17)`.  Oddness and sign follow from `(6)`.  Expanding the two
hyperbolic sines under the integral gives `(18)`. `QED`

The convergence is measure-valued at every odd confluence order.  For odd \(n\geq3\), define
\[
 \eta_{x,n}
 =
 {2(2^n-2)\over(\log x)^n}
 \sum_{p\leq x}\sum_{k\geq1}
 k^{n-1}(\log p)^np^{-k}
 \delta_{\log p/\log x}.
\tag{22}
\]
Then
\[
\boxed{\qquad
 \eta_{x,n}
 \Longrightarrow
 2(2^n-2)u^{n-1}\,du
 \quad\text{on }[0,1].
\qquad}
\tag{23}
\]
For \(n=3\), the limiting density is \(12u^2du\) and has total mass \(4=\Psi'''(0)\).

Indeed, the \(k=1\) part of `(22)` is
\[
 2(2^n-2)u^{n-1}\,d\nu_x.
\]
The \(k\geq2\) total variation is \(o(1)\), because
\[
 \sum_p\sum_{k\geq2}
 k^{n-1}(\log p)^np^{-k}<\infty.
\]
Weak convergence of \(\nu_x\) proves `(23)`.

This is an oriented companion to the even critical-window Hellinger--Wick profile already proved
in the corpus.  It measures the ratio of the two critical-to-drift affinities, not the affinity
between the two reflected drift laws.

## 5. Fixed-displacement accelerated boundary

For fixed \(0<c<1/2\), the proved prime--Wold asymptotic gives
\[
 L_x(c)
 =
 {x^{2c}\over2c\log x}(1+o(1)).
\tag{24}
\]
With
\[
 a_x=\prod_{p\leq x}(1-p^{-1}),
\]
Mertens' product theorem therefore yields
\[
\boxed{\qquad
 \lim_{x\to\infty}a_x\log L_x(c)
 =
 2e^{-\gamma}c.
\qquad}
\tag{25}
\]

Equations `(15)`, `(17)`, and `(25)` exhibit one source current in three inequivalent charts:

```text
finite analytic chart:
  cubic confluence jet -12 P_x'''(1);

critical-window chart:
  odd entire profile Psi(t);

fixed-displacement cofinal chart:
  linear accelerated Stokes valuation 2 exp(-gamma) c.
```

The linear charge in `(25)` is not a finite Taylor coefficient of `(5)`.  It appears only after
cofinalization and two logarithmic accelerations.  Conversely, `(25)` forgets the complete
factorial confluence tower retained by `(13)`--`(16)`.

### What the flat-radical theorem now forces

The completion demanded by these formulas is not an infinite-rank Rees completion.  Let
\[
 a_x=\prod_{p\leq x}(1-p^{-1}).
\]
For fixed \(c>0\), `(24)` and Mertens' theorem give
\[
 \log\log S_x(c)
 =
 {2e^{-\gamma}c+o(1)\over a_x}.
\tag{26a}
\]
Thus \(S_x(c)\) has height-two asymptotic size
\[
 \exp\!\left(
  \exp\!\left({2e^{-\gamma}c+o(1)\over a_x}\right)
 \right).
\tag{26b}
\]
Every fixed finite Rees order, and even every ordinary height-one essential multiplier
\(\exp(O(a_x^{-K}))\), has zero value under the accelerated valuation in `(25)`.  Infinite rank
does not alter this full-norm statement.

The standard adelic/Weyl continuation can carry saturated height-two type after its complementary
record is retained, so height alone is still not selective.  The required object has two
independent obligations:

```text
height:
  retain the source-defined height-two Hellinger/Stokes monomial;

internality:
  realize its boundary as a derived morphism over the fixed ordinary-integer source algebra,
  without retuning that algebra action.
```

The second obligation is decisive.  Distinct reflected source characters have no nonzero internal
relative class in any degree.  Hence an external height-two joining may exist off line, but a
nonzero internal Stokes/Bockstein landing cannot.  The RH theorem must prove that the Xi conormal
is the latter object.  Asking only for an essential multiplier, a bigger matrix, or an
unrestricted transseries carrier solves the height obligation and leaves the selector untouched.

## 6. Frozen universal conjecture

### Public sentence

Riemann zeros are not spectral particles transported through one completed space; they are the
failure of “take all primes” and “merge reflected spectral directions” to commute inside one
ordinary-integer source object.

`[BOLD CONJECTURE] [EULER_COFINAL_CONFLUENCE_STOKES_BOCKSTEIN_LAW]`

> The ordinary-prime Euler--Gamma quadrant current admits a Hausdorff enhanced totalization
> carrying simultaneously:
>
> 1. the complete spectral confluence filtration of `(14)`--`(16)`;
> 2. the cofinal accelerated valuation of `(25)`;
> 3. the non-scalar Wold thermofield/Boolean continuation record;
> 4. the literal Gamma-completed co-Poisson/Sonin source-error syzygy; and
> 5. a source-derived dagger.
>
> In that totalization, the commutator of irregular cofinalization with strict Xi Cartier
> specialization,
> \[
> {\mathfrak B}_{\rm ar}
> =
> \left[
>  \Psi_{\rm cof}^{\rm irr},
>  \operatorname{Sp}_{\Xi}
> \right]{\mathfrak R}_{E},
> \tag{26}
> \]
> is the full nonzero top Xi principal conormal.  Its two central ordinary-prime actions are
> source inverse and analytic adjoint.

Equivalently, `(26)` is an arithmetic height-two bridge equation: the perturbative
Euler--Gamma confluence tower and the nonperturbative Hellinger Stokes monomial are two
realizations of one source class, and their specialization commutator is the Xi conormal
Bockstein.  This is only terminology until the commutator and its strict source action are
constructed.

This is an ontological reversal: the divisor is the boundary commutator of two operations, not a
set of points inserted into a spectral carrier.

If `(26)` is a nonzero internal class, the all-degree reflected-character support theorem forces
the two central actions to coincide.  Their ratio at \(n=2\) is
\[
 2^{\,2\Re\rho-1},
\]
so every Xi zero has \(\Re\rho=1/2\).  This implication is already formalized conditionally; the
construction and nonvanishing in `(26)` are not.

### Shadow map

| Corpus result or failure | Shadow of `(26)` |
|---|---|
| finite-Rees flat-radical invariance | ordinary perturbative realization kills the cofinal part of the commutator |
| exact essential Hellinger sewing cost | exponential of the annulus mass `(10)` |
| accelerated modular drift | tropical boundary valuation `(25)` |
| Euler--Gamma divided-log jet weld | spectral confluence realization `(14)`--`(16)` |
| first-trace essential-normal edge | first nearby-cycle face of the commutator |
| nonzero Boolean two-curvature | degree-two failure of finite prime-order descent |
| full co-Poisson quotient flatness | every finite face of the connection closes before cofinalization |
| closed source-linear no-sewing | the commutator cannot descend as an ordinary closed boundary operator off diagonal |
| reflected-character Ext support | any surviving internal class is supported on the critical diagonal |
| generalized-prime off-line systems | external sector changes with no ordinary-integer strict commutator landing |

### Exact local Wold--Gamma factorization

The local coefficient prediction below is already forced by two independently formalized
ordinary-prime source laws.  Put
\[
 q=p^{-1},\qquad L=\log p,
\]
and let
\[
 \pi_p(e)=(1-q)q^e,\qquad
 h_p(e)={e+1\over2}L .
\]
The synchronized Euler--Gamma depth theorem gives
\[
 M_{2,p}
 :=
 \sum_{e\geq0}\pi_p(e)h_p(e)^2
 =
 {L^2(1+q)\over4(1-q)^2}.
\tag{27}
\]
The \(p\)-component of the cubic annulus current factors as
\[
\boxed{\qquad
 12L^3\sum_{k\geq1}k^2q^k
 =
 48L\,{q\over1-q}\,M_{2,p}.
\qquad}
\tag{28}
\]
Indeed,
\[
 \sum_{k\geq1}k^2q^k={q(1+q)\over(1-q)^3},
\]
and substitution of `(27)` proves `(28)`.

This is not a fitted scalar coincidence.  Its three factors are already source objects:

1. \(q/(1-q)\) is the all-positive-depth Wold/geometric activation;
2. \(M_{2,p}\) is the complete synchronized Gamma half-height second moment;
3. \(48L\) is the dyadic-confluence normalization forced by `(15)` and the physical
   half-height convention.

Lean already proves the all-depth identity defining \(M_{2,p}\) as
`hasSum_gammaSewnSynchronizedEulerDepthProbability_mul_halfHeight_sq` in
`GammaSewnSynchronizedEulerFisherBarycenter.lean`.  Equation `(28)` proves the local coefficient
part of the falsifier.  It still does not define a map on the Boolean face-defect record: applying
the diagonal character \(D_p\mapsto1\) kills the nonzero two-curvature before this scalar moment
is read.

### Parameter-free prediction and next falsifier

The normalized Boolean first-trace **edge** at \(p\), after the complete valuation-depth
order-two Gamma moment, must give the \(p\)-component of `(13)`:
\[
 12(\log p)^3\sum_{k\geq1}k^2p^{-k}
 =
 12(\log p)^3{p^{-1}(1+p^{-1})\over(1-p^{-1})^3}.
\tag{29}
\]
Equation `(28)` proves this local coefficient factorization.
The nonzero Boolean two-curvature must not map directly to this one-current.  It must be the
boundary of a source-defined two-prime annulus filler whose three-prime coboundary vanishes.
Failure of that exact non-scalar chain-level filling falsifies `(26)` before any Xi or Sonin
boundary argument.

## 7. Hostile audit

1. **Not RH.**  Equation `(26)` is unproved and RH-bearing.
2. **The annulus is not a selector.**  It exists for every \(c\), and generalized Euler products
   can have analogous finite identities.
3. **Positivity is irrelevant to exclusion.**  Nonnegativity in `(11)` constructs the cost; it
   does not force that cost to vanish.
4. **Essentiality remains nonselective.**  The standard Weyl joining can pay an essential cost by
   retuning the source action.
5. **The Stokes-triangularity shortcut is false.**  Abstract wild polarization may pair two
   off-line exponential factors after a zero-dependent metric retuning.  Only one fixed
   ordinary-source dagger and strict conormal landing can exclude that escape.
6. **Cubic does not mean degree-three detector.**  Spectral Taylor order, Boolean homological
   degree, and exterior determinant degree are different gradings.  In particular, Boolean
   two-curvature must be filled, not identified with the cubic one-current.  The prediction above
   requires an actual chain map, not a numerical analogy.
7. **Scalar continuation is insufficient.**  Meromorphic continuation of the ratio built from
   `(1)` does not prove continuation of the source current or nonvanishing of its boundary class.
8. **No Lean wrapper yet.**  The existing Lean corpus already proves both endpoint algebraic
   families.  Formalizing only the scalar rearrangement in `(5)` or the factor \(36\) in `(15)`
   would not construct the missing chain map.

## 8. Literature boundary

Hellinger affinities, Euler products, Mertens weak limits, dyadic finite differences, and
irregular/Stokes filtrations are parent mathematics.  Malgrange--Ramis multisummability and
D'Agnolo--Kashiwara enhanced nearby cycles supply general language for coexisting exponential
orders and confluence data.

Targeted arXiv searches found those parent theories but no source identifying the reflected
prime-valuation Hellinger sewing multiplier with the dyadic annulus `(10)` of the literal
Euler--Gamma/co-Poisson quadrant current, or the three-chart fracture `(15)`/`(17)`/`(25)`.
This is collision evidence only.  The card claims a corpus-new bridge, not established external
priority.

## Gates

- [x] finite Euler--Hellinger dyadic difference
- [x] literal quadrant-annulus identity
- [x] exact cubic confluence and Gamma-jet coefficient
- [x] oriented shrinking-window profile
- [x] fixed-displacement accelerated boundary
- [x] hostile countermodel and category audit
- [x] exact local Wold-activation/Gamma-second-moment factorization
- [ ] construct Boolean-curvature-to-Gamma-cubic chain map
- [ ] attach literal Sonin source-error syzygy
- [ ] construct Hausdorff enhanced totalization
- [ ] prove strict multiplicity-faithful Xi Cartier landing
- [ ] prove source inverse equals analytic adjoint on landed class
- [ ] RH
