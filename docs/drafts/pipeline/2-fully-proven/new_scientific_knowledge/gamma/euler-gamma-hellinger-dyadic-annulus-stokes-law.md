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

## Lean: the dyadic Euler-log identity and the exact confluence order

Sections 1 and 3 are now Lean, unconditionally, on the corpus's own finite Hellinger objects.  Two
modules, `#print axioms` clean (only `propext`, `Classical.choice`, `Quot.sound`).

### The all-orders dyadic jet law

`HTGeometry/DyadicReflectionJetLaw.lean` formalizes `(14)`--`(15)` for an arbitrary function, in both
a global and a local (`ContDiffOn` on an open set) form -- the local form is what the prime-Euler
logarithm needs, since it is smooth only on a half-line:

```text
dyadicReflectionCombination f s c = f(s-2c) - f(s+2c) - 2 f(s-c) + 2 f(s+c);

iteratedDeriv_dyadicReflectionCombination(_of_contDiffOn) :
  D^(n)(0) = ((-2)^n - 2^n - 2((-1)^n - 1)) f^(n)(s);
..._even : even orders vanish;
..._odd  : odd orders equal -2(2^n - 2) f^(n)(s);
iteratedDeriv_three_... : D'''(0) = -12 f'''(s);
dyadicReflectionCombination_coeff_ne_zero : the odd coefficient is nonzero for every odd n <> 1.
```

The proof is the affine scaling law `iteratedDeriv n (f(s + a . )) 0 = a^n f^(n)(s)`, applied to the
antisymmetric pair `f(s-ac) - f(s+ac)` whose `n`-th jet is `((-a)^n - a^n) f^(n)(s)`.  The local
version is an induction on `n` using the chain rule on the open preimage together with locality of
iterated derivatives.  Mathlib has the scaling law only for globally smooth functions; the local form
is corpus-owned.

### The finite Euler factorization and the sewing cost

`RHTower/EulerHellingerDyadicLogIdentity.lean` builds `(1)`--`(5)` on the corpus's existing
`primeValuationSquaredHellingerBelow` and `realPrimeEulerPartitionBelow`:

```text
primeEulerLogBelow s N            = log Z_N(s)                                   -- P_N
primeEulerLogBelow_eq_sum         : P_N(s) = sum_(p<N) -log(1 - p^(-s));
primeValuationSquaredHellingerBelow_eq_partitionRatio :
  H_N(c) = Z_N(1-c)^2 / (Z_N(1) Z_N(1-2c));                                      -- (4)
reflectedSewingMultiplierBelow c N = H_N(-c)/H_N(c);                             -- (3)
logReflectedSewingBelow_eq :
  log S_N(c) = P_N(1-2c) - P_N(1+2c) - 2 P_N(1-c) + 2 P_N(1+c);                  -- (5)
logReflectedSewingBelow_eq_dyadic :
  log S_N = dyadicReflectionCombination P_N 1 -- the sewing cost *is* the dyadic combination;
logReflectedSewingBelow_neg       : the cost is odd in the drift;
contDiffOn_primeEulerLogBelow     : P_N is smooth on (0, infty).
```

Combining the two modules gives section 3 in exact form:

```text
logReflectedSewing_zero                     : L_N(0) = 0;
iteratedDeriv_one_logReflectedSewing        : L_N'(0) = 0;
iteratedDeriv_two_logReflectedSewing        : L_N''(0) = 0;                      -- (12)
iteratedDeriv_three_logReflectedSewing      : L_N'''(0) = -12 P_N'''(1);         -- (13)
iteratedDeriv_logReflectedSewing_even/_odd  : the all-orders law (15).
```

So the cubic confluence order of the essential annulus, and the exact coefficient `-12`, are proved
statements about the corpus's own finite Hellinger object rather than a computation on the paper side.
The centre is `s = 1`: the sewing cost is the dyadic reflection combination of the finite Euler
logarithm about the critical abscissa.

- 2026-08-03 -- Sections 1 and 3 formalized.  Still outside Lean: the positive dyadic-annulus
  representation `(9)`--`(11)` (the prime-power segment measure, its two-variable Laplace transform
  and the `cosh` symmetrisation), the per-prime series form of `(5)` with the
  `sinh(2u) - 2 sinh u = 2 sinh u (cosh u - 1)` sign law `(6)`, and the shrinking-window profile
  `(17)`, which needs Mertens-type asymptotics.  The five open gates are unchanged: they are
  construction tasks (Boolean-curvature chain map, Sonin syzygy, Hausdorff totalization, Xi Cartier
  landing, adjoint identification), not formalization gaps.

### Lean: the prime-power series, the sign, and the dyadic annulus

Sections 1--3 are now complete in Lean, including the positive annulus representation.

`RHTower/EulerHellingerDyadicSignSeries.lean` gives the final line of `(5)` and the sign law `(6)`:

```text
sinh_two_mul_sub_two_sinh      : sinh(2u) - 2 sinh u = 2 sinh u (cosh u - 1);
sinh_two_mul_sub_two_sinh_pos  : that step is positive for u > 0;
localSewingLog p c             : the local contribution at a prime;
hasSum_localSewingLog :
  local contribution = 2 sum_k (p^(-k)/k) [sinh(2ck log p) - 2 sinh(ck log p)];
localSewingLog_pos             : each local contribution is positive for 0 < c < 1/2;
logReflectedSewingBelow_eq_sum_localSewingLog : the cost is the finite sum of them;
logReflectedSewingBelow_pos    : positive drift gives strictly positive cost;
logReflectedSewingBelow_neg_of_neg : negative drift gives strictly negative cost.
```

The series comes from `-log(1-x) = sum_k x^k/k` applied to the four abscissae, recombined by the same
dyadic pattern; the per-term identity is closed by `linear_combination` against the two prime-power
sinh identities, so no estimate enters.  With oddness this is the card's statement that `L_x` has the
sign of `c`, with no cancellation between primes or between powers.

`RHTower/EulerQuadrantAnnulusPairing.lean` builds the quadrant current of `(7)`--`(8)` as a pairing
and proves `(9)`--`(11)`:

```text
eulerQuadrantPairing F N =
  sum_(p<N) sum_k (1/k) int_0^(k log p) F t (k log p - t) dt;                    -- (8)
integral_segment_exp   : int_0^L e^(-zt-w(L-t)) dt = (e^(-zL) - e^(-wL))/(w-z);
integral_segment_cosh  : int_0^L cosh(a(2t-L)) dt = sinh(aL)/a;
eulerQuadrantLaplace_eq :
  <e^(-zt-wu)>_N = (P_N(z) - P_N(w))/(w-z);                                      -- (9)
logReflectedSewingBelow_eq_laplace_annulus :
  L_N(c) = 4c [ H_N(1-2c,1+2c) - H_N(1-c,1+c) ];                                 -- (10)
logReflectedSewingBelow_eq_cosh_pairing :
  L_N(c) = < 4c e^(-(t+u)) ( cosh(2c(t-u)) - cosh(c(t-u)) ) >_N.                 -- (11)
```

`(11)` is proved without the symmetrisation argument of the paper: on a segment `t + u` is the
constant `k log p`, so the integrand's segment integral collapses to
`2 p^(-k) [ sinh(2ck log p) - 2 sinh(ck log p) ]`, which is exactly the `k`-th term of the prime-power
series above.  The annulus representation and the signed series are therefore literally the same
object, and the positivity of the annulus for `c > 0` is the positivity already proved term by term.

- 2026-08-03 -- Sections 1, 2 and 3 of this card are fully formalized: the finite Euler factorization,
  the dyadic Euler-log form of the sewing cost, its all-orders jet tower with the exact cubic
  coefficient `-12`, the prime-power series with its sign law, the quadrant Laplace transform, and
  both boxed annulus representations `(10)` and `(11)`.  Everything is unconditional and
  `#print axioms` clean.  What remains unformalized is the shrinking-window profile `(17)`--`(18)` of
  section 4, which needs Mertens-type prime asymptotics, and section 5's fixed-displacement
  accelerated boundary; the five open gates are construction tasks, not formalization gaps.

### Lean: sections 4 and 6

Three further modules close section 4 (the shrinking-window profile and the measure-valued
confluence law) and the local Wold/Gamma factorization of section 6.  All are unconditional and
`#print axioms` clean (only `propext`, `Classical.choice`, `Quot.sound`).

`RHTower/MertensPrimeWindowWeakConvergence.lean` is new reusable infrastructure: the finite prime
measures

```text
nu_N = (1/log N) sum_(p <= N) (log p / p) delta_(log p / log N)
```

converge weakly to Lebesgue measure on `[0,1]`.

```text
mertensPrimeWeight n                       = log n / n at primes, 0 elsewhere;
mertensPrimeWeightSum N                    = sum_(p <= N) log p / p;
abs_mertensPrimeWeightSum_sub_log_le       : Mertens' first theorem in prime form;
mertensPrimeWindow g N                     = sum_(p <= N) (log p / p) g(log p / log N);
tendsto_mertensPrimeWindow_div_log_of_contDiff :
  the C^1 case, by Abel summation against the Mertens error plus the substitution u = log t/log N;
tendsto_mertensPrimeWindow_div_log         : every g continuous on [0,1], by Weierstrass;
tendsto_mertensPrimeWindowBelow_div_log    : the same for the strict cutoff p < N.
```

The only arithmetic input is `Mertens.mertens_first_prime`; the rest is Abel summation, one
logarithmic substitution, integration by parts, and polynomial approximation.

`RHTower/EulerHellingerShrinkingWindowProfile.lean` proves `(17)`, `(18)` and `(22)`--`(23)`:

```text
dyadicSinhWindowTest t u                   = 2 (sinh(2tu) - 2 sinh(tu)) / u, continuous at u = 0;
orientedHellingerDyadicProfile t           = Psi(t) = int_0^1 dyadicSinhWindowTest t;
orientedHellingerDyadicProfile_neg/_pos    : Psi is odd and has the sign of t;
abs_dyadicSinhStep_sub_cube_le             : |sinh(2v) - 2 sinh v - v^3| <= |v|^5 for |v| <= 1/2;
abs_orientedHellingerDyadicProfile_sub_cube_le :
  |Psi(t) - (2/3) t^3| <= 2 |t|^5 for |t| <= 1/2 -- the cubic jet (18);
tendsto_logReflectedSewing_criticalWindow  : L_N(t / log N) -> Psi(t);                  -- (17)
confluenceWindowPairing n phi N            : the order-n prime-power window pairing;
tendsto_confluenceWindowPairing            : eta_(N,n) => 2(2^n - 2) u^(n-1) du.        -- (23)
```

The first prime power is exactly the Mertens window of the continuous test function; all higher
prime powers are bounded by `8|c| K sum_p (log p) p^(-3/2)` uniformly, hence `O(1/log N)`.  The
order-`n` tail is bounded by `K_n sum_p (log p)^n p^(-2)`, hence `O((log N)^(-n))`.

`RHTower/EulerHellingerCubicWoldGammaFactorization.lean` closes the explicit series form of `(13)`
and the local factorization `(27)`--`(29)`:

```text
iteratedDeriv_three_primeEulerLogBelow     : P_N'''(1) in closed form, prime by prime;
cubicAnnulusPrimeCurrent p                 = 12 (log p)^3 sum_(k>=1) k^2 p^(-k);
cubicAnnulusPrimeCurrent_eq                : its closed form -- (29);
iteratedDeriv_three_logReflectedSewing_eq_cubicAnnulusCurrent/_eq_tsum/_pos :
  L_N'''(0) = 12 sum_(p<N) (log p)^3 sum_k k^2 p^(-k) > 0 -- the full statement (13);
gammaSewnSynchronizedEulerHalfHeightSecondMoment_eq : M_(2,p) at unit aperture -- (27);
cubicAnnulusPrimeCurrent_eq_woldActivation_mul_secondMoment :
  12 L^3 sum_k k^2 q^k = 48 L (q/(1-q)) M_(2,p) -- (28).
```

The local third derivative is closed in closed form (`-L^3 q(1+q)/(1-q)^3`) by an explicit
three-step `HasDerivAt` chain on the open half-line, so the coefficient `-12` and the positivity of
the annulus current are proved statements about the corpus's own finite Hellinger object.

- 2026-08-06 -- Sections 1, 2, 3, 4 and the local factorization of section 6 are fully formalized.
  Outstanding: section 5's fixed-displacement accelerated boundary `(24)`--`(25)`, which needs
  Mertens' third theorem with the constant `e^(-gamma)`.

### Section 5: the remaining construction plan

`(25)` is `lim a_x log L_x(c) = 2 e^(-gamma) c` with `a_x = prod_(p<=x)(1-1/p)`.  It factors as

```text
a_x log L_x(c) = (a_x log x) . (log L_x(c) / log x),
```

so it needs exactly two unconditional inputs.

1. `log L_x(c) / log x -> 2c` for fixed `0 < c < 1/2`.  This does not need the prime number theorem
   or the full prime--Wold asymptotic `(24)`; Mertens' first theorem suffices.
   - upper: `-log(1-t) <= t/(1-t)` on the four abscissae gives
     `L_N(c) <= K_c sum_(p<N) p^(2c-1) + O(1) <= K_c N^(2c)/(2c) + O(1)`, hence
     `log L_N(c) <= 2c log N + O(1)`;
   - lower: for every `theta < 1`, the already formalized positivity of every local term gives
     `L_N(c) >= sum_(N^theta <= p < N) (p^(2c-1) - 2p^(c-1) - p^(-2c-1))`, and Mertens' first
     theorem bounds `sum_(N^theta <= p < N) 1/p >= (1-theta)/2` for large `N`, so
     `log L_N(c) >= 2c theta log N + O_theta(1)`.
2. Mertens' third theorem `a_x log x -> e^(-gamma)`.  Absent from mathlib and from this corpus.
   The build is
   - `M1` Mertens' second theorem with constant: `sum_(p<x) 1/p - log log x -> M`, by Abel
     summation of `mertensPrimeWeightSum` against `1/log t` (the error `E(t) = W(t) - log t` is
     bounded, and `int^infty dt/(t log^2 t)` converges);
   - `M2` the constant identification `M = gamma + B`, `B = sum_p (log(1-1/p) + 1/p)`, by the
     classical Abelian argument: on `s > 1`,
     `sum_p p^(-s) = log zeta(s) - R(s)` with `R(1) = -B`, and mathlib's
     `log_riemannZeta_add_log_sub_isLittleO_ofReal` gives `sum_p p^(-s) + log(s-1) -> B`; on the
     other side partial summation of `M1` gives `sum_p p^(-s) + log(s-1) -> M - gamma`, using
     `int_0^infty (log u) e^(-u) du = -gamma`;
   - `M3` assembling `prod_(p<x)(1-1/p) = exp(B_x - A(x))` with `A(x) = log log x + M + o(1)`.

The only genuinely missing analytic input beyond mathlib is `int_0^infty (log u) e^(-u) du = -gamma`
(equivalently `Gamma'(1) = -gamma`) together with the two Abel summations.

#### Section 5 progress

Three of the four Mertens-third inputs are now unconditional in Lean (`#print axioms` clean).

```text
HTGeometry/GammaLogIntegralEulerMascheroni.lean
  integral_log_mul_exp_neg_Ioi        : int_0^infty (log t) e^(-t) dt = -gamma
                                        (via Complex.hasDerivAt_GammaIntegral at s = 1).

RHTower/MertensSecondTheorem.lean                                              -- M1
  primeRecipSum N                     = sum_(p <= N) 1/p;
  mertensFloorError t                 = sum_(p <= t) (log p)/p - log t, uniformly bounded;
  mertensErrorWeight t                = 1/(t log^2 t);
  integrableOn_mertensErrorWeight     : integrable on (2,infty), by the antiderivative -1/log t;
  mertensSecondConstant               = 1 - log log 2 + int_2^infty error . weight;
  tendsto_primeRecipSum_sub_logLog    : sum_(p<=N) 1/p - log log N -> M.

RHTower/PrimeZetaLogAsymptotic.lean                                            -- half of M2
  hasSum_log_of_hasProd               : log of a positive infinite product is the sum of logs;
  hasProd_primeEulerFactor            : the real Euler product for zeta on s > 1;
  hasSum_negLog_primeEulerFactor      : sum_p -log(1 - p^(-s)) = log zeta(s);
  primeZeta s                         = sum_p p^(-s);
  primeLogDefect s                    = sum_p (-log(1-p^(-s)) - p^(-s)), summable for s >= 1;
  primeZeta_add_primeLogDefect        : P(s) + D(s) = log zeta(s);
  tendsto_primeLogDefect              : D is right-continuous at 1 (dominated convergence);
  tendsto_primeZeta_add_log_sub       : P(s) + log(s-1) -> -D(1) = sum_p (log(1-1/p)+1/p).
```

What is left is the Abelian half of `M2`: `P(s) + log(s-1) -> M - gamma`.  The route is fixed by
mathlib's `tendsto_sum_mul_atTop_nhds_one_sub_integral₀` applied with `c = primeRecipWeight` and
`f t = t^(-delta)`, which gives the improper Abel representation

```text
P(1 + delta) = delta int_1^infty t^(-delta-1) (sum_(p <= t) 1/p) dt,
```

after which `sum_(p<=t) 1/p = log log t + M + o(1)` splits the integral into
`delta int_2^infty (log log t) t^(-delta-1) dt` (which is `-gamma - log delta + o(1)` after the
substitution `u = delta log t` and the `-gamma` integral above), `M . 2^(-delta) -> M`, and a
vanishing error term.  Comparing the two limits gives `M = gamma + sum_p (log(1-1/p)+1/p)`, hence
Mertens' third theorem and `(25)`.
