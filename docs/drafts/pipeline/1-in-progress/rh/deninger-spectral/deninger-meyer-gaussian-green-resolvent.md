# Deninger--Meyer Gaussian Green resolvent and source-algebra defect

- **ID:** `deninger-meyer-gaussian-green-resolvent`
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper) + FRONTIER CONJECTURE
- **Label:** `DM_GAUSSIAN_GREEN_RESOLVENT_CARTAN_TAIL`
- **Parent:** `rh-current-frontier-map`, Route L
- **Source:** literal Meyer Poisson quotient, canonical half-density seminorm, and the
  reflection-fixed logarithmic Gaussian
- **Statement:** The literal Poisson range is a convolution ideal in the all-weight Meyer source.
  Half-density conjugation turns the quotient completion into a commutative `L1`-type Banach
  algebra.  For an off-critical Xi character, the completed Gaussian Neumann inverse has exact
  finite exponential tail `|Re(rho)-1/2|` and infinite tilted Xi mass.  Its forced Poisson preimage
  has successor pole order, admits a literal Möbius--Gaussian source series on a safe chamber, and
  leaves one simple Gamma/Green residue after completed-Xi transport.  Thus the missing arithmetic
  theorem is singular continuation of this explicit source series into the Xi-zero graph domain.

## Goal

Replace repeated continuity criteria by a concrete Deninger source object and compute its exact
failure.  The object is the Green primitive obtained by inverting one reflection-adapted Gaussian
packet in the canonical half-density completion.  Its defect is not abstract unboundedness: it is a
positive, explicit, finite-exponential tail whose rate equals the Cartan displacement.

This card does **not** claim RH.  It constructs the source convolution algebra and identifies the
new arithmetic theorem needed to close Route L.

## Gates

- [x] 0 -> 1 in-progress: source-pure, explicit construction, paper proof, hostile internal audit
- [ ] 1 -> 2 fully-proven: formalize full convolution-ideal theorem and two-sided Green asymptotic
- [ ] 2 -> 3 formalized: direct Lean and targeted module build green; axiom audit clean
- [ ] 3 -> 4 publication-ready: integrate theorem, proof, and novelty audit into paper
- [x] Lean subgate: exact finite Green source, arbitrary Cartan moments, infinite interior transform,
  exact moment wall, local successor-pole lift, universal simple Gamma residue, safe-chamber literal
  Möbius--Gaussian source series, direct compile, targeted leaf builds, and axiom audits

## 1. Literal source convolution algebra

Write the all-weight logarithmic Meyer space as

\[
 \mathscr S_M=\{g\in C^\infty(\mathbb R):
   g^{(j)}(t)=O(e^{-A t})\ (t\to+\infty),\quad
   g^{(j)}(t)=O(e^{B t})\ (t\to-\infty)
   \text{ for all }j,A,B\}.
\tag{1}
\]

For `g,h in S_M`, define additive logarithmic convolution

\[
                    (g*h)(t)=\int_{\mathbb R}g(u)h(t-u)\,du.
\tag{2}
\]

### Theorem 1 `[PROVED HERE]`: strong-log convolution closure

`S_M` is a commutative nonunital algebra under `(2)`.

### Proof

Differentiation under the integral is justified by the all-exponential bounds and gives

\[
                    (g*h)^{(j)}=g*h^{(j)}.
\tag{3}
\]

For every real `A`, both `e^{A t}g(t)` and `e^{A t}h^{(j)}(t)` are bounded and integrable.  Hence

\[
 e^{At}|(g*h)^{(j)}(t)|
 \le \|e^{A\cdot}g\|_\infty\,
      \|e^{A\cdot}h^{(j)}\|_1.
\tag{4}
\]

Taking arbitrary positive and negative `A` gives both ends of `(1)`.  Bilinearity, commutativity,
and associativity follow from absolute Fubini.  QED.

Let `H_cap` be Meyer's even Schwartz cap, characterized by

\[
                       f(0)=0,\qquad \int_{\mathbb R}f(x)\,dx=0,
\tag{5}
\]

and let

\[
                 Zf(t)=\sum_{n\ge1}f(ne^t)
\tag{6}
\]

be the literal logarithmic Poisson boundary.

### Theorem 2 `[PROVED HERE]`: Poisson range is a convolution ideal

For `g in S_M` and `f in H_cap`, define

\[
             (K_gf)(x)=\int_{\mathbb R}g(u)f(e^{-u}x)\,du.
\tag{7}
\]

Then `K_gf in H_cap` and

\[
                         g*Zf=Z(K_gf).
\tag{8}
\]

Consequently `B_P=Z(H_cap)` is a two-sided convolution ideal in `S_M`, and the literal Meyer
cohomology `H_M=S_M/B_P` is a commutative nonunital algebra.

### Proof

All derivatives of `(7)` may be taken under the integral:

\[
 (K_gf)^{(j)}(x)=\int g(u)e^{-ju}f^{(j)}(e^{-u}x)\,du.
\tag{9}
\]

For each Schwartz seminorm `(m,j)`,

\[
 |x|^m |(K_gf)^{(j)}(x)|
 \le
 \left(\sup_y |y|^m|f^{(j)}(y)|\right)
 \int |g(u)|e^{(m-j)u}\,du,
\tag{10}
\]

which is finite by `(1)`.  Thus `K_gf` is Schwartz.  Evenness follows from evenness of `f`.
Moreover

\[
 K_gf(0)=f(0)\int g=0,
 \qquad
 \int K_gf(x)\,dx=\left(\int g(u)e^u\,du\right)\left(\int f(y)\,dy\right)=0.
\tag{11}
\]

Hence `K_gf in H_cap`.  Absolute Fubini, using the all-exponential decay of `g` and Schwartz
bounds of `f`, gives

\[
\begin{aligned}
 (g*Zf)(t)
 &=\int g(u)\sum_{n\ge1}f(ne^{t-u})\,du\\
 &=\sum_{n\ge1}\int g(u)f(e^{-u}ne^t)\,du
 =\sum_{n\ge1}(K_gf)(ne^t)=Z(K_gf).
\end{aligned}
\]

This proves `(8)` and the ideal assertion.  QED.

## 2. Half-density conjugation

Define

\[
                 (Tg)(t)=e^{t/2}g(t),\qquad p_{1/2}(g)=\|Tg\|_1.
\tag{12}
\]

### Theorem 3 `[PROVED HERE]`: exact `L1` algebra law

For `g,h in S_M`,

\[
                         T(g*h)=(Tg)*(Th)
\tag{13}
\]

and therefore

\[
                         p_{1/2}(g*h)
                         \le p_{1/2}(g)p_{1/2}(h).
\tag{14}
\]

The quotient seminorm on `H_M` is submultiplicative.  Its Hausdorff completion is consequently a
commutative nonunital Banach algebra; its unitization will be denoted `Hhat_1/2^+`.

### Proof

Equation `(13)` is the pointwise identity `e^{t/2}=e^{u/2}e^{(t-u)/2}` under the integral.  Young's
`L1` inequality gives `(14)`.  Since `B_P` is an ideal, multiplying arbitrary boundary-shifted
representatives and then taking both quotient infima proves submultiplicativity downstairs.
Completion and unitization are standard.  QED.

## 3. Explicit Gaussian Green primitive

Let

\[
 h_\tau(t)=e^{-t/2}e^{-i\tau t}e^{-\pi t^2},
 \qquad Th_\tau(t)=e^{-i\tau t}e^{-\pi t^2}.
\tag{15}
\]

The existing reflected-Gaussian theorem gives `h_tau in S_M` and `p_1/2(h_tau)=1`.  Gaussian
convolution gives

\[
 (Th_\tau)^{*n}(t)
 =e^{-i\tau t}\,n^{-1/2}e^{-\pi t^2/n}.
\tag{16}
\]

Fix a nonzero horizontal displacement

\[
 a=\Re\rho-\frac12,\qquad
 L=\frac{a^2}{4\pi},\qquad \lambda=e^L>1.
\tag{17}
\]

In `Hhat_1/2^+`, the element `lambda*1-[h_tau]` is invertible by its Neumann series.  After applying
`T` and removing the harmless phase, its nonconstant Green kernel is

\[
 G_a(t)=\sum_{n\ge1}e^{-nL}n^{-1/2}e^{-\pi t^2/n}.
\tag{18}
\]

### Theorem 4 `[PROVED HERE]`: bounded capacity, exact critical moment blow-up

The kernel `(18)` is positive and integrable, with

\[
                 \int_{\mathbb R}G_a(t)\,dt
                 =\sum_{n\ge1}e^{-nL}=\frac1{e^L-1}.
\tag{19}
\]

But its Xi-tilted mass diverges exactly:

\[
                 \int_{\mathbb R}e^{at}G_a(t)\,dt=+\infty.
\tag{20}
\]

More strongly, each summand has unit tilted mass:

\[
 \int_{\mathbb R}e^{at}
 e^{-nL}n^{-1/2}e^{-\pi t^2/n}\,dt=1.
\tag{21}
\]

### Proof

The normalized Gaussian in `(16)` has integral one, so Tonelli gives `(19)`.  Completing the square,

\[
 -nL-\frac{\pi t^2}{n}+at
 =-\frac\pi n\left(t-\frac{na}{2\pi}\right)^2.
\tag{22}
\]

Translation and Gaussian scaling prove `(21)`.  Tonelli then turns `(20)` into the divergent sum
`sum 1`.  QED.

### Theorem 4.5 `[PROVED HERE, FORMALIZED]`: exact Cartan moment wall

For arbitrary real tilt `b`, one Green summand satisfies

\[
 \int_{\mathbb R}e^{bt}e^{-nL}n^{-1/2}e^{-\pi t^2/n}\,dt
 =\exp\!\left(\frac{n(b^2-a^2)}{4\pi}\right).
\tag{21a}
\]

Consequently, throughout the open Cartan strip `b^2<a^2`,

\[
 \int_{\mathbb R}e^{bt}G_a(t)\,dt
 =\frac{q_{a,b}}{1-q_{a,b}},\qquad
 q_{a,b}=\exp\!\left(\frac{b^2-a^2}{4\pi}\right),
\tag{21b}
\]

whereas for `b^2>=a^2` the corresponding moments of the first `N` Green terms tend to infinity;
indeed they are at least `N`. Thus `|a|` is the exact exponential-moment abscissa, not only an
upper or lower tail estimate. The boundary case `b=a` recovers `(21)` term by term.

### Proof

Complete the square with `b` in place of `a`:

\[
 bt-\frac{na^2}{4\pi}-\frac{\pi t^2}{n}
 =\frac{n(b^2-a^2)}{4\pi}
  -\frac\pi n\left(t-\frac{nb}{2\pi}\right)^2.
\tag{21c}
\]

Gaussian integration gives `(21a)`. If `b^2<a^2`, the ratio `q_{a,b}` lies in `(0,1)` and Tonelli
gives `(21b)`. If `a^2<=b^2`, every term in the finite moment sum is at least one. QED.

Lean module `DeningerMeyerGaussianGreenPrimitive` proves `(21a)`, `(21b)`, the exterior lower
bound, divergence of finite moments, the raw height-centered Meyer source law, and the combined
exact Cartan-moment wall without project-specific axioms.

### Theorem 5 `[PROVED HERE]`: Cartan slope is exact Green-tail exponent

For `a != 0`,

\[
                  \lim_{|t|\to\infty}
                  -\frac{1}{|t|}\log G_a(t)=|a|.
\tag{23}
\]

In particular `G_a` has finite exponential type and is not an all-weight Meyer function.

### Proof

For every `n`, arithmetic--geometric mean gives

\[
 nL+\frac{\pi t^2}{n}\ge2|t|\sqrt{\pi L}=|a||t|.
\tag{24}
\]

Split the sum at `n<=A|t|`.  The first part is bounded by a linear factor times
`e^{-|a||t|}`.  For the tail, choose `A` so large that `LA/2>|a|` and use
`n^{-1/2}e^{-Ln}<=e^{-Ln/2}`.  This proves the upper logarithmic bound.

For the reverse bound, put `x=|t|sqrt(pi/L)` and `n=ceil(x)`.  Then

\[
 nL+\frac{\pi t^2}{n}
 \le |a||t|+L,
\tag{25}
\]

so one summand is at least `(x+1)^(-1/2)e^{-|a||t|-L}`.  Polynomial factors disappear after
division by `|t|`; `(23)` follows.  QED.

## 4. Exact source-algebra obstruction

At an actual Xi point `rho=sigma+i tau`, Mellin evaluation is an algebraic convolution character
on `H_M`.  It sends `h_tau` to

\[
                 E_\rho(h_\tau)=e^{(\sigma-1/2)^2/(4\pi)}=\lambda.
\tag{26}
\]

Thus the unitized algebraic character kills `lambda*1-[h_tau]`.  This element cannot be a unit in
the algebraic Meyer quotient.  If `a!=0`, it is nevertheless a unit in the half-density completion,
and `(18)` is its canonical Green inverse.

### Corollary `[PROVED HERE]`: one-element inverse-closedness defect

Every off-critical actual Xi point creates an explicit failure of inverse-closedness of the
algebraic Meyer quotient in its canonical half-density completion.  Conversely, on the critical
line the same element is killed by a continuous completion character and is not a completion unit.
Therefore RH is equivalent to inverse reflection for this explicit divisor-height-centered Gaussian
family.

This equivalence is diagnostic, not the proposed proof.  New content is `(8)`, `(13)`, and the
concrete completed inverse `(18)` with exact laws `(20)` and `(23)`.

## 5. Singular Poisson lift and actual Möbius--Gaussian source

Fix a spectral center `c` and an ambient parameter `r`.  Define

\[
 \chi_c(s)=\exp\!\left(\frac{(s-c)^2}{4\pi}\right),\qquad
 D_{c,r}(s)=\chi_c(r)-\chi_c(s),
\tag{28}
\]

and the universal two-variable singular lift

\[
                    F_{c,r}(s)=\frac{1}{\zeta(s)D_{c,r}(s)}.
\tag{29}
\]

No zero enumeration occurs in `(29)`: `r` is a free ambient spectral parameter.  For an off-line
Xi zero `rho`, take `c=1/2+i Im(rho)`, so `rho-c=Re(rho)-1/2 != 0`.

### Theorem 6 `[PROVED HERE, FORMALIZED]`: forced successor pole

If `rho` lies in the open critical strip, `Xi(rho)=0`, `rho != c`, and
`m=ord_rho(Xi)`, then

\[
             \operatorname{ord}_{\rho}D_{c,\rho}=1,
 \qquad
             \operatorname{ord}_{\rho}F_{c,\rho}=-(m+1).
\tag{30}
\]

On a punctured neighbourhood of `rho`,

\[
 \zeta(s)F_{c,\rho}(s)=D_{c,\rho}(s)^{-1},\qquad
 \zeta(s)D_{c,\rho}(s)F_{c,\rho}(s)=1.
\tag{31}
\]

### Proof

Differentiation gives

\[
 D'_{c,\rho}(\rho)
 =-\chi_c(\rho)\frac{\rho-c}{2\pi}\ne0.
\tag{32}
\]

Thus `D` has order one.  In the open strip, the completed factorization
`Xi=archFactor*zeta` has nonvanishing `archFactor`, so zeta and Xi have the same analytic order
`m`.  Orders add under multiplication and change sign under inversion, proving `(30)`.  Isolated
zeros of zeta and the simple zero of `D` give `(31)`.  QED.

### Theorem 7 `[PROVED HERE, FORMALIZED]`: universal Gamma/Green residue

On the same punctured germ,

\[
             \Xi(s)F_{c,\rho}(s)
             =\operatorname{archFactor}(s)D_{c,\rho}(s)^{-1},
\tag{33}
\]

and

\[
             \operatorname{ord}_{\rho}(\Xi F_{c,\rho})=-1.
\tag{34}
\]

Its normalized residue is not free:

\[
 \lim_{s\to\rho}(s-\rho)\Xi(s)F_{c,\rho}(s)
 =-\frac{2\pi\,\operatorname{archFactor}(\rho)}
         {\chi_c(\rho)(\rho-c)}\ne0.
\tag{34a}
\]

Hence the Meyer preimage retains `m+1` singular levels, while completed Xi cancels precisely the
`m` arithmetic levels and presents one simple Gaussian residue to the Gamma boundary.  This is an
exact comparison with the actual completed Gamma factor, not a fitted Hodge chain.

### Proof

Substitute `Xi=archFactor*zeta` into `(31)`.  Since `archFactor` is nonzero and `D` has order one,
the right side of `(33)` has order `-1`.  Equivalently, adding the Xi order `m` to the lift order
`-(m+1)` gives `(34)`.  Dividing the numerator value by
`D'_(c,rho)(rho)=-chi_c(rho)(rho-c)/(2*pi)` gives `(34a)`; every factor is nonzero in the stated
off-center strip.  QED.

There is also a literal source construction before singular continuation.  Put

\[
 q_{c,r}(s)=\chi_c(s)\chi_c(r)^{-1}.
\tag{35}
\]

### Theorem 8 `[PROVED HERE, FORMALIZED]`: safe-chamber Möbius--Gaussian source

If `Re(s)>1` and `|q_{c,r}(s)|<1`, the series

\[
 \mathscr F_{c,r}(s)
 =\sum_{k\ge0}
   L(\operatorname{mPart}_1\mu,s)\,
   \chi_c(r)^{-1}q_{c,r}(s)^k
\tag{36}
\]

converges and equals `F_{c,r}(s)`.

### Proof

On `Re(s)>1`, the literal `mPart_1` Möbius L-series is `zeta(s)^{-1}`.  The remaining sum is
geometric and equals

\[
 \chi_c(r)^{-1}(1-q_{c,r}(s))^{-1}
 =D_{c,r}(s)^{-1}.
\]

Multiplication proves `(36)=(29)`.  QED.

Theorem 8 is the concrete arithmetic source object missing from the previous formulation.  Its
Gaussian index `k` is convolution depth; its Möbius coefficient is literal ordinary-prime data.
The new theorem is not the classical identities separately, but the exact source assembly whose
continuation has the forced local laws `(30)`--`(34)`.

Lean modules:

- `DeningerMeyerXiGaussianSingularPoissonLift.lean` proves `(30)`--`(34)`.
- `DeningerMeyerXiGaussianGammaResidue.lean` proves the exact nonzero residue `(34a)`.
- `DeningerMeyerMobiusGaussianNeumannSource.lean` proves convergence and `(36)`.

## 6. New hard frontier

`[CONJECTURE: DM_MOBIUS_GAUSSIAN_SINGULAR_CONTINUATION]`

The two-variable source `(36)` continues from its safe chamber as a coefficient-faithful section
of one source-pointed Hausdorff Meyer/Gamma graph completion, before restricting `r` to the Xi
divisor.  At every actual Xi zero its germ must equal `(29)` modulo a holomorphic source germ, and
completed-Xi transport must land in the actual Gamma/co-Poisson incidence domain with the simple
residue `(33)`.

For an off-line zero, this continuation would place the explicit Green inverse in an admitted
source sector while preserving the algebraic evaluation that kills `lambda*1-[h_tau]`.  It would
therefore contradict `(26)` and prove RH.

The unresolved datum is no longer existence or local form of the correction: `(36)` constructs it
where source series converge, and `(30)`--`(34)` force its zero-fibre principal part and Gamma
residue.  Missing science is the coefficient-faithful singular continuation theorem in the actual
Meyer/Gamma graph topology.  Regular completion is impossible by `(20)`, `(23)`, and existing full
verticality of the off-line Xi graph.

## Fake rejection

1. **Boundedness restatement.** Declaring `(18)` Meyer-admissible is equivalent to deleting the
   computed tail and supplies no proof.
2. **Ordinary `L1` completion.** It constructs `(18)` but necessarily loses the tilted moment `(20)`.
3. **Scalar positivity.** Every term of `(18)` is positive; positivity causes, rather than repairs,
   the divergence in `(20)`.
4. **Regular Gamma/Hellinger bridge.** Updated paper separates Gamma/Hellinger and Meyer routes.
   Regular transport conserves Cartan slope and cannot cancel `(23)`.
5. **Divisor-indexed subtraction.** Subtracting `e^{-|a||t|}` after reading `a` is circular.  Valid
   correction must be generated from prime Poisson boundary uniformly before evaluating `rho`.
6. **Closed-graph repair.** Existing Xi graph-closure theorem proves full vertical fibre off line;
   closure after completion cannot supply the conjectured continuation.
7. **Local principal-part bookkeeping.** Equations `(30)`--`(34)` alone do not construct a global
   source section.  Closure credit requires continuation of the literal series `(36)`.
8. **Divisor-indexed Mittag--Leffler subtraction.** Choosing principal parts separately after
   enumerating Xi zeros discards source provenance.  Required section is continuation of the
   two-variable source `(36)` before divisor restriction.

## Novelty audit

- Corpus search found no strong-log convolution algebra, Poisson-boundary convolution-ideal theorem,
  Gaussian Neumann resolvent, or exact Cartan-tail identity.
- Meyer's spectral construction supplies nuclear quotient and Xi spectrum, not the half-density
  Banach algebra or `(18)`--`(23)`.
- Gaussian convolution powers, geometric resolvents, Young's inequality, and saddle estimates are
  classical individually.  No novelty is claimed for those ingredients.
- Möbius inversion, reciprocal-zeta Dirichlet series, local analytic order calculus, and geometric
  summation are classical individually.  No novelty is claimed for them.
- Claimed project-specific advance is their exact assembly in literal Meyer cohomology: the same
  horizontal Xi displacement simultaneously equals the algebraic Gaussian character, completion
  inverse threshold, exact bilateral exponential-moment abscissa, critical moment boundary, and
  Green-tail rate.  New singular layer additionally proves that the literal Möbius--Gaussian source
  has forced Xi-zero pole depth `m+1` but a multiplicity-independent simple completed Gamma residue.

## Lean plan

1. `DeningerMeyerHalfDensityConvolution.lean`
   - half-density conjugation `(13)` for raw convolution;
   - weighted Young inequality `(14)`;
   - strong-log closure under scaling and exponential modulation.
2. `DeningerMeyerPoissonConvolutionIdeal.lean`
   - construct `K_gf`;
   - prove cap endpoint laws and boundary intertwining `(8)`.
3. `DeningerMeyerGaussianGreenPrimitive.lean`
   - **DONE:** normalized widened Gaussian terms and raw height-centered source;
   - **DONE:** exact arbitrary Cartan moments `(21a)` and infinite interior transform `(21b)`;
   - **DONE:** exact moment-wall dichotomy and saddle-ray equality;
   - remaining: formal two-sided pointwise logarithmic limit `(23)`.
4. Build quotient nonunital seminormed algebra, Hausdorff completion, and unitization.
5. Formalize Gaussian one-element inverse-closedness defect and corrected-tail frontier interface.
6. `DeningerMeyerXiGaussianSingularPoissonLift.lean`
   - **DONE:** simple Gaussian denominator and exact successor pole `m+1`;
   - **DONE:** punctured Poisson anomaly and completed Gamma/Green identity;
   - **DONE:** universal simple residue after Xi transport.
7. `DeningerMeyerXiGaussianGammaResidue.lean`
   - **DONE:** exact normalized Gamma/Green residue limit;
   - **DONE:** closed nonzero coefficient independent of Xi multiplicity.
8. `DeningerMeyerMobiusGaussianNeumannSource.lean`
   - **DONE:** literal `mPart_1` Möbius L-series times Gaussian Neumann depths;
   - **DONE:** safe-chamber summability and exact equality with singular lift;
   - remaining: singular graph-topology continuation to critical-strip Xi fibres.

## Log

- 2026-08-02 -- Updated paper read.  Gamma/Hellinger-to-Meyer artificial-chain plan retired.
- 2026-08-02 -- Discovered and proved Poisson convolution-ideal law and half-density `L1` algebra law.
- 2026-08-02 -- Constructed completed Gaussian Neumann Green primitive; proved bounded ordinary
  capacity, termwise unit tilted mass, divergent Xi moment, and exact Cartan tail exponent.
- 2026-08-02 -- Internal corpus and focused primary-literature searches found classical ingredients
  but no source-specific theorem `(8)` plus `(18)`--`(23)`.
- 2026-08-02 -- Proved and formalized exact arbitrary-tilt law `(21a)`, geometric transform `(21b)`,
  and full Cartan moment wall. Direct Lean passes; targeted leaf build and clean axiom audit pass.
- 2026-08-02 -- Constructed and formalized universal singular Poisson--Gaussian lift.  At a Xi zero
  of multiplicity `m` its pole order is exactly `m+1`; completed Xi transport leaves one simple
  Gamma/Green residue.
- 2026-08-02 -- Constructed literal safe-chamber Möbius--Gaussian Neumann source and proved its
  exact sum is the singular lift.  Frontier sharpened to source-topological continuation of this
  object, not existence of another correction or another bounded carrier.
- 2026-08-02 -- Extracted and formalized the exact nonzero completed Gamma residue
  `-2*pi*archFactor(rho)/(chi_c(rho)*(rho-c))`; continuation now has forced normalization, not only
  forced pole order.

## 2026-08-03 source-topology obstruction and exact survivor

The updated Hellinger--Hodge--Green paper makes the global polarized singular completion the live
gate. The raw Gaussian--Gamma residue packet cannot be placed in the ordinary unweighted Xi
incidence completion. At fixed safe centre `c = 2`, define

```text
R(q) = -2*pi*archFactor(rho_q)/(chi_2(rho_q)*(rho_q-2)),
W(q) = -chi_2(rho_q)*(rho_q-2)/(2*pi*archFactor(rho_q)).
```

`DeningerMeyerXiGaussianResidueNonadmission.lean` proves unconditionally:

```text
W(q) * R(q) = 1,
W(q) -> 0       along the cofinite filter on XiZeroCopy,
norm(R(q)) -> +infinity along that filter,
not Summable (fun q => norm(R(q))^2).
```

The decisive analytic estimate is a uniform strip bound obtained from Euler reflection rather than
Stirling:

```text
norm(GammaR(rho))^(-1) <= exp((pi/2)*norm(rho)).
```

The Gaussian character then contributes a negative quadratic in centered spectral norm, forcing
`W -> 0`. This is a genuine no-go for raw unweighted admission, not another equivalence with RH.

The strongest positive survivor is exact. For every horizon grade `h`, the source-faithful diagonal
weight `d = h*W` satisfies

```text
(d(q)*R(q)) = h(q),
Summable (fun q => norm(d(q)*R(q))^2)
  <-> Summable (fun q => norm(h(q))^2).
```

Thus analytic residue normalization and infinite-divisor grading are independent. `W` is forced by
the literal Möbius--Gaussian source; it leaves the constant packet and cannot itself provide
admission. The next hard theorem is no longer an unspecified singular completion:

```text
Construct h from the ordinary-prime/Gamma/co-Poisson source before divisor restriction; prove
h in l2; prove the h*W weighted sector is conservative under resolved augmentation; then prove its
Hermitian/Gram domination.
```

Arbitrary rapid weights, divisor-indexed Hilbert norms, and ordinary meromorphic interpolation fail
source provenance and do not address this theorem.

## 2026-08-03 reflected-Gaussian resolved admission

The independent horizon grade is now constructed from the fixed Paugam-invariant reflected Meyer
Gaussian before Xi-divisor restriction:

```text
h(q) = Mellin(g_ref)(rho_q)
     = xiGaussianHeatTerm(1/(4*pi), q).
```

It is nonzero, reflection invariant, line-conjugation compatible, and square-summable. With the
forced analytic residue inverse `W` and singular residue `R`, the weighted packet satisfies

```text
(h(q) W(q)) R(q) = h(q),
sum_q |h(q)|^2 < infinity.
```

This admitted vector now lands coefficient-faithfully in actual cross-prime Calderon--Witt
incidence. Each decoded divisor coefficient is `h(r) * w_pq != 0`. Its pre-codiagonal resolved
defect is the nonzero antidiagonal

```text
(h(r) w_pq, -h(r) w_pq),
```

whose raw codiagonal is zero. The resolved-provenance quotient retains the entire admitted
incidence vector through an explicit left inverse, so its quotient class is nonzero for every
Hellinger displacement.

Closed gates: source-derived horizon grade, `ell^2` singular admission, actual incidence landing,
and resolved-coface conservativity for the fixed source. Remaining Route-L frontier is narrower:
identify this source-graded completed singular vector with the actual global Deninger Green
resolved range, then derive its Hermitian Gram domination. No RH or positivity conclusion is
claimed before those two steps.

Lean:

```text
DeningerMeyerReflectedGaussianHorizonAdmission.lean
DeningerMeyerReflectedGaussianResolvedAdmission.lean
```

## 2026-08-03 exact compact-source Green range wall

The updated Hellinger--Hodge--Green paper correctly moves the shared frontier to a joint
prime--divisor range intertwiner.  A corpus audit now proves why the reflected-Gaussian admitted
vector cannot first be identified with the range of the existing compact-source comparison Green
map.

Continuous compact-support arithmetic cohomology in the present model is exactly the algebraic
direct sum of finite Xi jets.  Oriented Green reflection is an automorphism of that direct sum.
Therefore its completed comparison range is exactly

```text
range(deningerArithmeticSourceGreen)
  = range(Finsupp(XiZeroCopy,C) -> ell^2(XiZeroCopy,C)).
```

The reflected-Gaussian horizon vector is nonzero at every copy of the infinite Xi divisor.  Hence
it is outside this range.  Dense range proves the sharp survivor: it is in the closure.  Both facts
survive the actual completed Calderon--Witt incidence equivalence and the split-injective resolved
Hellinger--Gamma provenance quotient:

```text
admitted resolved class in closure(resolved compact Green range)
                         \ resolved compact Green range.
```

This kills the previous wording "identify the admitted vector with the current compact-dual Green
range."  No coefficient adjustment can make that true.  The current module is explicitly a Xi
comparison model, not an independently constructed global arithmetic Green complex.

Correct Route-L frontier is now ordered:

```text
construct source-native nonlocal completion of compact-support cohomology;
extend finite oriented Green reflection to it, with the admitted horizon vector in its range;
identify that completed range with the compatible part of the closed adaptive prime-normal range;
derive Hermitian Gram domination on the common resolved range.
```

The first genuinely arithmetic missing theorem is the third line.  Density makes any continuous
extension unique, so the completion cannot hide a new coefficient choice.

Formalized in:

```text
DeningerMeyerReflectedGaussianGreenRangeWall.lean
```

## 2026-08-03 canonical completed source Green primitive

The nonlocal source completion and its Green primitive are now constructed, not left as a name.
The source Gelfand triple's Hilbert middle is the multiplicity-exact Xi-jet `ell^2` carrier, with
dense finite source jets.  Finite oriented Green reflection extends uniquely to the isometric
operator

```text
(Ghat a)(q) = epsilon(q) a(Rq),
Ghat^2 = -1.
```

It agrees with current compact-source Green transport after the canonical Riesz source embedding.
Hence it is surjective and is the only continuous extension with the correct finite coefficients.

For admitted reflected-Gaussian residue `h_ref`, explicit completed source primitive is

```text
u_ref = -Ghat(h_ref),
u_ref(q) = -epsilon(q) h_ref(q),
Ghat(u_ref) = h_ref.
```

This primitive is unique, nonzero, and maps exactly to already constructed actual incidence and
resolved provenance classes.  Therefore completion, Green extension, and primitive existence are
closed.  They cannot be revisited as Route-L frontier.

Remaining hard theorem is genuinely arithmetic:

```text
identify compatible range of completed source Green/provenance
  with closed adaptive prime-normal source range,
then prove Hermitian Gram domination on that common range.
```

Surjectivity of `Ghat` alone proves no RH statement; it makes clear why arithmetic range restriction
is indispensable.

Formalized in:

```text
DeningerMeyerReflectedGaussianCompletedSourceGreen.lean
```
