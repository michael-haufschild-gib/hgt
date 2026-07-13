# Canonical Schur truncations cross from rational DA interior to singular maximal-HT boundary only cofinally

- **ID:** `singular-maximal-ht-schur-defect-collapse-law`
- **Stage:** 2-fully-proven on paper / needs audit
- **Type:** THEOREM / COFINAL DOUBLE-BOUNDARY LAW
- **Lane:** general hypertranscendence; singular Herglotz carriers; Schur geometry
- **Scientific status:** `[PROVED HERE] [NOVELTY UNVERIFIED]`
- **Parents:** `spectral-type-stratified-moment-fiber-maximal-ht.md`,
  `nevanlinna-boundary-bauer-retract-maximal-ht.md`,
  `pick-defect-finite-selector-maximal-ht-phase-law.md`
- **Statement:** In every indeterminate Hamburger moment fiber, every infinite-support singular
  spectral chart has a residual maximal full-translation HT phase. For every singular carrier in
  that phase, all finite Schur defects are strict and their Szego product is zero. More strongly,
  its canonical Bernstein--Szego truncations are positive analytic absolutely continuous carriers
  with rational, hence differentially algebraic, transforms; the `N`-th truncation matches the
  first `N` Schur/Taylor coordinates and converges to the singular HT carrier. Thus both the
  spectral boundary and the differential-algebraic boundary are crossed only in the cofinal
  limit. On the canonical Nevanlinna Bauer simplex, singular-continuous maximal-HT carriers form a
  residual set. The same double-boundary signature is forced conditionally on the oriented Xi
  source.

## Goal

The finite-selector theorem distinguishes singular finite Pick matrices from positive-defect
levels. It leaves open how a nonrational singular carrier reaches the boundary when every finite
matrix is positive definite. The answer is not merely a vanishing product. There is a canonical
finite-stage carrier at every depth, and every one of those carriers lies in the opposite spectral
and differential-algebraic phase from the limit.

The new HT law is:

> **A singular maximal-HT carrier is the cofinal limit of canonical rational-DA, absolutely
> continuous carriers that reproduce arbitrarily long finite germs. Its spectral singularity and
> differential transcendence must therefore be carried by the completed Schur tail.**

## Cayley normalization

Let `nu` be a singular probability measure on `R` with infinite support and Cauchy transform

```text
m_nu(z)=integral_R 1/(x-z)d nu(x).                         (1)
```

Push `nu` to the unit circle by a real-line/disk Cayley transform. Singularity and support
cardinality are preserved. Let `mu_hat` be the resulting probability measure on the circle, let
`F` be its Caratheodory function, and let `f` be its Schur function:

```text
F(w)=integral_(unit circle) (zeta+w)/(zeta-w)d mu_hat(zeta),
F(w)=[1+w f(w)]/[1-w f(w)].                               (2)
```

The transformations between `m_nu`, `F`, and `f` are fixed conformal and fractional-linear maps.
The measure `mu_hat` is singular and has infinite support.

Let

```text
alpha_0,alpha_1,...                                        (3)
```

be the Schur--Verblunsky parameters of `f`, and put

```text
delta_n=1-|alpha_n|^2.                                    (4)
```

## Strict finite defects `[SEARCH]`

Verblunsky's theorem gives the exact finite-stage alternative:

- a measure with `N` support points has `|alpha_j|<1` for `j<N-1` and
  `|alpha_(N-1)|=1`, at which point the Schur algorithm terminates;
- a nontrivial infinite-support measure has

```text
|alpha_n|<1,
delta_n>0                                                   (5)
```

for every `n`.

Thus no finite Schur step of `(1)` is singular. Equivalently, every reduced finite
Caratheodory--Fejer Pick matrix of the complete Taylor germ is positive definite.

## Necessary cofinal entropy collapse `[SEARCH + SPECIALIZATION]`

Let `D_N(mu_hat)` be the `(N+1) by (N+1)` Toeplitz Gram determinant of
`1,z,...,z^N` in `L^2(mu_hat)`. Szego recursion gives

```text
D_N(mu_hat)=product_(j=0)^(N-1) delta_j^(N-j).             (6)
```

Szego's theorem gives

```text
lim_(N->infinity) D_N(mu_hat)^(1/N)
 =product_(j=0)^infinity delta_j
 =exp(integral_0^(2pi) log w(theta)d theta/(2pi)),         (7)
```

where `w` is the absolutely continuous density of `mu_hat`.

Since `mu_hat` is singular, `w=0` almost everywhere. The logarithmic integral is `-infinity`, so

```text
product_(j=0)^infinity delta_j=0,
lim_(N->infinity) D_N(mu_hat)^(1/N)=0.                    (8)
```

Equations `(5)` and `(8)` are the infinite-interior law:

```text
delta_n>0 for every finite n,
product_n delta_n=0.                                      (9)
```

No individual finite defect detects the boundary. The product collapse is a necessary cofinal
signature of singularity.

It is not a characterization of singular spectral type. An absolutely continuous measure whose
density has nonintegrable logarithm also has zero Szego product. Accordingly, `(9)` must not be
called *the* singular phase: it is the scalar entropy shadow of the exact inner/singular boundary
condition.

## Canonical finite DA skeleton `[SEARCH + PROVED HERE]`

Let `phi_N` be the orthonormal polynomial of degree `N` for `mu_hat`. Its zeros lie strictly in the
disk, so the Bernstein--Szego measure

```text
d mu_hat^[N](theta)=d theta/[2 pi |phi_N(e^(i theta))|^2]   (10)
```

is a probability measure with strictly positive real-analytic density on the circle. Its
Verblunsky coefficients are

```text
alpha_j(mu_hat^[N])=alpha_j(mu_hat)  for j<N,
alpha_j(mu_hat^[N])=0                for j>=N.              (11)
```

Hence `mu_hat^[N]` has the same first `N` circle moments as `mu_hat`; equivalently, its
Caratheodory function `F_N` has the same Taylor germ through order `N`:

```text
F_N(w)-F(w)=O(w^(N+1)) at w=0.                             (12)
```

The exact formula

```text
F_N(w)=psi_N^*(w)/phi_N^*(w)                               (13)
```

makes `F_N` rational. Its Schur function and every fixed Cayley pullback are rational as well, so
they are differentially algebraic. Since every fixed Verblunsky coordinate eventually agrees,

```text
mu_hat^[N] -> mu_hat weakly,
F_N -> F locally uniformly on the disk.                    (14)
```

For singular `mu_hat`, `(10)--(14)` cross an actual spectral boundary: every finite carrier is
absolutely continuous with full circle support, while the limit is singular. If the limiting
Cauchy transform is hypertranscendental, they simultaneously cross a differential-algebraic
boundary: every finite transform is rational DA, while the limit is HT. These two changes occur
despite exact agreement of an arbitrarily long initial analytic germ.

## Cofinal aperture concentration `[PROVED HERE]`

Write

```text
d mu_hat^[N]=rho_N d theta/(2 pi).                         (15)
```

Because `mu_hat` is singular, there is a Borel null set `E` with `mu_hat(E)=1`. For every
`epsilon>0`, outer regularity gives an open `U_epsilon` containing `E` with normalized Lebesgue
measure less than `epsilon`. Weak convergence and the Portmanteau theorem give

```text
liminf_N mu_hat^[N](U_epsilon)>=mu_hat(U_epsilon)=1,
therefore lim_N integral_(U_epsilon) rho_N d theta/(2 pi)=1. (16)
```

Thus the finite carriers have positive density everywhere, yet asymptotically all of their mass
lies in an arbitrarily small boundary aperture. In particular, the densities are not uniformly
integrable.

More sharply, for every `p>1`,

```text
||rho_N||_(L^p) -> infinity.                               (17)
```

Otherwise an infinite bounded subsequence would have a weakly convergent subsequence in reflexive
`L^p`; its measure limit would have an `L^p` density. But the measure sequence already has the
unique weak limit `mu_hat`, which is singular. This contradiction proves `(17)`.

The cofinal geometry is therefore polarized:

```text
geometric-mean aperture  product_n delta_n -> 0,
every superlinear density norm ||rho_N||_p -> infinity.    (18)
```

The first limit records entropy collapse; the second records mass concentration. Neither occurs at
any finite Schur stage.

## Strict finite positivity forces cofinal loss of coercivity `[PROVED HERE]`

Let

```text
0<lambda_min(N)<=lambda_max(N)                             (18a)
```

be the extreme eigenvalues of the Toeplitz Gram matrix `G_N` of `1,z,...,z^N` in
`L^2(mu_hat)`. Every diagonal entry of `G_N` is one, so

```text
trace(G_N)=N+1,
lambda_max(N)>=1.                                         (18b)
```

Its determinant is `D_N(mu_hat)`. Equation `(8)` implies

```text
lambda_min(N)
 <=det(G_N)^(1/(N+1)) ->0,
lambda_max(N)/lambda_min(N)->infinity.                    (18c)
```

Thus every finite Gram form is strictly positive, but the nested family has no uniform coercivity
constant. The positive cone is approached through interiors whose metric aperture collapses.

The `N`-th Bernstein--Szego measure has the same first `N` circle moments as `mu_hat`. Therefore
its Gram matrix on `1,z,...,z^N` is exactly `G_N`, not merely asymptotic to it. The rational-DA,
absolutely continuous model reproduces the full level-`N` ill-conditioning of the singular HT
carrier while still lying spectrally in the interior.

### Cofinal metric-weld pinching

This loss of coercivity constrains any proposed source realization. Suppose `Q_N` is a positive
source Gram form with a uniform lower bound

```text
Q_N>=c I,  c>0,                                             (18d)
```

and a finite carrier map `W_N` realizes the target section by congruence:

```text
G_N=W_N^* Q_N W_N.                                         (18e)
```

For a unit vector minimizing `||W_N v||`, equations `(18d)--(18e)` give

```text
c sigma_min(W_N)^2<=lambda_min(G_N).
```

Hence `(18c)` forces

```text
sigma_min(W_N)->0,
||W_N^(-1)||->infinity                                    (18f)
```

whenever the inverse is defined. A uniformly invertible, uniformly bi-Lipschitz, or unitary weld
from a uniformly coercive source geometry is impossible. A valid source-to-carrier identification
must pinch at the cofinal boundary.

The formalized prime-clock law supplies an example of a source coordinate whose Hessian, after the
natural `(log N)^2` normalization, stays uniformly coercive and has its sharp `1/log N` crossover.
No theorem presently identifies that scalar source coordinate with the collapsing Schur direction.
The statement above therefore constrains such a future identification; it does not manufacture the
missing zero-preserving source weld.

The companion `singular-maximal-ht-toeplitz-weld-graph-saturation.md` determines the endpoint of
this pinching. For a purely singular carrier, the raw analytic-polynomial graph is dense in the
full source--carrier product. The unique compatible positive-triangular repair is inverse Cholesky
orthogonalization; it produces the unitary OPUC frame and obeys the exact law

```text
||C_N||=lambda_min(G_N)^(-1/2)->infinity.                 (18g)
```

Thus the missing marking is not arbitrary: in the canonical triangular category it is exactly the
divergent orthogonal-polynomial frame.

## Residual maximal translation HT in the same phase `[PROVED HERE VIA PARENT]`

Fix any indeterminate normalized Hamburger moment sequence. The spectral-type companion constructs
inside its exact representing-measure fiber:

1. positive charts of infinite pure-point measures;
2. positive charts of singular-continuous measures;
3. more generally, every exact pure-point/singular-continuous mass vector with zero absolutely
   continuous component.

Bounded positive reweighting preserves the singular measure class and infinite support. In every
such chart, a dense residual set of Cauchy transforms has a differentially algebraically
independent full complex translation family.

Every point in these charts satisfies `(9)`, while the residual subset is maximally translation
HT. All points still share the same complete Hamburger moments and the same formal translated
derivative asymptotic germ at upper infinity.

Choose one carrier from the residual subset of a singular chart and apply `(10)` to its circle
pushforward. Therefore one exact complete-moment constraint contains carriers satisfying
simultaneously

```text
maximal full-translation HT,
strict positivity of every finite Schur defect,
zero cofinal defect product,
pure singular spectral type,                              (19)
```

and every such carrier has a canonical sequence of rational-DA, absolutely continuous
finite-prefix models converging to it. The approximating measures do not remain in the original
complete Hamburger moment fiber; they preserve the growing interior germ `(12)`, not all moments.
This distinction is essential.

## Generic phase on the canonical Bauer simplex `[PROVED HERE]`

The Bauer-retract parent gives an affine homeomorphism

```text
Beta:P(RP^1(R)) -> K_s subset M(s).                        (19a)
```

and proves that maximal full-translation HT is residual in `K_s`.

The atomless probabilities on the projective circle form a dense `G_delta`. Indeed, for each
`k`, the probabilities possessing an atom of mass at least `1/k` form a closed set, and atomless
probabilities are dense by arbitrarily small continuous spreading. The probabilities singular to
projective Lebesgue measure also form a dense `G_delta`. Singularity is equivalent to the
existence, for every `k`, of an open set of Lebesgue measure below `1/k` carrying mass above
`1-1/k`; a countable arc basis makes this a `G_delta`, and atomic probabilities prove density.

Their intersection is the residual set of singular-continuous parameter laws. Exact spectral-type
transport in the parent theorem sends such a law to a singular-continuous real-line carrier. Since
`Beta` is a homeomorphism, singular-continuous carriers are residual in `K_s`. Intersecting with
the residual maximal-HT subset gives

```text
{nu in K_s : nu is singular continuous and m_nu has
 maximal full-translation HT} is residual in K_s.          (19b)
```

Every point of `K_s` has all prescribed Hamburger moments. Thus `(19b)` identifies the generic
spectral/differential phase inside one exact complete constraint, not merely inside separately
chosen positive charts.

For every carrier in `(19b)`, the Bernstein--Szego sequence `(10)` is rational DA and absolutely
continuous and converges to that carrier after Cayley transport. Those approximants cannot stay in
the exact moment fiber: a residual point of `(19b)` is singular continuous, whereas every finite
approximant has a positive analytic density and only the growing interior germ is fixed. The
rational-DA skeleton therefore approaches the generic constrained phase *transversely* to the
complete-moment simplex.

## Cofinal double-boundary law

> **Within a complete indeterminate moment constraint, singular spectral type and maximal
> translation hypertranscendence coexist. Each such carrier is approached canonically by
> rational-DA, absolutely continuous Schur truncations matching longer and longer analytic germs.
> Every finite defect is strict; the Szego entropy aperture collapses only cofinally; and the exact
> singular boundary is the inner limit. The finite Gram metrics remain positive but lose every
> uniform coercivity bound.**

This is stronger than saying that finite data do not suffice. It identifies the canonical finite
carriers, their exact spectral and differential type, their growing jet agreement, the positive
finite defects, and the nonuniform limit in which both boundary phenomena appear.

## General HT consequence

Hypertranscendence is compatible with both positive Hilbert geometry and inner boundary behavior.
For singular Herglotz carriers, no finite Schur truncation witnesses a defect: every truncation is
strictly inside the positive cone and is itself rational DA. The global singular phase is the inner
boundary limit; zero multiplicative aperture is a necessary entropy consequence.

A proposed finite-stage rigidity argument must therefore distinguish:

```text
pointwise finite positivity: delta_n>0 for each n,
uniform/cofinal positivity: inf_N product_(n<=N)delta_n>0.  (20)
```

The first is compatible with singular maximal HT; the second excludes the zero-entropy cofinal
phase. To characterize singularity itself one must additionally prove the inner boundary law.

## RH consequence `[COMPANION BRIDGE; RH NOT PROVED]`

The companion `xi-schur-inverse-limit-atomic-condensation-law.md` applies this geometry to the
normalized full-upper-half-plane Xi logarithmic derivative. It proves the exact criterion

```text
RH
 iff every finite reduced Xi Caratheodory--Fejer matrix is positive definite
 iff every finite Xi Schur defect is strictly positive.    (21)
```

Under these equivalent conditions, the associated circle carrier is infinite pure point, its
Szego product is zero, and its canonical Bernstein--Szego densities concentrate onto arbitrarily
small neighborhoods of the Cayley image of the Xi divisor with every `L^p`, `p>1`, norm diverging.

This is a route classification, not an orientation proof. It says positively that a source-faithful
Schur route must remain in every finite positive chamber while creating atomic concentration only
at the inverse limit. Any uniform superlinear density bound on the canonical truncations would
exclude the required carrier.

## Parent-theory and novelty attack

1. `[SEARCH]` The Cayley/Herglotz correspondence, Schur algorithm, Verblunsky theorem, Toeplitz
   determinant factorization, and Szego product theorem are classical.
2. `[SEARCH]` Barry Simon's *OPUC on One Foot*, Theorems 4.3--4.4 and equations
   (8.1)--(8.5), gives the Bernstein--Szego approximation, rational Caratheodory formula, and exact
   normalization used here:
   `https://web.ma.utexas.edu/mp_arc/c/05/05-78.pdf`.
3. `[BRIDGE]` Exact singular spectral charts and residual maximal full-translation HT are inherited
   from the spectral-type moment-fiber theorem.
4. `[PROVED HERE]` Their intersection with Bernstein--Szego approximation gives the double-boundary
   law: a residual family of singular maximal-HT limits, each with a canonical rational-DA,
   absolutely continuous finite-prefix skeleton.
5. `[PROVED HERE]` Generic-measure Baire theory and the intrinsic Bauer homeomorphism strengthen
   the chart theorem to a residual singular-continuous maximal-HT phase on the entire canonical
   simplex; its rational-DA approximation skeleton is transverse to the exact moment constraint.
6. `[COMPANION BRIDGE]` The Xi inverse-limit criterion and atomic-condensation consequence are
   separated into `xi-schur-inverse-limit-atomic-condensation-law.md`.
7. `[COMPANION THEOREM]` Full graph saturation and the uniquely forced divergent triangular repair
   are separated into `singular-maximal-ht-toeplitz-weld-graph-saturation.md`.
8. `[CANDIDATE RESIDUE]` Preliminary exact searches found no theorem linking residual maximal
   translation differential independence, exact moment-fiber singular strata, canonical
   Bernstein--Szego finite-prefix models, and the simultaneous DA-to-HT / AC-to-singular cofinal
   transition.
9. The theorem remains `[NOVELTY UNVERIFIED]` pending OPUC, moment-problem, and differential-algebra
   specialist audit.

No numerical experiment and no RH assumption enter the general theorem.

## Honest significance score

**82/100 candidate; plausible range 70--90.** The Schur, Bernstein--Szego, and Szego mechanisms are
classical. The candidate new residue is the exact double-boundary interaction with residual
maximal-HT singular strata. That interaction is mathematically sharper than the product statement,
but it does not by itself establish a true 90: priority remains unverified, and Xi orientation is
not proved.

## Lean status

No Stage 3 claim is made. Exact formalization requires Cayley transport of measures, circle
Lebesgue decomposition, Schur parameters, Verblunsky recursion, Toeplitz determinants, Szego's
theorem, and the parent residual maximal-HT theorem. These layers are not jointly formalized.

Formalization audit (needs-audit pass): no bounded self-contained kernel closes a gate. The
substantive steps — strict finite defects `(5)` (Verblunsky), the zero Szego product `(6)`--`(9)`,
Bernstein--Szego approximation `(10)`--`(14)`, and the cofinal `L^p`/coercivity collapse — all need
OPUC/Szego theory absent from mathlib, layered on the parent Nevanlinna/transversality stack. The
one abstractly-extractable linear-algebra identity (`λ_max/λ_min → ∞` from `trace = N+1` and
`det → 0`) is a spectral wrapper that certifies nothing without the absent Szego determinant input.
No partial file is added.

## Gates

- [x] real-line singular measure transported to circle without changing type/support cardinality
- [x] strict interior Schur defects at every finite stage
- [x] Toeplitz determinant factorization fixed
- [x] zero cofinal Szego product proved as a necessary, not sufficient, singularity signature
- [x] canonical Bernstein--Szego carriers constructed
- [x] exact finite-germ agreement and rational differential algebraicity proved
- [x] weak/local-uniform convergence to the singular HT carrier proved
- [x] small-aperture mass concentration and all-`L^p` blow-up proved
- [x] cofinal graph endpoint and unique triangular repair separated into companion theorem
- [x] residual maximal full-translation HT placed in the same exact phase
- [x] exact Xi inverse-limit positivity criterion scoped without claiming RH
- [x] primary OPUC normalization checked
- [x] preliminary novelty search
- [ ] independent specialist proof audit
- [ ] full primary-source priority audit
- [ ] unconditional Lean formalization of the entire theorem

## Log

- 2026-07-12 -- Combined the singular spectral HT charts with Verblunsky/Szego theory. Proved that
  every finite Schur defect is strict while the infinite defect product and normalized Toeplitz
  determinant vanish, and derived the same law conditionally for an oriented Xi source.
- 2026-07-12 -- Corrected zero product from a purported singularity phase to a necessary entropy
  shadow. Added the canonical Bernstein--Szego finite-prefix skeleton and isolated the genuine
  double transition: rational DA to HT and absolutely continuous to singular, only cofinally.
