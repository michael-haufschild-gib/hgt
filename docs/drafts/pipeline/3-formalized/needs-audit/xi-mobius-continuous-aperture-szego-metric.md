# The continuous Möbius--Szegő true-aperture metric

- **ID:** `xi-mobius-continuous-aperture-szego-metric`
- **Stage:** 3-formalized / needs external specialist novelty audit
- **Type:** THEOREM PACKAGE / POSITIVE REPAIR OF A CRITICAL-APERTURE NO-GO
- **Scientific status:** `[PROVED HERE] [CANDIDATE NEW SOURCE-SPECIFIC KNOWLEDGE]`
  `[EXTERNAL NOVELTY UNVERIFIED] [NOT AN RH PROOF]`
- **Parents:** `xi-mobius-schur-valuation-marking`;
  `xi-transverse-valuation-szego-true-aperture-metric`;
  `finite-fusion-infinite-hypertranscendence`
- **Lean modules:** `RHTower/XiMobiusContinuousApertureSzegoMetric.lean`;
  `RHTower/XiMobiusContinuousApertureDyadicProjection.lean`;
  `RHTower/XiMobiusContinuousApertureCCMTangent.lean`

## Frontier correction

The existing valuation--Szegő construction separates positive **integral** shifts.  The RH
consumer is the full transverse family and needs every real aperture `a>0`, especially the germ
`a -> 0+`.  Replacing the critical local weight `p^(-1)` by the moving disk node `p^(-a)` is not
an all-prime repair: its completed diagonal is asymptotic to `p^(-2a)`, so the prime sum has the
sharp convergence wall `a>1/2` and diverges throughout the required small-aperture regime.

The positive repair is forced by the actual local Möbius Schur factor.  Keep its physical
critical weight `q_p=p^(-1)` fixed and sample its spectral argument on the aperture ray `z=a e`.
This separates the source weight from the observation aperture exactly as the coordinate-field
and hypertranscendence results require.

## Actual ray samples and their depth derivative

For a prime `p`, real `a>0`, and `e>=0`, put

```text
q_p=exp(-log p)=p^(-1),
r_(p,a)=exp(-a log p)=p^(-a),

B_(p,a)(e)
 =bernoulliSignedSchurFactor(q_p,log p,a e)
 =(1-q_p r_(p,a)^e)/(1+q_p).                         (1)
```

This is a literal sample of the existing source multiplier, not an auxiliary sequence.  Its
forward depth difference is

```text
D_(p,a)(e)=B_(p,a)(e+1)-B_(p,a)(e)
 =q_p/(1+q_p) * (1-r_(p,a)) r_(p,a)^e
 =1/(p+1) * (1-p^(-a))p^(-ae).                       (2)
```

Thus every positive real aperture is represented by a Hardy coherent state, while the fixed
critical Möbius weight supplies an aperture-independent square-summable prime damping.

## Exact continuous-aperture kernel

For `a,b>0`, geometric summation gives

```text
K_p(a,b)
 =sum_(e>=0) D_(p,a)(e)D_(p,b)(e)
 =1/(p+1)^2
   *(1-p^(-a))(1-p^(-b))/(1-p^(-(a+b))).              (3)
```

In particular,

```text
K_p(a,a)=1/(p+1)^2 * (1-p^(-a))/(1+p^(-a))
         <=1/(p+1)^2<=p^(-2).                         (4)
```

Therefore

```text
sum_p K_p(a,a)<infinity                               (5)
```

for **every** `a>0`, with one summable majorant independent of the aperture.  This is the
continuous true-aperture completion missing from the integral construction.

The damping cancels after unit normalization.  For `a,b>0`,

```text
1-K_p(a,b)^2/(K_p(a,a)K_p(b,b))
 =((p^(-a)-p^(-b))/(1-p^(-(a+b))))^2.                 (6)
```

Hence distinct real apertures have strictly positive pseudohyperbolic separation already at one
fixed prime.  More strongly, for distinct apertures `a_0,...,a_(N-1)`, the first `N` depth
differences form

```text
M_(e,j)=1/(p+1)(1-p^(-a_j))(p^(-a_j))^e,
```

a Vandermonde matrix times a nonzero diagonal.  It has nonzero determinant and its Gram is
positive definite.

## Infinitesimal aperture law

Define the all-prime diagonal energy

```text
E(a)=sum_p K_p(a,a),
C_M=sum_p log(p)/(p+1)^2.                              (7)
```

The logarithmically weighted inverse-square series is summable, so `0<C_M<infinity`.  Since

```text
(1-exp(-a log p))/(1+exp(-a log p))
 =a log(p)/2+o_p(a),                                  (8)
```

and, for `a>0`,

```text
0<=K_p(a,a)/a<=log(p)/(p+1)^2,                        (9)
```

dominated convergence proves the exact source slope

```text
E(a)/a -> C_M/2,                 a->0+.                (10)
```

Consequently the source-prescribed scalar normalization

```text
E_4(a)=(8/C_M)E(a)                                    (11)
```

has the four-unit germ

```text
E_4(a)=4a+o(a)=4(1-exp(-a))+o(a).                     (12)
```

This closes the **incoming continuous-aperture Hilbert budget**.  It does not prove that the Xi
boundary leakage is its contractive image.

## Cauchy tangent law and the CCM interface

The scalar slope is the diagonal of a stronger two-aperture limit.  For fixed `alpha,beta>0`,
let `t->0+`.  Then at every prime

```text
K_p(t alpha,t beta)/t
 -> 1/(p+1)^2 * alpha beta/(alpha+beta) * log p,       (13)
```

and the same logarithmic prime-square majorant as in `(9)` gives

```text
K(t alpha,t beta)/t
 :=sum_p K_p(t alpha,t beta)/t
 -> C_M * alpha beta/(alpha+beta).                    (14)
```

Thus the four-unit normalized tangent kernel is

```text
K_4^tan(alpha,beta)=8 alpha beta/(alpha+beta).         (15)
```

This is not an arbitrary positive kernel.  It is the derivative-dressed universal Cauchy Gram:

```text
alpha beta/(alpha+beta)
 = integral_(0,infinity) alpha exp(-alpha x)
     * beta exp(-beta x) dx.                          (16)
```

Its normalized correlation and defect are

```text
Corr_tan(alpha,beta)=4 alpha beta/(alpha+beta)^2,
1-Corr_tan(alpha,beta)=((alpha-beta)/(alpha+beta))^2. (17)
```

This places the infinitesimal true-aperture source exactly inside the existing complex CCM
polar--prime Mellin colligation.  Specializing
`cauchy_eq_prime_sub_shiftedPolar_add_criticalMellinDefect_complex` at
`s=alpha+beta` and multiplying by `alpha beta` gives

```text
alpha beta/(alpha+beta)
 = alpha beta * (resolved von-Mangoldt channel
                 - shifted polar channel
                 + critical Mellin-defect channel).  (18)
```

Therefore the first-order source-to-Xi problem is canonically localized: it is not a search for an
aperture kernel, but control of the already-defined CCM critical Mellin defect after the derivative
dressing.  Any proposed response contraction whose germ disagrees with `(18)` is not compatible
with the actual Möbius source.

## Paper proof

Equation `(1)` is the definition of `bernoulliSignedSchurFactor` with
`exp(-(log p)ae)=r_(p,a)^e`.  Subtraction gives `(2)`.  Multiplying two copies of `(2)` and summing
the geometric series with ratio `r_(p,a)r_(p,b) in (0,1)` gives `(3)`.  Setting `a=b` and factoring
`1-r^2=(1-r)(1+r)` gives `(4)`; comparison with the convergent inverse-square series proves `(5)`.

After dividing `(3)` by the two diagonal values, elementary denominator clearing gives `(6)`.
The map `a |-> exp(-a log p)` is injective because `log p>0`, so the displayed finite matrix is a
weighted Vandermonde with nonzero determinant.

For `(9)`, use `1-exp(-x)<=x` at `x=a log p` and `1+exp(-x)>=1`.  The majorant is summable by
comparison with `sum_n log(n)/n^2`.  The derivative at zero of
`(1-exp(-a log p))/(1+exp(-a log p))` is `log(p)/2`; dominated convergence gives `(10)`, and
`1-exp(-a)=a+o(a)` gives `(12)`.  No numerical computation is used.

For `(13)`, divide the three exponential gaps in `(3)` by `t`.  Their limits are respectively
`alpha log p`, `beta log p`, and `(alpha+beta) log p`, so the quotient has the displayed limit.
For `t>0`, the Szegő fraction is at most either numerator gap; hence
`0<=K_p(t alpha,t beta)/t<=alpha log(p)/(p+1)^2`.  Dominated convergence proves `(14)`.
Equation `(16)` is the elementary Laplace integral, `(17)` is denominator clearing, and `(18)` is
the existing unconditional CCM colligation identity.  No zero-location hypothesis enters.

## Hostile audit and no-go closure

1. **Moving the source weight is false.**  The naive feature with weight `p^(-a)` has diagonal
   comparable to `p^(-2a)` and is not all-prime Hilbertian for `a<=1/2`.  The repair must retain a
   fixed critical damping independent of the observation aperture.
2. **The fixed damping is not imposed.**  `q_p/(1+q_p)=1/(p+1)` is the coefficient obtained by
   differentiating the actual local Möbius Schur factor in valuation depth along `z=ae`.
3. **No finite reporter collapse.**  Every finite real-aperture packet remains full rank by the
   weighted Vandermonde theorem, in agreement with the transverse hypertranscendence barrier.
4. **No RH claim.**  Equations `(10)`--`(12)` calibrate the source input only.  The open theorem is
   still a source-defined nonexpansive map from this continuous marked RKHS to the physical Xi
   boundary graph.
5. **Finite-packet contractions are coordinate theatre.**  The weighted Vandermonde sampling
   matrix is invertible, so for every finite Hermitian response matrix `X`, its pullback
   `M^* X M` is positive semidefinite exactly when `X` is.  This is the positive survivor of the
   finite-source-map no-go: the true aperture coordinates transport the complete sign/inertia
   obstruction without changing it.  Therefore a finite packetwise factorization cannot provide
   the missing RH positivity; the required source-to-Xi map must be globally aperture-coherent and
   genuinely non-invertible at the infinite completed level.

## Exact depth-projection theorem and dyadic Loewner refinement

The required infinite non-invertibility is not merely an abstract condition.  It is already
present canonically in the actual aperture kernel.  Put `L_p=log p`, `c_p=1/(p+1)`, and for
`alpha>0` define the continuous-depth feature

```text
f_(p,alpha)(x)=c_p alpha L_p exp(-alpha L_p x),  x>=0.    (19)
```

For `h>0`, let `P_h` be orthogonal projection in `L^2(0,infinity)` onto functions constant on the
depth bins `[e h,(e+1)h)`, `e>=0`.  The bin integral of `(19)` is

```text
integral_[eh,(e+1)h) f_(p,alpha)
 =c_p(1-exp(-h alpha L_p))exp(-e h alpha L_p).            (20)
```

Since the normalized indicator of a bin has squared norm one, `(20)` gives the exact identity

```text
<P_h f_(p,alpha),P_h f_(p,beta)>
 =K_p(h alpha,h beta)/h.                                 (21)
```

The unprojected Gram is

```text
<f_(p,alpha),f_(p,beta)>
 =c_p^2 L_p alpha beta/(alpha+beta).                      (22)
```

Consequently, for every finite aperture packet, in Loewner order,

```text
(K_p(h alpha_i,h alpha_j)/h)_(i,j)
 <=(c_p^2 L_p alpha_i alpha_j/(alpha_i+alpha_j))_(i,j),  (23)
```

and the difference is the Gram of the discarded within-bin fluctuations `(I-P_h)f`.  Summing over
primes is legitimate because the diagonal of `(22)` is
`alpha log(p)/(2(p+1)^2)`.  Thus the complete true-aperture metric is the direct-sum conditional
expectation of the Cauchy tangent Hilbert space, and `(23)` remains true after the all-prime sum.

The refinement law is stronger.  Since the dyadic partition refines the `h` partition,
`P_h L^2` is a closed subspace of `P_(h/2)L^2`.  If

```text
r_alpha=exp(-(h/2)alpha L_p),
```

then direct denominator clearing gives the exact positive innovation kernel

```text
K_p((h/2)alpha,(h/2)beta)/(h/2)
  -K_p(h alpha,h beta)/h
 =c_p^2/h *
   (1-r_alpha)^2(1-r_beta)^2/(1-(r_alpha r_beta)^2).      (24)
```

The right side is itself a Szego Gram, with depth features
`c_p(1-r_alpha)^2(r_alpha^2)^e/sqrt(h)`.  Therefore the normalized true-aperture
Grams increase in Loewner order under every dyadic refinement and converge to the Cauchy tangent
Gram.  This is the globally coherent, genuinely non-invertible Hilbert map which finite aperture
coordinates could not reveal: finite sampling is invertible, but valuation-depth binning is an
orthogonal projection with an infinite within-bin kernel.

The same identity exposes the first source-specific nonlinear term.  Put
`C_M,3=sum_p log(p)^3/(p+1)^2`.  Expanding the hyperbolic-sine form of `(3)` gives

```text
K(h alpha,h beta)
 =h C_M alpha beta/(alpha+beta)
  -h^3 C_M,3 alpha^2 beta^2/(12(alpha+beta))+o(h^3).     (25)
```

There is no quadratic term.  The first departure from the universal Cauchy tangent is a negative
positive-semidefinite cubic curvature.  The superficial comparison with the Xi three-node theorem
does **not** survive audit: Taylor order three in `h` and exterior detector degree three are
different filtrations.  More decisively, on a positive finite packet the curvature kernel

```text
H_3(alpha,beta)=alpha^2 beta^2/(alpha+beta)
```

is exactly `D H_1 D`, where `H_1(alpha,beta)=alpha beta/(alpha+beta)` and
`D=diag(alpha_i)` is invertible.  Hence `H_3` and `H_1` have identical rank and inertia.  The cubic
curvature cannot be the missing finite Xi amplifier.  The positive survivor is sharper: the
genuinely new structure lies in the infinite within-bin martingale decomposition `(24)`, while its
leading finite aperture-coordinate shadow is sign-neutral.

Lean formalizes the stronger all-prime form of `(24)`: the unscaled innovation
`2K((h/2)alpha,(h/2)beta)-K(h alpha,h beta)` is the inner product of an explicit vector in
`ell^2(Nat.Primes x Nat)`, and every finite all-prime innovation matrix is positive semidefinite.
It then identifies this Gram with the difference of successive normalized mesh matrices and proves
the Loewner refinement theorem unconditionally.  It also proves primewise that this innovation
divided by `h^3` tends to the exact positive coefficient
`c_p^2 (alpha L_p/2)^2 (beta L_p/2)^2 / ((alpha+beta)L_p)`.
The finite curvature congruence and its positive-semidefinite equivalence are formalized as well.

## Relation to the signed-Jordan/response frontier

The two-node Xi response theorem shows that every negative Jordan direction is invisible through
order two and that an off-line orbit first appears in a three-node correlation.  The metric above
supplies a positive source correlation system at every real aperture and at every finite order,
with a summable all-prime realization and the correct infinitesimal scale.  Therefore the remaining
three-node problem is no longer to invent an aperture metric or to isolate a separately truncated
Jordan mass.  It is exactly to prove that the Xi three-node response is a contractive image of
this source correlation system.  Such a contraction would forbid the negative atomic cubic and
therefore close the response route to RH.

## External novelty boundary

McCarthy--Shalit characterize complete-Pick Hilbert spaces of Dirichlet series and exhibit general
prime-coordinate maps `s |-> (b_p p^(-s))` with square-summable weights.  Seip and related work
locate the classical `Re s=1/2` Hilbert--Dirichlet threshold.  Those results make the abstract
prime-weighted RKHS and the Szegő calculation parent theory.  The candidate-new content here is the
source-specific conjunction that the **actual critical Möbius Schur multiplier**, sampled on the
valuation ray `z=ae`, produces `(2)`; that this repairs the false moving-weight aperture at every
`a>0`; and that its all-prime energy has the exact source slope `(10)` and four-unit normalization
`(12)`.  No matching statement was found in the live corpus or the targeted primary-source search.
The later targeted search for `(21)`--`(24)` likewise returned only generic Szego/Bergman
orthogonal-projection parent theory, not exponential depth-bin projection of the fixed critical
Möbius multiplier, its prime direct sum, or the displayed dyadic innovation law.

Primary comparisons:

- J. E. McCarthy and O. M. Shalit, *Spaces of Dirichlet series with the complete Pick property*,
  https://arxiv.org/abs/1507.04162.
- K. Seip, *Zeros of functions in Hilbert spaces of Dirichlet series*,
  https://arxiv.org/abs/1206.2815.

## Gates

- [x] integral-aperture gap and naive moving-weight no-go identified
- [x] actual continuous Möbius ray sample and forward difference proved
- [x] exact local kernel, normalized metric, and finite-rank theorem proved
- [x] uniform all-prime summability proved
- [x] infinitesimal source slope and four-unit normalization proved on paper
- [x] full two-aperture Cauchy tangent law and CCM germ interface proved on paper
- [x] exact continuous-depth projection and dyadic Loewner refinement proved on paper
- [x] vanishing quadratic term and first cubic source curvature proved on paper
- [x] internal corpus novelty audit
- [ ] external specialist novelty audit
- [x] Lean formalization of `(1)`--`(6)`, `(10)`, `(13)`--`(15)`, and `(17)`--`(18)`
- [ ] Lean formalization of the continuous `L^2` projection identities `(19)`--`(23)`
- [x] Lean formalization of the exact local and all-prime dyadic Loewner refinement `(24)`
- [x] Lean formalization of the primewise cubic innovation coefficient underlying `(25)`
- [x] finite curvature congruence no-go and rank/inertia survivor formalized
- [ ] Lean formalization of the all-prime cubic curvature and `C_M,3` limit `(25)`
- [ ] source-to-Xi Pick contraction
- [ ] RH

## Log

- 2026-07-19 -- Found that the previous true-aperture metric was only integral and that its naive
  continuous substitution hits the critical `a=1/2` summability wall.  Sampling the actual local
  Möbius Schur factor on `z=ae` keeps the critical source damping fixed, yields an all-prime
  summable continuous Szegő metric for every `a>0`, and has a finite nonzero four-unit-normalizable
  aperture germ.
- 2026-07-19 -- Identified the normalized mesh kernel as the depth-bin projection of the continuous
  Cauchy exponential Gram.  Lean formalizes the exact dyadic innovation as a local and all-prime
  `ell^2` Gram and proves unconditional Loewner monotonicity under mesh halving.  The first
  nonlinear source correction is cubic, with the quadratic term forced to vanish.
- 2026-07-19 -- Hostile cubic audit retired the tempting identification of aperture Taylor order
  with Xi exterior detector degree.  The leading curvature kernel is an invertible diagonal
  congruence of the Cauchy tangent on every positive finite packet, so it preserves rank and
  inertia.  Lean formalizes this no-go and its positive infinite-martingale survivor.
