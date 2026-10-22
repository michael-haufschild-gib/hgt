# Möbius--theta prime-normal singular source graph

- **ID:** R-MT-prime-normal-graph
- **Stage:** 1-in-progress
- **Type:** THEOREM (physical-source upgrade) with open Ward conjecture
- **Source:** `rh-current-frontier-map.md` · Route R
- **Statement:** High-exponent Möbius--theta rungs possess a canonical, target-free singular
  residual flag which recovers every arithmetic logarithmic translate before transform.  Its
  reflected Fourier--Laplace normal cocycle is exactly the unsquared modular displacement.  This
  constructs the closed single-valued source graph required by oriented admission and reduces
  Route R to one explicit graph-energy/Ward intertwining estimate.

## Why this is the frontier

The physical landing theorem constructs

```text
Psi_m(x) = sum_(n>=1) mu(n)n^(-m/2) Phi(x-m log n),
FL(Psi_m)(w) = zeta(m s(w))^(-1) XiC(w),
s(w)=1/2+iw.
```

Ordinary `L2` and `ell^1` completion sees only `Psi_m -> Phi`; it erases every arithmetic label.
This is exactly the previously proved cofinal source-collapse obstruction.  Product-topology
retention is not a repair: if a closed relation has all finite output projections surjective, its
multivalued fibre is the whole product and the relation transports no constraint.

The needed object must therefore be a single-valued closed graph over a stronger source topology.
The construction below is forced by the asymptotics of the already physical rungs.  It contains
no `Xi`, spectral point, zero, or divisor datum.

## Internal novelty audit

Corpus search finds the physical Möbius--theta landing, scalar high-exponent shell peeling, the
countable scalar prime-normal reader, its prime-two reflection orientation, co-moving diffuse
Möbius graph laws, and the general product-topology no-go.  The reflected exponential cocycle is
therefore not new as a scalar identity.  What is absent is the residual operator below:
lower-label subtraction, exponential half-density renormalization, and logarithmic recentering
applied jointly to the physical full-theta source.  No existing declaration recovers
`mu(p) Phi` as an `L2` limit from those physical rungs or proves that the known scalar orientation
is the transform shadow of this target-free normal flag.

## Construction

Let `H=L2(R,C)`, let `U_a Phi(x)=Phi(x-a)`, and let `Phi` be the canonical theta-cusp source.
For an integer label `p>=2`, remove every smaller label before taking the high-exponent limit:

```text
Psi_[p,m] = sum_(n>=p) mu(n)n^(-m/2) U_(m log n) Phi.
```

Define the `p`-normal residual reader

```text
N_[p,m]
  = p^(m/2) U_(-m log p) Psi_[p,m].                         (R-PN.1)
```

Here `U_(-m log p)f(x)=f(x+m log p)`, so the `p`-label is returned to the source origin.  Directly,

```text
N_[p,m]
 = mu(p) Phi
   + sum_(n>p) mu(n)(p/n)^(m/2) U_(m log(n/p)) Phi.          (R-PN.2)
```

The reader is singular in the ordinary source norm: its gain is `p^(m/2)` and is unbounded as
`m -> infinity`.  This is required, not a defect; every bounded label-blind reader was already
classified as codiagonal-only.

## Prime-normal extraction theorem `[PROVED HERE]`

For every integer `p>=2`,

```text
N_[p,m] -> mu(p) Phi in H as m -> infinity.                  (R-PN.3)
```

More generally, the same statement holds for every bounded arithmetic coefficient sequence
`|a(n)|<=1`, with limit `a(p)Phi`.

### Proof

Translation is unitary on `H`.  Therefore (R-PN.2) gives

```text
||N_[p,m]-mu(p)Phi||_2
  <= ||Phi||_2 sum_(n>p) (p/n)^(m/2).                         (R-PN.4)
```

For `m>=3`, the summands are dominated by `(p/n)^(3/2)`, whose tail is summable.  For each fixed
`n>p`, `(p/n)^(m/2)->0`.  Tannery's theorem sends the sum in (R-PN.4) to zero, proving (R-PN.3).
No cancellation, zero information, or target transform is used.

Consequently the full arithmetic label sequence is retained by the single-valued map

```text
N(Psi) = (lim_m N_[p,m])_(p>=2) = (mu(p)Phi)_(p>=2).          (R-PN.5)
```

Equip the algebraic domain of source-rung families with the initial source seminorms together with
the coordinate graph seminorms
`Psi |-> sup_(m>=M) ||N_[p,m]||_2` for every fixed `(p,M)`, and retain the normal limits as part of
the completed source point.  On this stronger source domain the reader is single-valued by
definition of a graph completion, and the actual Möbius--theta point belongs to it by (R-PN.3).
Its projection to ordinary `L2` need not remain injective: that loss is exactly the already proved
cofinal-collapse obstruction.  No claim of closability in the ordinary source norm is made.
This is the allowed graph-over-stronger-domain alternative in the oriented-admission theorem,
not a closed multivalued relation in the product output topology.

## Transform and reflected normal cocycle `[PROVED HERE]`

On every honest common Fourier--Laplace domain, translation and (R-PN.1) give

```text
FL(N_[p,m])(w)
 = XiC(w) sum_(n>=p) mu(n)(p/n)^(m s(w)).                    (R-PN.6)
```

For `Re s(w)>0`, the right side tends to `mu(p)XiC(w)` once `m` is large enough for absolute
convergence.  Thus the prime-normal reader commutes with landing away from the divisor, and its
analytic continuation has the same common Xi zero fibre.

Before recentering, the isolated `p`-normal amplitudes in the two reflected orientations are

```text
A+_[p,m](s)=mu(p)p^(-m s),
A-_[p,m](s)=mu(p)p^(-m(1-s)).
```

Whenever `mu(p) != 0`, their unsquared modulus cocycle is

```text
|A-_[p,m](s)| / |A+_[p,m](s)|
  = p^(m(2 Re(s)-1)).                                         (R-PN.7)
```

Writing `delta(s)=2 Re(s)-1` and `t=m log p`, this is `exp(delta(s)t)`.  Exchanging orientations
gives `exp(-delta(s)t)`, hence the reflection-odd graph profile is exactly

```text
R_delta(t)=exp(delta t)-exp(-delta t).                         (R-PN.8)
```

This is the profile appearing in the Hellinger--Hodge finite-energy classification and agrees
with the earlier scalar reflection-tail law.  New content here is its derivation as the transform
shadow of a target-free physical source normal flag, not the exponential identity by itself.

## Zero-normal jet consequence `[PROVED HERE]`

Let `w0` be a zero of `XiC` of analytic order `r`.  Every physical complete channel vanishes at
`w0`.  Since its transform is `M_j(s(w))XiC(w)` and the head multiplier is a holomorphic unit on
the strict-right domain, its first nonzero spectral normal jet is

```text
d^r FL(C_K(0))(w0) = M_0(s(w0)) d^r XiC(w0),                  (R-PN.9)
```

and similarly for every unit channel.  Projectivizing the first nonzero normal jet cancels the
common Xi derivative and leaves the complete source multiplier vector.  Prime-normal extraction
of that projective vector yields (R-PN.7).  Thus multiplicity, label, and unsquared orientation
survive in one source-derived normal graph.

## Exact remaining conjecture

### Conjecture R-PN-Ward (source-graph Hellinger admission)

The prime-normal graph transport induced by the physical Möbius--theta source and the exact
Calderon--Witt Green primitive intertwines the reflected normal cocycle with the source-forced
Hellinger tail, and the transported reflection-odd profile has finite positive energy:

```text
integral_0^infinity (1-exp(-t))
  |exp(delta_rho t)-exp(-delta_rho t)|^2 dt < infinity         (R-PN.10)
```

for every nontrivial Xi zero `rho`, with `delta_rho=2 Re(rho)-1`.

By the Hellinger--Hodge reflection theorem, (R-PN.10) forces `delta_rho=0`.  Equivalently it gives
the source-derived four-unit Ward boundary lift and hence RH.  This is not marked proved.  It is
the remaining scientific theorem after physical landing and singular graph construction.

## Hostile audit

1. **Not scalar peeling.** (R-PN.1) acts on physical translated theta sources in `L2`; (R-PN.3)
   is a norm limit before transform.
2. **Not product-topology theatre.** Outputs are retained in the stronger graph-domain point;
   finite projections are not declared freely surjective.  No false closability claim is made
   after forgetting the graph coordinates and projecting to ordinary `L2`.
3. **Not a bounded-reader shortcut.** Reader gain `p^(m/2)` is explicitly unbounded.  This is the
   singularity forced by prior label-blindness and source-collapse theorems.
4. **Not target-fed.** Definitions use only `mu`, integer order, logarithmic translation, and
   `Phi`.  `XiC` first appears after applying the already proved source transform.
5. **Not an RH proof by renaming.** Finite Hellinger energy (R-PN.10) is still unproved and is
   explicitly equivalent to the missing Ward sign.  Physical `L2` membership alone does not
   imply it; claiming otherwise would be representation theatre.
6. **Actual new knowledge.** The proven advance is exact construction of the singular,
   source-pointed physical normal graph and identification of the known scalar modular cocycle as
   its transform shadow.  It removes the physical-source/normal-reader welding unknown.  Only
   graph-energy admission remains.

## Lean plan

- [ ] Define direct power-indexed physical rungs and prove equality with the `mPart` rungs.
- [x] Prove the `L2` prime-normal extraction theorem by Tannery domination:
      `tendsto_mobiusThetaPrimeNormalResidual` and its prime specialization
      `tendsto_mobiusThetaPrimeNormalResidual_of_prime` in
      `MobiusThetaPhysicalSourceToXiLanding.lean`.
- [x] Define complete physical source channels and prove finite telescoping plus codiagonal limit:
      `sum_range_mobiusThetaCompletePhysicalChannel` and
      `tendsto_sum_range_mobiusThetaCompletePhysicalChannel`.  The quantitative refinement
      `summable_norm_mobiusThetaCompletePhysicalChannel_three` proves the codiagonal is actually
      `ell^1(L2)`, using an explicit geometric prime-normal envelope.
- [x] Prove the Fourier--Laplace formula (R-PN.6) on its honest domain, including exact
      integral--series interchange for every coefficient `n >= p`.
- [x] Formalize reflected cocycle (R-PN.7)--(R-PN.8).
- [ ] Package the single-valued closed graph and zero multivalued fibre.
- [ ] Prove zero-normal analytic-order retention and projective multiplier extraction.
- [ ] Attack Conjecture R-PN-Ward directly; do not replace it by its RH-equivalent consumer.

## 2026-08-02 internal-jet complex normal graph update `[FORMALIZED]`

The source/normal/reflection weld is now proved for every internal Xi jet order, not only for the
zeroth physical vector.  Define the raw translated `p`-head before recentering by

```text
H_[k,p,m](x)
 = mu(p) p^(-m/2)
   (-i(x-m log p))^k Phi(x-m log p).                         (R-PN.11)
```

Direct Fourier--Laplace integration on the honest theta strip gives

```text
FL(H_[k,p,m])(w)
 = L_p(m s(w)) XiC^(k)(w),
L_p(z)=mu(p)p^(-z),  s(w)=1/2+iw.                            (R-PN.12)
```

This is a source theorem: the left side is the integral of (R-PN.11), and `XiC` enters only after
the integral is evaluated.  The singular normal reader is also exact before transform:

```text
p^(m/2) H_[k,p,m](x+m log p)
 = mu(p)(-ix)^k Phi(x).                                      (R-PN.13)
```

For prime `p`, `L_p(ms)` never vanishes and its reflected modulus quotient and odd profile are

```text
|L_p(m(1-s))| / |L_p(ms)| = p^(m(2 Re(s)-1)),                (R-PN.14)

quotient(s)-quotient(1-s)
 = exp(delta m log p)-exp(-delta m log p),
delta=2 Re(s)-1.                                              (R-PN.15)
```

Finally, if `rho` has Xi multiplicity `r`, the adjacent raw-head conormal lands exactly as

```text
(FL(H_[r-1,p,m])(w_rho), FL(H_[r,p,m])(w_rho))
 = (0, L_p(m rho) XiC^(r)(w_rho)),                            (R-PN.16)
```

and the second coordinate is nonzero.  Hence the same target-free source head simultaneously
retains prime label, unsquared reflected orientation, and arbitrary divisor multiplicity.  This
removes the prior logical gap between physical prime-normal extraction and the divisor conormal;
no quotient by `XiC`, target-selected coefficient, or scalar postulate is used.

Lean module:
`RHTower/MobiusThetaInternalJetPrimeNormalComplexGraph.lean`.  The exact declarations are
`mobiusThetaInternalJetRawHeadFourierLaplace_eq`,
`mobiusThetaInternalJetRawHeadNormalReader_eq`,
`mobiusThetaPrimeRawAmplitude_reflectionOddProfile`, and
`mobiusThetaInternalJetRawHeadConormalPair_at_divisor`.

### Updated open core

The source graph itself, its complex Xi landing, its reflection character, and its multiplicity
conormal are no longer open.  Remaining RH-bearing theorem is not another landing formula.  It is
arithmetic admission of this labelled conormal graph into a source-derived Gamma/co-Poisson
sector transverse to the codiagonal kernel, equivalently the R-PN-Ward energy bound (R-PN.10).
The updated Hellinger--Hodge Gaussian countertransport theorem shows why uniform half-density
capacity alone cannot prove this: off-line evaluation can diverge on a uniformly
capacity-bounded reflected family.  Required estimate must therefore use the Möbius/ordinary-prime
incidence retained by (R-PN.11)--(R-PN.16), not regular completion or scalar closure.

## 2026-08-02 complete residual complex landing update `[FORMALIZED]`

The raw head is no longer used as a surrogate for the full source.  For each `j >= 0`, set
`n=p+j` and form the recentered source packet

```text
N_[k,p,m,j](x)
 = p^(m/2) mu(n)n^(-m/2)
   (-i(x-m(log n-log p)))^k Phi(x-m(log n-log p)).            (R-PN.17)
```

The complete residual source is the source-side sum
`N_[k,p,m]=sum_(j>=0) N_[k,p,m,j]`.  On the honest domain
`|Im(w)|<1` and `1/m<Re(s(w))`, absolute integral-norm summability proves the unconditional
interchange

```text
FL(N_[k,p,m])(w)
 = [sum_(n>=p) mu(n)(p/n)^(m s(w))] XiC^(k)(w).              (R-PN.18)
```

This is exactly (R-PN.6) for every internal jet order.  No tail coefficient is dropped, and the
left side is synthesized before either transform evaluation or divisor selection.

Write the bracketed multiplier as `M_[p,m](w)`.  Splitting its first coefficient gives

```text
M_[p,m](w) = mu(p) + sum_(n>p) mu(n)(p/n)^(m s(w)).           (R-PN.19)
```

For every fixed `Re(s(w))>0`, the strict tail tends to zero.  The proof is a complex Tannery
argument with exact norm

```text
|mu(n)(p/n)^(m s(w))| = |mu(n)|(p/n)^(m Re(s(w)))
```

and the summable exponent-independent majorant `(p/n)^(3/2)` once
`m Re(s(w)) >= 3/2`.  Consequently

```text
M_[p,m](w) -> mu(p).                                         (R-PN.20)
```

For prime `p`, `mu(p)=-1`, so (R-PN.20) yields eventual nonvanishing of the *complete* residual
multiplier; this is derived rather than postulated.  If `rho` has Xi multiplicity `r`, then for
all sufficiently large `m` the complete adjacent source pair satisfies

```text
(FL(N_[r-1,p,m])(w_rho), FL(N_[r,p,m])(w_rho))
 = (0, M_[p,m](w_rho) XiC^(r)(w_rho)),                       (R-PN.21)
```

with nonzero second coordinate.  This closes the head-only gap in the previous update: complete
arithmetic retention, prime isolation, and arbitrary multiplicity now coexist in one target-free,
division-free source graph.

Lean declarations in
`RHTower/MobiusThetaInternalJetPrimeNormalComplexGraph.lean`:

- `mobiusThetaInternalJetPrimeNormalResidualFourierLaplace_eq` proves (R-PN.18).
- `tendsto_mobiusThetaPrimeNormalResidualMultiplier` proves (R-PN.20).
- `eventually_mobiusThetaPrimeNormalResidualMultiplier_ne_zero_of_prime` derives complete
  residual nonannihilation.
- `eventually_mobiusThetaInternalJetPrimeNormalResidualConormalPair_at_divisor` proves
  (R-PN.21).

### Frontier after complete residual landing

Fourier--Laplace landing and divisor nonannihilation are closed for the actual infinite residual,
not only its head.  Remaining RH-bearing obstruction is source-derived Gamma/co-Poisson admission:
prove that this labelled complete residual graph lies in an arithmetic sector transverse to the
codiagonal kernel, or equivalently establish R-PN-Ward (R-PN.10).  Uniform capacity, ordinary
closed-graph completion, and ungraded product topology remain ruled out by the updated
Hellinger--Hodge countertransport results.

## 2026-08-02 adaptive all-prime coefficient conservativity update `[FORMALIZED]`

The divisor-independent global schedule `m(p,N)=8pN` upgrades separate-prime residual
nonannihilation to simultaneous countable coefficient conservativity.  At every fixed strip point
with `N Re(s)>=1/2`, each exact strict residual column has `l1` norm at most `1/4`; the proof uses
Bernoulli's inequality and a telescoping quartic majorant, without prime-density input.  Therefore
the exact all-prime spectral codiagonal is the isometric Mobius prime head plus a quarter-contraction:

```text
||A_(N,s)a||_1 >= (3/4)||a||_1.
```

It is injective and has closed range on the completed `l1` prime coefficient space.  The exact
basis-column theorem rules out an abstract triangular recoding: every column is the head plus the
full physical residual already landed in (R-PN.18).

Lean module:
`RHTower/MobiusThetaAdaptivePrimeNormalCodiagonal.lean`.

This closes completed coefficient-space codiagonal instability, not R-PN-Ward.  The operator still
depends on spectral evaluation through `s`; it has not been identified with a divisor-independent
Gamma/co-Poisson source norm or the actual Green resolved range.  Exact remaining arrow is the
coefficient-faithful map from the physical affine-head-plus-interval source completion into the
Gamma/co-Poisson Hellinger/Hodge space, with unsquared orientation and four-unit Gram order retained.
