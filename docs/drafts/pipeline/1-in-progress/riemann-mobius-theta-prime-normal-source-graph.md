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
- [ ] Prove the `L2` prime-normal extraction theorem by Tannery domination.
- [ ] Define complete physical source channels and prove finite telescoping plus codiagonal limit.
- [ ] Prove the Fourier--Laplace formula (R-PN.6) on its honest domain.
- [ ] Formalize reflected cocycle (R-PN.7)--(R-PN.8).
- [ ] Package the single-valued closed graph and zero multivalued fibre.
- [ ] Prove zero-normal analytic-order retention and projective multiplier extraction.
- [ ] Attack Conjecture R-PN-Ward directly; do not replace it by its RH-equivalent consumer.
