# The exact CCM radial nonstationary prime sector vanishes cofinally

- **ID:** `ccm-exact-radial-nonstationary-sector-bound`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper), `[BRIDGE]`
- **Scientific status:** `[PROVED HERE] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Parent theories:** Dunster's exterior Liouville--Green expansion with Olver remainders,
  nonstationary phase, and the Hilbert-kernel summation bound
- **Statement:** For the actual constrained prolate source, every off-diagonal radial Gram entry
  with both indices at least two satisfies
  `|G_lambda(j,k)|<=C*d_1/(c*j*k*|j-k|)`. The complete logarithmically weighted sector is therefore
  `O(d_1/c)=o(d_1)`.

## Setup

Let

```text
G_lambda(j,k)
 =lambda integral_1^infinity
   q_lambda(lambda*j*x)q_lambda(lambda*k*x)dx,

c=2*pi*lambda^2,
d_1=1-chi_4(lambda)^2.                                         (1)
```

Here `q_lambda` is the Fourier transform of the constrained `m=0,4` prolate source. The `m=4`
component carries the `d_1` scale; the `m=0` component and its cross term are smaller by
`O(lambda^(-4))` in exterior norm.

## Phase-preserving exterior expansion

Dunster's Section 2 Liouville--Green construction applies uniformly on every unbounded interval
`z>=1+delta`. Fix `delta=1`. For an integer `r>=2`, put

```text
U_(lambda,r)(x)=sqrt(lambda*x)q_lambda(lambda*r*x),   x>=1.
```

Retaining two terms in his expansions `(2.19)`--`(2.22)` gives, after the boundary and
constrained-source normalizations, an exact representation of the form

```text
U_(lambda,r)(x)
 =sqrt(d_1)/r *sum_(epsilon in {+1,-1})
    exp(i*epsilon*c*xi_c(r*x))a_(epsilon,c,r)(x),                 (2)
```

where the amplitudes, including the Olver remainder, satisfy symbol bounds

```text
|a_(epsilon,c,r)(x)|<=C*x^(-1/2),
|d/dx a_(epsilon,c,r)(x)|<=C*x^(-3/2),                            (3)
```

uniformly in `c`, `r>=2`, and `x>=1`. Dunster states the Olver remainder bound on complex
unbounded domains containing `z>=2`, but that additive bound alone does not justify factoring the
remainder through an oscillatory exponential. The exact interaction-picture theorem in
`radial-pswf-interaction-picture-transport.md` supplies the missing phase-preserving statement:
after Dunster's Liouville transform, the two amplitudes satisfy exact first-order transport
equations driven by the short-range potential `psi=O(xi^(-2))`. Their total variation is therefore
`O(c^(-1))`, uniformly on the exterior sector. Restoring the explicit geometric prefactor gives
`(3)`. The phase is

```text
xi_c(z)=integral_1^z sqrt((t^2-sigma_4(c)^2)/(t^2-1))dt,
sigma_4(c)^2=O(c^(-1)).                                         (4)
```

The point of `(2)` is that the remainder remains inside the two oscillatory branches. The
pointwise Bessel-envelope remainder from the pole-uniform Section 3 formula does not retain this
information and is not the correct tool in the sector `z>=2`.

## Exact two-index estimate

For `r>=2`,

```text
d/dx xi_c(r*x)
 =r*sqrt((r^2*x^2-sigma_4(c)^2)/(r^2*x^2-1)).                   (5)
```

As a function of `r>=2`, the right side has derivative bounded above and below by positive
absolute constants, uniformly for `x>=1` and large `c`. Hence

```text
|d/dx[xi_c(j*x)-xi_c(k*x)]|>=c_0*|j-k|,
|d/dx[xi_c(j*x)+xi_c(k*x)]|>=c_0*(j+k).                         (6)
```

Since

```text
G_lambda(j,k)=integral_1^infinity
 U_(lambda,j)(x)U_(lambda,k)(x)dx/x,
```

insert `(2)` for both factors. The product amplitudes, including the `dx/x` measure, obey

```text
|b_(j,k,c)(x)|+|b_(j,k,c)'(x)|
 <=C/(j*k*x^2),                                                 (7)
```

and vanish at infinity. One integration by parts in each of the four phase branches, using
`(6)`--`(7)`, gives the exact bound

```text
|G_lambda(j,k)|
 <=C*d_1/(c*j*k*|j-k|),
 j,k>=2, j!=k.                                                   (8)
```

No fixed-index limit is taken in `(8)`: all constants are uniform in the two arithmetic indices.

## Arithmetic summation

The elementary estimate

```text
sum_(j>=2;j!=k)1/(j*k*|j-k|)
 <=C*(1+log k)/k^2                                              (9)
```

and `(8)` imply

```text
sum_(k>=2)log(k)
 sum_(j>=2;j!=k)|G_lambda(j,k)|

 <=C*d_1/c *sum_(k>=2)log(k)(1+log k)/k^2
 =O(d_1/c)=o(d_1).                                              (10)
```

Thus the complete exact radial prime sector with `j,k>=2`, `j!=k`, vanishes at the leakage scale.

## Positive route consequence

The actual off-diagonal radial charge now has only one unsolved sector:

```text
-2 sum_(k>=2)log(k)G_lambda(1,k).                               (11)
```

The limiting-model theorem `ccm-limiting-radial-first-row-weber-bound.md` proves the required
summable scale for `(11)`. What remains is a hybrid transfer: use Dunster's pole-uniform Bessel
representation for the first factor and his phase-preserving exterior expansion for the second,
uniformly through `k/c`.

## Novelty and significance verdict

The theorem closes a real CCM estimate, but its mathematical content is an application of
Dunster's published Olver expansion and standard one-dimensional nonstationary phase. It does not
clear the parent-theory novelty gate and is classified as a bridge.

## References

- T. M. Dunster, *Asymptotics of Prolate Spheroidal Wave Functions*, arXiv:1601.00699, especially
  Section 2, formulas `(2.19)`--`(2.22)`.
- A. Connes, C. Consani, H. Moscovici, *Zeta Spectral Triples*, arXiv:2511.22755.
- `radial-pswf-interaction-picture-transport.md`, exact ODE transport and Lean formalization.

## Lean decision

**Correction, 2026-07-27.**  The Liouville--Green *coordinate* and the exact interaction-picture
decomposition **are** formalized — `RHTower/RadialPSWFExteriorPhase.lean` and
`RHTower/RadialPSWFInteractionPicture.lean`, the latter stating explicitly that the oscillatory
decomposition is an exact consequence of the differential equation rather than a factored big-`O`.
What is absent is the **remainder estimate** on the interaction potential and any
nonstationary-phase interface.  Formalizing this bridge would still not close the surviving
first-row or true-Weil comparison.  No Lean file is added by this card.

The arithmetic-summation layer `(9)`--`(10)` of this card **is** now formalized, in
`RHTower/RadialGramOffDiagonalDecay.lean` (exact partial-fraction row sum, the row bound
`R K <= 3(1 + log K)/K`, and summability of `sum_K log K (1 + log K)/K^2`), axiom-clean.

## Gates

- [x] phase-preserving exterior expansion selected
- [x] two-index phase derivative separated uniformly
- [x] Olver remainder retained inside oscillatory branches
- [x] exact `j,k>=2` Gram estimate proved
- [x] logarithmically weighted arithmetic sector summed
- [ ] exact first-row hybrid Bessel/Liouville--Green transfer
