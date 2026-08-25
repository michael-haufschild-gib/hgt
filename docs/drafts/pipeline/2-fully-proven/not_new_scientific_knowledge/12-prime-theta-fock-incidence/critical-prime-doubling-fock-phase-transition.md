# Critical prime incidence has a quartic doubling-Fock phase transition

- **ID:** `critical-prime-doubling-fock-phase-transition`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / POSITIVE HILBERT CARRIER / BRIDGE
- **Scientific status:** `[PROVED] [BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Statement:** In the polynomial doubling-Fock space with potential
  `phi_m(z)=(1+|z|^2)^(m/2)`, the normalized critical-prime evaluation operator is bounded exactly
  for `m>=4` and compact exactly for `m>4`.  The quartic carrier has intrinsic scale `1/log N` at
  prime cutoff `N` and is bounded but essentially noncompact.

## Carrier family

Fix `m>2` and put

```text
phi_m(z)=(1+|z|^2)^(m/2).                                  (1)
```

Let

```text
F_m^2={f entire:int_C |f(z)|^2 exp(-2phi_m(z)) dA(z)<infinity}.  (2)
```

The Riesz measure `Delta phi_m dA` is doubling and

```text
Delta phi_m(z) asymp (1+|z|)^(m-2).                        (3)
```

Let `rho_m(z)` be the standard doubling-Fock scale, characterized up to fixed constants by

```text
int_(D(z,rho_m(z))) Delta phi_m dA=1.
```

Equation `(3)` gives

```text
rho_m(z) asymp (1+|z|)^(1-m/2).                            (4)
```

Write `K_m` for the reproducing kernel.  The diagonal kernel estimate for doubling-Fock spaces is

```text
K_m(z,z) asymp exp(2phi_m(z))/rho_m(z)^2.                  (5)
```

## Critical prime incidence

For every prime `p`, put

```text
lambda_p=log p,
w_p=(log p)^2/p.                                           (6)
```

Define the normalized prime evaluation operator

```text
(S_m f)_p=sqrt(w_p) f(lambda_p)/sqrt(K_m(lambda_p,lambda_p)).  (7)
```

The theorem is

```text
S_m:F_m^2 -> ell^2(P) is bounded  iff m>=4,
S_m:F_m^2 -> ell^2(P) is compact  iff m>4.                 (8)
```

In particular, `m=4` is the exact bounded/noncompact boundary.

## Reduction to a doubling-Fock Carleson measure `[SEARCH]`

By `(5)`, the square of `(7)` is comparable to the Fock-Carleson embedding associated with the
positive discrete measure

```text
mu_m=sum_p w_p rho_m(lambda_p)^2 delta_(lambda_p):

sum_p w_p |f(lambda_p)|^2/K_m(lambda_p,lambda_p)
 asymp int_C |f(z)|^2 exp(-2phi_m(z)) dmu_m(z).             (9)
```

For a fixed sufficiently small `a>0`, the classical doubling-Fock Carleson theorem says that this
embedding is bounded exactly when

```text
sup_z mu_m(D(z,a rho_m(z)))/rho_m(z)^2<infinity,            (10)
```

and compact exactly when the quotient in `(10)` tends to zero as `|z|->infinity`.

When `D(z,a rho_m(z))` meets the positive real tail, every point in the disk has comparable
`rho_m` scale.  Hence the quotient in `(10)` is comparable to

```text
sum_(|log p-x|<=C rho_m(x)) w_p                            (11)
```

for a positive real `x` comparable to `|z|`.  Disks away from that tail contain no support of
`mu_m`, and bounded regions contribute only a finite constant.

## Prime mass computation `[PROVED]`

The logarithmic-window prime-mass law proved in
`critical-prime-sampling-microlocalization-law.md` is

```text
sum_(|log p-x|<=r) (log p)^2/p = 2xr+o(1)                 (12)
```

uniformly for `0<r<=1`.  Combining `(4)`, `(11)`, and `(12)` gives

```text
mu_m(D(z,a rho_m(z)))/rho_m(z)^2
 asymp x rho_m(x)
 asymp x^(2-m/2)                                           (13)
```

along the positive real tail.  More precisely, fixed changes in the disk radius change only the
positive multiplicative constant in `(13)`.

Therefore:

```text
m<4  => x^(2-m/2)->infinity,
m=4  => x rho_4(x) stays between positive constants,
m>4  => x^(2-m/2)->0.                                     (14)
```

The Carleson and vanishing-Carleson criteria `(10)` now prove `(8)`.

## Positive Hilbert--Polya law

This theorem constructs, without RH or divisor input, entire-function Hilbert spaces in which the
full critical prime incidence is mathematically well posed.

1. **Subquartic carriers are too coarse.** Their normalized kernels remain coherent across too much
   critical prime mass, so prime evaluation is unbounded.
2. **The quartic carrier is critical.** Its intrinsic radius at `x=log N` is

   ```text
   rho_4(log N) asymp 1/log N,                             (15)
   ```

   and prime incidence is bounded but not compact.
3. **Superquartic carriers are confining.** They resolve a scale strictly smaller than `1/log N`,
   and the normalized prime incidence becomes compact.

Thus the `1/log N` boundary is not only a necessary loss-of-coherence scale.  It is the exact
bounded/noncompact threshold in a natural analytic RKHS family.  A direct Hilbert--Polya
architecture may use a quartic carrier when an essential, noncompact arithmetic channel is wanted,
or a superquartic carrier when determinant-class regularization requires compact prime incidence.

The theorem does not identify the spectrum of a self-adjoint operator with the zeta-zero heights.
It supplies a source-defined point-evaluable Hilbert carrier for the prime side.  The remaining
load-bearing theorem is a distinguished archimedean/divisor incidence whose characteristic entire
function is `Xi`.

## Attacks and boundaries

1. **Normalization.** The operator uses normalized evaluation vectors.  Zero-free real entire
   gauges change `K_m(lambda,lambda)` and `f(lambda)` compatibly, so the criterion is intrinsic.
2. **Critical weights.** Replacing `w_p` changes the exponent in `(13)`.  The quartic threshold is
   tied to the explicit-formula weight `(log p)^2/p`.
3. **Complex-plane disks.** The measure is supported on the positive real axis.  The full supremum
   in `(10)` reduces to the real-tail estimate because an adapted disk either misses the support or
   has center and scale comparable to a real-tail disk.
4. **Compactness.** Boundedness at `m=4` does not imply compactness: the normalized local mass stays
   uniformly positive along a sequence tending to infinity.
5. **No spectral claim.** Fock-Carleson compactness is compactness of the source incidence map, not
   compact resolvent for a Hilbert--Polya Hamiltonian.
6. **No finite-prime shortcut.** Every finite cutoff is finite rank.  The theorem classifies the
   cofinal all-prime operator and therefore cannot be replaced by finite positivity.

## Scientific verdict

`[BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE]`.  The boundedness and compactness criteria are standard
doubling-Fock Carleson theory, and the only arithmetic input is the classical PNT window asymptotic.
The exact quartic transition is a useful RH-facing specialization, but it is a direct application of
the parent machinery rather than a new scientific mechanism.

Primary parent sources:

- R. Oliver and D. Pascuas, *Toeplitz operators on doubling Fock spaces*, Journal of Mathematical
  Analysis and Applications 435 (2016), 1140--1170, `https://arxiv.org/abs/1508.02887`;
- N. Marco, X. Massaneda, and J. Ortega-Cerda, *Interpolating and sampling sequences for entire
  functions*, Geometric and Functional Analysis 13 (2003), 862--914;
- J. Marzo and J. Ortega-Cerda, *Pointwise estimates for the Bergman kernel of the weighted Fock
  space*, Journal of Geometric Analysis 19 (2009), 890--910;
- the classical prime number theorem with a zero-free-region error term.

## Lean status

The Lean tree now proves the literal critical-prime operator endpoints and constructs the normalized
sampler from finite normalized-kernel Gram-row bounds in
`formal/GaloisForLFunctions/RHTower/CriticalPrimeKernelSchurSampling.lean`.  Vanishing tail Gram
rows imply compactness, while unit normalized kernels force the sampler outside Hilbert--Schmidt
class and its incidence outside trace class.  It also proves the full scalar form of `(13)--(14)` in
`formal/GaloisForLFunctions/RHTower/CriticalPrimeFockWindowPhaseTransition.lean`: at the exact
polynomial Fock radius the prime-log mass diverges for `2<m<4`, converges to `2` at `m=4`, and
converges to zero for `m>4`.
`formal/GaloisForLFunctions/RHTower/PolynomialMomentFockNorm.lean` now proves that every coefficient
carrier vector has integrable literal plane density and the exact norm identity
`int_C |F(z)|^2 exp(-2 phi_m(|z|)) dA=||f||^2`.  Concrete normalized-kernel/Carleson estimates and
their prime-log specialization remain open.  The scalar phase transition and exact carrier do not
yet formalize the substantive operator theorem, so the card remains at Stage 2.

`PolynomialMomentFockKernelBound.lean` additionally sums the annular moment lower bounds into an
explicit diagonal-kernel and point-evaluation growth envelope.  Off-diagonal localization and the
discrete Carleson estimate remain the operator-producing gap.

`formal/GaloisForLFunctions/RHTower/MomentFockKernel.lean` and
`formal/GaloisForLFunctions/RHTower/PolynomialMomentFock.lean` now construct the exact radial
monomial moments of `exp(-2(1+r^2)^(m/2))`, prove those moments finite and strictly positive, prove
all point-kernel coefficient sequences square-summable, construct bounded evaluations and unit
normalized prime-log kernels, and provide the distinguished constant vector.
`MomentFockEntire.lean` proves every carrier vector defines an entire function and that its entire
power-series value is exactly the bounded RKHS evaluation. `PolynomialMomentFockNorm.lean` proves
weighted-square integrability and the exact complex-plane norm isometry.  Remaining analytic core
is the concrete normalized-kernel/Carleson estimate needed for boundedness and compactness.

`PolynomialFockPotentialGeometry.lean` now formalizes exact radial slope, curvature, planar
Laplacian density, positivity, the uniform comparison

```text
2m(1+r^2)^(m/2-1) <= Delta phi_m(r) <= m^2(1+r^2)^(m/2-1),
```

and induced two-sided reciprocal-square-root adapted-radius bounds for `m>=2`.  Its targeted leaf
build and axiom audit passed with only `propext`, `Classical.choice`, and `Quot.sound`.
Off-diagonal normalized-kernel localization and the concrete discrete Carleson estimate remain the
operator-producing gap, so this card remains at Stage 2.

## Gates

- [x] polynomial potential and adapted scale computed
- [x] normalized evaluation reduced to a discrete Fock-Carleson measure
- [x] local critical-prime mass evaluated at the adapted scale
- [x] boundedness threshold `m=4` proved
- [x] compactness threshold `m>4` proved
- [x] RH-free source construction and exact limitations stated
- [x] parent-theory novelty claim rejected
- [ ] complete unconditional Lean formalization
