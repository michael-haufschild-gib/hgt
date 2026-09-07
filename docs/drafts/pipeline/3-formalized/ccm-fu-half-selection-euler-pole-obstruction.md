# CCM-FU: literal half-selection Euler product and pole obstruction

- **Stage:** 3-formalized
- **Type:** unconditional source identities, holomorphic correction and no-continuation theorem
- **Source:** [PE5 investigation](../5-failed/ccm-fu-bernoulli-prime-energy.md)
- **Boundary:** the [separate discrete transfer and growth certificate](ccm-fu-half-selection-growth-obstruction.md) closes PE5's all-scale refutation. PE4, SD1 and RH remain open.

## Exact arithmetic source

Let `a(n)=mu(n)/2^omega(n)` and `b(n)=log(n)-tau(n)+2 gamma` off zero. The arithmetic function `halfSelectionMoebiusAF` has exactly the real coefficients `halfSelectionMoebiusWeight` used by the existing Bernoulli mean. It is multiplicative, has coefficient1 at1 and coefficient-1/2 at each prime, and vanishes at all higher prime powers. Its L-series converges absolutely on `Re(s)>1` and has Euler product `prod_p(1-p^(-s)/2)`.

The arithmetic function `halfSelectionDivisorConvolution` is literally `g=a*b`, with the existing divisor increment lifted to complex coefficients. It satisfies

`sum_(n<=N)g(n)=sum_(d<=N)a(d)D(floor(N/d))`,
`H(M)=sum_(k<M)(sqrt(k+1)-sqrt(k))*sum_(n<=k)g(n)`.

The real mean is cast into complex numbers in the second identity; no source is changed. The L-series of g converges absolutely on `Re(s)>3/2` and equals `L(a,s)B(s)`, where B is the [already verified divisor-source continuation](ccm-fu-divisor-source-harmonic-boundary.md).

## Correction product

The local identity `(1-X/2)^2=(1-X)*(1+X^2/(4(1-X)))` gives

`R(s)=prod_p(1+p^(-2s)/(4(1-p^(-s))))=L(a,s)^2*zeta(s)`

on `Re(s)>1`, with an exact convergent-product certificate. For every positive sigma and `Re(s)>=sigma`, each correction factor minus1 has norm at most

`p^(-2 sigma)/(4*(1-2^(-sigma)))`.

For sigma>1/2 this is summable over primes. Locally uniform product limits prove that R is holomorphic on all `Re(s)>1/2`. At1 the literal local factor is `1+1/(4p(p-1))`. Every finite product is real and at least1; so `Im R(1)=0` and `Re R(1)>=1`. In particular R(1) is nonzero.

## Closed analytic obstruction

`not_exists_analytic_halfSelectionDivisor_extension` proves, with no external hypothesis, that there is no holomorphic F on `Re(s)>1/2` agreeing with the actual `LSeries g` on `Re(s)>2`.

Let Z be the existing entire continuation of `(s-1)zeta(s)`, with Z(1)=1. Such an F would satisfy

`F(s)^2 Z(s)=(s-1)B(s)^2 R(s)`

first on `Re(s)>2` by exact source multiplication, then on the entire connected strict half-plane by analytic uniqueness. Evaluation at1 gives F(1)=0. Differentiation makes the left derivative zero and the right derivative `B(1)^2 R(1)`, which is nonzero because `B(1)>=1/30` and `R(1)>=1`. This contradiction uses neither a Tauberian premise nor information about zeta zeros.

The [separate transfer certificate](ccm-fu-half-selection-growth-obstruction.md) formalizes two discrete Abel summations and the first- and second-difference Dirichlet bounds. It applies this no-continuation theorem to prove unbounded normalized magnitude of H on every tail and to refute every fixed averaged-energy budget.

## Lean audit

- `MobiusHalfSelectionEulerProduct.lean`:11 public theorems; literal coefficients, multiplicativity, norm bound, local factors, absolute summability and exact product identity.
- `MobiusHalfSelectionEulerCorrection.lean`:9 public theorems; uniform prime-square majorant, local and global holomorphy, locally uniform convergence and the real positive value at1.
- `MobiusHalfSelectionPoleObstruction.lean`:6 public theorems; exact source convolution, absolute L-series product, finite summatory/weighted-mean landing and no holomorphic extension.

All three leaves passed scratch checks and `lake env lean <file> -o <exact olean>`. All26 new public theorems were axiom-audited once: only `propext`, `Classical.choice` and `Quot.sound`. No added axiom, numerical certificate or unproved source premise enters these results. Imports are wired once into `RHTower.lean`; no umbrella or dependency build was run.

Global lint was run once. Its sole error concerns the concurrent, unwired `HTGeometry.PolynomialODEOddCompactProductC` module; none of these three leaves is flagged.
