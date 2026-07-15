# Complete monotonicity of the Xi Gamma-shape trace is equivalent to RH

- **ID:** `xi-gamma-shape-completely-monotone-rh`
- **Stage:** 2-fully-proven/not_new_scientific_knowledge
- **Type:** THEOREM (paper) / POSITIVE RADIAL RH CRITERION / BRIDGE
- **Scientific status:** `[PROVED HERE] [NOT FORMALIZED] [NOT AN RH PROOF]
  [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Parents:** `xi-global-meixner-shape-landau-rh.md`,
  `xi-reciprocal-translation-prime-seam-norm-law.md`, and Bernstein's theorem for completely
  monotone functions
- **Statement:** The nonnegative Xi prime-seam trace is automatically completely monotone on its
  maximal Gamma--Meixner shape interval.  RH is equivalent to extending this same trace as a
  finite completely monotone function to every positive shape.  Equivalently, its radial Hankel
  kernel extends with nonnegative generator spectrum.  Ordinary Hankel positivity without that
  spectral condition is insufficient.

## Setup

For each rational prime `p`, let

```text
lambda_p=(1/2)log(cosh(2log p))>0,
A_p=sum_rho mult_Xi(rho)
      |orbitwiseNatPrimeSeamCharge(p,rho)|^2/|rho-1/2|^2 >=0,
G_Xi(theta)=sum_p A_p exp(-theta lambda_p).                 (1)
```

Put

```text
a_Xi=sup_q |Im(xiSpectralPoint(q))| in [0,1/2].             (2)
```

The reciprocal-translation norm formula gives

```text
A_p=2(log p)^2/p * (N(log p)-N(0)),                        (3)
lim_(L->infinity) log N(L)/L=2a_Xi.                        (4)
```

Consequently the exact abscissa of convergence of `(1)` is

```text
alpha_G=2a_Xi.                                             (5)
```

For the upper bound, if `theta>2a_Xi`, equation `(3)` is bounded by a constant times
`(log p)^2 p^(-1-theta+2a_Xi)`, whose prime sum converges.  For the lower bound, if
`theta<2a_Xi`, choose a divisor copy with horizontal charge greater than `theta/2`; its positive
summand dominates a divergent prime series.  The endpoint value is not needed.

## Completely monotone safe carrier

On `theta>2a_Xi`, termwise differentiation is justified locally and gives, for every `n>=0`,

```text
(-1)^n G_Xi^(n)(theta)
 =sum_p A_p lambda_p^n exp(-theta lambda_p) >=0.            (6)
```

Thus `G_Xi` is completely monotone on its exact convergence interval.  Equivalently, whenever
`theta_i>a_Xi`,

```text
[G_Xi(theta_i+theta_j)]_(i,j)
 =sum_p A_p
   [exp(-theta_i lambda_p)exp(-theta_j lambda_p)]_(i,j)
 >=0.                                                       (7)
```

This is an unconditional reflection-positive radial Hankel carrier on the safe shape domain.

## Exact extension criterion

The following are equivalent:

```text
1. RH.
2. The germ G_Xi on theta>1 extends to a finite completely monotone function on theta>0.
3. The kernel in (7) extends to all positive theta_i as a Laplace-positive Hankel kernel whose
   representing generator spectrum is contained in [0,infinity).                         (8)
```

Under RH every prime seam vanishes, so `G_Xi=0` and the extension is immediate.

Conversely, let `F` be the extension in item 2.  Bernstein's theorem gives a unique positive
measure `mu` on `[0,infinity)` such that

```text
F(theta)=integral exp(-theta lambda) dmu(lambda).           (9)
```

On `theta>1`, the same function is the Laplace transform of

```text
nu_Xi=sum_p A_p delta_(lambda_p).                           (10)
```

Fix `theta_0>1`.  The tilted measures `exp(-theta_0 lambda)mu` and
`exp(-theta_0 lambda)nu_Xi` are finite, and their Laplace transforms agree on an open interval
containing zero.  Uniqueness of Laplace transforms for finite positive measures identifies the
tilted measures and therefore `mu=nu_Xi`.  Since `(9)` is finite for every `theta>0`, the
abscissa of `(10)` is nonpositive.  Equation `(5)` gives `a_Xi=0`, which is RH.

Items 2 and 3 are the Bernstein representation in scalar and kernel language.  The phrase
"nonnegative generator spectrum" is essential.  Plain positive-semidefinite Hankel extension is
too weak: `K(s,t)=exp(s+t)` is positive semidefinite but corresponds to the negative frequency
`lambda=-1` and is not completely monotone.

## Positive content and limitation

This theorem is the nontrivial positive successor to two failed shortcuts.

1. Finite-stage entire Gamma-shape traces need not have a holomorphic cofinal limit.  What survives
   unconditionally is complete monotonicity and reflection positivity on the exact safe domain.
2. A unitary prime-phase orbit cannot by itself produce a rich Hankel carrier.  The Gamma--Meixner
   shape parameter supplies the required transverse radial semigroup.

The criterion does not lower the logical strength of RH by itself.  Its use is architectural: a
source proof may construct a positive contraction semigroup and a finite trace for every real
shape, avoiding complex normal-family estimates.  It must still identify that source trace with
`G_Xi` on the safe interval without defining the source metric from the Xi divisor.

## Parent-theory boundary

Bernstein's theorem, uniqueness of Laplace transforms, Gram positivity of Laplace kernels, and
Landau abscissa arguments are classical.  The exact coefficient series and abscissa `(5)` are
project bridge material built from already proved Xi seam identities.  No independent novelty is
claimed for their combination.

## Gates

- [x] nonnegative coefficient measure identified
- [x] exact convergence abscissa `2a_Xi` proved on paper
- [x] complete monotonicity on the safe shape interval proved on paper
- [x] radial Hankel positivity on the safe shape interval proved on paper
- [x] completely-monotone extension equivalence with RH proved on paper
- [x] plain Hankel-positivity overclaim excluded
- [ ] formalize only if the analytic infrastructure is reusable beyond this criterion
