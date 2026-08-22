# Reflected bi-heat completion anomaly

- **ID:** `reflected-bi-heat-completion-anomaly`
- **Stage:** 2-fully-proven / needs-audit
- **Type:** THEOREM CANDIDATE / source-defined reflection pairing
- **Scientific status:** `[PROVED ON PAPER; NOVELTY UNVERIFIED]`
- **Source:** prime Dirichlet wave, additive Gaussian aperture, and functional-equation reflection
- **Statement:** Analytically regularizing the additive heat pairing between the Dirichlet wave at
  `s` and its reflected wave at `1-conj(s)` produces a universal logarithmic scale anomaly.
  After that anomaly, two distinct small-aperture channels carry the same completed-zeta
  coefficient.  The construction is intended to test whether the internal reflected metric can
  force the external clock coordinate without inserting the zeta divisor.

## Candidate object

Fix `s` with `1/2 < Re(s) < 1`, put `z=conj(s)`, and for `x>0`, `Re(epsilon)>0` define

```text
B_(z,epsilon)(x)
  = sum_(m,n>=1)
      m^(-(z+epsilon/2))
      n^(-(1-z+epsilon/2))
      exp(-pi x (m-n)^2).
```

The total diagonal exponent is `1+epsilon`, so the series is absolutely convergent.  The
reflection constraint appears before any zero is read: at `epsilon=0` the two exponents sum to
one.  The candidate renormalized pairing is

```text
Bhat_z(x)=FP_(epsilon=0) B_(z,epsilon)(x).
```

## Absolute convergence and the universal pole

`[PROVED]` For every `Re(epsilon)>0`, the double series defining `B_(z,epsilon)(x)`
is absolutely convergent.  Group the terms by `k=m-n`.  For `k>=0`, the absolute value of the
corresponding row is bounded by

```text
sum_(n>=1) (n+k)^(-Re(z)-Re(epsilon)/2)
                 n^(-(1-Re(z))-Re(epsilon)/2)
  <= sum_(n>=1) n^(-1-Re(epsilon)).
```

The rows with `k<0` satisfy the same bound after interchanging `m,n`.  Summation against
`exp(-pi x k^2)` proves absolute convergence.

For fixed `k`, subtract `sum_n n^(-1-epsilon)` from the shifted row.  The difference is locally
uniformly convergent at `epsilon=0`: splitting into `n<|k|` and `n>=|k|`, the second range follows
from the mean-value estimate for `(1+|k|/n)^(-a)-1`, and the first is finite.  The resulting bounds
grow at most polynomially in `|k|`, so the Gaussian sums them.  Therefore `B_(z,epsilon)(x)` has a
simple meromorphic pole at `epsilon=0` with exact residue

```text
Theta(x)=sum_(k in Z) exp(-pi x k^2).                  (1)
```

This proves that

```text
Bhat_z(x)=FP_(epsilon=0) B_(z,epsilon)(x)              (2)
```

is canonical once the symmetric exponent regulator is fixed.  The residue is independent of `z`:
the reflected inner metric forces a universal logarithmic divergence before any zeta zero enters.

## Reflected bi-heat expansion

`[PROVED]` As `x` decreases to zero,

```text
Bhat_z(x)
  = (1/(2 sqrt(x)))
      (log(4 pi x)-EulerGamma-psi(z)-psi(1-z))
    + (1/2) Lambda(z) x^((z-1)/2)
    + (1/2) Lambda(z) x^(-z/2)
    + zeta(z) zeta(1-z)
    + o(1),                                             (3)
```

up to terms exponentially small in `1/x`, where

```text
Lambda(z)=pi^(-z/2) Gamma(z/2) zeta(z).
```

Here `EulerGamma` is Euler's constant and `psi=Gamma'/Gamma`.  Terms exponentially small in `1/x`
are absorbed by `o(1)`.  The repeated coefficient is forced by the functional equation, not
imposed by the regularization.

### Proof

For `Re(epsilon)` initially large enough that both factors are square-integrable, Fourier
multiplication writes `B_(z,epsilon)(x)` as the Gaussian average of

```text
Li_(z+epsilon/2)(exp(-i theta))
  Li_(1-z+epsilon/2)(exp(i theta)).                    (4)
```

Both sides are holomorphic for `Re(epsilon)>0`, so the identity extends throughout that half-plane.
Jonquiere's local expansion gives, on the two sides of `theta=0`, a product of two singular
branches, two singular--regular cross terms, the regular product, and a remainder.

The averaged singular--singular coefficient is

```text
G_z(epsilon)
  = Gamma(1-z-epsilon/2) Gamma(z-epsilon/2) sin(pi z). (5)
```

Indeed the positive and negative branch phases are respectively

```text
exp(+i pi(z-1/2)),  exp(-i pi(z-1/2)).
```

At `epsilon=0`, Euler reflection gives `G_z(0)=pi`.  The Gaussian moment of order
`epsilon-1` is

```text
(4 pi x)^((epsilon-1)/2) Gamma(epsilon/2)/sqrt(pi).    (6)
```

Using

```text
Gamma(epsilon/2)=2/epsilon-EulerGamma+O(epsilon),

G_z(epsilon)
  = pi * (1-(epsilon/2)(psi(z)+psi(1-z))+O(epsilon^2)),
```

the finite part of `(5)*(6)` is exactly

```text
(1/(2 sqrt(x)))
  (log(4 pi x)-EulerGamma-psi(z)-psi(1-z)).             (7)
```

Its pole is `1/(sqrt(x) epsilon)`.  Poisson summation gives

```text
Theta(x)=x^(-1/2)(1+O(exp(-pi/x))),                    (8)
```

so `(7)` agrees with subtraction of the exact residue `(1)` up to exponentially small terms.

The first cross term has coefficient

```text
(1/2) pi^((z-1)/2) Gamma((1-z)/2) zeta(1-z)
  = (1/2) Lambda(1-z)                                  (9)
```

and multiplies `x^((z-1)/2)`.  The second has coefficient

```text
(1/2) pi^(-z/2) Gamma(z/2) zeta(z)
  = (1/2) Lambda(z)                                    (10)
```

and multiplies `x^(-z/2)`.  The completed functional equation
`Lambda(1-z)=Lambda(z)` proves that the two coefficients coincide.  The regular--regular product
is `zeta(z)zeta(1-z)`.

The omitted analytic terms are `O(theta)` on one factor.  Multiplication by the two singular
branches gives orders `theta^z` and `theta^(1-z)`.  Their Gaussian moments are `o(1)` because
`0<Re(z)<1`; all remaining terms decay faster.  This proves `(3)`.  QED.

## Clock and superspace interpretation

The two completed channels have scale orders

```text
(Re(z)-1)/2,  -Re(z)/2.                                (11)
```

They have equal real order exactly when `Re(z)=1/2`.  Reflection `z |-> 1-z` exchanges them.  Thus
the critical line is the self-dual scale slice of the renormalized inner pairing, while the
digamma term in `(7)` is the archimedean metric counterterm.  This realizes the user's proposed
clock mechanism without introducing an evolution equation: the external aperture scale is fixed
by the singular order of a static reflected pairing.

On the critical line the two unregularized factors in `(4)` are conjugates, so the regulated object
is an ordinary positive heat norm before its universal pole is removed.  Off the line it is a
biorthogonal, generally complex pairing.  Finite-part subtraction does not preserve positivity.

## Terminal RH attack

Let `rho` be a hypothetical zero with `1/2<Re(rho)<1` and put `z=conj(rho)`.  Schwarz reflection and
the functional equation give

```text
zeta(z)=zeta(1-z)=Lambda(z)=0.                         (12)
```

Consequently every zeta-bearing term in `(3)` disappears, leaving the universal anomaly `(7)` and
an `o(1)` remainder.  No contradiction occurs: the anomaly is defined and generally complex off
the line, and finite-part positivity exists only at the already self-dual slice.

Therefore the repeated completed coefficient is an exact zero detector but not a zero localizer.
Demanding that disappearance of both channels occur only where their real scale orders coincide is
precisely

```text
Lambda(z)=0 implies Re(z)=1/2,
```

which is RH.  The inner metric forces the kinematic self-dual clock, but it does not force analytic
defects to occupy that clock slice.

The archimedean reality selector has been separated and formalized in Lean as
[`reflected-digamma-anomaly-reality-selector.md`](../../../3-formalized/not_new_scientific_knowledge/reflected-digamma-anomaly-reality-selector.md).
For nonzero height, the imaginary part of the anomaly in `(7)` vanishes exactly when
`Re(z)=1/2`.  This strengthens the kinematic selector but does not create a theorem requiring a
hypothetical off-line zero's finite-part pairing to be real.

## Multiplicity-sensitive scale tomography

Subtract the explicit anomaly `(7)` and write the result as `R_z(x)`.  The local polylogarithm
expansion is uniform with all `z`-derivatives on compact subsets of `0<Re(z)<1`, so `(3)` may be
differentiated termwise there.

`[PROVED]` Suppose `z_0` is a zero of `Lambda` of order `m>=1`.  Then for `0<=j<m`,

```text
partial_z^j R_z(x) at z=z_0 = o(1),
```

whereas the first nonzero transversal response is

```text
partial_z^m R_z(x) at z=z_0
  = (1/2) Lambda^(m)(z_0)
      (x^((z_0-1)/2)+x^(-z_0/2))
    + o(x^((Re(z_0)-1)/2)+x^(-Re(z_0)/2)).             (13)
```

Indeed every derivative of `Lambda` below order `m` vanishes.  Consequently all derivatives of
the exponentials which would produce powers of `log x` are multiplied by zero.  The regular product
`zeta(z)zeta(1-z)` has order `2m` at `z_0`, so it contributes nothing at derivative order `m`.

Thus the first nonzero response detects multiplicity and horizontal location simultaneously.  The
difference of the two real scale orders in `(13)` is

```text
((Re(z_0)-1)/2)-(-Re(z_0)/2)=Re(z_0)-1/2.              (14)
```

RH is therefore equivalent to equality of the two real scale orders in the first nonzero
transversal response at every nontrivial completed-zeta zero.  This is a source-derived tomography
of a hypothetical off-line zero, not a theorem excluding one.

## Parent-theory and preliminary literature boundary

The ingredients are established parents:

- the local polylogarithm expansion is DLMF 25.12.12;
- complex polylogarithm kernels as tempered distributions and their Hadamard finite parts are
  developed by Gay--Sebbar;
- analytic finite-part traces and their regulator anomalies belong to the
  Kontsevich--Vishik/Grubb/Paycha theory; and
- the Gaussian moments, Poisson transformation, Gamma identities, and zeta functional equation
  are classical.

Exact-formula searches for the complementary-order product
`Li_z(exp(-i theta)) Li_(1-z)(exp(i theta))`, its Gaussian finite part, the digamma anomaly `(7)`,
and the repeated completed coefficient in `(3)` did not locate an equivalent statement.  Nearby
work treats individual polylogarithm kernels, canonical traces, periodic-zeta covariance kernels,
and automorphic regularized inner products, not this additive reflected pairing.

This is only a preliminary parent audit.  Because the proof is a controlled composition of those
parents, the result remains `[NOVELTY UNVERIFIED]`; it is not promoted to candidate new scientific
knowledge before a broader independent comparison.

### Parent references

- NIST DLMF, §25.12(ii), equation 25.12.12:
  <https://dlmf.nist.gov/25.12.E12>
- R. Gay and A. Sebbar, *Pseudo-differential operators on the circle, Bernoulli polynomials*,
  Quantum Studies: Mathematics and Foundations 11 (2024):
  <https://doi.org/10.1007/s40509-024-00316-9>
- A. Cardona, C. Ducourtioux, and S. Paycha, *From tracial anomalies to anomalies in Quantum Field
  Theory*, Communications in Mathematical Physics 242 (2003):
  <https://arxiv.org/abs/math-ph/0207029>
- G. Grubb, *A resolvent approach to traces and zeta Laurent expansions* (2005):
  <https://arxiv.org/abs/math/0311081>

## Proof and audit gates

- [x] absolute convergence for `Re(epsilon)>0`
- [x] simple meromorphic pole and exact theta residue
- [x] finite-part small-`x` expansion with branch phases and remainder orders
- [x] completed functional equation recovered as equality of two clock-channel coefficients
- [x] hypothetical off-line zero tested with no contradiction
- [x] multiplicity and horizontal scale tomography derived from the first nonzero response
- [ ] independent proof audit of the meromorphic continuation and finite-part normalization
- [ ] parent-literature audit across relative heat traces, Rankin--Selberg pairings, and scattering

## Kill condition

The kill condition is met: a hypothetical off-line zero deletes both completed channels while
leaving the universal anomaly consistent.  The theorem survives as a source measurement theorem
and as a terminal obstruction to the claim that the reflected inner metric alone forces zero
localization.  It is not an RH proof.

## Lean gate

The analytic expansion requires a polylogarithm boundary and meromorphic finite-part API not
currently present in the formal tree.  No placeholder interface is permitted.  Formalization starts
only if a substantive algebraic or summability core can be proved without axiomatizing the
expansion.

The substantive digamma core is now formalized in
`formal/GaloisForLFunctions/HTGeometry/ReflectedDigammaAnomaly.lean`: strict horizontal monotonicity,
conjugation, and the anomaly-reality equivalence are checked without new axioms.  The full expansion
`(3)` and tomography theorem `(13)` remain paper-only.
