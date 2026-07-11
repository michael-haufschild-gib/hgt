# Degree-one Euler sources are finite-jet open but full-jet faithful

- **ID:** `euler-source-finite-jet-local-openness`
- **Stage:** 2-fully-proven / not-new
- **Type:** `[BRIDGE]` theorem (paper), with Lean-certified algebraic core
- **Scientific status:** `[NOT NEW SCIENTIFIC KNOWLEDGE]`.  After erasing the source vocabulary,
  finite-jet openness is the holomorphic inverse-function theorem applied to a weighted Vandermonde
  Jacobian, while full-jet faithfulness is ordinary Dirichlet-series uniqueness.  The combination is
  useful infrastructure but introduces no new parent mechanism.
- **Statement:** Fix `k` distinct primes and a complex base point.  The map from the `k` complex
  degree-one Euler-factor parameters near the trivial product to the first `k` derivatives of the
  negative logarithmic derivative is locally biholomorphic at the trivial product.  Conversely,
  for the all-prime degree-one class `|a_p| <= 1`, the full infinite jet at one point of `Re s>1`
  uniquely recovers every local parameter.  At coefficient level, the exact image consists of the
  streams supported on prime powers whose `log p`-normalized `p`-power rays are geometric; every
  such stream has a unique genuinely prime-indexed parameter field.  Thus Euler-source geometry is
  finite-jet open but its full image is an all-prime ray-compatible locus.

## Goal

Test the completed-flux report's remaining source-image route inside the actual nonlinear Euler
factor class, rather than inside a linear prime packet.  The result positively identifies where a
source selector can live: not in any finite jet, even after Euler-factor nonlinearity and all
prime-power repetitions are imposed.  The infinite jet, however, is faithful to the whole bounded
all-prime parameter field.  A selector must couple unboundedly many orders or recover the fixed
arithmetic parameters themselves.

## Gates

- [x] 0 -> 1: source-pure statement and explicit Jacobian identified
- [x] 1 -> 2: complete holomorphic inverse-function and full-jet recovery proofs; no open
  mathematical dependency
- [ ] 2 -> 3: the weighted Vandermonde Jacobian is formalized in
  `EulerSourceJetJacobian.lean`; formalization of the analytic local-biholomorphism corollary remains
- [x] novelty audit: downgraded by the parent-theory and anti-theatre gates

## The map

Fix distinct primes `p_0,...,p_(k-1)` and `s_0 in C`.  For `a=(a_i)` near zero, define

```text
L_a(s) = product_i (1-a_i p_i^(-s))^(-1),

F_a(s) = -L_a'(s)/L_a(s)
       = sum_i (log p_i) a_i p_i^(-s)/(1-a_i p_i^(-s)).
```

All denominators are nonzero on a product neighbourhood of `(a,s)=(0,s_0)`.  Define the finite
source-jet map

```text
Phi_(s_0,k)(a)_j = (d/ds)^j F_a(s)|_(s=s_0),    0 <= j < k.
```

This is a holomorphic map from a neighbourhood of `0 in C^k` to `C^k`.

## Theorem and proof

At `a=0`, only the first power of each local parameter contributes.  Commutation of the parameter
and section derivatives gives

```text
partial Phi_j / partial a_i (0)
  = (log p_i) p_i^(-s_0) (-log p_i)^j.
```

Thus the Jacobian is a Vandermonde matrix at the distinct nodes `-log p_i`, followed by the
nonzero diagonal scaling `(log p_i) p_i^(-s_0)`.  Its determinant is

```text
product_i ((log p_i) p_i^(-s_0))
  * product_(i<r) ((-log p_r)-(-log p_i)),
```

up to the harmless convention for row/column order.  Every factor is nonzero: primes exceed one,
the real logarithm is injective on positive reals, and complex powers of nonzero bases are nonzero.
The complex holomorphic inverse-function theorem therefore supplies neighbourhoods `U,V` of zero
such that

```text
Phi_(s_0,k) : U -> V
```

is biholomorphic.  In particular, every sufficiently small `k`-jet is the logarithmic-flux jet of a
genuine finite degree-one Euler product.

If a holomorphic function `H` of these `k` jet coordinates vanishes on all such Euler-source jets,
then it vanishes on the open set `V`; hence its germ is zero.  This proves the finite-equation
consequence.

## All-prime full-jet faithfulness

Let `a=(a_p)` and `b=(b_p)` range over the closed prime polydisc `|a_p|,|b_p| <= 1`.  On `Re s>1`
define

```text
F_a(s) = sum_p (log p) a_p p^(-s)/(1-a_p p^(-s)),
F_b(s) = sum_p (log p) b_p p^(-s)/(1-b_p p^(-s)).
```

The series converge absolutely and locally uniformly.  Indeed, on `Re s >= 1+delta`, every summand
is bounded by

```text
(log p) p^(-(1+delta))/(1-p^(-(1+delta))),
```

and the sum of these majorants is the ordinary von-Mangoldt series at `1+delta`.  Hence `F_a` and
`F_b` are holomorphic on the Euler half-plane.

Assume `Re s_0>1` and

```text
F_a^(j)(s_0) = F_b^(j)(s_0)    for every j >= 0.
```

The Taylor series are equal, so the two holomorphic germs agree.  The identity theorem on the
connected half-plane `Re s>1` gives `F_a=F_b` there.  Expanding every geometric denominator gives
the absolutely convergent ordinary Dirichlet series

```text
F_a(s) = sum_p sum_(m>=1) (log p) a_p^m p^(-m s),
F_b(s) = sum_p sum_(m>=1) (log p) b_p^m p^(-m s).
```

Uniqueness of ordinary Dirichlet series makes every coefficient equal.  At the integer `n=p`, only
the first power of the `p`-factor contributes, so

```text
(log p) a_p = (log p) b_p.
```

Since `log p` is nonzero, `a_p=b_p` for every prime.  Therefore the full jet map is injective on the
entire bounded all-prime degree-one Euler class.  In particular, it includes the zeta parameter
field `a_p=1`.

Combining this with local openness yields the exact pro-jet dichotomy:

```text
every finite jet projection contains an open set,
but the complete jet uniquely determines every bounded all-prime Euler parameter.
```

This locates the first faithful source coordinate at the inverse limit of all jet orders while
proving that every finite stage is analytically nonselective.

## Exact coefficient-image classification

For a coefficient stream `c : N -> C`, define ray compatibility by the two conditions

```text
c(n)=0                                      if n is not a prime power,
c(p^m)=(log p) * (c(p)/(log p))^m           for every prime p and m>=1.
```

Then the following are equivalent:

```text
c is ray-compatible,
there exists a unique a : Primes -> C with
  c(p^m)=(log p) a(p)^m and c(n)=0 off prime powers.
```

Equivalently, the image is cut out without existential parameters by the quadratic equations

```text
c(p^m)c(p^n)=(log p)c(p^(m+n))       for all primes p and m,n>=1,
```

together with prime-power support.  After adjoining the normalized exponent-zero coordinate `1`,
these are exactly the `2 x 2` Hankel minors using that zeroth row and column; they imply every minor
vanishes.  The quadratic system is genuinely all-order: every exponent appears, while its complete
solution set is still the unique-parameter Euler image above.

Existence is explicit: `a(p)=c(p)/(log p)`.  Uniqueness is already read at exponent one because
`log p` is nonzero.  This is the exact coefficient-space image of the degree-one Euler source,
not merely a necessary family of ray identities.  Transporting it through ordinary Dirichlet-series
uniqueness gives the corresponding full-germ image on any half-plane of absolute convergence.

The parent-theory verdict remains unchanged.  After erasing the arithmetic labels this is the
rank-one toric description of geometric sequences, producted over the primes, followed by standard
Dirichlet-series uniqueness.  It is the needed exact classifier, but it is `[BRIDGE]`, not new
scientific knowledge.

## What is genuinely stronger than the existing finite-prime theorem

`PinnedAffinePrimeJetRigidity.lean` treats a linear Dirichlet polynomial with freely chosen prime
coefficients.  Here the varied object is the nonlinear logarithmic derivative of an Euler product:
each parameter automatically generates the whole prime-power ray

```text
(log p_i) sum_(m>=1) a_i^m p_i^(-m s).
```

The theorem proves that those forced nonlinear tails do not create a finite-jet equation.  Their
first-order weighted Vandermonde remains nonsingular, so the nonlinear Euler class itself is locally
finite-jet full.

## Positive source-image consequence

The first possible Euler selector is an all-order compatibility.  Full-jet faithfulness proves this
without choosing a particular moment inversion.  At a far-right real base point,
the full jet is a determinate moment sequence for the prime-power atomic measure.  Degree-one Euler
factors impose geometric rank-one laws along each recovered prime ray.  The present theorem proves
that no truncation of that recovery can be replaced by a finite holomorphic constraint: every finite
projection already contains an open set.

For zeta, membership in the broad degree-one Euler class is still insufficient.  The required
selector must recover the fixed parameters `a_p=1` at every prime and then couple that datum to the
completed reflection constraint.  This theorem removes finite Euler-factor shape from the list of
possible missing mechanisms; it does not prove the remaining coupling or RH.

## Scope boundary

- The parameters `a_i` vary in complex neighbourhoods of zero.  The theorem concerns the analytic
  class of degree-one Euler products, not the much thinner automorphic/unitary locus `|a_i|=1`.
- Local openness is around the trivial product, not around the zeta parameter `a_i=1`.
- The result proves that Euler-product shape alone has no finite-jet equation.  It does not say that
  the fixed zeta source can realize arbitrary jets.
- Full-jet faithfulness is proved on the natural closed polydisc `|a_p| <= 1` in the Euler
  half-plane.  Parameters with faster allowed growth require a different convergence class and are
  not claimed here.
- This is a constraint theorem, not an exhaustion procedure: no support limit is used.

## Lean certificate

Module:
`formal/GaloisForLFunctions/RHTower/EulerSourceJetJacobian.lean`

Declarations:

- `eulerSourceJetJacobian`
- `existsUnique_eulerSourceJetJacobian_preimage`
- `eulerSourceJetJacobian_bijective`
- `degreeOneEulerFluxCoeff`
- `degreeOneEulerFluxCoeff_prime`
- `degreeOneEulerFluxCoeff_eq_zero_of_not_isPrimePow`
- `degreeOneEulerFluxCoeff_prime_pow`
- `degreeOneEulerFluxCoeff_prime_ray_mul`
- `degreeOneEulerFluxCoeff_one_eq_vonMangoldt`
- `degreeOneEulerParameter_eq_of_LSeries_eq`
- `DegreeOneEulerRayCompatible`
- `degreeOneEulerRayCompatible_iff_exists_parameter`
- `degreeOneEulerPrimeFluxCoeff`
- `degreeOneEulerPrimeFluxCoeff_injective`
- `degreeOneEulerRayCompatible_iff_existsUnique_primeParameter`
- `DegreeOneEulerQuadraticCompatible`
- `degreeOneEulerQuadraticCompatible_iff_rayCompatible`
- `degreeOneEulerQuadraticCompatible_iff_existsUnique_primeParameter`

The exact source check and exact target build pass.  The audited theorem declarations have
axiom footprint `[propext, Classical.choice, Quot.sound]`.  Lean certifies both the nonsingular
Jacobian, prime-power support, the geometric prime-ray law, the zeta/von-Mangoldt specialization,
recovery of every prime parameter from equality of the convergent Euler-flux L-series, and the exact
unique-parameter characterization of the complete compatible coefficient locus.  It does not yet
package the several-complex-variable inverse-function theorem or the analytic step from equality of
all derivatives to equality of the half-plane L-series.

## Parent-literature audit so far

The exact coefficient classifier has two immediate classical parents.  Completely multiplicative
Euler factors are geometric series (DLMF 27.4), and the `2 x 2` Hankel-minor ideal is the standard
determinantal presentation of a rational normal curve.  Producting those one-parameter loci over
the primes gives precisely the ray-compatible image above.  This independently confirms the
`[BRIDGE]` verdict; the quadratic packaging is not new scientific knowledge.

The closest checked parents are Ihara--Matsumoto `M`-function/value-distribution theory and Samprit
Ghosh, *Distribution of values of higher derivatives of L'/L(s,chi)*, arXiv:2601.05189.  Those works
vary unitary Euler phases and study distributions of individual logarithmic derivatives (with
higher-derivative extensions and local Jacobians).  The checked statements do not give the joint
`k`-parameter to `k`-derivative local-biholomorphism theorem above, nor its conclusion that the
finite-jet projection of the nonlinear degree-one Euler class has interior, coupled with full-jet
recovery of every bounded all-prime Euler parameter.

The exact joint packaging was not found in the checked sources, but that absence does not rescue
novelty: the proof is a routine composition of standard parent theorems.  Its positive use is to
locate the missing RH content outside source recovery itself.  Recovering the global Euler parameter
field does not relate a recovered source germ to the location of one of its poles.  The remaining
object must therefore be a pointed source--divisor incidence constraint, not another source-image
membership test.
