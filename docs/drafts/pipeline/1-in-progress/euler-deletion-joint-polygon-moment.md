# Mixed Euler-deletion polygon: first surviving polynomial moment

**Stage:** finite arithmetic identity formalized; infinite development still a conjecture.
**RH status:** no implication. **Novelty:** arithmetic specialization unverified; generic ancestry published.
This is an arithmetic source-construction test, not a qualifying proof architecture yet.

## Source and proposed development

Use the literal coefficients `a_p(n)=1-p[p divides n]`. For moduli 2 and 3, accumulate the
vectors `(a_2(n),a_3(n))` for integers `n=1,...,6`, interpolating each increment by a straight
segment. The vertices are

`(0,0),(1,1),(0,2),(1,0),(0,1),(1,2),(0,0)`.

The proposed infinite object is the chronological product of
`exp(n^(-s)*(a_2(n)*X+a_3(n)*Y))` in a complete complex normed algebra, retaining two
noncommuting source generators. The corpus already constructs the one-modulus exponential
development, its commutative zero landing, and each finite mixed chronological word. It does not
follow from those statements alone that this joint product converges in one algebra norm.

## Conjecture loop

1. **A quadratic mixed block obstruction sets a half-plane threshold. Fails for the unweighted
   exponential block.** The polygon has zero signed area. This is a different lift from the raw
   product of `1+jump`; its quadratic diagonal correction must not be silently identified with
   the geometric exponential development.
2. **The next obstruction is cubic. Fails in the polynomial-moment test.** The moments that
   detect the two cubic planar commutators vanish as well.
3. **Every polynomial one-form of coefficient degree at most three integrates to zero, whereas
   `integral x*y^3 dx = 1/10`. Paper derivation below; Lean verified for every coprime pair.** Thus this
   exact closed arithmetic polygon retains higher ordered information after all those low-degree
   tests vanish.

## Exact paper calculation

Within a unit segment let `t` range over `[0,1]`. The two coordinate families are

`x=t,1-t` with velocities `+1,-1`,

`y=t,1+t,2-2t` with velocities `+1,+1,-2`.

The six segments realize every pair once. For all natural `a,b`, the sum of the integrands for
`x^a*y^b dx` is exactly

`(t^a-(1-t)^a) * (t^b+(1+t)^b+(2-2t)^b)`.

For `a+b<=3`, its integral is zero: `a=0` is identically zero; the cases `a=1` have second
factor `3`, `3`, or `6t^2-6t+5`; `a=2` gives the same first factor as `a=1`; and `a=3,b=0`
is odd under `t -> 1-t`. These exhaust the monomials. For `a=1,b=3`, the integrand is

`(2t-1)*(9-21t+27t^2-6t^3)`

`=-9+39t-69t^2+60t^3-12t^4`.

Its elementary integral is `1/10`. Exact differentials of `x^a*y^(b+1)` transfer the low-degree
vanishing to the `dy` forms too. This calculation uses symbolic integration, not a numerical
experiment.

## General arithmetic identity to formalize

For positive coprime moduli `p,q`, the same literal polygon has period `p*q`. Its segment
starting at integer `n` has coordinates `(n mod p,n mod q)`, by the existing exact prefix-sum
identity for deletion coefficients. The Chinese remainder theorem factors the segment sum as

`sum x^a*y^b*x_velocity = A_{p,a}(t)*M_{q,b}(t)`,

where `M_{p,k}(t)=sum_{j=0}^{p-2}(j+t)^k+((p-1)*(1-t))^k` and
`A_{p,k}(t)=sum_{j=0}^{p-2}(j+t)^k-(p-1)*((p-1)*(1-t))^k`.
These are finite sums of the actual segment positions and velocities.

Symbolic power-sum identities give

`A_{p,1}(t)=p*(p-1)*(2*t-1)/2`,

`M_{q,3}(t)=q^2*(q-1)^2/4-q*(q-1)*(4*q-5)*t/2`
`+3*q*(q-1)*(2*q-3)*t^2/2-q*(q-1)*(q-2)*t^3`.

Consequently the general identity is

`integral x*y^3 dx = p*(p-1)*q*(q-1)*(q-2)/120`.

This derivation is algebraic, with no experiment or numerical evidence. Lean has verified the
formula from the literal segment definition. Reversing the two coordinate labels gives the corresponding formula with `p-2`.
For coprime moduli both greater than one, at least one of these two moments is nonzero.
All polynomial one-forms of coefficient degree at most three vanish for every such coprime
pair. Lean verifies every monomial case; swapping coordinates supplies the other differential.

## Gates not yet discharged

- Audit the relation to full noncommutative exponential jets. Vanishing polynomial moments must
  not be assumed to prove vanishing of every signature coefficient in arbitrary degree.
- Prove the needed uniform block remainder and weight-variation estimates before asserting an
  infinite-product convergence region. No threshold is yet claimed for the joint product.
- Find an arithmetic relation special to zeta zeros. An existing product, a unit limit, or zero
  abelianization alone does not supply critical-line selection.
- Search primary literature for the specific arithmetic construction and its generic signature /
  polygon-moment ancestry before making a novelty claim.

## Source evidence

`research 'deletion signature'`, `research 'ordered product'`,
`research 'noncommutative convergence'`, `research 'palindromic product'`, and
`research 'deletion cubic'`, paired with `rg`.
Inspected `NoncommutativeAbelDevelopment`, `NoncommutativeDiscreteDevelopment`,
`EulerDeletionNoncommutativeDevelopment`, and `EulerDeletionNoncommutativeAbelianShadow`.
Their convergence theorems retain their stated scalar-coefficient or one-modulus scope.

## Primary literature boundary

[Boedihardjo–Ni–Qian, *Uniqueness of signature for simple curves* (2014), Theorem 1 and
Corollary 2](https://arxiv.org/pdf/1304.0755) express appropriate planar log-signature coefficients
as winding moments and determine the first four levels by those moments. Their proof of
Corollary 2 explicitly lists the eight relevant Lie elements. Thus the proposed bridge from
low polynomial one-forms to low signature levels has established ancestry; it is not a new
mechanism. Their sharpness example also warns that winding data alone do not recover all
fifth-level information. This does not identify the present arithmetic polygon with their example.

[Ursitti, *Computation of some transcendental integrals from path signatures*
(2016)](https://arxiv.org/pdf/1601.03135) explicitly recovers polynomial path integrals from
signatures. The general strategy of probing a signature with a polynomial one-form is therefore
published. Searches of the exact coprime/deletion/sawtooth specialization have not established
its publication status. Search misses are not a novelty certificate. No qualifying radical RH
architecture is established by this finite calculation.

## Formal certificate

Module `formal/GaloisForLFunctions/RHTower/EulerDeletionJointPolygonMoment.lean`, namespace
`RHTower.DeletionJointPolygon`. Lean parameters `p,q` represent the actual moduli `p+1,q+1`.

- `position_zero_eq_prefix`, `segment_endpoint`, `common_period_closed`: literal arithmetic
  prefix provenance, consecutive segment joins, and full-period closure.
- `integrand_factorization`: CRT identity for arbitrary polynomial exponents.
- `circulation_eq_segment_sum`: agreement with the sum of actual segment line integrals.
- `circulation_one_three`: the displayed general exact moment.
- `circulation_low_degree`: all ten monomials with coefficient degree at most three.
- `moduli_two_three_closed_low_degree_nonzero`: closed theorem with no hypotheses combining
  path closure, both families of low-degree tests, and the nonzero `1/10` moment.

Scratch `lake env lean /tmp/hgt-joint-polygon-17TZsg/LowDegree.lean` passed. Scratch
`Axioms.lean` also passed: all eight audited endpoint/factorization/integration/capstone theorems
use only `propext`, `Classical.choice`, and `Quot.sound`. No unfinished proof, added axiom,
external computation certificate, or numerical experiment is used. Narrow leaf build and global
lint results will be recorded after their current audit completes. The umbrella import is wired;
no umbrella build is requested.

## Decision

The positive survivor is the full coprime-family factorization and exact first surviving
polynomial moment, not merely a negative observation about a chosen toy polygon. Preserve this
as a proved arithmetic input. Do not count a standard path-signature interpretation as the
requested radical architecture. The joint weighted construction remains an explicit candidate
object, with its infinite norm and zero-specific arithmetic relations still to be proved.
