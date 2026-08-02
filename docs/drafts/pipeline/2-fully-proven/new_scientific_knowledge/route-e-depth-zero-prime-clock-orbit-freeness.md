# Route E depth-zero source has a free complete prime-clock orbit

## Status

Paper proof complete. Source-side Lean proof complete in
`GaloisForLFunctions/RHTower/MobiusDepthZeroPrimeClockOrbitFreeness.lean`, using new generic
infrastructure
`GaloisForLFunctions/HTGeometry/PrimeClockCyclicOrbitFreeness.lean`.

This is a source-classification theorem, not a Möbius cancellation estimate and not RH.

## Statement

Let \(\mathcal A\) be space of prime-power profiles, let
\(\mathcal A_{\mathrm{fin}}\) be profiles supported on finitely many prime rays, and put
\(\mathcal Q=\mathcal A/\mathcal A_{\mathrm{fin}}\). Let
\[
(Ta)(p,e)=-(e+1)\log p\,a(p,e).
\]
For canonical Route E depth-zero profile
\[
d_E(p,0)=p^{-1/2},\qquad d_E(p,e)=0\quad(e\geq1),
\]
complete orbit
\[
\bigl\{[T^k d_E]:k\geq0\bigr\}
\]
is linearly independent in \(\mathcal Q\).

Equivalently, for every nonzero polynomial \(P\in\mathbb C[X]\),
\[
P(T)d_E\notin\mathcal A_{\mathrm{fin}}.                 \tag{1}
\]

Finite-abscissa Dirichlet carrier is
\[
\mathcal Ld_E(s)=\sum_p p^{-(s+1/2)},\qquad \Re s>\tfrac12.
\tag{2}
\]
By exact prime-source correspondence in updated source-horizon theorem, (1) implies
\(\mathcal Ld_E\) is differentially transcendental over coordinate field enlarged by every
finite-prime Euler germ.

## Proof

Suppose a finite relation
\[
\sum_{k=0}^{m}c_k[T^kd_E]=0
\]
holds in \(\mathcal Q\). Then outside a finite set of prime rays,
\[
p^{-1/2}\sum_{k=0}^{m}c_k(-\log p)^k=0.
\]
First factor never vanishes. Polynomial
\[
P(z)=\sum_{k=0}^{m}c_kz^k
\]
therefore vanishes at infinitely many distinct points \(-\log p\), so \(P=0\) and every
\(c_k=0\). This proves orbit freeness.

Generic Lean proof packages same argument invariantly. For an injective diagonal clock,
polynomial saturation says a nonzero clock polynomial preserves finite-ray locality in both
directions. A nonlocal quotient class therefore has no nonzero polynomial annihilator; expanding
a finitely supported relation as a polynomial proves linear independence of its cyclic orbit.

Convergence in (2) follows by comparison with
\(\sum_{n\ge2}n^{-(\Re s+1/2)}\). Updated exact source--analytic correspondence then converts
clock-orbit freeness into differential independence of analytic carrier.

## Scientific consequence

Earlier phase-node result excluded one singular scalar mechanism. Orbit freeness is stronger:
no finite differential-algebraic construction over arbitrary finite-prime Euler data can
manufacture or annihilate canonical Route E all-prime source. Any successful Route E producer
must preserve this infinite clock module or act through a singular/relation-valued category
outside that completion.

This does not orient source or bound a Möbius partial sum. It rules out a complete finite-local
analytic surrogate class without replaying an RH-equivalent estimate.

## Lean certificate

Generic infrastructure:

- `rayClockPolynomialOrbit`
- `rayClockPolynomialOrbit_linearIndependent_of_not_local`

Route E specialization:

- `routeEDepthZeroPrimeClockOrbit`
- `routeEDepthZeroRotatedPrimeClockOrbit`
- `routeEDepthZeroPrimeClockOrbit_linearIndependent`
- `routeEDepthZeroRotatedPrimeClockOrbit_linearIndependent`
- `routeEDepthZeroPrimeClockPolynomial_not_local`
- `routeEDepthZeroRotatedPrimeClockPolynomial_not_local`

All statements are unconditional.

## Novelty audit

Polynomial root finiteness and torsion-free cyclic modules are classical. Source-horizon exact
correspondence is parent project theorem. Candidate project-new content is its Route E
specialization: precise depth-zero all-prime profile left by Möbius/Gamma reduction is a free
infinite prime-clock module and therefore cannot be replaced by any finite-local
differential-algebraic Euler circuit. No priority claim is made for abstract algebra.
