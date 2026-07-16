# Positive prime--archimedean moment representation to RH

- **ID:** `prime-arch-positive-moment-representation-to-rh`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** Any positive real measure representing every normalized prime--Gamma moment
  implies the complete prime--Gamma Hankel cone and hence RH; infinite support is unnecessary.

## Goal

Remove the genuinely superfluous infinite-support hypothesis from the existing moment-measure route.
The old route used strict leading determinants and therefore asked the measure to charge every
cofinite set. The non-strict trace-Hankel criterion for RH needs only positivity of polynomial
squares, which every positive representing measure supplies.

## Theorem

Let

\[
M_k=\texttt{normalizedPrimeArchMoment}(k).
\]

If there exists a positive real measure `μ` such that every monomial is integrable and

\[
M_k=\int_{\mathbb R}x^k\,d\mu(x)
\qquad(k\ge0),
\]

then for every real polynomial `P`,

\[
\operatorname{Re}Q_{\mathrm{prime}\text{-}\Gamma}(P)
=L_M(P^2)
=\int_{\mathbb R}P(x)^2\,d\mu(x)
\ge0.
\]

Restricting to integer polynomials discharges the existing countable prime--Gamma source criterion,
so

\[
\text{positive representing measure for }(M_k)_{k\ge0}
\Longrightarrow
\text{complete source Hankel positivity}
\Longrightarrow
\mathrm{RH}.
\]

No infinite-support, moment-determinacy, Xi-divisor, root-location, or anti-Herglotz hypothesis is
used.

## Hypothesis discharge

The previous interface

\[
\text{infinite-support representing measure}\Longrightarrow\mathrm{RH}
\]

is now strictly weakened to arbitrary positive support. Infinite support remains useful only for
the stronger conclusion that every leading Hankel determinant is strictly positive.

## Positive analytic target

Construct any source-defined positive measure with the normalized prime--Gamma moments. A finite,
discrete, compactly supported, or indeterminate representation is all sufficient. In particular,
future Stieltjes, Sonin-barycenter, Nevanlinna, or theta pushforward constructions need not prove
support infinitude before entering the RH chain.

The formalized Euclidean spectral specialization in
`euclidean-spectral-pushforward-hankel-rh-capstone.md` now supplies a physics-native entry point:
any positive spectral measure whose integer Euclidean-clock samples equal the normalized
prime--Gamma moments pushes forward to this arbitrary positive representation.  Infinite spectral
support and nonzero clock spacing remain necessary only for the stronger strict-determinant
hierarchy, not for RH.

## Classification

The implication is the standard representing-measure proof of Hankel positivity, so it is not new
scientific knowledge. The project-specific gain is a real hypothesis removal at the prime--Gamma/RH
interface.

## Lean certificate

Module:

- `formal/GaloisForLFunctions/RHTower/PrimeArchMomentMeasureRH.lean`

Main declarations:

- `PrimeArchMomentRepresentation`
- `re_primeArchSourceTraceHankel_eq_momentFunctional_sq`
- `primeArchSourceTraceHankelIntNonnegative_of_momentRepresentation`
- `riemannHypothesis_of_primeArchMomentRepresentation`
- `primeArchMomentRepresentation_of_infiniteSupport`
- `PrimeArchEuclideanSpectralRepresentation`
- `primeArchMomentRepresentation_of_euclideanSpectral`
- `riemannHypothesis_of_primeArchEuclideanSpectralRepresentation`

Verification:

- `lake build GaloisForLFunctions.RHTower.PrimeArchMomentMeasureRH` passes.
- Formal lint passes.
- Axiom audit: only `propext`, `Classical.choice`, and `Quot.sound`.

## Gates

- [x] 0 → 1 in-progress: the strict-support hypothesis isolated as consumer-side overstrength
- [x] 1 → 2 fully-proven: direct moment-functional proof closes the non-strict cone
- [x] 2 → 3 formalized: arbitrary positive representation implies RH in Lean
- [ ] 3 → 4 publication-ready: construct a source-defined representing measure
