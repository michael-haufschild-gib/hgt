# Route Q selected power-reciprocal all-degree no-go

- **ID:** `route-q-selected-power-reciprocal-all-degree-no-go`
- **Date:** 2026-08-11
- **Status:** dependency-closed paper proof; unconditionally formalized in Lean
- **Route:** Q, theta--Cassini likelihood hierarchy
- **Claim retired:** the source-selected power-reciprocal theta carrier can represent every
  normalized prime--archimedean moment.

## Frozen conjecture

Let

\[
 \nu=\nu_{B(0)},\qquad
 a=\alpha_*>4,\qquad
 q_a(t)=t^{-a},
\]

where `nu` is the exponentially tilted higher theta likelihood spectral measure and `alpha_*` is
the unique exponent selected by the zeroth and first source moments.  Let

\[
 \mu_a=c\,(q_a)_*\nu
\]

be the mass-calibrated Route-Q carrier.  The proposed producer was

\[
 m_k=\int x^k\,d\mu_a(x)\quad(k\ge 0),
\]

with `m_k = normalizedPrimeArchMoment k`.

## Conjecture loop

1. **Sparse-support conjecture — failed.**  The theta likelihood carrier was first treated as a
   discrete power image of square-gap atoms.  This is false: every theta atom contributes both a
   Dirac mass and a positive Lebesgue ray.  No support-counting contradiction is available.
2. **Positive survivor from that failure.**  The same ray makes `nu` positive on every nonempty
   open subset of `(3,infinity)`.  Since `q_a` is continuous and nonconstant there, its image has
   connected continuum support.
3. **All-degree matching conjecture — disproved.**  Corpus unrestricted-carrier rigidity says any
   positive measure matching every `m_k` is exactly the compact atomic Xi-divisor measure.  That
   measure is carried by the closed countable set
   `xiThermalCompactNodeSet`.  But `mu_a` assigns positive mass to its complement.

## Dependency-closed proof

The `n=2` theta spectral summand contains

\[
 w_2\,1_{(3,\infty)}(t)\,dt,\qquad w_2>0.
\]

It follows that restricted Lebesgue measure on `(3,infinity)` is absolutely continuous with
respect to the full higher spectral measure.  The Gibbs tilt has a strictly positive density, so
the same restricted Lebesgue measure is absolutely continuous with respect to `nu`.  Hence every
open set meeting `(3,infinity)` has positive `nu`-mass.

Let `K = xiThermalCompactNodeSet`.  `K` is closed and countable.  If
`q_a((3,infinity))` were contained in `K`, then its connected image would be a countable connected
subset of the real line and therefore a singleton.  This contradicts
`q_a(4) != q_a(5)` for `a>0`.  Thus choose `t>3` with `q_a(t)` outside `K`.  Continuity and closedness
of `K` give an open neighborhood `U` of `t` with `q_a(U)` disjoint from `K`.  Full ray support gives
`nu(U)>0`; positive calibration gives

\[
 \mu_a(K^c)>0. \tag{1}
\]

Assume all-degree matching.  Then `mu_a` is an `IsPrimeArchMomentWitness`.  The unconditional
rigidity theorem `IsPrimeArchMomentWitness.eq_primeArchXiCompactMomentMeasure` first derives RH from
the witness and then uses compact moment determinacy to obtain

\[
 \mu_a=\mu_{\Xi}. \tag{2}
\]

The canonical measure `mu_Xi` is carried by `K`, so `(2)` contradicts `(1)`.  Therefore

\[
 \boxed{\neg\,\forall k,\quad
 m_k=\int x^k\,d\mu_{\alpha_*}(x).}
\]

No zero computation, RH premise, or numerical enclosure is used.

## Exact new insight

Matching mass, barycenter, the strict `1/81` support contraction, and even the degree-two ratio gate
cannot make a continuous monotone source reporter into the Xi carrier.  Complete moment matching
forces **source-side quantization**: positive source regions must collapse onto countably many
positive-mass Xi fibres.  The required producer is therefore a discontinuous plateau/quotient law,
not a reparameterized continuous likelihood coordinate.

This is the positive survivor.  Route Q should not be retried with another continuous injective or
strictly monotone scalar transform of the same full-ray source.  A Frankenstein successor may use
Route U's canonical first-contact strata, Route G's source-selected Clark/HB atoms, or a comparable
source-derived partition to construct the required quantized fibres before bounded scalarization.

## No-go closure audit

- Negative statement: selected power carrier cannot match all degrees.
- Sharp boundary: any complete source reporter must have positive-measure fibres over every
  enumerated Xi thermal node.
- Replacement hypothesis: construct a source-derived measurable plateau quotient whose
  pushforward is the canonical atomic Xi moment measure; continuity/strict monotonicity is forbidden.
- Lean: `RHTower/ThetaCusp/ThetaCuspCalibratedPowerReciprocalAllDegreeNoGo.lean` formalizes open-ray absolute
  continuity, positive mass outside `K`, and the final all-degree no-go.
