# Square-root prime windows detect purity

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Target:** B130 scale locality; partial B139.
- **Lean:** `SurfaceOfSpecZ/ScaleLocality/PrimeSquareRootWindows.lean`.

## Statements

Let `Z` be a tempered zero configuration without real zeros and
`f_Z(u)=2 Re lagStructure Z (boxSpline 1 3) u`. Fix `r>0`.

If some `K` bounds `f_Z(log p)` below by `-K` at every prime in
arbitrarily late windows `|log p-T|≤r√T`, then every zero lies on the
critical line. Centers may be arbitrarily sparse; no greatest depth
need be attained.

Equivalently, for each impure such `Z`, each `r>0`, and each `K`, every
sufficiently late window contains a prime with `f_Z(log p)<-K`.

For the actual zeta configuration, existence of these local prime lower
bounds is equivalent to RH.

## Proof

Suppose the configuration has width at most `a`. The existing derivative
bound is `|f_Z(u)-f_Z(v)|≤2L(u-v)exp(au)` for `0≤v≤u`.
The prime-gap bound `x^(2/3)` supplies a prime with
`0≤u-log p≤2G exp(-u/3)`. At sufficiently late centers, a prime chosen
for a point in the interior half-window remains in the full observed
window. Hence there is a fixed `M` such that

`f_Z(u)≥-M exp(αu)` on the interior half-window

for every `α≥max(0,a-1/3)`.

The continuous square-root-window depth theorem bounds the width by
`α`. Starting with the configuration strip width `1/2`, two applications
give `1/2 → 1/6 → 0`. Reflection then gives purity. Negating this
criterion yields the eventual negative-prime statement. For zeta, RH
already gives a global prime lower bound, proving the reverse implication.

## Certificates

- `prime_squareRoot_windows_transfer`
- `onLine_of_prime_squareRoot_windows`
- `eventually_prime_squareRoot_window_negative`
- `riemannHypothesis_of_prime_squareRoot_windows`
- `riemannHypothesis_iff_prime_squareRoot_windows`

Direct `lake --old env lean` audit passes. Transitive axioms are exactly
`propext`, `Classical.choice`, and `Quot.sound`; modules are umbrella-wired.

## Boundary

This specifies explicit decisive sparse windows. It does not prove the
arithmetic lower bound in B130. Arbitrarily slowly growing logarithmic
window radii, as required by full B139, remain open. No external novelty
claim; web search was excluded.
