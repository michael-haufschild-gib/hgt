# Vinogradov–Korobov saving for the signed incidence cost

- **ID:** vinogradov-korobov-signed-incidence-cost
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Wall:** Π47; the uniform signed prime–pole cost.
- **Target:** Universal `c,K>0` such that every real odd compactly supported
  `C¹` test on `[-r,r]`, `r>0`, satisfies
  `|reflectedPrimePolarCost(F,r)| ≤ K exp(r−c Q(r))(¼∫F²+∫F′²)`, where
  `Q(r)=vkScale(exp(max(2r,4)))`. Thus `Q(r)=(2r)^(3/5)(log(2r))^(−5/3)`
  for `r≥2`.

## Derivation

The exact Abel identity bounds this cost by
`∫₀^{2r}2exp(−s/2)|E(s)|ds` times `∫F²+½∫F′²`, at most four times
the stated Sobolev energy, where
`E(s)=exp(s)+s−1−ψ(exp(s))`.

Split `0≤s≤2r` at `s=r`. On the first half, the existing global
`|E(s)|≤K₀exp(s)` bound gives `K₀exp(r/2)` after weighting. On the second
half, the actual prime number theorem gives the saving
`exp(−κ vkScale(exp(s))/24)`, and
`vkScale(exp(s))≥(4/9)vkScale(exp(2r))`. The polynomial polar terms are
absorbed by `exp(s/2)`. Hence the whole weighted integrand is bounded by
`K₁exp(r−κ Q(r)/54)` for large `r`.

The contour estimates give `κQ(r)≥2sqrt(2r)` and `κQ(r)≤2r` eventually.
Half the saving absorbs the integral's factor `r`, leaving `c=κ/108`.
For bounded apertures, `Q(r)≤max(2r,4)` and the existing cost bound absorb
the compact range into `K`.

## Scope and novelty

The existing incidence estimate saves only `exp(−c sqrt(r))`. Existing
VK window-ceiling and fixed-test lag theorems do not supply this uniform
bound over arbitrary odd tests. The exact logarithmic loss of the corpus's
prime number theorem is retained. No derivative-energy bound is assumed.

This does not give a pure `L²` ground-energy floor or a fixed zero-free
strip. Π51 and the subexponential cost target in Π47 remain open.

## Corpus inputs

- `ReflectedPrimePolarAllocation`: the exact Abel bound and all-scale
  Chebyshev defect bound.
- `VinogradovKorobovPrimeNumberTheorem`: actual prime-count error.
- `ReceiverBoundedInTheVinogradovKorobovBand.four_ninths_mul_vkScale_le`:
  comparison across power scales.
- `VinogradovKorobovChebyshevParameters.eventually_vk_conditions`:
  upper and lower bounds on the contour saving.

## Lean certificate

`ArithmeticIncidencePositivity/VinogradovKorobovSignedCost.lean`:

- `incidenceVKScale_of_two_le`: exact large-aperture scale.
- `exists_abs_reflectedPrimePolarCost_le_vinogradovKorobov_mul_sobolev`:
  the uniform signed-cost theorem, with `c=vkKappa/108`.

The direct production `lake --old env lean` check passes; transitive axioms
are only `propext`, `Classical.choice`, and `Quot.sound`. The AIP umbrella
import is wired. Π47 is partially solved; its subexponential target remains open.
