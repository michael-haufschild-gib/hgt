# HB: exact zero-delay source and current coefficients

Status: twelve closed Lean theorems. Complete physical extinction and RH remain unproved.

Proof chain: literal theta-cusp source → Xi occurrence → retained spin-two source → physical causal radial/left-QNM action → fixed Hawking-clock extinction → RH.

Module: `GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMZeroDelayCurrent`.
Namespace: `RHTower.D4BMZeroDelayCurrent`.

The [source-specific calculation](../1-in-progress/hb-zero-delay-current-match.md) evaluates the whole zero-delay radial triangle from the finite-clock transfer. The cubic onset primitive and antisymmetrization turn the characteristic contact into endpoint moments. Complementary source exponents then give the exact horizon and null-slice scalar coefficients of the retained physical lift currents.

| Declaration | Closed statement |
|---|---|
| `physical_radial_amplitude` | The positive-base profile is the corpus's original ingoing source amplitude at zero transform frequency, with its independent amplitude factor restored. |
| `physical_reduced_source` | The onset coefficient used below is exactly the coefficient in the existing full reduced time forcing; both fixed onset and its first derivative remain. |
| `onsetMoment_eq` | The integral of the original onset weight through any nonnegative physical radius is its explicit cubic lift primitive. |
| `contactQ_integral` | The entire antisymmetrized zeroth-jet triangle is `alpha_s I_s J_t-alpha_t J_s I_t+(s-t)J_s J_t`. |
| `contactDelta_integral` | The entire first-jet triangle is `(K_s J_t-J_s K_t)/2`. |
| `terminal_radial_density` | The complementary terminal integrand is exactly `8 delta k_s k_t u^6/(1+u)^7`. |
| `terminal_integral` | The complete terminal triangle has that integrated null-slice radial weight. |
| `horizon_contact_coefficient` | The horizon coefficient is exactly `delta(lambda-2)(lambda-6)/512`. |
| `nullSlice_integral` | The finite radial integral is exactly `log(2)-1327/1920`. |
| `terminal_integral_closed` | The complete terminal triangle is `8 delta k_s k_t (log(2)-1327/1920)`. |
| `sourceMoment_eta_endpoint` | The original source moment satisfies `alpha_s I_s=1+4s 2^(2s)` at every complex frequency. |
| `contactQ_integral_closed` | The complete zeroth-jet triangle is `2 k_t 2^(2t)-2 k_s 2^(2s)+delta(lambda-2)(lambda+2)/256`, for `t=-s-3`. |

Here `I_s`, `J_s`, and `K_s` are actual finite integrals of the original source profile and onset weight. No integrability, derivative identity, boundary cancellation, spectral selection, or RH premise is supplied. The endpoint formula uses no division by a frequency polynomial and includes its exceptional frequencies.

The finite-clock transfer onto the actual native kernel remains a paper identity. The comparison of these scalar coefficients with the physical current must retain the angular Green boundary and physical face orientations. The remaining endpoint moment terms, positive-delay bulk, positive characteristic delays, terminal integral, and all independent SS/SV/VV contributions remain part of the full cancellation problem. This leaf proves neither that cancellation nor the native-circle representation of the complete unprojected physical response.

Validation: foreground `lake env lean` scratch checks passed without warnings. The final foreground `lake build GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMZeroDelayCurrent` built the new leaf in 44 seconds (three jobs), using 3,987 frozen existing own-module caches and eleven external package caches. No existing module or umbrella was rebuilt. Only the twelve new public declarations were axiom-audited; every one reports exactly `propext`, `Classical.choice`, and `Quot.sound`. No axioms or computational proof oracles were added. Installed source, `.olean`, and `.ilean` were byte-compared with the audited artifacts. The import is wired into `GaloisForLFunctions/RHTower.lean`.

The corpus index was refreshed and `scripts/formal_tools.py lint` passed, with existing large-file warnings. Scoped whitespace checks passed. Owned scratch and frozen-audit files were removed after verifying no owned Lean/Lake process remained. No mathematical computations or frontier-map edits were made.
