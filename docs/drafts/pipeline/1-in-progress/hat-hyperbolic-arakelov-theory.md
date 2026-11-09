# Hyperbolic Arakelov theory of Spec ℤ (HAT)

- **ID:** hat
- **Stage:** 1-in-progress
- **Type:** CONJECTURE (programme)
- **Source:** docs/reports/review-0811/obstacles-summary.md §2.8 (B118′), §2.13
- **Statement:** RH as a Hodge index theorem on an arithmetic surface whose archimedean fibre is `ℍ³`
  with the dilation geodesic; topologically, Möbius cancellation as vanishing of a middle cohomology
  of an orientation cover over ℤ.

Lean: `formal/GaloisForLFunctions/HyperbolicArakelovTheory/`, umbrella
`HyperbolicArakelovTheory.lean`, README in the folder.

## Goal
Answer Q1–Q6 of the README (B118′; locked diagonal; genera; ample class; orientation cover;
windows), develop the tools of §2.13, formalize every answer.

## Gates
- [x] 0 → 1  in-progress: programme well-posed
- [ ] 1 → 2  per result
- [ ] 2 → 3  per result

## Conjectures and results

| # | Statement | Paper | Lean |
|---|---|---|---|
| H1 | Image distances: `cosh d(z_t, γz_u) = ½(‖a‖²u/t + ‖d‖²t/u + ‖b‖²/(tu) + ‖c‖²tu)` | proved | `TheImagesOfTheDegreeGeodesic` |
| H2 | Endpoint Eisenstein condition ⇒ dilation limit `Σ_{c=0} w_i 2πG_{1/2}(|log(‖a_i‖²r)|)`, continuous at resonance-free ratios; no such carrier carries the torsion; Poincaré at `½` + bounded `γ^{±1}(∞)` + bounded isometric radii + finite stabilizer ⇒ Eisenstein | proved | `TheDilationLimitOfATwistedCarrier` |
| H3 | Bounded geometry at `(M, pM)` for infinitely many `M` ⇒ jump `O(1/M)`; no such carrier carries the torsion | proved | `CarriersOfBoundedGeometry` |
| H4 | `2cosh(d/2) = (3/2)φ_{3/2} + ½φ_{1/2}`, `2πG_{1/2} = 2πG_{3/2} + ½φ_{1/2}`, `C_∞ = (3/2)φ_{3/2} − 2πG_{3/2}`; `C_∞ < 0 ⇔ e^{3d} < e^d + 1` | proved | `TheArchimedeanCompensationIsSpherical` |
| H5 | Locked dampings (`ρ(r) → 1`) have diagonal `D(1) − I(n,n)/φ(n)`; none is eventually PSD | proved | `LockingTheDampingsGivesTheDiscriminant` |
| H6 | Weil's `p`-kernel = tree Green function at the Ramanujan edge `2√p`; `λ_s = 2√p ⇔ s = ½`; adelic Green formula | proved | `TheFinitePlacesAreTrees` |
| H7 | Poincaré convergence at `½` + `diag(a, a⁻¹) ∈ Γ` (`‖a‖ > 1`) ⇒ no carrier (resonant primes `Σ1/p < ∞`, `⌈Q^j⌉` returns) | proved | `CarriersWithAClosedDegreeGeodesic` |
| H8 | Poincaré convergence at `½` + conical degree end ⇒ no carrier (≲ `S e^R √P` near elements, each spoils ≤ 1 prime ≤ P; Chebyshev) | proved | `CarriersAtAConicalLimitPoint` |
| H9 | B118′(1): every embedding with a cluster point fails for Newtonian kernels; cusp-escaping embeddings | partial | open |
| H10 | B118′(2) at non-conical limit points (geometrically infinite groups) | — | open |

## Log
- 2026-11-09 — programme created; README; H1–H8 formalized.
