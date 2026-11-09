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
| H9 | B118′(1): Newtonian kernel with a cusp expansion (zero modes `t^{½}, t^{3/2}`, Wronskian `b₁ ≠ a₂`) on a space with proper height and finitely many cusps ⇒ no injective embedding carries the Frobenius intersection (cluster ⇒ Newtonian; escape ⇒ zero mode) | proved | `EmbeddingsIntoACompactQuotient`, `EmbeddingsIntoAFiniteVolumeQuotient` |
| H10 | Poincaré convergence at `½` + `D_Γ(M) = Σ_{γ≠1}e^{−d(z_M,γz_M)/2} ≤ C` for infinitely many `M` ⇒ no carrier; conical ⇒ `D_Γ ≤ e^R S` | proved | `CarriersAlongAnEndOfBoundedSelfEnergy`, `CarriersAtAConicalLimitPoint` |
| H11 | Convergence at `½` excludes parabolics (`γ^k = ±(1 + kN)`, harmonic series); `∞ ∈ Ω(Γ)` ⇒ endpoint Eisenstein; B118′(2) for finitely generated groups (with Beardon–Maskit, Canary + tameness) | proved | `TheBoundaryOfAGroupConvergentAtOneHalf` |
| H12 | Orientation cover over ℤ (RIAC discriminant cover): centred count `M(N) = Ω_±(√N)`; weight `½` ⇔ RH | proved | `TheMiddleCohomologyOfTheOrientationCover` |
| H13 | Beyond B118′ as posed (which is for geometrically finite groups): infinitely generated torsion-free groups: self-energy bounded on the thick part (Sullivan `λ₀ = 1`, elliptic estimate), thin forever ⇒ loxodromic end ⇒ conical | classical sketch | open (thick-part bound not in Lean) |

## Log
- 2026-11-09 — programme created; README; H1–H12 formalized.
