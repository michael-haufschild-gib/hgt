# Xi Hermitian Stokes support barcode

- **ID:** XI-HERMITIAN-STOKES-SUPPORT-BARCODE
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `arithmetic-stokes-bockstein-universality-law.md` and `route-r-source-positive-polarization-stokes-flatness.md`
- **Statement:** The rank-one enhanced exponential supports attached to the Xi source-inverse and Hermitian-adjoint nearby-pole factors have radial symmetric difference `[-|Re rho - 1/2|, |Re rho - 1/2|)`; its width is the norm of the Xi boundary fracture and the absolute reflected prime-tail entropy.

## Goal

Apply irregular enhanced Riemann--Hilbert support calculus to an actual Xi normal factor. Close the local source-inverse/Hermitian-adjoint comparison exactly, expose why a real enhanced structure alone cannot imply RH, and identify the precise source-defined support defect a future arithmetic producer must annihilate.

## Gates

- [x] 0 → 1 in-progress: source-pure Xi coefficients, explicit enhanced support model, hostile attack
- [x] 1 → 2 fully-proven: complete calculation below, `[PROVED HERE]`, no open dependency
- [x] 2 → 3 formalized: `XiHermitianStokesSupportBarcode.lean`; targeted build and axiom check pass
- [ ] 3 → 4 publication-ready: standalone note and verified external novelty audit

## Exact claim

For `rho : C`, set

`a_rho = rho - 1/2`, `a_rho^H = -conj(a_rho)`.

These are already the corpus source-inverse and analytic-adjoint depth-successor nearby-pole coefficients. In the standard enhanced exponential support convention, put

`S_rho = {(theta,t) | 0 <= t + Re(a_rho exp(-i theta))}`,

`A_rho = {(theta,t) | 0 <= t + Re(a_rho^H exp(-i theta))}`.

Let `B_rho` be the symmetric difference of their fibers at the marked source direction `theta = 0`. Then:

1. `S_rho = A_rho` iff `Re rho = 1/2`.
2. `[PROVED HERE]` `B_rho = [-|Re rho - 1/2|, |Re rho - 1/2|)`.
3. The endpoint distance is
   `2 |Re rho - 1/2| = ||xiNearbyPoleDualityAdjunctionFracture rho|| = |riemannReflectedSourceEntropy rho|`.
4. Therefore every actual Xi-divisor barcode is empty iff RH.

The fourth item is an exact reformulation, not a proof of barcode emptiness.

## Paper proof

Write `x = Re rho - 1/2`. The depth-successor pole law gives

`depthSuccessorNearbyPole (-(rho - 1/2)) = rho - 1/2 = a_rho`

and

`depthSuccessorNearbyPole (conj(rho - 1/2)) = -conj(rho - 1/2) = a_rho^H`.

At `theta = 0`, the two phases are `x` and `-x`. Hence their enhanced-support fibers are the upper rays `[-x,+infinity)` and `[x,+infinity)`. Their symmetric difference is the half-open interval between the two endpoints. If `x >= 0` it is `[-x,x)`; if `x <= 0` it is `[x,-x)`. Both cases are exactly `[-|x|,|x|)`. This proves item 2 and shows emptiness iff `x = 0`.

For full support equality, equality of exponential epigraphs recovers equality of their phase functions. Evaluation at `theta = 0` gives `x = -x`, hence `x = 0`. Conversely, if `x = 0`, then `a_rho` is purely imaginary and `a_rho = -conj(a_rho)`, so both phases and supports agree. This proves item 1.

The interval endpoint distance is `2|x|`. The corpus boundary-fracture law gives

`xiNearbyPoleDualityAdjunctionFracture rho = 2x`,

while the source Green-fracture law identifies the same complex scalar with `-riemannReflectedSourceEntropy rho`. Taking norms proves item 3. Item 4 follows from the existing actual-Xi-divisor support criterion for RH.

## Hostile attack and positive survivor

**Killed claim:** a real or Hermitian enhanced object forces every exponential factor to be individually fixed and therefore forces RH.

Irregular Riemann--Hilbert conjugation sends an exponential coefficient `a` to `-conj(a)`. A real structure may pair two distinct factors in a free two-cycle; it does not force `a = -conj(a)`. The corpus real-source quartet already realizes off-line free orbits. Generic reality, unmarked microstalk ranks, and coefficient-blind Witt data therefore cannot kill the horizontal Xi displacement.

**Positive survivor:** fixed Hermitian exponential orbits are exactly critical-line factors. Free two-cycles carry a nonempty marked support barcode whose width is the absolute canonical source entropy. This is stronger than a renamed zero test: it identifies the complete missing enhanced-support region and connects it to an arithmetic source invariant.

**Remaining open core:** construct a source-pure irregular Riemann--Hilbert comparison morphism whose cone has empty marked barcode, or prove source-defined positivity/exactness forcing that cone to vanish. Assuming support equality or barcode emptiness is exactly RH-sized and remains forbidden.

## External audit

- D'Agnolo--Kashiwara's irregular Riemann--Hilbert correspondence supplies the enhanced exponential support model: <https://arxiv.org/abs/2408.04260>.
- Hohl's Kashiwara-conjugation theorem identifies enhanced de Rham/solution conjugation; locally Hermitian duality sends `E^phi` to `E^(-conj phi)`: <https://arxiv.org/abs/2307.15608>.
- Hepler--Hohl recover moderate/rapid nearby cycles and their duality from enhanced ind-sheaves, but do not provide a zeta source or same-fiber fixed-factor theorem: <https://arxiv.org/abs/2206.06095>.
- Targeted searches found no primary source applying this marked support-barcode calculation to Xi or deriving RH from irregular Stokes data. This is a noncollision check, not a priority claim.

## Classification

`[BRIDGE] [FORMALIZED] [NOVELTY-UNVERIFIED]`. Parent irregular Riemann--Hilbert mechanisms are known; exact Xi/source-entropy bridge was absent from audited corpus and literature. Keep outside `new_scientific_knowledge` until independent novelty review.

## Log

- 2026-08-24 — internal corpus audit isolated source-inverse/analytic-adjoint nearby-pole open core.
- 2026-08-24 — primary-literature audit killed generic-real-structure route.
- 2026-08-24 — complete support-barcode calculation proved on paper; advanced to Stage 2.
- 2026-08-24 — formalized as `RHTower.riemannHypothesis_iff_forall_xiHermitianStokesRadialBarcode_eq_empty` and supporting exact interval/width theorems; advanced to Stage 3.
