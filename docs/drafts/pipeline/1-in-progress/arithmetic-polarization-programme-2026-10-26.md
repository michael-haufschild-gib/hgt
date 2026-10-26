# Arithmetic Polarization programme

- **ID:** apol
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean) programme
- **Source:** docs/reports/review-2610/hard-obstacles-summary.md §4
- **Statement:** Develop the field "arithmetic polarization": positive structures on reflection pairs, their mechanisms (invariant, counting, elliptic, charged), localizers, collisions and completions.

## Goal
Lean folder `formal/GaloisForLFunctions/ArithmeticPolarization/`, umbrella `ArithmeticPolarization.lean`,
foundational README. Answer the eleven questions of §4.4 by theorems or sharp no-gos with survivors;
build the tools of §4.5.

## Gates
- [x] 0 → 1  in-progress
- [ ] 1 → 2  paper proofs for each pillar
- [ ] 2 → 3  each pillar in Lean, audited with `lake --old env lean`

## Pillars and modules

| Pillar | Module | Status |
|---|---|---|
| Π1 polarization law | `ThePolarizationLaw` | Lean, checked |
| Π2/Π3/Π6 local signs, elliptic localizers, dihedral dilemma | `TheEllipticLocalizers` | Lean, checked |
| Π4 twist and collision identities | `TwistedSectorsCollideQuartets` | Lean, checked |
| Π5 price of elliptic localization | `ThePriceOfEllipticLocalization` | Lean, checked |
| Π7 Fejér barrier for coupled contraction | `TheFejerBarrierForCoupledContraction` | Lean, checked |
| Π8 collision law | `TheCollisionLaw` | Lean, checked |
| Π9 diagonal collapse | `TheDiagonalCollapse` | planned |
| Π10 first gauge charge | `TheFirstGaugeChargeIsATwist` | Lean, checked |
| Q6 rigidity probe | — | planned |
| Q7 oscillatory capacity | — | planned |
| Q11 loss laws | — | planned |

## Key paper facts
- Reflection-commuting affine maps: `φ(s) = ½ + λ(s−½) + iκ`. Stabilizer of an off-line pair
  `{½ ± a + iγ}`: `{id, σ_γ}`, `σ_γ(s) = 1 + 2iγ − s`.
- With `ĝ(s) = ∫ g(u) e^{(s−½)u} du`: `(e^{−iγu} r)^(s) = r̂(s − iγ)`, `(g(−·))^(s) = ĝ(1 − s)`,
  `σ_γ g := e^{−2iγu} g(−u)` has transform `ĝ(σ_γ s)`.
- `Z.W(e^{−iγu}r, e^{−iγu}r) = (Z − iγ).W(r, r)`; ordinate-γ quartet ↦ real pair; at a real pair
  `2 r̂(½+a) r̂(½−a)` is `≥ 0` on even, `≤ 0` on odd real tests.
- Prime side of the twisted test: atoms `2 K(log n) cos(γ log n)`.

## Log
- 2026-10-26 — created; README first draft written.
