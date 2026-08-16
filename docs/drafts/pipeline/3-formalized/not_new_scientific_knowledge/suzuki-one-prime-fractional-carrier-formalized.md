# One-prime fractional polynomial carrier — Lean certificate

- **ID:** `suzuki-one-prime-fractional-carrier-formalized`
- **Stage:** 3 — formalized in Lean 4
- **Paper proof:**
  `./suzuki-one-prime-fractional-carrier.md`
- **Lean module:**
  `formal/GaloisForLFunctions/RHTower/SuzukiOnePrimeFractionalCarrier.lean`
- **Status:** `[FORMALIZED] [AXIOM-CLEAN] [MATHEMATICALLY STANDARD] [NOT RH]`

## Certified theorem surface

| Statement | Lean declaration |
|---|---|
| fractional orbit weight | `RHTower.fractionalPolynomialOrbitWeight` |
| strict positivity | `RHTower.fractionalPolynomialOrbitWeight_pos` |
| shift ratio | `RHTower.fractionalPolynomialOrbitShiftRatio` |
| exact ratio cocycle | `RHTower.fractionalPolynomialOrbitShiftRatio_cocycle` |
| weighted shift | `RHTower.fractionalPolynomialOrbitShift` |
| exact group law | `RHTower.fractionalPolynomialOrbitShift_add` |
| general fractional ratio bound | `RHTower.abs_fractionalPolynomialOrbitShiftRatio_le` |
| rank-one `2/3` square summability | `RHTower.summable_fractionalPolynomialOrbitWeight_twoThirds_sq` |
| rank-one polynomial energy bound | `RHTower.tsum_sq_fractionalPolynomialOrbitWeightedShift_le` |

## Verification

```text
lake env lean GaloisForLFunctions/RHTower/SuzukiOnePrimeFractionalCarrier.lean
lake build GaloisForLFunctions.RHTower.SuzukiOnePrimeFractionalCarrier
```

Exact leaf build passed. `#print axioms` for every theorem above reports only `propext`,
`Classical.choice`, and `Quot.sound`. Module is wired into `GaloisForLFunctions.RHTower`; umbrella
was not built.

## Scope boundary

This module constructs the fractional valuation representation and proves its sharp polynomial
energy growth. It does not postulate or wrap the Gamma-resolvent one-block estimate. That analytic
estimate and vector-valued Fourier/Bochner assembly remain open.

