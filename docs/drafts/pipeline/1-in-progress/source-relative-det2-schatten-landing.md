# Source-relative det2 Schatten landing

- **ID:** source-relative-det2-schatten-landing
- **Stage:** 1-in-progress
- **Type:** SOURCE CONJECTURE / RH-SUFFICIENT CROSS-ROUTE BRIDGE
- **Source:** `rh-current-frontier-map.md` §1; `../2-fully-proven/new_scientific_knowledge/prime-depth-bv-wold-schatten-wall.md`
- **Statement:** The source-built relative transition from Route R's depth-one resolved frame to the physical/unit-double endpoint has the proved relative anomaly coefficients and is Schatten-1.

## Goal

Prove, before Xi-divisor enumeration, that actual source relative transition between

1. retained Route-R resolved rational-adelic frame at Wold depth one, and
2. physical/unit-double corrected ordinary-prime endpoint frame

has diagonal logarithmic coefficient

```text
(2 Re(s)-1)(1-p^(-1))^3 log(p)/p + 2 log(p)/p^2
```

and belongs to source Schatten-1 determinant class.  The Schatten-wall theorem then forces
`Re(s)=1/2` at every Xi divisor and proves RH.

## Gates

- [x] 0 → 1 in-progress: well-posed, source-pure, exact target and hostile falsifiers stated
- [ ] 1 → 2 fully-proven: source operator constructed; coefficient identity and Schatten-1 factorization proved
- [ ] 2 → 3 formalized: all source constructions and proof formalized in Lean
- [ ] 3 → 4 publication-ready: standalone proof and novelty audit

## Approach

Use three already constructed organs without scalarizing them prematurely:

- Route R: strict resolved rational-adelic prime-isotropy boundary and graded-`det₂` local anomaly;
- physical seam: unit-double/physical cancellation with trace-class remainder `2 log(p)/p²`;
- HTGeometry: product-of-Hilbert--Schmidt-is-trace-class and source-pointed parallel conservative factorization.

Construct one global relative operator.  Required coefficient identity must be a matrix-entry theorem of that operator, not a postulated sequence equality.

## Hostile audit

- Counterterm chosen using `s` would insert conclusion and is forbidden.
- Local `det₂` existence does not imply all-prime Schatten-1 landing.
- Calling coefficient family summable by definition is exactly RH criterion.
- Depth `e≥2` is useless for selection: anomaly is summable for every centered rate.
- Reflection product equals one for every rate and cannot supply positive same-fibre descent.
- If source transition naturally lands only in Schatten-2, conjecture is false in stated form; strongest survivor is precise ideal threshold, not RH.

## Log

- 2026-08-04 — isolated after proof of depth-one Schatten-wall classification.
