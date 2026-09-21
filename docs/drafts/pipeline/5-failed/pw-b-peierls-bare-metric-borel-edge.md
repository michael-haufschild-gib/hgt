# PW-B bare Peierls metric / Borel-edge identification

- **ID:** pw-b-peierls-bare-metric-borel-edge
- **Stage:** 5-failed
- **Type:** FALSIFIED
- **Source:** `docs/drafts/pipeline/1-in-progress/rh-current-frontier-map.md` · PW-B / B2 ordered target
- **Statement:** Literal Peierls metric square coefficient cannot itself be any natural-grade PW Borel recoil edge, although damping-shifted branches exactly realize `q ↔ 1-q`.

## Goal

Close spectral-coordinate premise of literal ordered Peierls-to-PW bridge and test strongest direct coefficient identification without hiding a contact normalization.

## Gates

- [x] 0 → 1 in-progress: literal physical rates, PW Borel edge, and Xi divisor nonreality identified from source modules.
- [x] 1 → 2 fully-proven: exact shifted-rate functional-equation pair and bare-coefficient obstruction dependency-closed.
- [ ] 2 → 3 formalized audit: direct Lean check and axiom audit green; leaf OLean audit remains pending under no-long-build rule.
- [ ] 3 → 4 publication-ready: not applicable to retired bare-coefficient subroute.

## Approach

Literal rates are `r₊=q−2` and `r₋=−q−1`, so `(r₊+2,r₋+2)=(q,1−q)`. Thus every literal source pair labels exact PW forward/reverse Borel edges. Bare square-metric numerator is `(q−2)(q−3)`. Equating it to `(q+2k)(q+2k+1)` leaves `(4k+6) Im(q)=0`, contradicting nonreality of each Xi-divisor support point.

## No-go closure

- **Exact killing theorem/mechanism:** `d4BMPeierlsMetricSquareNumerator_ne_forwardBorelEdge` rules out direct bare metric coefficient as PW recoil edge for every `k : Nat` and actual `XiZeroCopy`.
- **Strongest positive survivor:** `d4BMPeierlsFunctionalEquationPair_eq_xi_reflected` and `d4BMPeierlsFunctionalEquationPair_borelEdge` give literal all-grade source realization of PW spectral labels `(q,1−q)`. Coordinate/pairing premise is discharged.
- **New insight:** Remaining PW-B seam is not a spectral-coordinate problem. It is a coefficient-transmutation problem: exchange-odd contact including lift defect must correct displayed natural-grade mismatch. This does not revive B2 as RH producer; it supplies its previously missing direct PW spectral bridge.
- **Status:** Paper proof is expansion of physical rates and imaginary parts of two quadratics. Lean module `formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingParikhWilczekLiteralPeierlsSpectralBridge.lean`; direct `lake env lean` passed and `#print axioms` reports only `propext`, `Classical.choice`, `Quot.sound`. Leaf `lake build` remains deferred because targeted builds replay thousands of unrelated dependencies.

## Log

- 2026-09-21 — literal Peierls spectral pairing discharged; bare metric/Borel coefficient identification retired.
