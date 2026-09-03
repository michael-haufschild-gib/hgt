# Completed cubic Green first-prime tail is strictly subunit

- **ID:** CCM-ROUTEP-CUBIC-COMPLETED-TAIL-SUBUNIT
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** Runpod audit of retired pre-divisor relative-projection route
- **Statement:** Above `log 2`, the signed scalar sum of Route-P open prime tail, literal CCM
  Gamma tail, and negative CCM polar tail has absolute value strictly below `1`.

## Goal

Extract strongest dependency-closed positive statement exposed by failed relative-projection
route. Result must preserve literal prime, polar, and Gamma source coefficients. It must not be
misread as trace-norm estimate or source-to-Xi index landing.

## Gates

- [x] 0 → 1 in-progress: source-pure definitions and exact coefficient normalization identified
- [x] 1 → 2 fully-proven: complete proof below, `[PROVED HERE]`, no open dependency
- [x] 2 → 3 formalized: Lean theorem `RHTower.abs_ccmRoutePCompletedCubicGreenTail_lt_one`;
  targeted module build and axiom audit pass
- [ ] 3 → 4 publication-ready: standalone exposition and external novelty audit

## Definitions

Let `L = log 2` and let common Green profile be

```text
F(h) = exp(-h/2) / (4 h^3),       h > L.
```

Literal source densities reduce to

```text
Gamma(h) = exp(-h) / (4 h^3 (1-exp(-2h))),
Polar(h) = (1+exp(-h)) / (4 h^3).
```

Let `B` be full primitive Route-P base cubic trace budget and `a₂` its natural-number atom at
`2`. Define

```text
P_open = B - a₂,
G = integral_(L,infinity) Gamma(h) dh,
Q = integral_(L,infinity) Polar(h) dh,
C = P_open - Q + G.
```

## Proof

`[PROVED HERE]`

1. For `h > L`, `exp(-h) ≤ 1/2`, hence `exp(-2h)=exp(-h)^2 ≤ 1/4` and
   `1-exp(-2h) ≥ 3/4`. Therefore

   ```text
   0 ≤ Gamma(h) ≤ (1/6) h^-3,
   0 ≤ Polar(h) ≤ (3/8) h^-3.
   ```

2. Existing inverse-power integration gives

   ```text
   integral_(L,infinity) h^-3 dh = 1/(2L^2).
   ```

   Existing exact bound `2/3 < log 2` implies `L^-2 < 9/4`. Thus

   ```text
   0 ≤ G < (1/6)(1/2)(9/4) = 3/16,
   0 ≤ Q < (3/8)(1/2)(9/4) = 27/64 < 1.
   ```

3. Direct unfolding of von Mangoldt and Route-P normalizations gives

   ```text
   a₂ = 1/(8 L^2).
   ```

   Mathlib's exact certified rational upper bound
   `log 2 < 0.6931471808` implies `L^2 < 2/3`; consequently `a₂ > 3/16 > G`.

4. Every natural-number Route-P weight is nonnegative and summable, so `0 ≤ P_open`. Existing
   unconditional arithmetic theorem gives `B < 1`. Hence

   ```text
   P_open + G = B - a₂ + G < B < 1.
   ```

5. Since `Q < 1` and `P_open,G ≥ 0`, `-1 < P_open-Q+G`. Since `Q ≥ 0` and
   `P_open+G < 1`, `P_open-Q+G < 1`. Therefore `|C| < 1`.

No premise, hypothesis, axiom, zero assumption, or numerical computation enters theorem.

## Lean certificate

- Module:
  `GaloisForLFunctions.RHTower.CCMRoutePCompletedCubicGreenTailSubunit`
- Main theorem:
  `RHTower.abs_ccmRoutePCompletedCubicGreenTail_lt_one`
- Supporting locks formalize:
  source-to-explicit Gamma and polar identities; nonnegativity; inverse-cube majorants;
  integrability; `G < 3/16`; `Q < 1`; exact first atom; first-atom lower bound; open-prime
  nonnegativity.

## Interpretation boundary

This theorem preserves signed scalar cancellation before absolute value. It does **not** prove
`‖T‖₁ < 1` for any operator. Lifting it to a trace-class operator requires a coefficient-faithful
nuclear factorization whose nuclear norm retains prime-polar-Gamma cancellation, plus an
independent source-to-Xi essential-codimension landing. Neither follows from scalar theorem.

## Log

- 2026-09-03 — Runpod finite-window audit discovered Gamma-completed scalar survivor.
- 2026-09-03 — paper proof closed and formalized in Lean without premises or new axioms; moved
  directly through stages 2 and 3.
