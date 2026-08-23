# CGL safe-line exponential tail

- **ID:** CGL-SAFE-LINE-EXP-TAIL
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** Chen–Gupta–Li §12.1 · `rh-current-frontier-map.md`
- **Statement:** The CGL left safe-line Mellin integrand has an explicit two-sided exponential tail, strong enough at the source cutoff `|v| ≥ log² T` once its Dirichlet-L strip constant is made polynomial in conductor and height.

## Goal

Replace the corpus's qualitative `K → ∞` truncation with a quantitative bound at the exact CGL cutoff. This discharges the analytic tail independently of zero-density input; the remaining uniformity obligation must be exposed as an explicit conductor-dependent L-bound rather than hidden in compactness.

## Gates

- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [ ] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3  formalized: Lean theorem, targeted check green, new declarations axiom-audited
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Approach

For `w = (1/2-β)+iv`, combine four already formalized factors:

1. `(Y+1)^Re(w) ≤ 1` for `1/2 < β < 1`;
2. the closed mollifier bound `‖M_X‖ ≤ X+1`;
3. uniform Gamma decay on `Re(w) ∈ [-1/2,0]`;
4. cubic strip growth of `L(1/2+i(γ+v),χ)`.

This gives `A(X+1)(5+|γ|)^3 |v|^N exp(-π|v|/2)` for `|v| ≥ 1`. Absorb the polynomial into half the Gamma exponent, integrate both rays exactly, and specialize to `B = log² T`. Then audit dependence of `A` on `χ`: current `bound_LFunction_strip` produces an existential character-dependent constant, so source-uniform closure requires building an explicit conductor-polynomial replacement.

## Current conjecture

**CGL-SAFE-TAIL-1.** For every certified primitive nonprincipal row, there is `A>0` such that for every `B≥1`, the norm of each exterior safe-line integral is bounded by

`A (X+1) (5+|γ|)^3 exp(-π B/4)`.

The exponent and cutoff are uniform in `β`; only the present L-strip constant can depend opaquely on `χ`.

## Log

- 2026-08-23 — Opened after formal closure of the exact `Y log²Y` coefficient tail. Located reusable Gamma-strip, cubic L-strip, mollifier, polynomial-absorption, and Laplace-tail lemmas. Fixed-row rate under attack; conductor-uniformity isolated as next hard core.
