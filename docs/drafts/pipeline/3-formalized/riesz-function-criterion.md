# Riesz's criterion and the Riesz exponent law

- **ID:** riesz-criterion
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** RH goal loop cycle 267 (MUST-769)
- **Statement:** `Θ = 2·inf{b : F(x) = O(x^b)}` for `F(x) = Σ_{k≥1}(−1)^{k+1}x^k/((k−1)!ζ(2k))`; RH ⟺ `F(x) = O(x^{1/4+ε})` for every `ε > 0`.

## Goal
Formalize Riesz's 1916 criterion with its exact exponent law, unconditionally, and record the
lower bound `F ≠ O(x^b)` for `b < ¼`.

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  fully-proven
- [x] 2 → 3  formalized: `RHTower.riemannHypothesis_iff_rieszPowerSeries_le`,
  `zetaZeroAbscissa_eq_two_mul_sInf_rieszFunction_exponents`; `lake build --old` green; axioms
  `[propext, Classical.choice, Quot.sound]`.
- [ ] 3 → 4  (no manuscripts by directive)

## Approach
- Power series: `F(x) = xR(x)`, `R(x) = Σμ(n)n^{−2}e^{−x/n²}` (swap of an absolutely summable double
  series; `Σμ(n)n^{−2k−2} = 1/ζ(2k+2)`), `rieszFunction_eq_tsum`.
- Mellin: `∫_0^∞R(t)t^{s−1}dt = Γ(s)Σμ(n)n^{2s−2}` on `0<Re s<½` (termwise Gamma integrals,
  `integral_tsum_of_summable_integral_norm`), `mellin_rieszSeries`.
- Lower half: `|R(x)| ≤ Cx^{−β}` ⇒ Mellin holomorphic on `0<Re s<β` ⇒ identity
  `mellin R · (w−1)ζ(w) = Γ(s)(1−2s)` (`w = 2−2s`) continues; a zero `ρ`, `Re ρ > 2−2β`, kills it at
  `s = 1−ρ/2`. Gives `Θ ≤ 2b` from `F = O(x^b)`.
- Upper half: Abel summation with `|M(N)| ≤ C(N+1)^a`; weight increments
  `|h(1/n²) − h(1/(n+1)²)| ≤ 3·128^θ x^{−2θ} n^{4θ−3}` from `|ue^{−xu} − ve^{−xv}| ≤ (u−v)(1+xv)e^{−xv}`
  and `(1+y)e^{−y} ≤ 8^θ y^{−2θ}`; choose `θ = (2−a−δ)/4` so the `n`-sum is `Σn^{−1−δ}`.

## No-go closure (mandatory when falsified)
Not a no-go. Lane note: a receiver of Mertens cancellation (no new source). Its Ω± refinement
(one-sided `±F ≤ cx^{1/4}` ⇒ RH + simple zeros) is the natural next cycle.

## Log
- 2026-10-05 — created and formalized (RieszFunctionMellinCriterion, RieszFunctionExponentLaw).
- 2026-10-05 — Ω± refinement formalized (MUST-770, RieszFunctionQuarterPowerOmega): `F = Ω±(x^{1/4})`; one-sided quarter-power bound ⇒ RH + simple critical zeros + residue bound.
- 2026-10-05 — companion Hardy–Littlewood criterion formalized (MUST-775): HardyLittlewoodMellinCriterion, HardyLittlewoodExponentLaw.
