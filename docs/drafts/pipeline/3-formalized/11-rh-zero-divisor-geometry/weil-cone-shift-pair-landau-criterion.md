# Shift-pair Weil positivity of Λ is equivalent to RH

- **ID:** MC-WEIL-SHIFT-PAIR-LANDAU
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** MC conjecture loop, cycle 164 (`1-in-progress/mc-conjecture-loop-2026-09-28.md`). It builds on the shift pairs of `weil-cone-window-pinning.md`.
- **Statement.** Let `g ≥ 0` be a real `C²` bump supported in `[−¼, ¼]` with `∫g ≠ 0`, and put `g_λ(u) = g(u/λ)`. Then RH holds iff `Re W_Λ(k) ≥ 0` for the autocorrelation `k` of every two-bump test `g_λ + g_λ(· − L)`, with `½ ≤ λ ≤ 1` and `L > 0`.
- **Single-bump form.** For one fixed `g`, positivity on `g + g(· − L)` for all `L > 0` forces `ρ̃_g(ρ − ½) = 0` at every zero `ρ` of `ζ` with `Re ρ > ½`. Here `ρ̃_g(z) = ∫ρ_g(v)e^{zv}dv` and `ρ_g` is the autocorrelation of `g`.

## Goal
- **Thin test family.** Weil's criterion asks for positivity on all of `C_c^2`. For `Λ`, a two-parameter family of two-bump tests suffices, and only the `σ = +1` half of the window pinning is used.
- **Relation to the Weil cone.** For `Λ`, the upper window bound `S_L(Λ) ≤ P₊P₋(e^{L/2} + e^{−L/2}) + C` already carries all of RH. The lower bound is not needed.
- **Survivor question for (P2).** The cone `C_sp` of `lam` that are positive only on shift pairs is much larger than `C`. What singles out `Λ` inside `C_sp` is the analytic continuation of its Dirichlet series. A general `lam` has none.

## Paper proof
1. **Upper window bound.** Positivity on `g + g(·−L)` gives `S(L) ≤ M(L) := P₊P₋(e^{L/2} + e^{−L/2}) + C`, with `C = 2P₊P₋ + 2∫|ρ̂μ|`. This is the pole and archimedean bound of the window-pinning card.
2. **Laplace transform.** `S(L) = Σ_{n≥2} Λ(n)(ρ(log n − L) + ρ(log n + L))/√n`. For `L > 0` only `ρ(log n − L)` survives, since `log 2 > ½`. Tonelli then gives `∫_0^∞ S e^{−σL} = ρ̃(σ) Σ Λ(n) n^{−½−σ} = −ρ̃(σ) ζ'/ζ(σ + ½)` for `σ > ½`.
3. **Landau measure.** `ν = (M − S)dL|_{(0,∞)} + dL` is a positive measure.
   - For real `σ > ½` its transform is `Φ(σ) = −(ρ̃(σ) − ρ̃(½))/(σ − ½) + P₊P₋/(σ + ½) + (C + 1)/σ + ρ̃(σ) ζ_u'/ζ_u(σ + ½)`, with `ζ_u = (s − 1)ζ`.
   - The pole at `½` cancels because `ρ̃(½) = P₊P₋`, by Fubini: `ρ̃(σ) = ∫g e^{−σu} · ∫g e^{σu}`.
   - `Φ` is analytic at every real `z > 0`. Landau's theorem therefore puts the abscissa at `0`.
4. **Residue.** Put `A = transform − (analytic terms)`. Then `ζ_u(z + ½)A(z) − ρ̃(z)ζ_u'(z + ½)` is analytic on `Re z > 0` and vanishes for real `z > ½`, so it vanishes identically.
   - At a zero `ρ` of multiplicity `m`, `(s − ρ)ζ_u'/ζ_u(s) → m`, while `(s − ρ)A(s − ½) → 0`.
   - Hence `m ρ̃(ρ − ½) = 0`.
5. **Dilations.** `ρ_{g_λ}(v) = λρ_g(v/λ)`, so `ρ̃_{g_λ}(z) = λ²ρ̃_g(λz)`.
   - An off-line zero makes `ρ̃_g` vanish on `[½, 1](ρ − ½)`, a segment with an accumulation point.
   - `ρ̃_g` is entire, so it would vanish identically. But `ρ̃_g(0) = (∫g)² ≠ 0`.
6. **Converse.** RH ⇒ `Λ` is Weil-positive on all tests.

## Novelty audit
- **Verdict: BRIDGE.**
  - The analytic engine is Landau's oscillation theorem (Landau 1905; Ingham, Ch. V): a one-sided `O(x^{1/2})` bound on `ψ(x) − x` is equivalent to RH.
  - What is new is the Weil-functional form: an explicit two-parameter family of two-bump tests carries all of Weil positivity for `Λ`.
- **Relation to Li's criterion.** Li's criterion is also a thin family (countable), but its tests are not compactly supported.
- **Compact-window results.** These results (Yoshida; Connes–Consani; arXiv 2608.24827) give positivity on a fixed window and do not reach RH. The shift-pair family has unbounded support.
- **Corpus.** The unsmoothed Chebyshev version is `RHTower.riemannHypothesis_of_logChebyshevDeficitPrimitive_ge`; this card smooths it and puts it in Weil-cone language.

## Lean
- `formal/GaloisForLFunctions/RHTower/WeilShiftPairLandau.lean` (namespace `RHTower.WeilOneSided`).
  - Capstones: `riemannHypothesis_iff_dilatedShiftPair_nonneg`, `riemannHypothesis_iff_dilatedShiftPair_narrowG` (concrete bump, hypothesis-free), `autoLaplace_eq_zero_of_shiftPair_nonneg`, `autoLaplace_eq_zero_of_primeWindow_le`.
  - Pieces: `integral_primeWindow_mul_exp` (Tonelli), `tsum_vonMangoldt_rpow_eq`, `autoLaplaceReal_eq` (Fubini), `laplaceReal_shiftMeasure_eq`, `abscissa_shiftMeasure_eq_zero`, `autoLaplace_dilateBump`.
- Wired into `RHTower.lean` after `WeilFullConeCompactness`. `#print axioms`: `propext, Classical.choice, Quot.sound`. The ilean sweep found no collisions.

## Log
- 2026-09-30 — created at stage 3 (MC cycle 164). The paper proof and the Lean proof were done together.
