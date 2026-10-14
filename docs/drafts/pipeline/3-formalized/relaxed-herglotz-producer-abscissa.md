# Relaxed Herglotz producers and the producer abscissa

- **ID:** RHP-ABSCISSA
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** loop rows 1180–1183 (`1-in-progress/rh-goal-loop-opus-2026-09-29.md`); STATUS MUST-1436, MUST-1442 (+add.)
- **Statement:** RH holds iff every half-plane `Re s > σ₀` with `σ₀ > ½` carries a Herglotz producer with `|lam(n)| ≤ log n`. None exists left of `½`, and `Λ` is one on `Re s > 1`.

## Goal
- Turn the producer (existence) half of the HF route into a ζ-free problem with slack.
- Uniqueness at `σ₀ = ½` (MUST-1433/1436) is used only in the limit.
- The producer abscissa `σ* ∈ [½, 1]` is ζ-free, and RH ⟺ `σ* = ½`.

## Gates
- [x] 0 → 1  in-progress: well-posed; Herglotz form of the Weil function; compactness idea.
- [x] 1 → 2  fully-proven: Tychonoff + dominated convergence + Harnack + Vitali + uniqueness; Carlson floor + log growth of the archimedean symbol.
- [x] 2 → 3  formalized:
  - `RHTower.AtomDomination.herglotzProducer_eq_vonMangoldt`
  - `RHTower.AtomDomination.riemannHypothesis_iff_exists_herglotzProducer`
  - `RHTower.RelaxedHerglotz.riemannHypothesis_iff_forall_herglotzProducerOn`
  - `RHTower.RelaxedHerglotz.riemannHypothesis_iff_forall_gt_half_herglotzProducerOn`
  - `RHTower.RelaxedHerglotz.not_isHerglotzProducerOn_of_lt_half`
  - `RHTower.RelaxedHerglotz.herglotzProducerOn_one_vonMangoldt`
  - `RHTower.RelaxedHerglotz.exists_herglotzProducerOn_one_and_floor`
  - `RHTower.RelaxedHerglotz.exists_herglotzProducerOn_of_forall_gt` (closedness of producer levels)
  - `RHTower.RelaxedHerglotz.producerAbscissa_mem_producerLevels`, `riemannHypothesis_iff_producerAbscissa_eq_half`
  - `RHTower.RelaxedHerglotz.abs_sub_vonMangoldt_lt_of_isHerglotzProducerOn` (relaxed producers converge to Λ; MUST-1452), `isHerglotzProducerOn_of_tendsto` (sequential closedness)
  - `RHTower.RelaxedHerglotz.exists_not_isHerglotzProducerOn_trivialWeights`, `exists_tendsto_LSeries_sub_le_of_isHerglotzProducerOn` (constant-term ceiling; MUST-1448 add.)
  - All have standard axioms. Modules: `RHTower/HerglotzProducerUniquenessUnconditional`, `RHTower/RelaxedHerglotzProducerCompactness`, `RHTower/RelaxedHerglotzProducerFloor`.
- [ ] 3 → 4  publication-ready.

## Approach
- **Definition.** `IsHerglotzProducerOn σ₀ lam`: the Weil function `Φ_lam(s) = ½ψ(s/2) − ½log π + 1/s + 1/(s−1) − Σ_{n≥2} lam(n)n^{−s}` has a holomorphic continuation with `Re ≥ 0` to `Re s > σ₀`.
  - For `σ₀ < 1`: the Dirichlet series has one simple pole (residue 1) at `s = 1`, and `Re D_lam ≤ Re(archimedean symbol)`.
  - Equivalently, `|s(s−1)Γ_ℝ(s)exp(Σ lam(n)n^{−s}/log n)|` is nondecreasing in `σ`.
- **Compactness (⟸).**
  - Weights lie in `∏[−log n, log n]`; Tychonoff gives a pointwise limit.
  - `Φ_k` converge on `Re s > 1` by dominated convergence.
  - Harnack on discs centred two units to the right gives local bounds on `Re s > ½ + 1/(m+2)`.
  - Vitali on each such half-plane; the limit is Herglotz on `Re s > ½`.
  - Uniqueness gives `Λ` and RH.
- **Floor.**
  - `‖½ψ(s/2) − ½log π + 1/s + 1/(s−1)‖ ≤ 6 log Im s` on `0 < Re s ≤ 3`, `Im s ≥ 4`.
  - The corpus Carlson floor then excludes producers left of `½`.
- **Right of the strip.** `ξ′/ξ` has `Re ≥ 0` on `Re s ≥ 1` (corpus), and equals `Φ_Λ` on `Re s > 1`.

## Findings beyond the theorem (paper, rows 1181–1183)
- Under RH the relaxed cones are fat: `Λ` plus small finitely supported perturbations.
- A fixed weight `≠ Λ` cannot be a producer for every `δ`, so relaxed families converge to `Λ`.
- Constructing relaxed producers at small `δ` is again uniform local exclusion:
  - truncations of `Λ` see off-line zeros;
  - pole-cancelling corrections are almost periodic and `O(1)` at low heights, where the margin is `≍ δ`.
- Multiplicative weights (`ζ − 1`) fail through Bohr–Montgomery large values. Prime-supported weights are additive.
  - Prime-gap weights `g(p) = p⁺ − p` are holomorphic to `Re s > 0.525`.
  - Their one-sided bound needs power-saving prime-sum cancellation, i.e. quasi-RH-strength input.
- Chaos heuristic: in the Bohr lift, a degree-`d` component has sup `≈ (log T)^{d(1−σ)}`. So producers on `Re s > σ₀` with `σ₀ < 1 − 1/d` cannot carry degree-`≥ d` components. Near `½`, the multiplicative structure must be degree `≤ 2` (heuristic, not proved).

## Log
- 2026-10-14 — created directly in 3-formalized (MUST-1436, MUST-1442 and addendum).
- 2026-10-14 — pole-weight rigidity: every Herglotz datum with pole weight β has β = 1 (`eq_one_of_herglotz_poleWeightFunction`). β ≤ 1 comes from the density ceiling plus Abel; β > 0 from the Fejér window; linear deviation from the rescaled summatory law; then MUST-1445. Module `RHTower/WeilPoleWeightAtMostOne`.
- 2026-10-14 — stability of uniqueness: producers on Re s > ½ + δ converge to Λ as δ → 0 (MUST-1452); trivial weights excluded at every level ≤ 1 by the constant term at s = 1 (MUST-1448 add.).
- 2026-10-14 — closedness of producer levels; `producerAbscissa` attained in [½, 1]; RH ⟺ `producerAbscissa = ½` (MUST-1442 add. 2).
- 2026-10-14 — row 1203 [L] MUST-1463: the pole-weight theorem in Weil form. W_β-positive for some real lam (no growth hypothesis) ⟹ β = 1 (`RHTower.eq_one_of_weilPositiveAt`). Bridge `RHTower/WeilPoleShiftHerglotzBridge`; corollaries in `RHTower/WeilPoleWeightForcedOne`. Row 1202: off-line zeros cannot amplify blind violations (exponent β − 1 < 0), so F(1) = −∞ could only come from critical-line large values of Re ζ.
