# Almost every height of a short window is nearly Weil-positive

- **ID:** almost-every-height-nearly-weil-positive
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Source:** walls ledger 3.14 ("Average to selected heights … Need: a selection theorem"); B1.4
  ("from averaged or almost-all-height statements to every height"); summary §4.5 "short-window
  selection lemmas from density information to individual heights".
- **Statement.** Let `Φ(γ) = Σ_q (Re q − 1/2)²/(1 + (Im q − γ)²)²` over the zero copies (`Φ ≡ 0` under RH).
  1. For every `A ≥ 0`, real `F₀ ∈ C²_c([−A,A])` and `γ ∈ ℝ`:
     `Q(F₀ cos γ·) + Q(F₀ sin γ·) ≥ −4(A+1)² e^A N(F₀)² Φ(γ)`.
  2. There are `C, Γ₀` with: for `Γ ≥ Γ₀`, `Γ^{99/100} ≤ H ≤ Γ/8`, `η > 0`,
     `|{γ ∈ [Γ, Γ+H] : Φ(γ) > η}| ≤ C H/(η log Γ)`.
  Hence outside a set of measure `C H/(η log Γ)` every height of the window has
  `Q_γ(F₀) ≥ −4η(A+1)² e^A N(F₀)²` for all apertures and all tests at once.

## Lean
`formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/AlmostEveryHeightIsNearlyWeilPositive.lean`:
`norm_depthDiff_le_depth`, `neg_offLineField_le_fullZeroForm`, `exists_window_sum_sq_depth_le`,
`exists_volume_offLineField_gt_le`, `exists_shortWindow_almostEvery_height_nearly_positive`.
Axioms: `propext`, `Classical.choice`, `Quot.sound`. Wired into `ArithmeticCastelnuovoSeveri.lean`.

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  fully-proven
- [x] 2 → 3  formalized

## Proof
1. **Depth difference.** With `z = x − iδ` (`x = Im ρ − γ`, `δ = Re ρ − 1/2`),
   `F̂(z) − F̂(z̄) = ∫ F₀(u) e^{ixu}(e^{δu} − e^{−δu}) du`, so `|F̂(z) − F̂(z̄)| ≤ 2|δ|A e^{|δ|A}‖F₀‖₁`
   (`|e^y − e^{−y}| ≤ 2|y|e^{|y|}`). Two integrations by parts give `(F₀'')^(w) = −w² F̂(w)`, hence
   `z²(F̂(z) − F̂(z̄)) = −((F₀'')^(z) − (F₀'')^(z̄)) + (z̄² − z²)F̂(z̄)`, `|z̄² − z²| = 4|x||δ|`,
   `|F̂(z̄)| ≤ e^{|δ|A}N/(1+x²)`. Since `|z|² ≥ x²` and `|x|/(1+x²) ≤ 1/2`:
   `(1+x²)|F̂(z) − F̂(z̄)| ≤ 4(A+1)|δ|e^{A/2}N`.
2. **Pointwise law.** `Re W(F₀e^{iγ·}) ≥ −Σ_ρ m_ρ |F̂(z_ρ) − F̂(z̄_ρ)|²/4` (the quadrature inequality with
   no zeros kept), and step 1 bounds each term by `4(A+1)² e^A N² δ_ρ²/(1+x_ρ²)²`.
3. **Squared depths near a window.** For copies with ordinates in `[Γ−H, Γ+2H]`: those with
   `δ ≤ 4800/log Γ` number `≤ 3H log Γ` and contribute `≤ 3·4800² H/log Γ`; the deeper ones satisfy
   `δ² ≤ 2e^{λδL}/(λL)²` with `λ = 1/19200`, `L = log 3Γ`, and Selberg's weighted near-line density on
   the window `[Γ−H−2, Γ+2H+2]` gives `Σ e^{λδL} = O(H log Γ + Γ^{3/4})`. Total `O(H/log Γ)`.
4. **Window average.** On `[Γ, Γ+H]`, `Φ ≤ Ψ := Σ_{local} δ_q²/(1+(Im q−γ)²) + 2(c + log(2Γ+4))/H²`
   (remote copies: `(1+x²)^{−2} ≤ H^{−2}(1+x²)^{−1}` and the Lorentzian mass is `≤ 8(c + log(|γ|+4))`).
   `∫_window Ψ ≤ π Σ_{local} δ² + 2(c + log(2Γ+4))/H ≤ (πC₃ + 1)H/log Γ`. Markov's inequality for the
   continuous `Ψ` bounds `|{Φ > η}|`.

## Scope
Near-positivity, not positivity: a lower bound `Q_γ ≥ 0` at a selected height needs the critical mass
near `γ`, which depends on how zero ordinates sit relative to `|F̂₀|²`. The exceptional set is
independent of the aperture and of the test.

## Subsumed
In the only aperture range where this bound yields positivity, `(A + 1)² e^A ≪ log Γ`, the
single-height law `zetaZeroConfig_re_W_heightShift_nonneg_of_sharp_horizon` already gives
`Q_γ(F₀) ≥ 0` at every height `log(1 + γ/8) ≥ C + (4 + ε)e^A + 2` for every test (tail conditions
aside). Not a contribution to the selection obstacle, which lives at logarithmic aperture.
