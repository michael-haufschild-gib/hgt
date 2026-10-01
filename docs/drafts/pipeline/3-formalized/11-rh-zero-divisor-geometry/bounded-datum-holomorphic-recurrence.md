# Bounded data carry no pole, for every coefficient class

- **ID:** MC-193
- **Stage:** 3-formalized (STATUS MUST-632)
- **Type:** THEOREM (Lean)
- **Source:** MC loop cycle 193. It closes the Lean hypothesis gap that the HF producer log (L244) recorded for `not_tendsto_lseries_atTop_of_bounded_datum` (L240). L244 proposed Bohr's uniform-convergence theorem; this proof avoids it.
- **Statement.**
  - Hypotheses: `a : ℕ → ℝ` with `Σ|a(n)|n^{−v} < ∞`; `L` holomorphic on `Re s > 1` with `L = Σ a(n)n^{−s}` on `Re s > v`; and `Re L(s) ≤ C + Re 1/(s−1)` on `Re s > 1`.
  - Conclusion: `Re L(σ) ≤ C` for all `σ > 1` (`re_le_of_bounded_datum_holomorphic`).
  - Hence `Re L(σ) ↛ +∞` as `σ → 1⁺` (`not_tendsto_re_atTop_of_bounded_datum_holomorphic`).

## Proof
1. **Uniform recurrence of absolutely convergent Dirichlet series** (`exists_large_lseries_shift_near`). Truncate at `N` with tail `≤ ε/4`. A simultaneous almost period for `log 2, …, log N` (`exists_large_simultaneous_almostPeriod`) gives `‖L(s+it) − L(s)‖ ≤ ε` uniformly on `Re s ≥ u`, at `t` beyond any threshold.
2. **Three lines** (`exists_large_shift_near_of_bounded`). `D_t(s) = G(s+it) − G(s)` is holomorphic on the strip `l ≤ Re s ≤ u`, with `|D_t| ≤ 2B` on the strip and `≤ η` on `Re s = u`. Hadamard (mathlib `norm_le_interp_of_mem_verticalClosedStrip'`) gives `|D_t(σ₁)| ≤ (2B)^{1−θ}η^θ ≤ ε`.
3. **Application to `G = e^L`.**
   - `|G| = e^{Re L} ≤ e^{C + 1/(l−1)}` on `Re s ≥ l`.
   - On the far line `G(s+it) − G(s) = G(s)(e^{L(s+it)−L(s)} − 1)` is small.
   - At large heights `|G(σ₁+it)| ≤ e^{C + (σ₁−1)/t²}`, while `|G(σ₁)| = e^{Re L(σ₁)}`, and recurrence brings `G(σ₁+it)` close to `G(σ₁)`.

## Lean
- Module `RHTower/BoundedDatumHolomorphicRecurrence.lean` (353 lines). Imports `HTGeometry/BohrFiniteRecurrence` and mathlib (`LSeries`, `Complex.Hadamard`).
- Audit:
  - standard axioms;
  - collision scan clean;
  - wired after `WeilBoundedDatumPoleObstruction` in `RHTower.lean`.
- Note: the olean of `WeilBoundedDatumPoleObstruction` was missing locally. This module does not import it; it only extends its namespace.

## Novelty / significance (honest)
- **Mathematics.** Classical in spirit: Bohr's recurrence for bounded Dirichlet series via three lines.
- **Corpus.** It upgrades L240's exclusion (no Gamma-free producer carries the pole) from coefficient classes with `σ_a ≤ 1` to all Dirichlet series that converge absolutely somewhere. That includes every Weil-positive system, by the box bound, once the Herglotz continuation of `L` to `Re s > 1` is available.
- **Frontier.** This is construction-side exclusion only. Existence for ζ's datum (PBAP) is unchanged.
