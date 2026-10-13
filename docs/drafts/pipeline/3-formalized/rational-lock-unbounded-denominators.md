# Rational almost-periodic locks with unbounded denominators (C2112)

- **ID:** rational-lock-unbounded-denominators
- **Stage:** 1-in-progress
- **Type:** CONJECTURE (paper plan; Lean not started)
- **Source:** Opus loop rows 2092–2106 (C2112); STATUS MUST-1246, 1247, 1310, 1315, 1322, 1327; this card was opened at loop row 1135.
- **Statement:** Let `G` be a Herglotz producer (hypotheses as in `AbelianTwist.bounded_denominator_lock_riemannHypothesis`). Suppose that on the lower critical line `G(1−s) = V(s)G(s)` with `V(s) = Σ_j c_j u_j^{−(s−½)}`, the `u_j` distinct positive rationals, and `Σ_j |c_j| max(1, 1/u_j) den(u_j)^{½+ε} < ∞`. Then RH.

## What is already closed (do not redo)
- Irrational frequencies, two-sided and unbounded: `integer_resonant_lock_rigidity`, `aggregated_resonant_lock_rigidity`. The Abel spectrum of non-rational frequencies vanishes.
- One-sided rational spectra: MUST-1246.
- Bounded spectra (any reals): MUST-1247.
- Bounded denominators, two-sided: MUST-1322 (periodic coefficients) and MUST-1327 (RH).
- Open: two-sided rational spectra with unbounded denominators. This card.

## Paper plan
1. **Period law.** For rational `x > 0`, `L(x) := √x Σ_n a(n)n^{−½}R(x/n)` is the radial limit at height `x`, where `R(r) = Σ_{u_j=r} c_j` (`tendsto_far_real_height` with `P = 0`), and `L(x+1) = L(x)` (`tendsto_far_translation`). So `L` lives on `ℚ/ℤ`.
2. **Hurwitz identity.** For `1 < Re s ≤ 3/2`, `Σ_{x∈ℚ₊} L(x)x^{−s} = F(s)V(s) = Σ_{x₀∈ℚ∩(0,1]} L(x₀)ζ(s, x₀)`. Absolute convergence: `Σ_{x₀}|L(x₀)| x₀^{−σ}` is controlled by `Σ_j|c_j| max(1,1/u_j)` and `Σ|a(n)|n^{−σ}`.
3. **Continuation to the line.** Uniformly in `a ∈ (0,1]`: `|ζ(s,a) − a^{−s} − (1+a)^{1−s}/(s−1)| ≤ ½ + |s|/(2σ)` (first-order Euler–Maclaurin), and `|E_{b/q}(w)| ≪ q^{1−Re w}(log q + C(w))` for the periodic zeta `E_x(w) = Σ e(nx)n^{−w}`, via `E_{b/q} = q^{−w}Σ_{j≤q} e(jb/q)ζ(w, j/q)`. At `Re w = ½` this is the `den^{½+ε}` weight. No Gauss-sum cancellation is needed.
4. **Functional equation and uniqueness**, as in MUST-1322, steps 3–5:
   - On the upper line, `G(w) = w(w−1)Γ_ℝ(1−w)(2π)^{−w}Γ(w)Σ_{x₀} L(x₀)(e^{−πiw/2}E_{x₀}(w) + e^{πiw/2}E_{−x₀}(w))`.
   - Extend to the quadrant (`eq_zero_of_vertical_halfLine`).
   - On `Re w > 1`, `e^{πiw}(F − B) = A − F` with `A = Σ_n P̂(n)n^{−w}`, `B = Σ_n P̂(−n)n^{−w}`, `P̂(n) = Σ_{x₀} L(x₀)e(nx₀)`.
   - Hence `a(n) = P̂(n)`: the coefficients are limit-periodic, with absolutely summable Fourier mass.
5. **Single character for limit-periodic Dirichlet exponentials.** This is the new core.
   - Expand `e(nb/q)` into characters of all moduli `q/d`, `d | q`. The character mass is `≤ τ(q)√q` per point (Gauss sums), hence summable under the weight.
   - Plant a zero with two characters, as in `exists_charProduct_zero`, robustly enough that the tail of large moduli (mass `→ 0`) cannot remove it (Rouché or sphere domination with a margin).
   - Conclude a single character, then run the MUST-1327 endgame: `G(1) ≠ 0` ⇒ the character is principal ⇒ RH.

## Risks
- Step 5 is a Saias–Weingartner-type theorem for limit-periodic coefficients. It may need more than summable character mass, e.g. a uniform zero-planting margin. Test first on two moduli `q₁ ≠ q₂` with infinitely many small perturbations.
- Step 3 needs Hurwitz bounds uniform in `a`. Check Mathlib (`HurwitzZeta`) for an Euler–Maclaurin form before proving one.

## Lean modules (planned)
- M1 `WeilRationalLockHurwitzIdentity` (steps 1–2).
- M2 `HTGeometry/HurwitzZetaUniformStripBound` (step 3).
- M3 `WeilRationalLockFourierCoefficients` (step 4).
- M4 `LimitPeriodicExpSingleCharacter` (step 5).
- M5 `WeilRationalLockRiemannHypothesis`.

## Log
- 2026-10-13 — card opened; irrational and mixed parts confirmed closed in the corpus; plan recorded.

## Step 5 core: resolved in Lean (Opus loop row 1146; MUST-1381 [L])
- `RHTower/CharacterProductZeroPlantingTwoLevel` (`exists_twoLevel_charProduct_zero`). The planting threshold `η` depends only on the level-`N` model, not on the large level `N'`.
  - Characters mod `N'` that do not factor through `N` see a fibre-pulled-back model vector with pairing exactly `0`, so the band between the two cutoffs costs only its coefficient mass.
  - The tail beyond `N'` costs `2e^{K}·mass`, with `K` fixed before `N'` is chosen.
- The risk recorded above ("dual-vector norm grows like `φ(N_Q)`") is gone. To use the lemma for step 5:
  1. pick `N` from the coefficient tail (`Σ_{cond ∤ N}|C| ≤ |C(χ₁)|/96`);
  2. obtain `η`;
  3. pick `N'` with `Σ_{cond ∤ N'}|C| ≤ η`;
  4. collect the band characters as `D` and the remaining characters as the far family.
- Remaining for step 5: the character expansion of a limit-periodic `a` (additive characters `e(nb/q)` into Dirichlet characters via Gauss sums, with smooth parts) and the Bohr-lift identity. Steps 1–4 are unchanged.

## Merged (2026-10-13)
This card duplicates `unbounded-denominator-lock-closure.md` (row 2106), which predates it. Its "risk" section was wrong: `Σ_{others} v_χ` has `ℓ¹` norm `≤ 3` at every level, so `K` is uniform without a two-level argument. Continue work on the row-2106 card. The Lean infrastructure from MUST-1381 is recorded there.
- 2026-10-13 — **Superseded.** This card duplicates `3-formalized/unbounded-denominator-lock-closure.md` (C2112). C2112 is closed in Lean as `rationalLock_riemannHypothesis` (MUST-1388). Kept only for its log.
