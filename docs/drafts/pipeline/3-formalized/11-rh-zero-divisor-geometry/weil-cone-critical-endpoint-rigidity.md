# Weil-cone rigidity at the critical endpoint `s = 1` (log-weighted absolute summability)

- **ID:** weil-cone-critical-endpoint
- **Stage:** 3-formalized (MUST-580)
- **Source:** MC conjecture loop, cycle 170. It extends MUST-576 (`3-formalized/11-rh-zero-divisor-geometry/weil-cone-abscissa-below-one-rigidity.md`).
- **Conjecture 170.** Let `lam` be full-cone Weil-positive with `Σ_n |lam(n) − Λ(n)| (1 + log n)² / n < ∞`. Then `lam = Λ`. In `v`-form: for `Σ_n |v(n)|(1 + log n)² n^{−1/2} < ∞`, `v(0) = v(1) = 0`, `|v| ≤ 2 log n + A` and `−ψ_v` PD, we get `v = 0`.

## Phase 1–2 (corpus audit, 2026-09-30)

**The Λ-size core.**
- HF's `krein-producer-loops` L140–L174 reduce every remaining producer candidate beyond Λ to Conjecture Ω:
  - statement: an integer Dirichlet series with residue-1 pole at `1`, continuous boundary on `σ = ½`, has `ess sup (Re A − ½ log t) = +∞`;
  - or its partial-atom version.
- Every linear identity is blind to atoms. Resonance at length `T^θ` gives only `(θ/2) log T` against the ceiling `½ log T`, which is the `α ≥ 1` wall.

**Absolute versus conditional abscissa.**
- Under RH every point of the cone has deviation of *conditional* abscissa `≤ ½`, by the Herglotz continuation of `A_lam` to `σ > ½`.
- MUST-576 is the *absolute* version with threshold `1`.
- The whole remaining (P2) core is therefore the gap between conditional `½` and absolute `1`.

**This cycle.** It closes the absolute side up to the endpoint `s = 1`, with a log² weight. That is the natural limit of the notch method.

## Phase 4 (kill attempt): SURVIVES PRELIMINARY ATTACK

The endpoint obstructions of MUST-576 (`η = 0`) are all removable.

1. **Pairing strip.**
   - Test `G = Ω q (2/(1+z²))² Γℝ(½+iz)^{−1} Γℝ(½−iz)^{−1}`. The double poles at `±i/2` are replaced by poles at `±i`, so `G` is holomorphic in `|Im z| < 1`.
   - Hence `𝓕g = O(e^{−¾|y|})`, and Fubini needs only `Σ|v| n^{−3/4}`.
   - Moment: `Ξ² g = Ω q r̃ |ζ|²` with `r̃ = ((¼+t²)/(1+t²))²`.
2. **Tail.** `r̃` has double zeros at `±i/2`, which cancel the simple poles of `ζ(½+iz)ζ(½−iz)` at `∓i/2`. So the moment is holomorphic in `|Im z| < 1` and `M♯(log n) = O(L^c n^{−c})` for every `c < 1`. Note `∫Ω = O(1)`.
3. **Window correction.** `M♯ = M_Ω − M_{Ω s̃}` with `s̃ = 1 − r̃ ≤ C/t²`.
   - By monotonicity, `|M_{Ω s̃}(log n)| ≤ ∫Ω s̃ q |ζ|² ≲ log L / L²`, uniformly in `n`.
   - Summed over `n ≤ N₁ ≈ L^{2+}` against `Σ_{n≤N}|v| ≤ √N S`, this is negligible.
4. **Near-resonance at `a = ½`.**
   - `L·nearMass ≤ C δ L² n^{−1/2}` (`mul_nearMass_mode_le` holds at `a = ½`).
   - With `δ = (log L)^{1/2}/L` this gives `o(L log L)`.
5. **Non-resonance with `n`-decay.**
   - Direct terms: dyadic detuning shells with `nearMass` at scales `2^j δ` give `C δ k L² √(k/h) (Lδ)^{−K} ∝ n^{−1/2}`.
   - Dual pairs with `ab ≥ L`: same bound.
   - Dual pairs with `ab < L`, `Δ ∈ [δ, 1/8]`: the right-line one-power bound `‖J − ω̂‖ ≤ C Y^{1/4} L^{−1/2}/Δ`, plus counting near-line small pairs.
     - The singleton part is `≤ 4 δ^{−1} √(k/h)`.
     - The dense part is `≤ C L^{1/2} log L`, only for `n ≤ K₀ L`.
     - Summed with the `(1+log n)²` weight, this is `O(L S₂ / log L)`.
   - Far pairs: dual-line `K`-fold, `L^{2−K}`, uniform in `n`.
6. **Diagonal.** `L(1+log n) n^{−1/2}` summed gives `L S₁ = o(L log L)`.

**Reach.** Rigidity for every deviation absolutely summable against `(log n)²/n`. The complement, `Σ|dev|(log n)²/n = ∞`, contains every `Λ`-comparable deviation (`(1−r)Λ + rC`, character twists, evaporation profiles). This is the HF core.

**Significance (honest).** The theorem closes the notch method; it does not reach the core. No known natural candidate lies in the newly covered band between `s < 1` and the log²-weighted endpoint.

## Lean programme
- E1 dyadic detuning sum (`nearMass` shells);
- E2 refined direct off-diagonal;
- E3 refined dual off-diagonal (right-line one-power bound for small pairs, near-line small-pair counting);
- E4 twisted-moment remainder and envelope at `a = ½`;
- E5 analytic: `r̃`-test pairing, holomorphic tail, `Ω s̃` correction;
- E6 assembly (reuse `eq_zero_of_forall_mainWeight_nonpos`).

## Log
- 2026-09-30 — created (cycle 170).

## Refined statement (proof gives one log, not two)
- **Theorem 170.** Let `lam` be full-cone Weil-positive with `Σ_n |lam(n) − Λ(n)| (1 + log n)/n < ∞`. Then `lam = Λ` on `n ≥ 2`.
- `v`-form: if `v(0) = v(1) = 0`, `|v| ≤ 2 log n + A`, `S₁ = Σ_n |v(n)| (1 + log n) n^{−1/2} < ∞` and `−ψ_v` is PD, then `v = 0`.
- **Why one log suffices.**
  - Use the resonance width `δ = 1/u` at scale `u`. Every off-diagonal term is then `O(u n^{−1/2})`.
  - The near-line small dual pairs are the only exception: they cost `O(u^{1/2} log u)` for `n < 2K₀³u`. The inequality `√n log X ≤ 4√X (1 + log n)` for `n ≤ X` absorbs them into `u (1 + log n) n^{−1/2}`.
  - The double pole of the test at `±i/2` gives `𝓕g = O((1+|w|) e^{−|w|/2})`. So the pairing also needs exactly `S₁`.
  - `(1 + log n)` is the diagonal's own weight: the `log(hk)` term of the twisted second moment.

## Phase 5 — paper proof (dependency-closed)
1. **Fibre reduction** (MUST-571, `eq_zero_of_forall_mainWeight_nonpos`).
   - It suffices to show `Y = Σ_n v(n) mainWeight_{P,ε,n₀}(n) ≤ 0`.
   - This must hold for `P = primes ≤ y`, `2 ≤ n₀ ≤ y` and `ε = ±1`. It uses `Σ|v| n^{−1/2} ≤ S₁`.
2. **Endpoint envelope** (E1–E4).
   - **Claim.** For `u ≥ 16` and `n ≥ 1`: `|M_u(log n) − mainWeight(n) e_P ∫ ω_u log t| ≤ D (u (1 + log n) n^{−1/2} + U(u))`, where `U(u) = u^{5/2}((u/8)^{−7} + e^{−u²/128}) + u² e^{−u²/32}`.
   - **Twist level.** twisted moment `−` diagonal `=` direct `+` dual `−` residue.
     - Direct part: `≤ C(L𝒩 + L Σ far)`.
     - Dual part: `≤ C(L𝒩 + L Σ far + L^{−1/4} Σ small + L^{5/2} T_K)`, using the swap symmetry.
     - Detuning shells: `Σ far ≤ 64 δ k L √(2k/h) (Lδ)^{−K} + ζ₂ L^{3/4}(L/8)^{−K}`.
     - Small pairs: `Σ small ≤ 48 k L^{3/4} J(δ)` with `J ≤ 2 log L` when `δ ≥ 1/L`. The sum vanishes for `h ≥ 2kL`.
   - **Modes.**
     - `k ≤ K₀`, `n ≤ K₀ h k` and `√(2k/h) ≤ 2K₀² n^{−1/2}`.
     - In the range `n < 2K₀³L` where small pairs exist: `L^{1/2} log L ≤ 8K₀² L (1 + log n) n^{−1/2}`.
3. **Pairing** (E5a).
   - On `|Im z| = ½ − η`: `|(2/(¼+z²))²| ≤ 16/(x² + η²)`, and the line mass of this bound is `16π/η`.
   - Shift to that line with `η = 1/(4 + |w|)`. This gives `|∫ G e^{−iwx}| ≤ B (1 + |w|) e^{−|w|/2}`. Negative `w` follows by conjugation, since `G` is real on `ℝ`.
   - Kernel smoothing: `∫ K(v−c)(1+|v|)e^{−b|v|} ≤ C (1+|c|) e^{−b|c|}`.
   - Fubini then applies under `S₁`. The spectral identity gives `Σ v Re M_Ω(log n) = −π ∫ G dσ ≤ 0`.
4. **Tail** (E5b).
   - In `s = ½ + iz`, shift `Re s = ½ → 3/2` across the simple pole of `ζ(s)` at `1`. The residue is `Ω_L(−i/2) Q(−i/2) ζ(0) e^{−y/2}`, with `|Ω_L(−i/2)| ≤ 4e`.
   - On the new line: `|ζ(3/2+it)| ≤ ζ(3/2)` and `|ζ(−½+it)| ≤ 6(1+|t|)(4+|t|)`.
   - Result: `|M_Ω(y)| ≤ C₁(1+L²) e^{−y} + C₂ e^{−y/2}`.
5. **Assembly** (E6), with `N = ⌈(1+L)⁴⌉`.
   - Pairing plus tail: `Σ_{n≤N} v Re M_Ω ≤ (C₁ + C₂) S₀`.
   - Scale split plus the per-scale bound: `Σ_{n≤N} v Re M_Ω ≥ Y_N e_P 2e^{−1} log(L−1) − D errConst(S₁, CU·T_N, L, 4) gaussHalf − small`.
     - Here `T_N ≤ N S₁` and `U(u)/u ≤ CU u^{−5}`.
     - The subtracted terms are bounded uniformly in `L`.
   - `Y ≤ Y_N + 3√n₀ Σ_{n>N} |v| n^{−1/2}`, and this tail tends to `0`.
   - The scale-family lemma with a vanishing tail gives `Y ≤ 0`. ∎

## Lean (formalized 2026-09-30)
Audit:
- Every module compiles clean under `lake env lean`.
- The final build ran with `lake build --old`.
- `#print axioms` (scratch file) reports only `propext`, `Classical.choice`, `Quot.sound`.
- All modules are wired into `RHTower.lean` after `WeilAbscissaRigidity`.
- The `.ilean` collision sweep found no clashes.

New modules (`formal/GaloisForLFunctions/RHTower/`):
- `ZetaNotchDetuningShells`: dyadic detuning shells; `tsum_farWeight_le`.
- `ZetaNotchOffDiagonalShells`:
  - `exists_norm_directOff_le_far` and `exists_norm_dualOff_le_far`;
  - the swap symmetries;
  - `smallWeight_eq_zero_of_le`, `shell_count_le_log`, `tsum_smallWeight_le`.
- `ZetaNotchCriticalEnvelope`:
  - `sqrt_mul_log_le` and `exists_norm_twistedMoment_sub_diag_le_shell`;
  - `shellEnvelope` and `shellEnvelope_mode_le`;
  - `critWeight` and `exists_norm_weightedMoment_sub_mainWeight_le_crit`.
- `ZetaNotchCriticalPairing`:
  - `norm_two_div_quarter_add_sq_sq_le` and `exists_norm_mixTest_le_near_pole`;
  - `exists_norm_integral_mixTest_mul_cexp_le`, giving `(1+|w|)e^{−|w|/2}`;
  - `sum_mul_re_mixMoment_nonpos_crit`.
- `ZetaNotchCriticalTail`: `mixTailIntegrand` and `exists_norm_mixMoment_le_crit`, via the residue shift past `s = 1`.
- `WeilCriticalEndpointRigidity`:
  - `exists_critUniform_le`, `critErrSum`, `setIntegral_critErrSum_le`;
  - `pairing_tail_crit`, `mainWeight_tail_crit`, `exists_scale_bound_crit`;
  - the theorems.

Refactors (generic cores, cycle-169 results re-derived from them):
- `WeilNullPotentialExpPairing`:
  - `nullPotential_pairing_eq_integral_of_smoothing` (abstract kernel-smoothing weight);
  - `integral_riemannAutocorr_mul_le_linexp`;
  - the `…_linexp` pairing forms.
- `ZetaNotchAnalyticPairing`: `sum_mul_re_mixMoment_nonpos_of_pairing` and `continuous_mixTest_ofReal`.
- `ZetaNotchDecayingEnvelope`:
  - `exists_norm_twistedMoment_sub_logWindow_le`;
  - `norm_weightedMoment_sub_main_le_of_twist`;
  - the mode lemmas `natCast_le_twistBound_mul_mode` and `sqrt_two_mul_div_mode_le`.
- `WeilAbscissaScaleBounds`: `sum_re_weightedMoment_ge_of_norm_le`.
- `WeilAbscissaRigidity`:
  - `scaleWeight_mul_inv_pow_le` and `exists_sum_re_mixMoment_ge_of`;
  - `nonpos_of_scale_family_tendsto`, which takes a vanishing truncation tail.

## Significance (Phase 7 input)
- The notch method is now closed on the absolute side, at its natural endpoint `Σ|dev|(1+log n)/n < ∞`.
- The weight `(1 + log n)` cannot be dropped with these tools. It is the diagonal's own `log(hk)` main-term weight. The pairing requires the same weight because of the test's double pole.
- What remains for (P2) is the region `Σ|dev|(1+log n)/n = ∞`. This contains every `Λ`-comparable deviation, which is HF's Conjecture Ω.

## Superseded (cycle 171)
- MUST-584 removes the logarithm: `Σ|lam − Λ|/n < ∞ ⇒ lam = Λ`. See `weil-cone-absolute-convergence-rigidity.md`.
- The "Significance" claim above, that the `(1 + log n)` weight is intrinsic, is wrong.
  - The errors only need to be `o(log L)`, and under `Σ|v|n^{−1/2} < ∞` the weighted partial sums are `o(log N)`.
  - A pairing test with the Gamma-weight poles at `±2i` needs only `Σ|v|n^{−3/4}`.
