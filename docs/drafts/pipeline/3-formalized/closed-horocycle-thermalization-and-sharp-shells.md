# Closed horocycle thermalization, zero-free strips, and sharp shells

- **ID:** closed-horocycle-thermalization-and-sharp-shells
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean verified)
- **Source:** ../../../reports/review-0811/obstacles-summary.md · §2.7 Q2, §2.10 Q2, CountingHolography README §12.4
- **Statement:** No exponent above `3/4` works for all smooth profiles or for any single sharp shell `1 < a < b`; every smooth profile thermalizes unconditionally at stretched-exponential super-square-root rate `O(y^{1/2} exp(-√(-log y)))` (hence `O(y^{1/2} (-log y)^{-A})` for all `A` and `o(y^{1/2})`); every sharp shell thermalizes unconditionally at log-free `O(y^{1/2})`; and the RH rate `O_ε(y^{3/4 - ε})` for sharp shells holds if and only if `RiemannHypothesis` holds together with `O_ε(X^{1/2 + ε})` Möbius × circle-problem cancellation.

## Gates
- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3  formalized: Lean module `CountingHolography/ClosedHorocycleThermalizationAndSharpShells.lean`, `lake --old env lean` green, `#print axioms` PASS

## Exact result

1. **Unconditional `y^{3/4}` ceiling (`δ ≤ 1/4`) for both smooth profiles and single sharp shells.**
   - There is no `α > 3/4` for which every `φ ∈ C_c^∞((1, ∞))` satisfies `horocycleMean (pseudoEisenstein φ) y - (6/π) mellin φ (-1) = O(y^α)`. Equivalently, power saving `y^{1/2 + δ}` fails unconditionally for every `δ > 1/4`, while for `0 < δ ≤ 1/4` the family of rates `O_ε(y^{1/2+δ-ε})` is equivalent to the zero-free strip `Re ρ ≤ 1 - 2δ` (`zeroFreeStrip_iff_fareyCount_rate`).
   - For **any single sharp shell** `1 < a < b`, if `horocycleMean (shellCount a b) y - (6/π)(1/a - 1/b) = O(y^α)` (`1/2 < α < 1`), then `Re s₀ ≤ 2 - 2α` for every zero `s₀` of `ζ` in `0 < Re s₀ < 1`. In particular, no single sharp shell `1 < a < b` can thermalize at `O(y^α)` for any `α > 3/4`.
2. **Unconditional super-square-root thermalization for smooth profiles.**
   For every smooth `ψ : ℝ → ℂ` compactly supported in `(1, ∞)` (and hence every `φ ∈ C_c^∞((1, ∞))` in `fareyCount φ y`), there exists `C > 0` such that for all `0 < y ≤ 1`:
   `‖horocycleMean (pseudoEisenstein ψ) y - (6/π) mellin ψ (-1)‖ ≤ C · y^{1/2} · exp(-√(-log y))`.
   Consequently, smooth horocycles satisfy the exact `O(y^{1/2})` bound on `(0, 1]` (removing the `-ε` loss of `horocycle_rate`), beat `y^{1/2}` unconditionally by `(-log y)^{-A}` for every `A ∈ ℕ`, and satisfy `(horocycleMean (pseudoEisenstein ψ) y - (6/π) mellin ψ (-1)) / y^{1/2} → 0` as `y → 0⁺`.
3. **Unconditional log-free `O(y^{1/2})` rate for sharp shells.**
   - Every quarter-disc lattice remainder `E(Y) = quarterDisc Y - π Y²/4 + Y/2` (`Y ≥ 0`) satisfies `|E(Y)| ≤ 8 √Y`.
   - Every horoball profile `H(X) = horoballSum X ⌊X⌋₊` (`X ≥ 1`) satisfies `|H(X) - 3/(2π) X²| ≤ 19 X`.
   - Every sharp shell `1 < a < b` satisfies `‖horocycleMean (shellCount a b) y - (6/π)(1/a - 1/b)‖ ≤ 76 (√(y/a) + √(y/b))` for all `0 < y ≤ 1/b`, removing the `log(1/y)` loss of `shell_rate`.
4. **Exact characterization of the RH rate for sharp shells.**
   - `H(X) - 3/(2π) X² = O_ε(X^{1/2 + ε})` for every `ε > 0` holds **if and only if** `RiemannHypothesis` holds **and** for every `ε > 0`, `∑_{d=1}^{⌊X⌋₊} μ(d) E(X/d) = O(X^{1/2 + ε})`.
   - For **any fixed** `1 < a < b`, `horocycleMean (shellCount a b) y - (6/π)(1/a - 1/b) = O_ε(y^{3/4 - ε})` holds **if and only if the same RH and Möbius–circle condition holds**. Consequently, one shell's RH rate implies every shell's RH rate; the obstruction is independent of endpoints.

## Proof

1. A zeta zero `ρ` with positive real part produces a scattering pole at `s=ρ/2`. The rate converse for smooth profiles gives `Re ρ ≤ 2-2α`. For a fixed sharp shell, continuous trapezoidal approximants pass the horocycle Mellin identity to its indicator by dominated convergence. Its Mellin transform at `-s` is `(a^{-s}-b^{-s})/s`, nonzero for `Re s>0` because `a^{-Re s}>b^{-Re s}`. Analytic continuation of the centered Mellin integral therefore gives the same bound on every zero. Hardy's zero on `Re ρ=1/2` rules out `α>3/4`.
2. Mellin inversion expresses the centered mean through `regularPart ψ`. Polynomial bounds for `1/ζ` on `Re s ≥ 1` and rapid Mellin decay permit a global contour shift to `Re w = -1/2`. The Vinogradov–Korobov zero-free rectangle permits a further finite shift to `Re w = -1/2-d(T)`. For `L=-log y`, choose `T=exp(c√L)`, with fixed sufficiently small `c>0`, and enough Mellin derivatives. The bound `d(T) ≫ 1/log T` absorbs the polynomial contour cost; rapid vertical decay controls the tails and horizontal edges. Each contribution is `O(y^{1/2} exp(-√L))`. A fixed lower bound on `y` handles the remaining compact interval. Multiplying by `L^A` gives every logarithmic saving, and the normalized error tends to zero.
3. For `Y ≥ 2` and `N = ⌊Y⌋₊ - 1`, on each `[k, k+1]` (`0 ≤ k < N`), `f(x) = √(Y² - x²)` is `C¹` with antitone derivative `f'(x) = -x/√(Y² - x²)`. Integration by parts gives `|(f(k) + f(k+1))/2 - ∫_k^{k+1} f| = |∫_k^{k+1} (x - k - 1/2)(f'(x) - f'(k)) dx| ≤ (f'(k) - f'(k+1))/2`. Telescoping over `0 ≤ k < N` bounds the `[0, N]` trapezoidal discrepancy by `-f'(N)/2 = N / (2√(Y² - N²)) ≤ Y / (2√(2Y - 1)) ≤ √Y`, while the `[N, Y]` boundary terms contribute `≤ 7 √Y`, giving `|E(Y)| ≤ 8 √Y` (and for `0 ≤ Y < 2`, `|E(Y)| ≤ 3Y/2 ≤ 3√Y`). Inserting `|E(X/d)| ≤ 8√(X/d)` (`∑_{d ≤ X} d^{-1/2} ≤ 2√X`), `|∑_{d ≤ X} μ(d)/d| ≤ 1` (`abs_sum_moebius_div_le_one`), and `|∑_{d ≤ X} μ(d)/d² - 6/π²| ≤ 1/⌊X⌋ ≤ 2/X` into `horoballSum_decomposition` gives `|H(X) - 3/(2π) X²| ≤ (2 + 1 + 16) X = 19 X`.
4. Under `RiemannHypothesis`, `mobiusMertensAllStrictHalfPowerBound_iff_riemannHypothesis` gives `M(N) = O_ε(N^{1/2 + ε})`. By `deningerHarmonicPartial_eq_mertens_boundary_sub_tail` (`∑_{n=1}^∞ μ(n)/n = 0`), `|∑_{d ≤ X} μ(d)/d| = O_ε(X^{-1/2 + ε})`, and Abel summation of `∑_{d > X} μ(d)/d²` against `M(N)` gives `|∑_{d ≤ X} μ(d)/d² - 6/π²| = O_ε(X^{-3/2 + ε})`. Hence in `horoballSum_decomposition`, both arithmetic main-term remainders `(π/4) X² (∑_{d ≤ X} μ(d)/d² - 6/π²)` and `-(X/2) ∑_{d ≤ X} μ(d)/d` are `O_ε(X^{1/2 + ε})` under RH. Thus `H(X) - 3/(2π) X² = O_ε(X^{1/2 + ε})` iff RH holds (forced by `re_le_of_single_shell_rate` on `shellCount 2 3`) and `∑_{d ≤ X} μ(d) E(X/d) = O_ε(X^{1/2 + ε})`.
5. Write `R(X)=H(X)-3X²/(2π)` and `r=√(a/b)∈(0,1)`. The unconditional shell limit identifies its centering constant. Substituting `y=1/(aX²)` in a single shell's RH rate bounds `R(X)-R(rX)` by `O_ε(X^{1/2+ε})`. Telescope down to the first `r^K X<1`; the geometric sum converges and the terminal remainder is bounded. This recovers the full horoball RH rate. Conversely, the horoball rate applied at `(ay)^{-1/2}` and `(by)^{-1/2}` gives the shell rate. Thus the previous equivalence applies to every fixed shell.

## No-go closure
- **Exact killing theorem/mechanism:** Hardy's critical-line zero (`exists_xi_zero_on_line`) plus nonvanishing of `(a^{-s} - b^{-s})/s` on `Re s > 0` (`not_horocycle_rate_gt_three_quarters`, `not_single_shell_rate_gt_three_quarters`) kills every power rate `y^{1/2 + δ}` with `δ > 1/4` even for a single sharp shell.
- **Strongest positive survivor:** Unconditional stretched-exponential super-square-root rate `O(y^{1/2} exp(-√(-log y)))` for all smooth profiles (`horocycle_rate_stretched_exp`), unconditional log-free `O(y^{1/2})` rate for all sharp shells (`shell_rate_sqrt`), and exact unconditional equivalences `horoball_rh_rate_iff_rh_and_moebius_circle` and `single_shell_rh_rate_iff_rh_and_moebius_circle`.
- **New insight:** Smooth horocycles unconditionally thermalize strictly faster than `y^{1/2}` (at rate `y^{1/2} exp(-√(-log y))`), whereas sharp shells achieve `O(y^{1/2})` unconditionally via concavity cancellation `|E(Y)| ≤ 8√Y` + bounded harmonic Möbius sums `|∑ μ(d)/d| ≤ 1`, and separate at the RH threshold `y^{3/4 - ε}` solely through the Möbius-twisted circle remainder `∑_{d ≤ X} μ(d) E(X/d)` because RH already pushes both `(π/4) X² (∑ μ(d)/d² - 6/π²)` and `(X/2) ∑ μ(d)/d` down to `O_ε(X^{1/2 + ε})`.
- **Status:** Paper proof and Lean formalization complete in `CountingHolography/ClosedHorocycleThermalizationAndSharpShells.lean`.

## Verification

`lake --old env lean` exits 0 with no output. All 23 audited declarations depend only on `propext`, `Classical.choice`, and `Quot.sound`; temporary audit commands removed. No proof placeholders or raised limits.

## Lean declarations

Module: [ClosedHorocycleThermalizationAndSharpShells.lean](../../../../formal/GaloisForLFunctions/CountingHolography/ClosedHorocycleThermalizationAndSharpShells.lean). Namespace: `GaloisForLFunctions.CountingHolography`.

| Result | Declarations |
|---|---|
| Exponent ceiling | `not_horocycle_rate_gt_three_quarters`, `not_fareyCount_rate_gt_three_quarters`, `not_horocycle_power_saving_gt_quarter`, `not_single_shell_rate_gt_three_quarters` |
| Smooth rates and corollaries | `horocycle_rate_stretched_exp`, `fareyCount_rate_stretched_exp`, `horocycle_rate_sqrt_exact`, `horocycle_rate_log_pow`, `horocycle_div_sqrt_tendsto_zero` |
| Explicit sharp bounds | `abs_circleRemainder_le_sqrt`, `abs_horoballSum_sub_le_linear`, `shell_rate_sqrt` |
| Single-shell converse | `mellin_shell_ne_zero`, `re_le_of_single_shell_rate`, `riemannHypothesis_of_single_shell_rate` |
| Exact remaining condition | `moebius_harmonic_and_sq_tail_of_rh`, `horoball_rh_rate_iff_rh_and_moebius_circle`, `single_shell_rh_rate_iff_rh_and_moebius_circle` |
