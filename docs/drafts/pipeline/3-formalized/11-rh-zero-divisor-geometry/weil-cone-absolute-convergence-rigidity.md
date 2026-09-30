# Weil-cone rigidity under absolute convergence at `s = 1`

- **ID:** weil-cone-absolute-convergence
- **Stage:** 3-formalized (MUST-584)
- **Source:** MC conjecture loop, cycle 171. It supersedes MUST-580 (`weil-cone-critical-endpoint-rigidity.md`).
- **Theorem.** Let `lam` be full-cone Weil-positive with `Σ_n |lam(n) − Λ(n)|/n < ∞`. Then `lam = Λ`.
  - `v`-form: if `v(0) = v(1) = 0`, `|v| ≤ 2 log n + A`, `Σ|v(n)| n^{−1/2} < ∞` and `±ψ_v` is PD, then `v = 0`.

## Phase 1–4
- **Starting point.** After MUST-580 I claimed (cycle-170 Phase 7) that the weight `(1 + log n)` is intrinsic to the notch: it is the diagonal `log(hk)` term, and the pairing needs it because of the double pole.
- **The claim was wrong.**
  - *Diagonal.* Under `Σ|v|n^{−1/2} < ∞`, the diagonal error `Σ_{n≤N}|v|(1+log n)n^{−1/2}` is `o(log N)`: split at a fixed `K` with a small tail. The main term is `≍ log L`. So the weight costs nothing as long as the error only has to be `o(log L)` rather than bounded.
  - *Pairing.* Moving the Gamma-weight poles from `±i/2` to `±2i` removes the double pole. The pairing then needs only `Σ|v|n^{−3/4}`.
- **Before settling on this target, two Ω-level attacks were tried and killed** (details in the loop card, row 171):
  1. A resonator-density rigidity (every cone point has zero density on multiples of each prime), via `|ζ|²`-notch resonators. **KILLED.** The twisted second moment's kernel `log(u/n)` is not localized: contributions from `n ∈ [u, u²]` are of the same order for `Λ`-size deviations. An exact prime-deficit balance at the pinning level cancels the `(log log)²` main term.
  2. `C ≠ ∅ ⇒ RH` via prime-blind tests (autocorrelations vanishing at all `±log n`). **KILLED.**
     - Two-bump and comb tests gain `e^{δY}` from an off-line zero `½ + δ + iγ₀`.
     - To avoid the dense set `log n` near height `Y`, the resolution must be `≤ e^{−Y}`. That costs `e^{Y}·Y` on the on-line zero sum.
     - Detection would need `δ > 1`. This is the `α ≥ 1` wall once more.
- **Verdict.** The weight-removal statement SURVIVES. It is the sharp absolute endpoint: absolute convergence of the deviation series at the pole `s = 1`.

## Phase 5 — paper proof
1. **Fibre reduction** (MUST-571). It suffices to show `Y = Σ v·mainWeight ≤ 0` for all `(P, ε, n₀)`, given `Σ|v|n^{−1/2} < ∞`.
2. **Pairing** (`sum_mul_re_shiftMoment_nonpos`).
   - The test is `G = Ω_L Q (2/(4+z²))² Γℝ(½+iz)^{−1}Γℝ(½−iz)^{−1}`. It is holomorphic on `|Im z| < 2` and `O(e^{−|Re z|})` on `|Im z| ≤ 3/4`. So `𝓕g = O(e^{−3|w|/4})`.
   - The exponential pairing of MUST-576 needs `Σ|v|n^{−3/4} ≤ Σ|v|n^{−1/2} < ∞`.
   - `Ξ²G = Ω q r |ζ|²` with `r = ((¼+t²)/(4+t²))² ≥ 0`, and `G ≥ 0` on ℝ. Hence `Σ_n v(n) Re M_r(log n) ≤ 0`.
3. **Tail** (`exists_norm_shiftMoment_le`).
   - The residue shift `Re s = ½ → 3/2` uses a multiplier `R` holomorphic and bounded by `1` on `−1 ≤ Im z ≤ 0`. The residue is `∝ R(−i/2) = r(−i/2) = 0`.
   - On the new line: `|ζ(3/2+it)| ≤ ζ(3/2)`, `|ζ(−½−it)| ≤ K(1+|t|)`, and `∫Ω_L(x)(1+|x|)dx ≤ C(1+L)`.
   - Result: `‖M_r(y)‖ ≤ C(1+L)e^{−y}`.
4. **Defect** (`exists_norm_defectMoment_le`).
   - `M_r = M_Ω − M_{1−r}`.
   - Pointwise: `|Ω q (1−r)|ζ|²| ≤ Ω_L(t)·C_Q·(15/2)/(4+t²)·36(|t|+3) ≤ 540 C_Q Ω_L(t)/(1+|t|)`.
   - With `∫Ω_L/(1+|x|) ≤ C/(2+L)`, this gives `‖M_{1−r}‖ ≤ C/(2+L)` for all `y`.
5. **Assembly** (`exists_scale_bound_abs`), with `N = ⌈(1+L)²⌉`:
   - Upper bound for the notch sum:
     - `Σ_{n≤N} v Re M_Ω = Σ_{n≤N} v Re M_r + Σ_{n≤N} v Re M_{1−r}`;
     - the first part is `≤ C(1+L)N^{−1/2}T_N ≤ C T_N` (pairing plus tail);
     - the second part is `≤ C·TF_N/(2+L)`.
   - Lower bound for the same sum:
     - the endpoint envelope (MUST-580) and the generic mixed-moment lower bound give `≥ Y_N e_P 2e^{−1}log(L−1) − D·errConst(SF_N, CU·TF_N, L, 4)·gaussHalf − TF_N·small`.
   - Error sizes:
     - `SF_N ≤ (1+log K)S₀ + (1+log N)T_K` and `TF_N ≤ √K S₀ + √N T_K`;
     - every coefficient of `TF_N` is `O(1/(1+L))`.
   - Conclusion: `Y_N e_P 2e^{−1}log(L−1) ≤ A + B((1+log K)S₀ + (1+log N)T_K + √K S₀ + T_K + T_N)`.
6. **Relative scale family** (`nonpos_of_scale_family_relative`).
   - Given `η`, choose `K` with `16 B T_K ≤ η`. Then `B(1+log N)T_K ≤ (η/4)log(L−1)`, and the `K`-dependent constants are `≤ (η/2)log(L−1)` for large `L`.
   - `Y ≤ Y_N + 3√n₀ T_N` with `T_N → 0`. Hence `Y ≤ 0`. ∎

## Lean (formalized 2026-09-30)
Audit: every module compiles clean under `lake env lean`, the final build used `lake build --old`, `#print axioms` reports the standard three, the modules are wired into `RHTower.lean`, and the `.ilean` collision sweep is clean.
- `ZetaNotchMixtureMoments`:
  - `integral_Ioi_mixWindowReal_mul_real`;
  - `exists_integral_mixWindowReal_mul_one_add_le`, giving `C(1+L)`;
  - `exists_integral_mixWindowReal_div_one_add_le`, giving `C/(2+L)`.
- `ZetaNotchCriticalTail`, refactored:
  - `weightedTailIntegrand` and `exists_norm_weightedMixMoment_le` (general multiplier, linear in `L`);
  - `exists_norm_riemannZeta_neg_half_le`;
  - the old `exists_norm_mixMoment_le_crit` is now a corollary.
- `ZetaNotchShiftedPoleTest`:
  - `shiftFactorC`, `shiftWeightC`, `shiftTest`, `shiftMoment`, `defectMoment`;
  - `sum_mul_re_shiftMoment_nonpos`, `shiftMoment_eq_sub`, `norm_zetaSq_le_linear`;
  - `exists_norm_defectMoment_le`, `exists_norm_shiftMoment_le`.
- `WeilAbsoluteConvergenceRigidity`:
  - `sum_range_abs_le_split`, `sum_range_weight_le_split`;
  - `nonpos_of_scale_family_relative`, `exists_scale_bound_abs`;
  - the theorems.

## Significance
- The absolute side of (P2) is now closed exactly, with no log loss. Every second cone point has `Σ|lam − Λ|/n = ∞`: its deviation Dirichlet series diverges absolutely at `s = 1`, the abscissa of the pole.
- The remaining (P2) class consists of deviations whose Dirichlet series diverges absolutely at `s = 1`. It contains all `Λ`-comparable deviations, i.e. HF's Conjecture Ω.
- Structural lesson. The `|ζ|²`-notch errors never needed to be bounded, only `o(log L)`. The logarithmic loss of MUST-580 was an artifact of demanding bounded errors.
