# Source-Side Farey–Hecke Operator Algebra, Three-Term Cusp-Erasure Obstruction, and Dyadic Cusp-Energy Separation

- **ID:** source-side-farey-hecke-commutator-and-dyadic-cusp-separation
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** [obstacles-summary.md](../../../reports/review-0211/obstacles-summary.md) (§2.6.2) · [route-pm-mayer-scattering-and-escape.md](../1-in-progress/route-pm-mayer-scattering-and-escape.md) (Mayer 4)
- **Statement:** On the canonical `s`-independent Hilbert space `H_LP = L²((0, ∞), w_LP(a) da)` (`w_LP(a) = (a + a⁻¹)^(-6) a^(-1/2)`), (1) `(I_s† I_s f)(a) = a^(4 Re s - 1) f(a)` and `I_s` is norm-bounded iff `Re s = 1/4`; (2) the Gauss–Mayer renewal head branch `(G_{0,s} f)(a) = a^(-2s) f(1 + a⁻¹)` (`Re s ≥ 0`) is bounded iff `Re s ≤ 1/4` (while every tail branch `m ≥ 1` is bounded across `Re s ≥ 0`, and `(G_{0,s}, G_{0,1/2 - conj s})` is simultaneously bounded on `0 ≤ Re s ≤ 1/2` iff `Re s = 1/4`); (3) the Farey–Lewis three-term operator `M_s = U_1 + V_s` is bounded across `Re s ≥ 0` with disjoint-half-line Koopman adjoints `U_1†` on `(1, ∞)` and `V_s†` on `(0, 1)`, cross-annihilation `U_1 V_s† = V_s U_1† = 0`, diagonal co-square `(M_s M_s† g)(a) = μ_s(a) g(a)` satisfying `μ_s(a) > 1` on `(0, ∞)` for `Re s ≤ 1/2`, strict self-commutator negativity `⟨[M_s†, M_s]ψ, ψ⟩_LP < 0` on every nonzero continuous three-term fixed point `ψ ∈ H_LP`, and universal Manin–Mühlenbruch Hecke intertwining `I_s T_{2,s} = T_{2,s} I_s` and `(1 - M_s) T_{2,s} = T̃_{2,s}(1 - M_s)`; (4) naive three-term reflection positivity fails unconditionally because for every `0 < Re s < 1/2` the continuous Eisenstein period `Ψ_s^Eis = period(2s, 1, -ζ(2s), state(2s), ·) ∈ H_LP \ {0}` satisfies `I_s Ψ = Ψ` and `M_s Ψ = Ψ` with `Q_s(Ψ) < 0 ↔ Re s ≠ 1/4`; and (5) for every signed Mayer solution `(f ∈ DiscSpace, c ∈ ℂ, ε² = 1)` on `Re s > 0` (`2s ≠ 1`), the derivative-free dyadic cusp extractor `Δ_{2,s}^∞ ψ(a) = ψ(2a) - 2^(1 - 2s) ψ(a)` satisfies `‖Δ_{2,s}^∞ ψ(a) + ε(1 - 2^(1 - 2s)) c‖ ≤ C a^(-2 Re s)` (`a ≥ 1`), so across `0 < Re s < 1/2`, `Δ_{2,s}^∞ ψ ∈ L²((1, ∞), da/a) ↔ c = 0`, separating Mayer scattering resonances from generic continuous scattering (`Δ_{2,s}^∞ Ψ_s^Eis ∈ L²((1, ∞), da/a) ↔ IsMayerScatteringResonance s`).

## Goal
Establish the autonomous source-side Hilbert operator calculus of `(I_s, G_{m,s}, M_s, T_{2,s})` directly inside `H_LP`, diagnose the exact cusp-erasure obstruction showing why `H_LP`-membership plus `(I_s, M_s)`-invariance cannot exclude off-line parameters, and close Route PM Task `Mayer 4` unconditionally via the positive-semidefinite dyadic cusp quadratic form `∫_1^∞ |ψ(2a) - 2^(1 - 2s) ψ(a)|² da/a` without factoring through `state_zero` or `core_hasMellin`.

## Gates
- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3  formalized: Lean module `GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering.FareyLewisTransferAndCuspSeparation`, `lake --old env lean` green, `#print axioms` `[propext, Classical.choice, Quot.sound]`

## No-go closure (mandatory when falsified)
- **Exact killing theorem/mechanism:** Naive source-side three-term reflection positivity (`ψ ∈ H_LP`, `I_s ψ = ψ`, `M_s ψ = ψ` `⇒ Q_s(ψ) = 0`) is false (`nonresonant_real_strip_eisenstein_counterexample`). Applying `1 - U_1` to the forced renewal equation erases the constant forcing `c = -ζ(2s)`, while `w_LP(a) = (a + a⁻¹)^(-6) a^(-1/2) asymp a^(-13/2)` integrates both the constant cusp wave `-ε c` and the outgoing wave `a^(1 - 2s)`. Hence for every `s` in `0 < Re s < 1/2` (witnessed off-line unconditionally at every real `σ ∈ (0, 1/2) \ {1/4}`), `Ψ_s^Eis` satisfies `I_s Ψ_s^Eis = Ψ_s^Eis` and `M_s Ψ_s^Eis = Ψ_s^Eis` in `H_LP`, yet `Q_s(Ψ_s^Eis) < 0` whenever `Re s ≠ 1/4`.
- **Strongest positive survivor:**
  1. Exact polar square `I_s† I_s = a^(4 Re s - 1)`, renewal head-branch critical-line boundedness dichotomy (`G_{0,s}` bounded iff `Re s ≤ 1/4`; `(G_{0,s}, G_{0,1/2 - conj s})` bounded iff `Re s = 1/4`), disjoint-half-line Koopman adjoints of `M_s = U_1 + V_s` with `U_1 V_s† = V_s U_1† = 0`, strict co-expansivity `M_s M_s† = μ_s > 1`, and universal Hecke intertwining `(1 - M_s) T_{2,s} = T̃_{2,s}(1 - M_s)`.
  2. Autonomous dyadic cusp-forcing recovery `lim_{a → +∞} (ψ(2a) - 2^(1 - 2s) ψ(a)) = -ε(1 - 2^(1 - 2s)) c` (`O(a^(-2 Re s))`) and quadratic-form separation `∫_1^∞ |ψ(2a) - 2^(1 - 2s) ψ(a)|² da/a < ∞ ↔ c = 0` across `0 < Re s < 1/2`.
- **New insight:** On `H_LP`, resonance placement (`Re s = 1/4 ↔ Q_s(Ψ_s^Eis) = 0`) and resonance detection (`c = 0 ↔ Δ_{2,s}^∞ Ψ_s^Eis ∈ L²((1, ∞), da/a)`) are orthogonal quadratic-form conditions: `Q_s` measures modular-inversion non-unitarity across the entire strip, whereas `∫_1^∞ |Δ_{2,s}^∞ ψ|² da/a` annihilates the outgoing `a^(1 - 2s)` wave and isolates the constant cusp forcing `-ε(1 - 2^(1 - 2s)) c`.
- **Status:** Complete dependency-closed paper proof `[PROVED HERE]`; unconditionally formalized in `GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering.FareyLewisTransferAndCuspSeparation`.

## Complete Paper Proof `[PROVED HERE]`

### 1. Polar Square of `I_s` and Gauss–Mayer Branch Boundedness Dichotomy on `H_LP`

Let `w_LP(a) = (a + a⁻¹)^(-6) a^(-1/2)` on `(0, ∞)` and `s̃ = 1/2 - conj s`, so `I_s† = I_{s̃}`.
For every `a > 0` and `f : ℝ → ℂ`:
```text
(I_{s̃}(I_s f))(a) = a^(-2 s̃) (a⁻¹)^(-2s) f((a⁻¹)⁻¹) = a^(2 conj s - 1 + 2s) f(a) = a^(4 Re s - 1) f(a),
```
since `2 conj s + 2s - 1 = 4 Re s - 1 ∈ ℝ`. Replacing `s` by `s̃` gives `(I_s(I_{s̃} f))(a) = a^(1 - 4 Re s) f(a)`.
By `‖I_s f‖_LP² = ∫_0^∞ ‖f(b)‖² b^(4 Re s - 1) w_LP(b) db`:
- If `Re s = 1/4`, `4 Re s - 1 = 0`, so `‖I_s f‖_LP² = ‖f‖_LP²` (`C = 1`).
- If `Re s > 1/4` (`δ = 2 Re s - 1/2 > 0`), testing on `f_R = 1_{(R, 2R]}` (`R ≥ 1`) gives `b^(2δ) ≥ R^(2δ)` on `(R, 2R]` while `0 < ‖f_R‖_LP² < ∞`, so `‖I_s f_R‖_LP² ≥ R^(2δ) ‖f_R‖_LP²` with `R^(2δ) → +∞` as `R → +∞`.
- If `Re s < 1/4` (`δ < 0`), testing on `f_r = 1_{(r, 2r]}` (`0 < r < 1/2`) gives `b^(2δ) ≥ (2r)^(2δ) → +∞` as `r → 0⁺`.
Hence `I_s` is bounded on `H_LP` iff `Re s = 1/4`.

For the `m`-th Gauss–Mayer renewal branch `(G_{m,s} f)(a) = (a + m)^(-2s) f(1 + (a + m)⁻¹)` (`m ∈ ℕ`, `Re s ≥ 0`):
- **Head branch `m = 0` (`G_{0,s} = I_s U_1`):** Substituting `a = (b - 1)⁻¹` (`b ∈ (1, ∞)`, `da = (b - 1)^(-2) db`) and using `(b - 1)^(-2) w_LP((b - 1)⁻¹) = (b - 1)^(-1) w_LP(b - 1)` yields
  ```text
  ‖G_{0,s} f‖_LP² = ∫_1^∞ ‖f(b)‖² ρ_s(b) w_LP(b) db,   ρ_s(b) := (b - 1)^(4 Re s - 1) w_LP(b - 1) / w_LP(b).
  ```
  Write `u = b - 1 > 0` (`b = u + 1`). For `0 < u ≤ 1` (`1 < b ≤ 2`), `(u + u⁻¹)^(-6) ≤ u^6` and `(b + b⁻¹)^(-6) b^(-1/2) ≥ (2 + 1)^(-6) · 2^(-1/2) = 3^(-6) 2^(-1/2)`, so
  `ρ_s(b) ≤ 3^6 √2 · u^(4 Re s + 9/2) ≤ 3^6 √2` for all `Re s ≥ 0`.
  For `b ≥ 2` (`u = b - 1 ≥ b/2`), `u + u⁻¹ ≥ b/2` and `b + b⁻¹ ≤ 2b`, so `(u + u⁻¹)^(-6) / (b + b⁻¹)^(-6) = ((b + b⁻¹)/(u + u⁻¹))^6 ≤ 4^6` and `(b/(b - 1))^(1/2) ≤ √2`; when `Re s ≤ 1/4`, `(b - 1)^(4 Re s - 1) ≤ 1` (`b ≥ 2`), giving global boundedness `sup_{b > 1} ρ_s(b) < ∞`.
  Conversely, when `Re s > 1/4` (`4 Re s - 1 > 0`), for `b ≥ 2`, `u + u⁻¹ ≤ b + 1 ≤ 2b ≤ 2(b + b⁻¹)`, so `w_LP(b - 1)/w_LP(b) ≥ 2^(-6)`, whence `ρ_s(b) ≥ 2^(-6) (b - 1)^(4 Re s - 1) → +∞` as `b → +∞`; testing on `1_{(R, R + 1]}` (`R ≥ 2`) disproves boundedness for any `C ≥ 0`.
  Replacing `s` by `s̃ = 1/2 - conj s` (`Re s̃ = 1/2 - Re s`) shows `G_{0,s̃}` is bounded on `0 ≤ Re s ≤ 1/2` iff `Re s ≥ 1/4`; thus `(G_{0,s}, G_{0,s̃})` is simultaneously bounded iff `Re s = 1/4`.
- **Tail branches `m ≥ 1`:** Substituting `b = 1 + (a + m)⁻¹ ∈ (1, 1 + m⁻¹)` (`a = (b - 1)⁻¹ - m`, `da = (b - 1)^(-2) db`) restricts `b` to `(1, 2]` where `w_LP(b) ≥ 3^(-6) 2^(-1/2)`, while `(a + m)^(-4 Re s) = (b - 1)^(4 Re s)` and `(b - 1)^(-2) w_LP((b - 1)⁻¹ - m) ≤ C_m`. Hence every `G_{m,s}` (`m ≥ 1`) is bounded across all `Re s ≥ 0`.

### 2. Farey–Lewis Operator `M_s`, Koopman Adjoints, Self-Commutator, and Hecke Intertwining

Define `(U_1 f)(a) = f(a + 1)`, `(V_s f)(a) = (a + 1)^(-2s) f(a/(a + 1))`, and `M_s = U_1 + V_s`.
1. **Boundedness (`Re s ≥ 0`):**
   - By `b = a + 1 ∈ (1, ∞)`, `‖U_1 f‖_LP² = ∫_1^∞ ‖f(b)‖² (w_LP(b - 1)/w_LP(b)) w_LP(b) db` with `w_LP(b - 1)/w_LP(b) ≤ 8192` for all `b > 1`.
   - Substituting `c = a/(a + 1) ∈ (0, 1)` (`a = c/(1 - c)`, `da = (1 - c)^(-2) dc`, `a + 1 = (1 - c)⁻¹`) yields `‖V_s f‖_LP² = ∫_0^1 ‖f(c)‖² (1 - c)^(4 Re s - 2) (w_LP(c/(1 - c))/w_LP(c)) w_LP(c) dc`, whose Radon–Nikodym ratio is bounded on `(0, 1)` for all `Re s ≥ 0`.
2. **Disjoint-Half-Line Adjoints and Cross-Annihilation:**
   Define
   ```text
   (U_1† g)(b) := 1_{(1, ∞)}(b) (w_LP(b - 1)/w_LP(b)) g(b - 1),
   (V_s† g)(c) := 1_{(0, 1)}(c) (1 - c)^(2 conj s - 2) (w_LP(c/(1 - c))/w_LP(c)) g(c/(1 - c)).
   ```
   Linear substitution `b = a + 1` gives `⟨U_1 f, g⟩_LP = ⟨f, U_1† g⟩_LP`, and Möbius substitution `c = a/(a + 1)` on `(0, ∞) → (0, 1)` gives `⟨V_s f, g⟩_LP = ⟨f, V_s† g⟩_LP`.
   For every `a > 0`, `a + 1 > 1 ⇒ U_1(V_s† g)(a) = 0`, `0 < a/(a + 1) < 1 ⇒ V_s(U_1† g)(a) = 0`, and `(0, 1) ∩ (1, ∞) = ∅ ⇒ ⟨U_1† g, V_s† h⟩_LP = 0`.
3. **Diagonal Co-Square `M_s M_s† = μ_s > 1` and Strict Self-Commutator Negativity:**
   For `a > 0`, `(M_s(M_s† g))(a) = μ_s(a) g(a)` with
   ```text
   μ_s(a) = w_LP(a)/w_LP(a + 1) + (a + 1)^(2 - 4 Re s) w_LP(a)/w_LP(a/(a + 1)).
   ```
   For `a ≥ 1`, `w_LP(a)/w_LP(a + 1) > 1`; for `0 < a < 1` and `Re s ≤ 1/2`, `(a + 1)^(2 - 4 Re s) ≥ 1` and `w_LP(a)/w_LP(a/(a + 1)) = q^6 (a + 1)^(-1/2) > 1` where `q = (2a² + 2a + 1)/((a + 1)(a² + 1))` satisfies `(2a² + 2a + 1)^4 > (a + 1)^5 (a² + 1)^4` on `(0, 1]`. Hence `μ_s(a) > 1` for all `a > 0` and `Re s ≤ 1/2`, and any nonzero continuous fixed point `M_s ψ = ψ` in `H_LP` satisfies `‖M_s ψ‖_LP² - ‖M_s† ψ‖_LP² = ∫_0^∞ (1 - μ_s(a)) ‖ψ(a)‖² w_LP(a) da < 0`.
4. **Universal Manin–Mühlenbruch Hecke Intertwining:**
   For `(T_{2,s} f)(a) = f(2a) + 2^(-2s) f(a/2) + 2^(-2s) f((a + 1)/2) + (a + 1)^(-2s) f(2a/(a + 1))` and `(T̃_{2,s} g)(a) = g(2a) + 2^(-2s) g(a/2) + g(2a + 1) + (a + 2)^(-2s) g(a/(a + 2))`, multiplicative-power algebra on `(0, ∞)` establishes `I_s(T_{2,s} f)(a) = T_{2,s}(I_s f)(a)` and `((1 - M_s)(T_{2,s} f))(a) = (T̃_{2,s}((1 - M_s) f))(a)` for all `f : ℝ → ℂ`, `s ∈ ℂ`, `a > 0`.

### 3. Autonomous Dyadic Cusp-Forcing Recovery & Cusp-Energy Separation (`Mayer 4`)

Let `w = 2s` with `Re w > 0` (`w ≠ 1`), `ε² = 1`, `f ∈ DiscSpace`, `regularized w hw f = ε • f + constant c`, and `ψ(a) := period w ε c f a`.
For `a ≥ 1`, `extension_eq_first` yields `ψ(a) = ε (transfer w f (a - 1) - c)` with `transfer w f (a - 1) = ζ(w) f(0) + ∑_{n=0}^∞ term_a(n)`. Splitting `∑_{n=0}^∞ term_{2a}(n)` into even and odd indices (`tsum_even_add_odd`), subtracting `2^(1 - w) ∑_{k=0}^∞ term_a(k)`, and applying `ZetaRealStrip.etaPair_eq` cancels `(1 - 2^(1 - w)) ζ(w) f(0)` identically and leaves a paired remainder bounded via `plane_difference` and `DQPT.dqptRp_sub_norm_le`:
```text
‖ψ(2a) - 2^(1 - 2s) ψ(a) + ε (1 - 2^(1 - 2s)) c‖ ≤ (24 + ‖2s‖) (1 + 1/(2 Re s)) ‖f‖ a^(-2 Re s)   (a ≥ 1).
```
Across `0 < Re s < 1/2`, `1 - 2^(1 - 2s) ≠ 0`, so `IntegrableOn (fun a => ‖ψ(2a) - 2^(1 - 2s) ψ(a)‖² / a) (Ioi 1) ↔ c = 0`. Specializing to `Ψ_s^Eis(a) := period (2s) 1 (-ζ(2s)) (state (2s)) a` proves `IntegrableOn (fun a => ‖Δ_{2,s}^∞ Ψ_s^Eis(a)‖² / a) (Ioi 1) ↔ IsMayerScatteringResonance s` and `Q_s(Ψ_s^Eis) < 0 ↔ Re s ≠ 1/4` across the entire open strip `0 < Re s < 1/2`.

## Lean Formalization
- `GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering.FareyLewisTransferAndCuspSeparation`:
  - `gaussMayerBranch`, `lewisShift`, `lewisParabolic`, `lewisFarey`, `lewisShiftAdj`, `lewisParabolicAdj`, `lewisFareyAdj`, `lewisFareyMultiplier`, `lewisHeckeT2`, `lewisHeckeT2Companion`, `dyadicCuspExtractor`, `eisensteinLewisPeriod`
  - `lewisModularInversion_adj_comp_self`, `lewisModularInversion_self_comp_adj`, `lewisModularInversion_normBounded_iff`
  - `lewisCriticalNormSq_gaussMayerBranch_zero`, `gaussMayerBranch_zero_normBounded_iff`, `gaussMayerBranch_zero_pair_normBounded_iff`, `gaussMayerBranch_tail_normBounded`
  - `lewisCriticalInner_shift_adj`, `lewisCriticalInner_parabolic_adj`, `lewisShift_comp_parabolicAdj`, `lewisParabolic_comp_shiftAdj`, `lewisCriticalInner_shiftAdj_parabolicAdj`, `lewisFarey_comp_fareyAdj`, `one_lt_lewisFareyMultiplier`, `lewisFarey_normBounded`, `lewisCriticalNormSq_fareyAdj`, `lewisFarey_selfCommutator_neg_of_fixed`
  - `lewisModularInversion_heckeT2`, `lewisThreeTermDefect_heckeT2`, `lewisFarey_heckeT2_of_fixed`
  - `dyadicCuspExtractor_bound`, `tendsto_dyadicCuspExtractor`, `dyadicCuspExtractor_sq_div_integrableOn_iff`
  - `eisensteinLewisPeriod_properties`, `eisensteinLewisPeriod_coIsometryDefect_lt_zero_iff`, `nonresonant_real_strip_eisenstein_counterexample`, `eisensteinLewisPeriod_dyadicCuspEnergy_integrable_iff_resonance`, `criticalLineResonance_iff_dyadicCuspEnergy_and_zero_coIsometryDefect`

## Log
- 2026-11-02 — complete dependency-closed paper proof recorded in `2-fully-proven/`
- 2026-11-02 — unconditionally formalized in Lean 4 and moved to `3-formalized/`
