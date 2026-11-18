# Single-functional rank-two completion of Weil's form, RH separation, and shifted-probe resonance

- **ID:** ecs-single-quartet-rank-two-completion-and-probe-resonance
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `ExclusionOfTheCriticalState/Index/SingleQuartetSecularAndWallRigidity.lean`; `ExclusionOfTheCriticalState/Zeros/TheExplicitFormulaHoldsForTwoSidedTests.lean`; `ExclusionOfTheCriticalState/WeilsFormOnProbesIsTheCaratheodoryKernelOfXi.lean`
- **Statement:** Under `HasSingleOffLineQuartet ρ₀` (`m = quartetCopyMult ρ₀`), adding the single complex square `m ‖Δ_{ρ₀}(G)‖²` (`Δ_{ρ₀}(G) = L G(1/2 - ρ̄₀) - L G(ρ₀ - 1/2)`) to `bareMixedEnergy G G` yields `onLineEnergy G + m ‖Σ_{ρ₀}(G)‖² ≥ m ‖Σ_{ρ₀}(G)‖² ≥ 0` on the entire half-line energy domain (with global Cauchy–Schwarz); `RiemannHypothesis` implies the weak completion `bareMixedEnergy G G + m ‖Δ_{ρ₀}(G)‖² ≥ 0` for all `(ρ₀, m)` while refuting the cosh-surplus lower bound `≥ m ‖Σ_{ρ₀}(G)‖²` via shifted exponential probes, and boundedness either above or below of `R ↦ bareMixedEnergy (probe p) (shiftProfile (probe p) R)` (`p > 4`) on `[0, ∞)` excludes every single off-line quartet.

## Lean
Module `ExclusionOfTheCriticalState/Index/SingleQuartetRankTwoCompletionAndProbeResonance.lean` (namespace `GaloisForLFunctions.ExclusionOfTheCriticalState`):
`rankTwoCompletedWeil_eq_onLineMixed_add_cosh`, `bareMixedEnergy_add_sinhFunctional_sq_eq`,
`coshFunctional_sq_le_bareMixedEnergy_add_sinhFunctional_sq`,
`bareMixedEnergy_sinhOrthogonal_eq_and_ge`, `bareMixedEnergy_coshOrthogonal_eq`,
`rankTwoCompletedWeil_cauchy_schwarz`, `bareMixedEnergy_eq_onLineMixed_of_riemannHypothesis`,
`rankTwoCompletedWeil_nonneg_of_riemannHypothesis`,
`abs_bareMixedEnergy_probe_shiftProfile_le_of_riemannHypothesis`,
`probe_shiftProfile_unbounded_above_and_below_of_singleQuartet`,
`not_hasSingleOffLineQuartet_of_probeShift_bddAbove`,
`not_hasSingleOffLineQuartet_of_probeShift_bddBelow`,
`exists_coshSurplus_violation_of_riemannHypothesis`. Axioms: `propext`, `Classical.choice`,
`Quot.sound`.

## Paper proof
1. **Polarized four-square identity and rank-two completion.** For `u_G = L G(ρ₀ - 1/2)` and `v_G = L G(1/2 - ρ̄₀)`, complex polarization gives `4 Re(u_G v̄_G) = ‖v_G + u_G‖² - ‖v_G - u_G‖² = ‖Σ_{ρ₀}(G)‖² - ‖Δ_{ρ₀}(G)‖²`, and in polarized form `2 v_Fᵀ J₄ v_G + Re(Δ_{ρ₀}(F) \overline{Δ_{ρ₀}(G)}) = Re(Σ_{ρ₀}(F) \overline{Σ_{ρ₀}(G)})`. Substituting into `bareMixedEnergy_singleQuartet` gives `bareMixedEnergy F G + m Re(Δ F \overline{Δ G}) = onLineMixed F G + m Re(Σ F \overline{Σ G})`. On the diagonal this yields `bareMixedEnergy G G + m ‖Δ_{ρ₀}(G)‖² = onLineEnergy G + m ‖Σ_{ρ₀}(G)‖² ≥ m ‖Σ_{ρ₀}(G)‖² ≥ 0`, coercivity `≥ 4m ‖u_G‖²` on `ker Δ_{ρ₀}`, and Cauchy–Schwarz across the whole energy domain.
2. **RH consistency of the weak completion vs. failure of cosh-surplus.** Under `RiemannHypothesis`, `offLineCopyFinset = ∅`, so `bareMixedEnergy F G = onLineMixed F G` and `bareMixedEnergy G G = onLineEnergy G ≥ 0`. Hence `bareMixedEnergy G G + m ‖Δ_{ρ₀}(G)‖² ≥ 0` holds for every `(ρ₀, m)`, showing no contradiction can arise from the weak rank-two completion alone without disproving `RiemannHypothesis`. Moreover, for `R ≥ 0`, `‖cexp(-(centredZero q · R))‖ = 1` on `onLineCopies` preserves `onLineEnergy`, so `|onLineMixed F (shiftProfile F R)| ≤ onLineEnergy F`; under `RiemannHypothesis`, `|bareMixedEnergy (probe p) (shiftProfile (probe p) R)| ≤ probeSymbol p / p` (`p > 4`) and `bareMixedEnergy G_R G_R ≤ 4 probeSymbol p / p` for `G_R = probe p + shiftProfile (probe p) R`.
3. **Quarter-turn shifted-probe resonance.** For `p > 4`, `1/2 < Re ρ₀ < 1`, `Im ρ₀ ≠ 0`, let `z_+ = ρ₀ - 1/2 = δ₀ + iγ₀` (`δ₀ > 0`) and `z_- = 1/2 - ρ̄₀` (`z̄_- = -z_+`). On `F = probe p` and `H_R = shiftProfile F R`, `u_F \overline{v_{H_R}} = c₀ e^{(δ₀ + iγ₀)R}` with `c₀ = 1 / (p² - z_+²) ≠ 0`, while `‖v_F \overline{u_{H_R}}‖ = ‖c₀‖ e^{-δ₀ R} ≤ ‖c₀‖`. Choosing quarter-turn phases `γ₀ R_N ∈ {0, π/2, π, 3π/2} + 2πℤ` (`R_N → +∞`) realizes `Re(c₀ e^{iγ₀ R_N}) ≥ ‖c₀‖/2` and `≤ -‖c₀‖/2`. Under `HasSingleOffLineQuartet ρ₀`, `|onLineMixed F H_R| ≤ onLineEnergy F` is bounded, so `bareMixedEnergy F H_{R_N}` diverges to both `+∞` and `-∞`; under `RiemannHypothesis`, the same `R_N` drives `m(‖Σ_{ρ₀}(G_{R_N})‖² - ‖Δ_{ρ₀}(G_{R_N})‖²)` above `4 probeSymbol p / p ≥ bareMixedEnergy G_{R_N} G_{R_N}`.

## What it changes
Exhibits the multiplicity-independent rank-two completion of Weil's half-line form under `HasSingleOffLineQuartet ρ₀`, proves formally why its positive-semidefiniteness is consistent with `RiemannHypothesis` while its cosh-surplus lower bound is strictly incompatible with `RiemannHypothesis`, and reduces exclusion of all single off-line quartets to either an upper bound or a lower bound on the single lag correlation `R ↦ bareMixedEnergy (probe p) (shiftProfile (probe p) R)` (`p > 4`).

## Log
- 2026-11-18 — created; proved; formalized.
