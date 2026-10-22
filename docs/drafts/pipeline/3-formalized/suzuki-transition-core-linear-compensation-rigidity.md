# Suzuki Transition-Core Linear Compensation Rigidity

- **ID:** SWA-LINEAR-COMPENSATION-RIGIDITY
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `SUZUKI-FE-REFLECTED-WALL-WARD-ASSEMBLY`
- **Statement:** Any eventually lower-semibounded rectangular Ward defect obtained from the exact positive Suzuki transition core needs a correction of positive linear size along apertures `8n`; consequently sublinear corrections and the literal growing-rank positive Cartan fission source cannot be RH producers.

## Goal

Kill the positive growing-rank survivor left by fixed-rank and fixed-scale no-gos. Audited chain:

`transition-core source correction`
`→ rectangular Ward-defect lower semiboundedness`
`→ Xi screw-curvature criterion`
`→ RH`
`→ shared HB/FZZ-P/RBH/PW-B endpoint`.

Proof is non-circular: it uses only unconditional square-root envelope for fixed-width Xi
rectangular curvature and unconditional PNT-sized linear lower bound for exact transition core.

## Gates

- [x] 0 → 1 in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2 fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3 formalized: Lean theorems, targeted `lake build` green, axiom audit clean
- [ ] 3 → 4 publication-ready: standalone paper

## Paper proof `[PROVED HERE]`

Write `K_L(N)` for real fixed-width Xi screw curvature, `E_N` for exact positive Suzuki
transition-core Cauchy energy, and

`D_L(N;c) = K_L(N) - (E_N - c_N)`.

Corpus theorems give `C ≥ 0` with `|K_L(N)| ≤ C sqrt(N)` on eventual logarithmic aperture
mesh, and `E_(8n) ≥ n/288` eventually. If `D_L(8n;c) ≥ b` eventually, then

`c_(8n) ≥ b - K_L(8n) + E_(8n)`
`          ≥ b - C sqrt(8n) + n/288`.

Because `C sqrt(8n) = o(n)` and constant `b = o(n)`, eventually
`C sqrt(8n) ≤ n/1152` and `b ≥ -n/1152`. Hence

`c_(8n) ≥ n/576`.

This contradicts every correction with `c_(8n)/n → 0`.

For literal completed growing-rank Cartan fission observable `F_N`, corpus proves
`F_N = E_N + 2R_N` with `R_N ≥ 0`. Treating it as corrected core gives
`c_N = E_N - F_N = -2R_N ≤ 0`, contradicting forced positive linear compensation. More strongly,
its rectangular Ward defect tends to negative infinity on `8n` for every width.

## No-go closure

- **Exact killing theorem/mechanism:** Xi rectangular curvature is at most square-root scale while
  exact transition-core energy has positive linear lower bound on `8n`; any semibounded defect
  forces positive linear cancellation. Positive Cartan fission adds mass.
- **Strongest positive survivor:** every viable assembly must retain coefficient-faithful signed
  correction satisfying `c_(8n) ≥ n/576` eventually. Growing rank alone is insufficient.
- **New insight:** bounded, sublinear, purely positive, fixed-finite-channel, and literal positive
  growing-rank completions are now excluded. Remaining source theorem must construct signed
  atomic–continuous cancellation at transition-core scale.
- **Status:** dependency-closed paper proof and unconditional Lean formalization complete.

## Lean certificate

- Module: `GaloisForLFunctions.RHTower.Suzuki.SuzukiTransitionCoreLinearCompensationNoGo`
- Positive survivor: `RHTower.eventually_linear_le_correction_of_transitionCoreWardDefect_bddBelow`
- Sublinear class kill: `RHTower.no_sublinear_transitionCore_rectangularWardProducer`
- Actual-source escape: `RHTower.tendsto_suzukiRectangularWardDefect_completedGrowingRankCartanFission_eight_mul_atBot`
- Route capstone: `RHTower.no_growingRankPositiveCartanFission_rectangularWardProducer`
- Direct check: `lake env lean GaloisForLFunctions/RHTower/Suzuki/SuzukiTransitionCoreLinearCompensationNoGo.lean` passed.
- Targeted audit: `lake build GaloisForLFunctions.RHTower.Suzuki.SuzukiTransitionCoreLinearCompensationNoGo` passed (`11979/11979`).
- Axiom audit: only `propext`, `Classical.choice`, `Quot.sound`.
- Umbrella: imported by `GaloisForLFunctions.RHTower`.
- Global formal lint reached unrelated pre-existing umbrella error: owned module `GaloisForLFunctions.RHTower.Deninger.DeningerQ8ActualTwoAdicInertia` is not reachable. New module has no forbidden declaration and is reachable from umbrella.

## Conjecturing loop

- **SWA-LC1:** bounded positive growing-rank fission might absorb transition core. Failed: fission adds nonnegative cubic mass.
- **SWA-LC2:** asymptotically sublinear signed renormalization might suffice. Failed: semiboundedness forces `≥ n/576` correction.
- **SWA-LC3 survivor:** coefficient-faithful signed atomic–continuous correction with linear mass and RH-strength cancellation. This is now only surviving wall-assembly scaling class.

## Novelty audit

Internal corpus had fixed-rank escape, bounded-correction/fixed-scale no-gos, exact positive
growing-rank Cartan fission, linear transition-core escape, and square-root Xi curvature envelope,
but no theorem combining them into linear compensation rigidity or killing actual growing-rank
fission. External primary-source audit through 2026-08-31 found Suzuki's screw-function/Weil
operator limit still conjectural and no prime-side linear compensation classification:
[Suzuki 2026](https://arxiv.org/abs/2606.09096),
[Suzuki screw line](https://arxiv.org/abs/2209.04658), and
[Suzuki screw function](https://arxiv.org/abs/2206.03682). Novelty claim is limited to exact
corpus source coordinates and shared four-route consequence.

`[LEAN-PROVED] [COMMON FOUR-ROUTE POSITIVE-GROWING-RANK KILL] [LINEAR-SIGNED-SURVIVOR]`

## Log

- 2026-08-31 — conjectured from exact corpus scaling laws, proved on paper, formalized, audited, and producer class retired.

