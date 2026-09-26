# Route 1 — sub-quantum chiral loss through the Gaussian Euler–continuum passage

- **ID:** R1-SQCP
- **Stage:** 5-failed
- **Type:** FALSIFIED (CIRCULAR) + THEOREM (Lean) positive survivor
- **Source:** `docs/reports/route-proposals/route1.md`
- **Statement:** `κ₋(D) < 1` for every admissible strict-right rectangle `D`, where `κ₋` is the negative-chirality Hankel energy lost by `Φₓ/|Φₓ|` as `x → 0⁺`.
- **Fact log:** `../1-in-progress/route1-chiral-passage/facts.md`

## No-go closure

- **Exact killing mechanism:**
  1. *Holomorphic rigidity.* Take zero-free holomorphic approximants that converge on an open anchor inside the disc. If their boundary arguments are bounded in `L¹` modulo constants, the limit is zero-free on the whole disc. By Bourgain–Brezis–Mironescu, bounded `H^(1/2)(S¹;S¹)` phase energy gives that `L¹` bound. Every strict-right zero `ρ` lies in a disc `B(1+i Im ρ, r)`, `r<1/2`, which reaches the safe chart `Re s>1` where `Φₓ → ξ`. So step 2 of the route (bounded, weakly convergent passage) already forbids the zero. The chiral losses of anchored approximants always balance, `κ₋ = κ₊`, and step 4 (`κ₋ ≤ B_base`) is logically idle.
  2. *Explicit formula.* `logDeriv Φₓ - logDeriv ξ = ½ Σ_ρ Γ((ρ-s)/2)(πx)^((s-ρ)/2) + O(x)`. Each zero is felt only to its left, growing like `x^(-(β-σ)/2)`. Under RH the passage converges in `C¹` on compacts of `Re s>1/2`. Under ¬RH it diverges diffusely along every sequence and never bubbles. Step 2 is therefore equivalent to RH: it is the Gaussian-smoothed form of `ψ(X) = X + O(X^(1/2+ε))`.
  3. *Fixed-x arm (stop-test fallback).* `Tr T_(D,x) = wind(u_D)` for every `x`. The only Euler-side identity, Brezis–Nirenberg `E₊ - E₋ = deg`, renormalizes back to the chiral losses of (2).
- **Strongest positive survivor:** anchored phase-passage rigidity.
  - (i) Schwarz difference formula: `G z - G z₁ = (i/π)∫ K (Im G - m) dθ`.
  - (ii) Interior increments are bounded by the boundary-argument oscillation.
  - (iii) Anchored bubbling exclusion.
  - (iv) Bounded `L¹` boundary argument of the Gaussian potential `Lₓ + Aₓ` along one sequence `x_k → 0⁺`, on every circle `C(1+iγ, r)`, implies RH.
- **New insight:** holomorphic readers have no sub-quantum regime. Their integer is protected by rigidity and changes only through divergence, so a budget must bound a growth exponent (`(β-σ)/2`), never a quantum. Test A of the route proposal ("strictly below one quantum, uniform in height") is the wrong gate for holomorphic passages: any finite bound per disc suffices, and even that is RH. A bubble in an unanchored limit is a boundary double zero of the interior limit (a Koebe factor), never an interior event.
- **Status:** paper proof dependency-closed; the only citation is Bourgain–Brezis–Mironescu (IHES 2004) for the `H^(1/2)` → `L¹`-lift step. The Lean survivor is `GaloisForLFunctions.RHTower.AnchoredPhasePassageRigidity`:
  - `schwarz_difference_formula`
  - `norm_sub_le_of_boundary_im_oscillation`
  - `ne_zero_of_anchored_boundaryArgOscillation_bounded`
  - `riemannHypothesis_of_gaussianPassage_boundaryArgOscillation_bounded`

  Axioms: `propext`, `Classical.choice`, `Quot.sound`. Not formalized: the BBM bridge and the explicit-formula converse (RH ⇒ bounded passage).

## Log
- 2026-09-26 — route 1 attacked and killed (CIRCULAR); survivor formalized.

## Correction and live fallback (2026-09-26)
The kill covers only the primary path, where a weak `H^{1/2}` passage makes the `κ₋` budget idle. The fallback is live: a fixed-`x` relative cubic defect with `Tr T_(D,x) = N(D) ≤ B_base`, which is frontier TG's open step.

Loops on the fallback:
- **R1-L1: a D-independent budget with a metric residual. FALSE [paper].**
  - `E_base = E_res(D) + N(D)` with `E_base` independent of `D` forces `E_res` to be locally constant in `D`, hence topological.
  - No seam energy, Hankel energy or curvature integral can be the residual.
  - Survivor: step 4 needs a localized bulk action `E(D) ≤ B_base` with `N(D) ≤ E(D)`.
- **R1-L2: Jensen localization. REDUCED [paper].**
  - The Riesz mass of `log|ξ/Φ_x|` in `D` equals that of `log|ξ|`, since `log|Φ_x|` is harmonic; the formation drops out.
  - Bounding the Jensen functional needs control of `log|ζ|` on circles, the `U(t) < 2` absolute-constant wall (CANNOT-437).
- **R1-L3: operator-norm relaxation. PROVED [L]** (`RHTower.RestrictedProjectionIndexOperatorNormCriterion`).
  - `‖(1 − P)R‖ < 1` makes the `+1` eigenspace of `R − P` trivial, so the relative index, i.e. the cubic trace, is `≤ 0`.
  - Every sub-unit Schatten budget on the forward seam implies this, so the trace budget is never the sharp condition.
  - With `R = R_{u_{D,x}}` and `P = R_{u_D}` (index `+N(D)`), Nehari turns the condition into `dist(conj w, H^∞(D)) < 1` for `w = phase(ξ/Φ_x)`, i.e. some `g ∈ H^∞(D)` with `Re(gξ) > 0` on `∂D`.
  - The formation is absorbed into `g`.
  - Route 1's sharp fallback is local positive-real-part mollification: the same terminus as HF via Selberg completions (`hf-positive-hodge-attack/krein-producer-loops.md`) and as route MC.
- **R1-L4: a sub-unit `L^∞` mollifier budget on circles. REDUCED.**
  - `sup_{∂D}|1 − ζM| < 1 ⇒ N(D) = 0`.
  - Mean-square control of `ζM_X − 1` for `σ > ½` bounds only the measure of exceptional heights: the zero-density method. Pointwise control is RH-strength (individual-zeros gate).

**Status.** Route 1 is live and reduced. Its open step, in its sharpest form, is `∀` admissible `D` `∃ g ∈ H^∞(D)` with `Re(gξ) > 0` on `∂D`, produced from arithmetic.

Further loops on the sharp fallback (2026-09-26):
- **R1-L5: the formation supplies `g`. REDUCED to the Θ-passage [paper].**
  - Take `M_x(s) = Σ μ(n)e^{−πxn²}n^{−s}`. By Mellin–Barnes, `M_x = 1/ζ + Σ_ρ Γ((ρ−s)/2)(πx)^{(s−ρ)/2}/(2ζ'(ρ)) + O(x)`.
  - As `x → 0`, `ζM_x → 1` exactly on `Re s > Θ`. The Möbius passage is global, like `Φ_x`.
  - At finite `x`, far zeros are damped by `e^{−π|γ−t|/4}`, so a local choice of `x` may work on zero-free discs. Proving that it works needs pointwise cancellation in `Σ c_x(n)n^{−s}`, where `c_x(n) = Σ_{d|n}μ(d)(e^{−πxd²}−1)`: RH-strength.
- **R1-L6: deformation audit, step 6 of the proposal, in sharp form [paper].**
  - For `ξ_Q = Q_pξ` (FE-symmetric one-prime factor, off-line zeros) the natural multiplier `1/(ζQ_p)` has coefficients of size `p^{k/2}(1+√ε)^k` at `p^k`, breaking every `O(n^{1/2−δ})` bound.
  - Deletions keep `|μ|` nearly bounded but lose the FE.
  - So a producer of `g` must use bounded Möbius coefficients and the FE together. That is the Selberg-class GRH input, and no countermodel satisfies both.
  - Answer to step 6: the step that fails for the deformation is coefficient growth of the multiplier.
- **R1-L7: a Grassmannian holomorphic filling. FAIL (gate).**
  - `z ↦ ((1−z)c + zF)H²`, with `F = ξ/Φ_x`, jumps between index components wherever the family's zero count in `D` changes. Its boundary is the curve `s ↦ c/(c−F(s))`, `s ∈ ∂D`.
  - A holomorphic disc in `Gr_res` stays in one component, so it cannot carry a `D`-dependent degree. This is the "holomorphic readers unquantized" gate.
  - A route-1 filling must be non-holomorphic, e.g. a harmonic-map flow with energy quantization.
- **R1-L8: energy-quantum form. REDUCED to log-derivative bounds [paper].**
  - `deg u_D ≤ E_{H^{1/2}}(u_D)/(quantum)`. For small discs `E ≈ (π/2)r²|ξ'/ξ(s₀)|²`.
  - So "`E < quantum` on all small admissible discs" means `|ξ'/ξ(s)|(σ−½) ≲ log t` in the strict-right strip: the Hadamard/log-derivative wall of route LA.

**Summary.** Route 1's live remainder has four equivalent sharp forms: local mollification, Jensen/`U(t)<2`, log-derivative bounds, and energy below the quantum. All are pointwise statements about ζ in the strip. The route supplies no lever beyond them; its distinctive inputs, the formation and `B_base`, drop out in each form. Live, not killed: a non-holomorphic producer of a local multiplier `g` remains unexcluded.
- **R1-L9: non-holomorphic path or harmonic-map flow. FAIL [paper].**
  - For `S¹`-valued maps, `|deg u| ≤ Σ|k||û_k|²`, with equality exactly at finite Blaschke-type phases.
  - A sub-unit budget can only cap energy lost along a path, and along the one arithmetic path (the formation) that loss is infinite under ¬RH.
  - A non-holomorphic path from `u_{D,x}` to `u_D` exists with finite energy for any degree, so it carries no arithmetic. The budget is idle for every path.
- **R1-L10: the route-1 principle "integer ≤ sub-unit trace budget" on Weil compressions (Alpöge–Furman rank-trace). Sharpening via `n₋(Q) ≤ p`: FALSE [paper].**
  - The final LP depends on off-line pairs `p` and multiple on-line zeros `s₂` only through `s₂+p`.
  - The worst case is `p = 0` (multiplicities), which a constraint on off-line pairs alone never touches, so 2/3 and 5/6 cannot improve this way.
  - Survivor: improvement needs multiplicity-sensitive input, i.e. third moments from restricted-support triple correlations (Rudnick–Sarnak/Hejhal) or pair-correlation support beyond 1. These give proportions, not RH.
- **Step 2 is exactly RH [L]** (`RHTower.GaussianPassageBoundedUnderRiemannHypothesis`, `riemannHypothesis_iff_gaussianPassage_boundaryArgOscillation_bounded`).
  - Under RH, Abel summation against `f(t) = e^{−πxt²}t^{−w}` and integration by parts give `Jₓ − Mₓ = f(1) − ∫₁^∞ f′(ψ − t)`.
  - With `|f′| ≤ t^{−σ−1}(2/e + |w|)` uniformly in `x`, and von Koch, the potential is bounded on every strict-right circle.
  - The converse was already proved (`AnchoredPhasePassageRigidity`).
  - This is a receiver; it produces nothing towards RH.
- **Step 2 at every abscissa [L]** (`xiZeroHalfPlaneBound_iff_gaussianPassage_bounded`).
  - For `0 ≤ α < ½`, the passage is bounded on every circle `C(1+iγ,r)` with `r < ½ − α` iff Xi has no zero with `Re ρ > ½ + α`.
  - Tools: a single-circle rigidity lemma (`xi_ne_zero_of_gaussianPassage_circle_bounded`) and the generalized von Koch bound.
  - The passage reads `Θ = sup Re ρ`. It cannot localize in height: one far zero with large real part unbounds it.
  - So route 1's step 2 is a global half-plane statement. A local version needs a finite-`x` certificate (local mollification), which is the MC terminus.
- **Fallback in its own carrier [L]** (`RestrictedUnitaryDatum.relativeIndex_eq_zero_of_seams`).
  - Adjoint seam `‖(1−P)U†P‖ < 1` gives cubic trace `≤ 0`; forward seam `‖(1−P)UP‖ < 1` gives `≥ 0`; both give index `0`.
  - The TG/route-1 "sub-unit trace budget" is therefore never needed: two operator-norm seam contractions suffice.
  - For boundary phases these are the Nehari distances of the relative phase and its conjugate to `H^∞` [P].
- **Integer identity [L]** (`RHTower.CircleArgumentPhaseRelativeIndex.DiscArgumentDatum.relativeIndex_eq_zeroCount`). For every `F` holomorphic near a closed disc and zero-free on the circle, the Hardy pair of the boundary phase `F/|F|` has relative index, and cubic trace, equal to the zero count inside. Programme card: `3-formalized/route1-cubic-index-equals-winding.md`. Route 1's identity `Tr T_(D,x) = N(D)` holds in Lean for each fixed `x`; the budget is the only open piece.
- **R1-L11: one-sided passage at a single real point (Landau lever). REDISCOVERED [paper]** (Ingham 1932, Gaussian form).
  - Write `F_σ(x) = L_x(σ) + A_x(σ)`, `σ ∈ (½,1)`. The Mellin transform in `x` is `∫₀^∞ x^{z−1}F_σ(x)dx = Γ(z)π^{−z} log[(s−1)ζ(s)/(s+1−σ)]` at `s = σ+2z`. This uses `∫₁^∞ (u^{−a} − u^{−b})/log u du = log((b−1)/(a−1))`.
  - `(s−1)ζ(s) > 0` on the real ray, so this continuation is analytic along real `z > 0`.
  - If `sup_{0<x≤1} F_σ(x) < ∞` (upper bound only), then `C − F_σ(e^{−u}) ≥ 0`. Landau's theorem for Laplace transforms with nonnegative density gives abscissa `≤ 0`, hence analyticity on `Re z > 0`, hence no zero with `β > σ`.
  - So route 1's step 2 needs neither circles, nor two sides, nor height uniformity: one real point, one side, `⟺ Θ ≤ σ`.
  - New insight: positivity (Landau) globalizes. A one-sided bound at any point sees every height; it never localizes.
- **R1-L12: seam asymmetry for holomorphic phases. CLASSICAL [paper].**
  - `F` holomorphic near `D̄`, zero-free on `∂D`; factor `F = B·O` (finite Blaschke product `B`, outer `O`). Then `T_u = T_{\bar{1/O}} T_{|O|} T_B` is always bounded below, so the forward seam `‖(1−P)UP‖ < 1` for every `D`.
  - The adjoint seam `T_ū = T_B^* T_{|O|} T_{1/O}` is injective iff `N(D) = 0`, and then `1 − ‖(1−P)U†P‖² ≥ (min_{∂D}|F| / max_{∂D}|F|)²`.
  - So of the corpus's two seams (`relativeIndex_eq_zero_of_seams`), only the adjoint seam carries content for holomorphic data. The forward seam's conclusion `ind ≥ 0` is `N ≥ 0`.
- **R1-L13: twisted Landau for height localization. FAIL [paper].**
  - The coefficients `Λ(n)n^{−σ}(1 + cos(t log n))/log n ≥ 0` put Landau's lever at height `t`.
  - The real ray of the Mellin transform is singular only at zeros with ordinate exactly `±t`. For generic `t` a one-sided bound again reads `Θ ≤ σ` over all heights.
  - Positivity cannot localize (corpus: localization blindness). A localized producer must be non-positive and non-holomorphic, the region R1-L9 already emptied.
- **R1-L14: mixed-bandwidth rank–trace (bandwidth-1 second moment + restricted-support cubic trace). FALSE at the scalar level [paper]; spectral version open (needs SDP, not run).**
  - Source: Alpöge–Furman arXiv 2608.13637 §7.2(e)–(f). With one compression, `tr G^k` is unconditional only for `X^k ≤ T^{2−ε}`, so `k = 3` forces bandwidth `λ ≤ 2/3` and caps rank at `λN`.
  - Conjecture: combine compressions by bounding heavy objects (`s₂ + p`) at bandwidth `λ` and feeding that into the bandwidth-1 chain `3s₁ + 4(s₂+p) ≥ (4−R)N`.
  - Scalar LP: `Σm = N`, `Σm² ≤ R₂N`, `Σm³ ≤ R₃N` gives `N₁ ≥ (4−R₃)N/3`, which beats `2−R₂` only if `R₃ < 2`.
  - Montgomery's extremal (2/3 simple + 1/6 doubles, mutually orthogonal) has `Σm³/N = 2/3 + 8/6 = 2 = m₃(1)`, the GUE cubic moment at bandwidth one. Cubic kernels of bandwidth `λ < 1` form a smaller class, so `R₃(λ) ≥ R₃(1) = 2`. The cubic constraint is inactive at the extremal.
  - The quartic moment separates (`10/3 > m₄(1) = 13/4`, the paper's conditional 13/18) but needs `λ ≤ 1/2` unconditionally. There the extremal's coarse geometry is not pinned by `F` on `[−1,1]`, so exclusion is an SDP question.
  - Lesson: the route-1 principle "integer ≤ trace budget" on Weil compressions is saturated by pair data at 2/3; any gain needs even moments at bandwidth one, i.e. Hardy–Littlewood-type prime-pair input.
- **R1-L11 survivor: covered by the corpus, not re-formalized.** Landau for nonnegative Laplace measures is [L] (`RHTower.LandauSingularAtAbscissa.false_of_analyticAt_abscissa`, `LaplaceTransformMomentDerivative.not_summable_moment_beyond_abscissa`). One-abscissa Landau transfers for prime–polar sources are [L] (`CCMSharpPrimeWindowExcessEnergyGate`, `CCMRectangularNegativePartEnergyGate`). The Gaussian one-point form is a specialization with no new content.
- **R1-L15: local Weil positivity at height `T`, level `a = A log log T`. SHARP BOUNDARY at `A = 1` [paper].**
  - Test function `f = e^{iγ₀u}h(u)`, `h = sinh(δu)1_{[−a,a]}`. Zero side: real zeros give `≈ log T · e^{2aδ}/(4δ)`; an off-line pair of depth `δ` at `γ₀` gives `≈ −e^{4aδ}/(8δ²)`.
  - Explicit-formula side: archimedean `≈ log T · ‖h‖²`. The prime term runs over `n ≤ e^{2a}` (autocorrelation support `[−2a,2a]`, profile `e^{δ(2a−u)}/(8δ)`) and has trivial size `≈ e^{a}‖h‖²/(½−δ)`.
  - `A < 1`: the archimedean term dominates the primes for free, and the pair is excluded only for `e^{2aδ} ≳ δ log T`, i.e. `δ > 1/(2A) > ½`, which is vacuous.
  - `A > 1`: excluding depth `δ < ½` needs `|Σ_{n≤(log T)^{2A}} Λ(n)n^{−1/2−iT}F(log n)| = o(e^{a}‖h‖²)` for every `T`. That is a short-prime-polynomial cancellation equivalent to bounds on `log ζ` at distance `≍ 1/log log T` from the line, i.e. local zero-freeness.
  - New insight: the exact-primes / exponent gate sits at `e^{a} = log T`. Local Weil positivity is free exactly up to the level where the prime polynomial's length reaches the archimedean density, and carries no zero information below that level. This is the one-log wall (MUST-440) in the Weil-localization carrier.
- **Route 1 consumer chain closed [L]** (`RHTower.XiRightDiscPhaseIndexRiemannHypothesis`; axioms `propext, Classical.choice, Quot.sound`; `lake build --old` green).
  - `riemannHypothesis_iff_forall_xiRightDisc_relativeIndex_eq_zero`: RH ⟺ on every circle bounding a closed disc strictly right of the line, with `xi ≠ 0` on the circle, the Hardy pair of the `xi` boundary phase has relative index `0`.
  - `riemannHypothesis_of_forall_xiRightDisc_adjointSeam_lt_one`: `‖(1−P)U†P‖ < 1` on every such disc implies RH.
  - Supporting lemmas: `xiDiscRelativeIndex_pos_of_zero`, `exists_xiRightDisc_of_zero`, `one_le_zeroMult_xi`.
  - Route 1 is now fully formal except its producer. A proof of the seam contraction (the local mollifier `g`) plugs directly into a Lean proof of RH. Converse (RH ⇒ seam contraction) not formalized: it needs Toeplitz invertibility for holomorphic phases (R1-L12).
- **R1-L16: producer via route SZ (Suzuki screw function). NO LEVER [paper + corpus audit].**
  - `Ψ(t) = Σ_γ (1 − cos γt)/γ²`. `Ψ″` is the Weil distribution on `(0,∞)`; RH ⟺ `Ψ ≥ 0` [L] (`riemannHypothesis_iff_suzukiPsiPointwiseNonnegative`).
  - Under RH, `Ψ(t) = Σ1/γ² − Σ cos(γt)/γ²` has infimum `0`, approached but not attained: zero slack.
  - The prime side is `Σ_{n≤e^t} Λ(n)n^{−1/2}(t − log n) ≈ 4e^{t/2}`. It cancels the polar growth only up to `O(1)`, so a producer needs a one-sided smoothed `ψ` bound with exact constant at `O(√x)` precision: the Landau/Ingham lever again (R1-L11).
  - The corpus covers the lane in depth (`SuzukiCheckpointEventDynamics`, `CCMFUSuzukiCheckpointAffineReduction`, `SuzukiScrewFirstGap`, `SuzukiScrewStrictPositivity`). Frontier SZ's open core (bound the moving signed residual by a Wronskian law derived from the source) is the same no-slack domination.
- **Status (2026-09-26, end of session): GENUINELY BLOCKED on the producer.** Every sharp form of route 1's remaining step is RH-equivalent: local mollifier, adjoint seam, level-wise Weil positivity, de Branges `E_a`, Suzuki `Ψ ≥ 0`. No countermodel is possible (each form holds for a zeta-like object iff it has no off-line zeros), so the route can be neither killed nor closed with known mechanisms. Everything except the producer is [L].
- **R1-L12 formalized; route 1's producer target is an exact equivalence [L]** (`RHTower.CircleHolomorphicPhaseSeamContraction`; axioms `propext, Classical.choice, Quot.sound`; `lake build --old` green).
  - `RestrictedUnitaryDatum.norm_adjointHankelSeam_lt_one`: `Ran R ∩ Ker P = 0` implies `‖(1−P)U†P‖ < 1`. Proof: compact `seam†seam` attaining its norm (`exists_unit_eigenvector_norm`).
  - `DiscArgumentDatum.fourierCoeff_circleLift_value_of_neg`: holomorphic boundary values have no negative Fourier modes (Cauchy).
  - `DiscArgumentDatum.hardy_phase_injective` (Coburn): `P M_u` is injective on `Ran P` for `u = F/|F|`. Proof: `g = s²u`, `M_g` preserves `Ran P`, so `‖M_s M_u f‖² = ⟪M_u f, M_g f⟫ = 0`.
  - `DiscArgumentDatum.norm_forwardHankelSeam_lt_one`: the forward seam of every holomorphic phase contracts.
  - **`riemannHypothesis_iff_forall_xiRightDisc_adjointSeam_lt_one`**: RH ⟺ the adjoint seam of the `xi` phase contracts on every right disc.
  - Route 1 is now completely formal as an equivalence; the only non-formal item is the producer, which is RH.
- **R1-L17: no uniform seam margin for `xi` itself [L]** (`RHTower.XiRightDiscAdjointSeamSupremum`; axioms `propext, Classical.choice, Quot.sound`; `lake build --old` green; lint passed).
  - `not_exists_uniform_xiRightDisc_seam_margin`: no `δ > 0` has `‖(1−P)U†P‖ ≤ 1−δ` on all zero-free right discs. Unconditional: it uses one on-line zero (Hardy).
  - `OnLineZeroData.one_sub_seam_sq_le`: `1 − ‖seam‖² ≤ 3(1−r²) + 6π/log(1+π/(1−r))` for the disc of radius `t` at `ρ₀ + t/r`, whatever the multiplicity.
  - Kills every route-1 producer that would deliver a height- or position-uniform seam contraction: compactness arguments, uniform Nehari distances, uniform `H^∞` mollifier bounds. A producer must be exactly margin-free near on-line zeros.
