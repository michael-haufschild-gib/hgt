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
