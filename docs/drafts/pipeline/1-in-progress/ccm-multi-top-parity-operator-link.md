# CCM parity: from the leading-order model to the restricted Weil operator, any finite top layer

- **ID:** ccm-multitop-link
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper), Lean in progress
- **Source:** rh-goal-loop-opus-2026-09-29 rows 917, 927–943; MUST-805, 920, 932, 936, 946, 947
- **Statement:** Let the non-real Xi spectral points form a finite set, let `δ > 0` be the largest `|Im z|`, and let the top layer be the quartets of `σ_j = t_j + iδ` (`t_j > 0` distinct) with copy counts `M_j`. If `F(θ(a₀)) > 0` for one real `a₀` (by MUST-947 this holds whenever every integer relation among the `t_j` has even coefficient sum), then at arbitrarily large apertures every ground state of the CCM restricted Weil form is reflection-odd.

## Goal
Generalizes MUST-805 (a unique top quartet) to every finite top layer that has one positive point. The step 1 of Connes' programme (an even ground state at all large apertures) then excludes every finite off-line configuration with such a top layer.

## Paper proof
Notation: `⟨f,g⟩ = ∫ f g` (bilinear). `ψ_j(s) = e^{−(δ−it_j)s}` on `[0,∞)`. `T(θ)[v] = Re Σ_j M_j e^{iθ_j} ⟨v,ψ_j⟩²`. `θ_j(a) = −2t_j a`.

1. **Quartet reduction.** For a parity source `u` (even or odd), every quartet point gives the same real part (`re_zeroSumTerm_quartet`). Write `u = u₁ + iu₂` with `u₁, u₂` real of the same parity.
   - Even: `Re(û(σ) conj û(σ̄)) = Re⟨u₁, cos σx⟩² + Re⟨u₂, cos σx⟩²`.
   - Odd: `Re(û(σ) conj û(σ̄)) = Re⟨u₁, sin σx⟩² + Re⟨u₂, sin σx⟩²`.
   - Proof: `û(σ) = ⟨u, cos σx⟩` and `conj û(σ̄) = ⟨ū, cos σx⟩` (even case; the odd case has the factors `i` and `−i`). Then `(A + iB)(A − iB) = A² + B²`.
2. **Half-line asymptotics.** Let `w` be real with the given parity on `[−a, a]`, and set `v(s) = w(a − s)` on `[0, a]`.
   - `⟨w, cos σx⟩ = e^{−iσa}(⟨v, ψ⟩ + r)` and `⟨w, sin σx⟩ = i e^{−iσa}(⟨v, ψ⟩ + r')`.
   - The remainders satisfy `|r|, |r'| ≤ e^{−δa} ‖v‖ / √(2δ)`, since they are the decaying exponential `e^{iσx}` paired over `[0, a]`.
   - Hence `Σ_j M_j Re⟨w, cos σ_j x⟩² = e^{2δa}(T(θ(a))[v] + E)`, the odd analogue has the opposite sign, and `|E| ≤ (3/2)(ΣM) e^{−δa} ‖v‖² / δ`.
3. **Projection.** For real `v ∈ L²(0, ∞)` there is `x` with `⟨realProfile x, ψ_j⟩ = ⟨v, ψ_j⟩` for all `j`.
   - Existence: solve `G y = b`. Here `b` is real-structured, so `y` is too, by injectivity of `G` and the swap symmetry of `G`.
   - Then `∫ (realProfile x)² ≤ ∫ v²`, because `v − P` is orthogonal to `P`.
   - Consequences: `T(θ)[v] = quadForm θ x ≥ −max(λ_max(θ + π𝟙), 0) ∫ v²` and `T(θ)[v] ≤ max(λ_max(θ), 0) ∫ v²`.
4. **Even floor.** Each lower copy is bounded by Cauchy–Schwarz by `2a e^{2a|Im z|} ‖u‖²` (MUST-805 `lowWeight`). Real copies contribute `≥ 0`. So for every even smooth source, `Q(u) ≥ −((e^{2δa}/2)(max(λ_max(θ+π𝟙), 0) + C e^{−δa}) + L(a)) ‖u‖²`. Density extends this to all even vectors (`floor_of_isEven_of_smooth`).
5. **Odd test.**
   - Choose the maximizer `x*` of `quadForm θ(a)` on the unit level. Its coefficients are bounded uniformly in `θ` by coercivity.
   - Model: `W(x) = 2 Re Σ_j x*_j e^{−(δ−it_j)a}(e^{−iσ_j x} − e^{iσ_j x})`. It is smooth and odd, and `W(a − s) = realProfile x* (s) + O(e^{−δa})` on `[0, a]`.
   - Cut it off smoothly inside `(−a, a)`. On-line copies contribute at most `(∫|u′|)² Σ|z|^{−2} = O(1) ‖u‖²`.
   - Result: `Q(u_n)/‖u_n‖² → −(e^{2δa}/2)(λ_max(θ(a)) + O(e^{−δa})) + O(a e^{2δ′a}) + O(1)`.
6. **Gap.**
   - If `F(θ) > 0`, then `λ_max(θ) > max(λ_max(θ + π𝟙), 0)`. Case split on the sign of `λ_max(θ + π𝟙)`; when it is negative, `quadForm θ > 0` on the unit level.
   - MUST-947 windows give `F(θ(a)) ≥ g/2` at arbitrarily large `a`.
   - Then the odd quotient lies below the even floor for large such `a`. As in MUST-805, every ground state is then odd.

## Gates
- [x] 0 → 1  in-progress
- [ ] 1 → 2  fully-proven: steps 1–6 above; the remaining written detail is the cutoff limit in step 5, which copies MUST-805's `oddTestSeq`
- [ ] 2 → 3  formalized

## Log
- 2026-10-11 — created; model side in Lean (MUST-946/947); starting module A (quartet reduction, half-line asymptotics, projection, even floor).
