# F2 — faithful Gaussian core completion

- **Stage:** 1-in-progress
- **Question:** Does the Gaussian sum of actual PM cores determine every upper-resonance coefficient?
- **Exact target:** For `ε>0`, vanishing of `Σ_s exp(−ε(Im s)²)x_(2s) core_s(a)` for all `a>0` implies `x_(2s)=0` for every upper resonance. Lower-half-plane coordinates are absent from this sum.
- **Gap:** Finite core independence does not imply uniqueness of the infinite series. Physical Haar energy has not been identified with the signed coefficient pairing.

## Endpoint estimate [K] and remaining mechanism

Write `w=2s`, `r=Re w∈(0,1)`. The existing theta Mellin identity gives
`∫₀∞ u^(w/2−1) θRay(u) du = Γℝ(w)ζ(w)=0` at a resonance.
The scaled Mellin identity also vanishes. Thus the exact theta correlation may replace its first factor `θRay(t)` by `θRay(t)+1/2`.

The audited elementary bound is
`|θRay(t)+1/2|≤min(1/2,√t/π)`.
Theta reciprocity reduces the second term to
`Σ_(n≥1) exp(−πn²/t)≤1/(exp(π/t)−1)≤t/π`.
Together with `|θRay(a²t)|≤1/(2a√t)`, splitting the corrected integral at `t=1` yields

`|fieldCore_w(a)|≤[2/(πr)+1/(1−r)] / (|Γℝ(w)|a)`.

Reciprocity supplies the other endpoint `O(a^(1−r))`. The Cauchy kernel's absolute first moment is at most `(1/2+1/r)/|averagingFactor(w)|`; Gamma normalization cancels as in the audited spectral estimate. Both reciprocal strip distances are controlled by the existing zero-free region. The [audited two-endpoint theorem](../3-formalized/f2-resonant-core-two-endpoint-bound.md) gives `|core_s(a)|≤K(s)min(a⁻¹,a^(1−r))`, with `K(s)=C(1+Im s)^N exp(π Im s/2)` uniformly over upper resonances. [Whole-axis Haar synthesis and common-strip Mellin interchange are Lean-audited](../3-formalized/f2-whole-axis-gaussian-mellin-synthesis.md). Each individual core also has a holomorphic Mellin transform on `r−1<Re u<1`.

For `0<σ<1`, the two-endpoint estimate bounds the absolute Mellin integral by
`K(s)(1/σ+1/(1−σ))`. This supplies a summable Gaussian majorant on every closed substrip and a concrete route to interchange the physical sum with its Mellin integral.

The continued Mellin kernel is
`symbol(w,u) Λ(u)Λ(w−u)/Γℝ(w)`.
Its pole at `u=w` is removable because `Λ(w)=0`; the raw total Gamma expression there must not be mistaken for the analytic extension. Its pole at `u=w−1` has nonzero residue. Those latter poles are distinct and locally finite. Normal convergence of the meromorphic Gaussian sum would permit coefficient extraction. This analytic step remains unproved. The corpus supplies countable-puncture connectedness (`HTGeometry.isPreconnected_diff_of_countable_of_convex_complex`) and `RHTower.XiGlobalKummer.norm_xi_le_real_axis`. The latter bounds xi uniformly on each fixed vertical strip. On compact subsets away from the moving poles, numerator Gamma factors are bounded and reciprocal Gamma factors grow at most exponentially in `Im s`; Gaussian damping supplies the proposed normal majorant. This series-specific bound remains to be formalized.

A stronger target is uniqueness from vanishing Mellin integrals. Haar almost-everywhere vanishing would then suffice directly, without an intervening continuity argument. This implication remains conditional on the unproved pole extraction.

## Gates

- [x] Uniform two-endpoint resonant-core estimate, paper proof and Lean.
- [x] Whole positive-line Haar synthesis and common-strip Mellin interchange, paper proof and Lean.
- [ ] Normal meromorphic convergence and upper-coordinate uniqueness.
- [ ] Determine whether almost-everywhere Haar equality suffices; do not infer it from pointwise uniqueness without regularity.

No positivity or bounded inverse is claimed.
