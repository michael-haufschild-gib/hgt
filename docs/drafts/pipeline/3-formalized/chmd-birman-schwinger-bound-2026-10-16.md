# CHMD: primitive bound states are paid for by off-line zeros (Birman–Schwinger upper bound)

- **ID:** chmd-birman-schwinger-bound-2026-10-16
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean), unconditional
- **Source:** CHMD route; continuation of chmd-spectral-riemann-criterion-2026-10-16 (`¬RH ⟺` primitive bound state) and chmd-pure-point-above-threshold-2026-10-16; corpus inputs: `ZeroConfig.W`/`Wsummand` (Zeta23), `WeilConditional.summable_Wsummand`, `ZeroSide.gammaOf_of_re_eq_half`, `weilForm_compactLift`
- **Statement:** If `offLineZeros = {ρ ∈ carrier : Re ρ ≠ 1/2}` is finite, then every orthonormal family `e_1, …, e_k` of primitive (`⟪e_i, 1⟫ = 0`) eigenvectors of the arithmetic resolvent with eigenvalues `μ_i > 1/2` satisfies `k ≤ 2 · offLineZeros.ncard`. Also: the zero-side defect inequality `Re W(f,f) + Σ_{off-line ρ} (m_ρ/2)|f̂(γ_ρ) − f̂(γ̄_ρ)|² ≥ 0` for all compactly supported `C²` tests, and the Lipschitz bound of the Weil quadratic form on the Doob graph.
- **Status:** STATUS MUST-1553. One leaf (`CHMDBirmanSchwingerBound`, 31 declarations), axioms propext/Classical.choice/Quot.sound; plain `lake env lean` audit clean; `lake build --old` green; wired; index refreshed; global lint clean of proof debt (remaining errors are other agents' unwired modules).

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  fully-proven (paper proof below = the Lean development)
- [x] 2 → 3  formalized: `re_W_add_defect_nonneg`, `weilForm_rieszLift_sum_le`, `exists_compactTests_negative_definite`, `card_le_two_mul_offLine_of_negative_definite`, `orthonormal_primitive_bound_states_le`
- [ ] 3 → 4  publication-ready

## Obstacle addressed
After MUST-1552 the CHMD route states RH as the absence of primitive bound states of the arithmetic
resolvent above `1/2`. The missing structure was the relation between such bound states and the
zeros themselves: do bound states merely *detect* off-line zeros (existence, MUST-1552) or are they
*counted* by them? This card proves the counting inequality in one direction: the total multiplicity
of primitive bound states is at most twice the number of off-line zeros. The mechanism is a
finite-rank positivity of the Weil form (positive up to the off-line defect functionals) transported
to the completed graph through the Lipschitz continuity of the Weil quadratic form and the density
of compact tests, followed by a rank argument.

## Paper proof
*Defect inequality.* `W(f,f) = Σ_ρ m_ρ a_ρ conj b_ρ`, `a_ρ = f̂(γ_ρ)`, `b_ρ = f̂(γ̄_ρ)`.
`|a − b|² = |a|² + |b|² − 2Re(a b̄)` gives `Re(a b̄) ≥ −|a−b|²/2`, hence
`Re(m a b̄) ≥ −(m/2)|a − b|²` for every zero; for on-line zeros `γ_ρ` is real so `a = b` and the
correction vanishes. The zero side is absolutely summable for `C²` compactly supported `f` (corpus),
so `Re W(f,f) = Σ_ρ Re(…) ≥ −Σ_{off-line}(m_ρ/2)|a_ρ − b_ρ|²`, a finite sum.

*Negative definiteness.* `Riesz(Σ c_i e_i) = Σ c_i Riesz(e_i)`; for primitive `w`,
`weilForm(Riesz w) ≤ E(Riesz w) = ⟪w,Rw⟫ − 2‖Rw‖²`; with `w = Σ c_i e_i`, orthonormality gives
`⟪w,Rw⟫ = Σ c_i² μ_i`, `‖Rw‖² = Σ c_i² μ_i²`, so `weilForm ≤ Σ c_i² μ_i(1 − 2μ_i) ≤ −δ Σ c_i²`,
`δ = min_i μ_i(2μ_i − 1) > 0`.

*Perturbation.* `weilForm p = B(p,p)` with `B` bounded bilinear (`|B(p,q)| ≤ C‖p‖‖q‖`,
`C = 3 + 2‖1‖² + 2‖τ‖²`), so `|weilForm p − weilForm q| ≤ C(‖p‖+‖q‖)‖p−q‖`. Choosing compact tests
`q_i` with `‖q_i − p_i‖ < η`, `η ≤ 1`, `C(2P+1)(k+1)η ≤ δ/2` (`P = Σ‖p_i‖`), and using
`(Σ|c_i|)² ≤ kΣc_i²`, one gets `weilForm(Σ c_i q_i) ≤ −(δ/2)Σ c_i² < 0` for `c ≠ 0`.

*Rank.* Write `q_i = compactLift v_i`; the combination `Σ c_i q_i` is a compact test
`compactLift w_c` with `w_c = Σ c_i v_i` a.e. (sources), so `weilForm(Σ c_i q_i) = Re W(f_c, f_c)`
with `f_c = Θ w_c = Σ c_i Θ v_i` a.e. The map `L : ℝ^k → ℂ^{off-line}`, `L(c)_ρ = Σ c_i d_ρ(Θ v_i)`,
is linear and `L(c)_ρ = d_ρ(f_c)` (Fourier transform is linear). If `L(c) = 0` then the defect
inequality gives `Re W(f_c,f_c) ≥ 0`, contradicting negativity unless `c = 0`. Hence
`k = dim ℝ^k ≤ dim_ℝ ℂ^{off-line} = 2 · #(off-line zeros)`.

## Lean module (namespace `RHTower.CHMDPolar`)
`RHTower/CHMDBirmanSchwingerBound.lean` — `offLineZeros`, `zeroDefect`, `zeroDefect_eq_zero`,
`defectWeight`, `neg_defectWeight_le_re_Wsummand`, `offLineFinset`, `mem_offLineFinset`,
`card_offLineFinset`, `re_W_add_defect_nonneg`, `rieszLift_sum`, `weilForm_le_sourceEnergy_of_primitive`,
`weilForm_rieszLift_sum_le`, `weilBilin`, `weilForm_eq_weilBilin`, `weilBilin_sub_left/right`,
`weilBilinConst`, `abs_weilBilin_le`, `abs_weilForm_sub_le`, `sum_sq_pos_of_ne_zero`,
`exists_compactTests_negative_definite`, `Lp_coeFn_sum_smul`, `paperFT_sum_mul`,
`contDiff_phiDoobTest_ofReal`, `hasCompactSupport_phiDoobTest_ofReal`,
`card_le_two_mul_offLine_of_negative_definite`, `orthonormal_primitive_bound_states_le`.

## Big picture
- CHMD spectral dictionary, complete at the structural level: `σ(R) ⊆ [0,1]`, `σ_ess(R) ⊆ [0,1/2]`
  with `1/2 ∈ σ_ess`; `σ(R) ∩ (1/2,1]` pure point, finitely degenerate, locally finite;
  `¬RH ⟺` a primitive bound state exists; and (this card) total primitive bound-state multiplicity
  `≤ 2·#(off-line zeros)` when finite.
- The factor `2` comes from counting the complex defect functionals as two real ones; the reflection
  symmetry `ρ ↦ 1 − ρ̄` and conjugation `ρ ↦ ρ̄` should reduce it to the number of off-line zero
  *quadruple-orbits*, i.e. the true Birman–Schwinger count.
- The lower half (each off-line zero pair forces a bound state) is the remaining direction; MUST-1552
  gives it for "at least one".

## Next conjectures
1. Lower bound: `#(off-line zero orbits) ≤` number of primitive bound states (with multiplicity):
   construct, from a deep zero, a negative-definite subspace of the Weil form of the right dimension
   (corpus: `IsolatedDeepZeroWeilDetection`, `Wsummand_modulatedTest_deep_pair`).
2. Sharpen the factor `2` by the parity/reflection structure of the defects.
3. Remove the finiteness hypothesis: a countable version with the defect sum as an infinite series.
