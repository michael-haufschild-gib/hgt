# Nonnegative CCM ground states force RH (Barta test with Riemann's kernel)

- **ID:** ccm-positive-ground-state-barta
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean, standard axioms; MUST-851)
- **Source:** RH goal loop (Opus) row 585; MUST-842/844 (`3-formalized/ccm-eigenvector-low-frequency-mass.md`); rows 377–378 (Collatz–Wielandt idea, pole-block obstruction)
- **Statement (Lean):** There are `C, b₁` such that every NONNEGATIVE eigenvector `x` of the restricted Weil form at aperture `b ≥ b₁` (`Q_b(x,s) = μ⟨x,s⟩` for every smooth interior source `s`) whose mass on the edge `|t| > b − 2e^{−2b}` is at most half of `‖x‖₁` has `|μ| ≤ C(1+b)` (`exists_abs_eigenvalue_le_of_nonneg`). Hence RH holds if for all large `b` some full ground state is nonnegative with `‖x‖₂ ≤ e^{b}‖x‖₁/6` (`riemannHypothesis_of_nonneg_fullGrounds_of_norm_le`), or more generally with edge mass at most half (`riemannHypothesis_of_nonneg_fullGrounds`).

## Goal
MUST-844 needs nonnegative and symmetric-decreasing ground states, because the Gaussian window of MUST-842 loses `e^{a}` to edge mass (row 579). Riemann's kernel `Φ > 0` is an exact radical vector: `Φ̂ = Ξ` vanishes at every zero (`RiemannKernelWeilRadical`). Used as a Barta/Collatz–Wielandt test vector, its truncation residual at the edge is proportional to the edge value `Φ(a)`. That is exactly the weight with which a nonnegative `u` pairs against `Φ_a` at the edge, so the edge mass cancels.

Result: the RH content of the CCM ground state is its sign (Perron–Frobenius). Positivity is an exact mechanism, not an estimate with margin (big-picture §4). Its known obstruction is the rank-two pole block (rows 377–378).

## Gates
- [x] 0 → 1  in-progress: mechanism identified (row 585)
- [x] 1 → 2  paper proof below (constants explicit up to absolute factors)
- [x] 2 → 3  formalized (2026-10-09, seven modules, standard axioms)
- [ ] 3 → 4  (not pursued: no stage 4)

## Lean
Modules (in `RHTower.lean`, in this order): `RiemannKernelTailDecayRate` (L1), `CCMRiemannKernelBartaSources` (A), `CCMRestrictedWeilCrossFormBound` (C1), `CCMRiemannKernelBartaLayerBounds` (C2), `CCMRiemannKernelBartaEdgeFormDomain` (C3), `CCMRiemannKernelBartaFarTail` (B), `CCMNonnegativeGroundStateRH` (D).
- C1 `norm_ccmRestrictedWeilForm_smooth_le`: `‖Q_a(u,v)‖ ≤ ‖u‖₁(P₀ + S₀ + 2A(8 + (3/2)log(1/δ)) + δ(A+A′))` from the lag data of `v`.
- C2 `exists_bartaEdge_bound`: `‖Q_{b+3}(v,T_b)‖ ≤ ‖v‖₁Φ(b−2w)C(1+b)` for smooth `v`; C3 extends it to the form domain by density.
- B `exists_bartaFar_bound`: `‖Q_{b+3}(x,Φχ_{b+2,1})‖ ≤ ‖x‖₁Φ(b−2w)C`. At every zero, `γ²Ŝ(γ) = (Φ″ − S″)^(γ)` and the defect is `O(e^{9|t|}e^{−πe^{2|t|}})` beyond `b+1`.
- D: nesting `Q_b(x,Φχ) = Q_{b+3}(x′,Φχ_{b+2,1}) − Q_{b+3}(x′,T_b)`, overlap `Re⟨x,Φχ⟩ ≥ Φ(b−2w)(‖x‖₁ − edge)`, Cauchy–Schwarz on the edge (length `4e^{−2b}`), and the subexponential criterion plus antitonicity for small apertures.
Deviation from the paper plan: the far tail uses the compact test and the radical of `Φ″` (two integrations by parts on the compact source), not the tail transform. The loss is polynomial (`C(1+b)`), which suffices.

## Paper proof
Notation: `Φ` is Riemann's kernel (even, positive, `Φ̂ = Ξ`). `w = e^{−2a}/(2π)`. `χ` is a smooth cutoff, equal to `1` on `[−(a−w), a−w]` and supported in `(−a,a)`. `χ″` is a smooth cutoff, equal to `1` on `[−(a+1), a+1]` and supported in `(−(a+2), a+2)`. `M = Φ(χ″ − χ)` is supported in `a−w ≤ |t| ≤ a+2`.

1. **Eigen identity.** `Φχ` is a smooth interior source at aperture `a`, so `μ⟨u, Φχ⟩ = Q_a(u, Φχ)` (`formEigen_of_isFullGround`, or any eigenvector).
2. **Nesting.** Extend `u` by zero to aperture `a″ = a+2`. Then `Q_a(u,Φχ) = Q_{a″}(u,Φχ)` (`exists_ccmArchimedeanFormDomain_extension`, `ccmRestrictedWeilSourceQuadratic_eq_of_val_eq`; bilinear version by polarization).
3. **Radical at the larger aperture.** `Q_{a″}(u, Φχ″) = Σ_q F_u(γ_q)(Φχ″)^(−γ_q)` (zero-side identity for smooth interior sources). At every zero, `(Φχ″)^ = Ξ − (Φ(1−χ″))^ = −(Φ(1−χ″))^`, of size `≤ Φ(a+1)e^{O(a)}/(1+|γ|²)`, using two integrations by parts and the `riemannKernelDeriv` bounds. With `|F_u(γ)| ≤ ‖u‖₁e^{a″/2}`, this gives `|Q_{a″}(u,Φχ″)| ≤ ‖u‖₁Φ(a+1)e^{O(a)}`, which is negligible against `Φ(a)` (double-exponential gap).
4. **Edge pairing (time domain).** `Q_a(u,Φχ) = Q_{a″}(u,Φχ″) − Q_{a″}(u,M)`. Compute `Q_{a″}(u,M)` with the kernel form (`suzukiRestrictedWeilForm_eq_constrainedKernelForm`, polarized and extended to the form domain by density): `A(S)⟨u,M⟩ + ∫_0^S K₊(h)[⟨u,M⟩ − ½(⟨u,τ_hM⟩ + ⟨τ_hu,M⟩)]dh + poles + primes`. Since `u` lives in `[−a,a]` and `M` in `|t| ≥ a−w`, only the edge contributes:
   - primes: `Σ_nΛ(n)n^{−½}(⟨u,τ_{log n}M⟩ + ⟨τ_{log n}u,M⟩) ≤ 2·max_nΛ(n)n^{−½}·(1+e^{−2π}+…)·Φ(a−w)‖u‖₁ ≤ 1.5Φ(a−w)‖u‖₁·(1+o(1))`. For fixed `y`, only prime powers with `log n ∈ (y+a, y+a+O(w))` matter, because `Φ(a+δ) ≤ Φ(a)e^{−(2πe^{2a}−5)δ}`, and consecutive ratios are `≤ e^{−2π}` for `n ≤ e^{2a}`;
   - poles: `≤ 2‖u‖₁e^{a/2}·∫_{|t|≥a−w}Φ(t)e^{|t|/2} ≤ C‖u‖₁Φ(a−w)e^{−a}`;
   - archimedean: for `h < w`, smoothness of `M` (`|M′| ≲ Φ(a−w)/w`) gives `≲ Φ(a−w)√w‖u‖₂`; for `h ≥ w`, `∫_w^S K₊ ≲ a`, giving `≲ aΦ(a−w)√w‖u‖₂`;
   - `A(S)⟨u,M⟩`: `|A(S)| = O(1)` and `|⟨u,M⟩| ≤ Φ(a−w)∫_{a−w≤|t|≤a}|u| ≤ Φ(a−w)√(2w)‖u‖₂`.
5. **Overlap.** For `u ≥ 0`: `⟨u,Φχ⟩ ≥ Φ(a−w)∫_{|t|≤a−w}u ≥ Φ(a−w)(‖u‖₁ − √(2w)‖u‖₂)`, using `Φ ≥ Φ(a−w)` on `[−(a−w), a−w]`. That requires eventual monotonicity of `Φ` plus positivity (`riemannKernelReal_pos`).
6. **Conclusion.** `|μ| ≤ [1.5‖u‖₁ + C a e^{−a}‖u‖₂]/(‖u‖₁ − C e^{−a}‖u‖₂)`, bounded under the stated `L²/L¹` condition. Then antitonicity and `exists_ccmRestrictedWeilGroundEnergy_lt_of_not_riemannHypothesis` give RH.

Sanity checks:
- For the pole-free Markov operator the residual of `Φ_a` is the pole vector `c·cosh(t/2)`, not `O(Φ(a))`, so the argument correctly gives only `|μ_H| ≲ e^{a/2}/Φ(a)`.
- Under ¬RH the very negative ground states change sign (resonance `e^{δ|t|}cos(γ₀t)`), consistent with the theorem.

## Lean plan (each step a module or section; search the corpus first)
- L1. `Φ` toolkit: eventual monotonicity of `riemannKernelReal` (or `riemannPhiKernel`) on `[t₀,∞)`; a decay-ratio inequality `Φ(t+δ) ≤ Φ(t)e^{−cδe^{2t}}`; bounds on `Φ′, Φ″` on the tail. Corpus: `RiemannKernelCuspSeries` (`riemannKernelDeriv`, `norm_riemannKernelDeriv_*`), `CuspSeriesBulkTailBounds`, `riemannKernelReal_pos`.
- L2. Cutoffs with transition width `w` (scaled `Real.smoothTransition`), and the sources `Φχ` (aperture `a`), `Φχ″` (aperture `a+2`) as `CCMComplexSmoothInteriorSource`.
- L3. Radical bound at aperture `a+2`: `‖Q_{a+2}(u, Φχ″)‖ ≤ ‖u‖₁·ε_a` with `ε_a/Φ(a) → 0`. Uses the zero-side identity (`zeroSide_eigen_of_formEigen` machinery: `tsum_mul_integral_eq_integral_zeroKernel`), `riemannPhiTransform_eq_zero_of_nontrivial`, `paperFT_riemannPhiKernel`, and the tail transform bounds (`TruncatedRiemannKernelWeilEnergy`: `nearRadicalTail_*`, extended to two derivatives).
- L4. Bilinear time-domain kernel form on the CCM form domain (polarization of `suzukiRestrictedWeilForm_eq_constrainedKernelForm`, plus a density extension), and the edge estimates of step 4.
- L5. Overlap bound for nonnegative `u`, assembly of the eigenvalue bound, and the RH capstone.

## Refined Lean route (2026-10-09, after corpus audit)
Polynomial losses suffice: `|μ_B| ≤ poly(B)` at all large `B` gives RH via `riemannHypothesis_of_polarGroundEnergy_subexponential` (`μ ≤ μ_polar`, antitone for small `B`).

- (i) Edge piece, time domain: for smooth interior `u, v` at aperture `a″`, `Q(u,v) = ccmRestrictedPolarPrimeFull(c_{uv}) − ccmArchimedeanWeilDistribution(c_{uv})` (`ccmRestrictedWeilForm_ccmComplexSmooth_eq_polarPrimeFull_sub_archimedean`, `SuzukiCCMMixedPolarFactorization`). The archimedean part has the sharp kernel form `F(0)/2·(log4π+γ) + ∫_0^∞ sharpIntegrand` (`ccmArchimedeanWeilSharpDistribution`). Bound it for `v = T₁ = Φ(χ″−χ)` by `K(a)‖u‖₁`, `K(a) = Φ(a−w′)·poly(a)`, using the cross-correlation `c_{uT₁}` (`|c(h)−c(0)| ≤ h‖u‖₁ sup|T₁′|` near `0`, and the `log(1/w′)` tail of `1/sinh`). The primes need a sparse sum: `Σ_n Λ(n)n^{−½}Φ(x ± log n)1_{tail}` with super-decay `Φ(t) ≤ Φ(s)e^{−πe^{2s}(t−s)}`.
- (ii) Extend (i) to form-domain `u` (the ground state) by density of smooth interior sources in the form domain, with `Q` and `‖·‖₁` continuous.
- (iii) Nesting `Q_a(u,Φχ) = Q_{a″}(u_ext,Φχ″) − Q_{a″}(u_ext,T₁)` (bilinearity, `exists_ccmArchimedeanFormDomain_extension`).
- (iv) Far tail by zero side: `Q_{a″}(u_ext,Φχ″) = −Σ_q F_u(γ_q)(Φ(1−χ″))^(−γ_q)`, with two integrations by parts. The bound `‖u‖₁Φ(a+1)e^{O(a)}` is negligible against `Φ(a)`.
- (v) Eigen identity; (vi) overlap `⟨u,Φχ⟩ ≥ Φ(a−w′)∫_{|t|≤a−w′}u`; (vii) assembly `|μ| ≤ poly(a)` when `‖u‖₂ ≤ e^{a}‖u‖₁/3` (edge mass `≤ √(2w′)‖u‖₂`, `w′ = e^{−2a}`); (viii) capstone.

Φ toolkit (L1), all termwise on the cusp series `S_R`, `R = 4π²X² − 6πX`:
- `DR + πX·R = −πX(4π²X² − 24πX + 15) ≤ 0` for `X ≥ 1.7`, so `Φ′(u) ≤ −πe^{2u}Φ(u)` for `u ≥ 0.27`;
- hence `Φ` is antitone on `[0.27,∞)`, and `Φ(t) ≤ Φ(s)e^{−πe^{2s}(t−s)}` for `0.27 ≤ s ≤ t`;
- `min_{[−b,b]}Φ = Φ(b)` for large `b` (compactness on `[0,0.27]`);
- lower bound `Φ(a) ≥ ½·(n=1 term)` and upper bounds for derivatives (`abs_cuspSeries_le`).

## Log
- 2026-10-09 — created (row 585): paper proof; Lean plan L1–L5.
- 2026-10-09 — L1 done: `RHTower/RiemannKernelTailDecayRate` (`riemannKernelReal_le_mul_exp`, `riemannKernelReal_antitoneOn`, `exists_riemannKernelReal_edge_min`), wired, `lake --old build` green.
- 2026-10-09 — modules fixed after the corpus audit:
  - A. Cutoffs `χ = ST((a−w−t)/w)ST((a−w+t)/w)` (1 on `|t| ≤ a−2w`, 0 for `|t| ≥ a−w`) and `χ″ = bulkCutoff(a+2)`. Sources `Φχ` (aperture `a`), `Φχ″` and `T₁ = Φ(χ″−χ)` (aperture `a″ = a+3`). Smoothness via `contDiff_riemannKernelDeriv`; `riemannPhiKernel_eq_ofReal`.
  - B. Far tail: `Q_{a″}(x,Φχ″) = ∫conj(timeRep x)·Z_{Φχ″}` (`ccmRestrictedWeilForm_eq_integral_representer`, `integral_timeRep_formRepresenter_eq`). `|Z(t)| ≤ e^{|t|/2}Σ_q|(Φ(1−χ″))^(γ_q)|`, with two integrations by parts (`abs_cuspSeries_le` for `Φ, Φ′, Φ″`). Lower bound `Φ(t) ≥ cuspTerm R 1 t`.
  - C. Edge: for smooth interior `v`, `Q(v,T₁) = ccmRestrictedPolarPrimeFull(c) − ccmArchimedeanWeilDistribution(c)`, `c(h) = ∫T₁(x)·conj v(x−h)`. Pole `≤ C‖v‖₁Φe^{−a}`; primes `≤ 11·max(Λ/√k)·Φ(a−w)‖v‖₁` (sparse sum, `criticalMellinAtomWeight`); archimedean, with the δ-split at `δ = sup|c|/sup|c′|`, `≤ C‖v‖₁Φ(a−w)·(1 + log(1+sup|T₁′|/sup|T₁|))`. Extend to the form domain by `denseRange_ccmComplexSmoothInteriorSource_toCCMFormVector`.
  - D. Assembly and capstone at all large apertures `B` via `riemannHypothesis_of_polarGroundEnergy_subexponential`.
- 2026-10-09 — module A done: `RHTower/CCMRiemannKernelBartaSources` (`bartaCutoff`, `bartaProfile`, `bartaSource`, `bartaLayerSource`, `bartaLayer_bounds`).
- 2026-10-09 — module C1 done: `RHTower/CCMRestrictedWeilCrossFormBound`, with `norm_ccmRestrictedWeilForm_smooth_le`: `‖Q_a(u,v)‖ ≤ ‖u‖₁(P₀ + S₀ + 2A(8 + (3/2)log(1/δ)) + δ(A+A′))`. Also `norm_ccmArchimedeanWeilSharpDistribution_le` and the cross-correlation Lipschitz and polar-prime bounds. Next: C2, which supplies `P₀, S₀, A, A′` for the layer `T₁` from the Φ decay.
- 2026-10-09 — module C2 done: `RHTower/CCMRiemannKernelBartaLayerBounds`. `exists_bartaEdge_bound`: `∃ C, ∀ b ≥ 1, ∀` smooth interior `v` at aperture `b+3`, `‖Q(v,T_b)‖ ≤ ‖v‖₁·Φ(b−2w)·C(1+b)`. Also `sum_rpow_tail_le` (sparse sum), `bartaLayer_pole_lag_le`, `bartaLayer_prime_lag_le`, `abs_deriv_bartaLayerFn_le`, `integral_bartaLayerFn_le`, `exp_neg_pi_exp_le_riemannKernelReal`, `setIntegral_Ioi_riemannKernelReal_le`. Next: C3, density extension to form-domain vectors.
- 2026-10-09 — modules C3, B, D done; card to 3-formalized. Capstones `riemannHypothesis_of_nonneg_fullGrounds{,_of_norm_le}`, standard axioms; loop row 597; MUST-851.
- 2026-10-09 — status of the hypothesis (loop rows 598–600). Without signs the receiver becomes the overlap bound `|μ|·|⟨x,Φχ⟩| ≤ C(1+b)Φ(b−2w)‖x‖₁` (`exists_abs_eigenvalue_mul_overlap_le`, `riemannHypothesis_of_fullGrounds_overlap`); that bound is nearly a reformulation, because `Φχ` is a near-null vector. The near-null cluster has dimension `≍ e^{2a}` (`zeta_weil_near_radical_dimension`). Under ¬RH the ground state is an outlier below it, orthogonal to every near-radical test up to `edge·C(1+a)/|μ|`. The hypothesis "ground state nonnegative" therefore contains RH (no outlier), so it cannot be produced independently. NO POSITIVE SALVAGE beyond the Lean theorems.
- 2026-10-09 — vacuity caveat (row 602, paper): under RH the cluster-model ground state changes sign about one unit before the edge (zeros of the extremal kernel polynomial), so the literal positivity hypothesis may fail even under RH. Canonical form: the overlap receiver `riemannHypothesis_of_fullGrounds_overlap`.
