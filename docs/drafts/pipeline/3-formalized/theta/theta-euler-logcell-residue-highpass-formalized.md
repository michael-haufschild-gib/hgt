# Literal Euler multiplication has a noncompact residue channel beyond the logarithmic continuum clock — Lean certificate

- **Paper card:** `theta-euler-logcell-residue-highpass.md`
- **Lean modules:**
  - `GaloisForLFunctions.HTGeometry.PositiveIntegerBlockOperators` — division-block operators `f ↦ w(m) f(⌊m/b⌋)` on `ℓ²(ℕ₊)`. It covers the block Gram identity, adjoint compositions `A_w* A_v = κ I`, isometries, norm bounds, composition, the Hilbert–Schmidt criterion and compact finite truncations.
  - `GaloisForLFunctions.RHTower.ThetaEulerLogCellResidueChannels` covers:
    - the essential norm of a block operator;
    - logarithmic cells, the cell weights `c_{n,r}`, and the operators `S_p`, `W_p`, `V_p`, `R_p`;
    - claims (1)–(7) and the invariant-hull statements;
    - the cell isometry `U`, the half-line right translation `T_a`, and the pullback `W_p = U* T_{log p} U`.
  - `GaloisForLFunctions.RHTower.QuasiPolynomialBlaschkeIsometry` — decaying quasi-polynomials. The Blaschke step `B_λ` has Laplace multiplier `(λ−q)/(λ+q)` and is an `L²(0,∞)` isometry (energy identity). It also proves `(ℒE)' = −ℒ(sE)`.
  - `GaloisForLFunctions.RHTower.ThetaEulerLogCellSeedVacuum` covers:
    - the literal seed atoms, the Hilbert–Schmidt synthesis `C`, and `C S_p = T_p C`;
    - the separators `g_k` built from finite Blaschke products;
    - the vacuum separation (10) and the source extraction (10a);
    - the bounded full-line synthesis (Gram bound and Schur test) and the zero-extended separator.
- **Umbrellas:** `GaloisForLFunctions.HTGeometry` (block operators) and `GaloisForLFunctions.RHTower` (the three RH-side modules).
- **Verification:**
  - Targeted `lake build` of every module.
  - `lake env lean` audit clean (no errors, no warnings) on all four modules.
  - `#print axioms` = `propext`, `Classical.choice`, `Quot.sound` for all 332 declarations of the four modules.
  - No `sorry`.
  - The only hypotheses are the card's quantifiers: integers `p, q ≥ 2` (primes where the card says prime), `n ∈ ℕ₊`, and vectors of the Hilbert spaces.

Dictionary:
- `H = ℓ²(ℕ₊) = lp (fun _ : ℕ+ => ℂ) 2` with `e_n = lp.single 2 n 1`.
- `S_p = eulerLabelShift p`, `W_p = logCellShift p`, `V_p = uniformResidueShift p`, `R_p = residueChannel p`.
- `ℓ_n = logCell n`; `c_{n,r} = logCellWeight p (n p + r) = √(ℓ_{pn+r}/ℓ_n)`; `I_n = logCellSet n`.
- `U = logCellEmbedding` (`U e_n = logCellVec n`); `T_a = halfLineRightShift a` on `L²(0,∞) = Lp ℂ 2 halfLineMeasure`.
- `‖·‖_ess = essentialNorm`; Schatten₂ = `ContinuousLinearMap.IsHilbertSchmidt`.
- `h = thetaCuspLogSeed`.
- `C = seedSynthesis` (`C e_n = seedAtomLp n`, representative `seedAtomFun n x = n^{-1/2} h(x + log n)`).
- `T_p = p^{-1/2} halfLineLeftShift (log p)`.
- `k = eulerSourceLp` (a.e. `thetaCuspFullSource` on `x ≥ 0`).
- The full-line synthesis is `seedLineSynthesis`, with atoms `seedAtomLine n`.

| Card item | Lean theorem |
|-|-|
| **(1)** `S_p S_q = S_{pq}`; `S_p` isometric, `S_p e_n = e_{pn}` | `eulerLabelShift_comp`, `norm_eulerLabelShift_apply`, `eulerLabelShift_single` |
| **(1)** the cells partition `[0,∞)`; `U e_n = 1_{I_n}/√ℓ_n` is an isometry | `pairwise_disjoint_logCellSet`, `orthonormal_logCellVec`, `logCellIsometry`, `norm_logCellEmbedding_apply`, `adjoint_logCellEmbedding_comp` |
| **(1)** translating `I_n` by `log p` gives `⋃_{r<p} I_{pn+r}`, so `U(H)` is `T_{log p}`-invariant with pullback `W_p = U* T_{log p} U` | `indicator_Ico_log_eq_sum`, `halfLineRightShift_logCellVec`, `halfLineRightShift_comp_logCellEmbedding`, `halfLineRightShift_mem_range_logCellEmbedding`, `logCellShift_eq_adjoint_comp` |
| **(1)** `W_p e_n = Σ_r c_{n,r} e_{pn+r}` with `c_{n,r} = √(ℓ_{pn+r}/ℓ_n)`; `Σ_r c² = 1` (telescope); `W_p W_q = W_{pq}`; `W_p` isometric | `logCellShift_single_apply`, `sum_logCell_block`, `sum_sq_logCellWeight`, `divBlockMass_logCellWeight`, `logCellWeight_mul`, `logCellShift_comp`, `norm_logCellShift_apply` |
| `V_p` isometric | `norm_uniformResidueShift_apply` |
| **(2)** `W_p − V_p ∈ Schatten₂`, via `ℓ_n = 1/n + O(n⁻²)`, `c_{n,r} = p^{-1/2} + O(1/n)` | `le_logCell`, `logCell_le`, `abs_logCell_ratio_sub_le`, `abs_logCellWeight_sub_le`, `isHilbertSchmidt_logCellShift_sub_uniformResidueShift` |
| **(3)** `‖S_p − W_p‖_ess = √(2 − 2/√p)`, with `‖(S_p − W_p)e_n‖² = 2 − 2c_{n,0}` | `divBlockMass_label_sub_logCellWeight`, `essentialNorm_eulerLabelShift_sub_logCellShift` (block essential norm: `essentialNorm_divBlockOp`) |
| **(4)** `R_p = S_p − p^{-1/2}V_p`, `V_p* R_p = 0`, `R_p* R_p = (1 − 1/p) I` | `residueChannel_eq`, `adjoint_uniformResidueShift_comp_residueChannel`, `adjoint_residueChannel_comp_self`, `norm_residueChannel_apply` |
| **(5)** `S_p = p^{-1/2} W_p + R_p + Schatten₂` | `isHilbertSchmidt_eulerLabelShift_sub` |
| **(6)** `‖S_pW_p − W_pS_p‖_ess = √(2 − 2/p)`, overlap only at `r = 0`, `‖·e_n‖² = 2 − 2c_{n,0}c_{pn,0}` | `divBlockGram_commutator`, `essentialNorm_commutator_eulerLabelShift_logCellShift` |
| **(7)**, **(8)** `⋂_p ker R_p* = ℂe_1` via the block averages and the prime-block maximum principle | `inner_residueChannel_single`, `adjoint_residueChannel_eq_zero_iff`, `sum_residueChannelWeight_block`, `forall_adjoint_residueChannel_eq_zero_iff`, `iInf_ker_adjoint_residueChannel` (maximum principle: `highpass_prime_average_supported_at_one`) |
| **(7)** `closure span{Ran R_p : p prime} = {f : f(1) = 0}` | `topologicalClosure_iSup_range_residueChannel`, `mem_vacuum_orthogonal_iff` |
| literal source shift `p^{-1/2}S_p`: residue part of norm `p^{-1/2}√(1−1/p)` on every basis vector | `norm_sourceShift_residue_single` |
| the smallest closed `S`-invariant subspace containing the prime vectors is `ℓ²(ℕ_{≥2})`; adding `e_1` gives `H`; the prime-only span is not invariant | `single_mem_vacuum_orthogonal`, `eulerLabelShift_mem_vacuum_orthogonal`, `vacuum_orthogonal_le`, `vacuum_orthogonal_sup_span`, `eulerLabelShift_two_not_mem_primeSpan` |
| **(9)**, **(11)** `C e_n = n^{-1/2}h(·+log n) = 2πn² u^{5/4}(2λ_n u − 3)e^{−λ_n u}`; `C` is Hilbert–Schmidt; `C S_p = T_p C` | `seedAtomFun_eq`, `summable_norm_seedAtomLp`, `seedSynthesis`, `isHilbertSchmidt_seedSynthesis`, `sourceShift_seedAtomLp`, `seedSynthesis_comp_eulerLabelShift` |
| **(12)**, **(13)** separating functional through Laplace zeros: `⟪g, C e_n⟫ = π n² e^{−λ_n}((2λ_n − 3)ℒr(λ_n) + 2λ_n ℒ(v r)(λ_n))`, i.e. `−2λ_n F'(λ_n) − 3F(λ_n)` for `F(s) = e^{−s}ℒr(s)` | `logSubst`, `integral_logSubst`, `separatorVec`, `inner_separatorVec_seedAtomLp` |
| Blaschke functions: the double zeros at `λ_n` (`n ≥ 2`), and `F'(λ₁) ∝ B(λ₁) ≠ 0` | `seedSeparator`, `seedSeparator_zeros`, `exp_neg_eight_le_prod_rateBlaschkeFactor_sq`, `integral_norm_sq_seedSeparator`, `integral_norm_sq_blaschkeStep`, `laplace_blaschkeStep` |
| **(10)** `C e_1 ∉ closure span{C e_n : n ≥ 2}`; ∃ `g ∈ L²(0,∞)`: `⟪g,Ce_n⟫ = 0` (`n ≥ 2`), `⟪g,Ce_1⟫ ≠ 0` | `seedAtomLp_one_not_mem_closure`, `exists_seed_vacuum_separator` |
| **(10a)** `k` converges absolutely in half-line `L²`, and `⟪g,k⟫ = Σ⟪g,Ce_n⟫ = ⟪g,h⟫ ≠ 0` | `hasSum_seedAtomLp`, `eulerSourceLp_coeFn`, `inner_eulerSourceLp_of_separator`, `exists_seed_vacuum_separator_source`, `seedAtomLp_one_coeFn` |
| the full-line synthesis is bounded: Gram matrix `(nm)^{-1/2}⟨h(·+log n), h(·+log m)⟩` decays like `e^{−2|log n − log m|}`, weighted Schur test | `abs_thetaCuspLogSeed_le`, `norm_inner_seedAtomLine_le`, `sum_schurWeight_le`, `norm_sq_sum_seedAtomLine_le`, `seedLineSynthesis`, `seedLineSynthesis_single` |
| the separator extended by zero separates the full-line atoms | `inner_halfLineExtend_seedAtomLine`, `exists_seed_vacuum_separator_line` |

Proof-route note:
- The card obtains the separating functional from the infinite Blaschke product `B(s)` and the Hardy–Laplace Paley–Wiener theorem.
- The Lean proof uses the finite products `∏_{j≤k+1} b_j²` instead. The corresponding separators `g_k` are explicit elements of `L²(0,∞)`, and their energy is constant because each Blaschke step is an `L²` isometry.
- They annihilate `C e_2, …, C e_{k+1}` and have `|⟪g_k, C e_1⟫| ≥ 2πλ₁e^{−λ₁}e^{−8}/(λ₁+1)²`. Hence `C e_1` is at positive distance from the higher atoms.
- The separator `g` of (10) is the component of `C e_1` orthogonal to their closed span. The theorem (10) is the card's statement, and the formula (13) is proved in the same Laplace form.
