# CCM published-result gap closure (from `docs/reports/ccm-comparison-us-vs-sota.md`)

- **ID:** `ccm-published-gap-closure-2026-10-21`
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean) / FORMALIZATION PROGRAM
- **Source:** `docs/reports/ccm-comparison-us-vs-sota.md` §"Published results still lacking"; parent ledger
  `ccm-primary-literature-to-lean-parity.md`
- **Statement:** Close, unconditionally in Lean (no premises, no axioms, no computations), the four
  published CCM results the report could not locate end-to-end.

## Targets (report priority order) and plan

| # | Published result | Plan | Status |
|---|---|---|---|
| T2 | CCM 2023 Thm 4.6: `θ_S : Sonin_λ(ℝ) ≃ Sonin_λ(X_S)` for every finite `S`, Fourier compatible | `θ_S = w_S ∘ E_S`, `E_S = ∏_{p∈S}(1 − p^{-1/2}ϑ(p))` (Neumann-invertible, `‖p^{-1/2}ϑ(p)‖<1`); `E_S^{±1}` preserve `ran(1−P_λ)`; `F_S θ_S = θ_S F` ⇒ `Sonin_λ(X_S) = θ_S(Sonin_λ(ℝ))` | **Lean-closed** (`FieldOneFiniteStageThetaSoninIsomorphism`, `FieldOneFiniteStageThetaHardyTitchmarsh`) |
| T4 | CCM 2023 Thm 5.2(iv): Jacobi/Gamma data = even metaplectic representation | build sl₂ operators from Jacobi coefficients, identify on even Hermite basis | **Lean-closed** (`CCMMetaplecticOscillatorTriple`, `CCMMetaplecticRepresentationIdentification`) |
| T3 | CCM 2025 Thm 5.10: `D_log^{(λ,N)}` self-adjoint, `det_reg(D_log − z) = −i λ^{−iz} ξ̂(z)` | finite-rank perturbation of `diag(πn/a)`; ζ-regularized determinant defined explicitly; unconditional dichotomy, simple-even as a corollary | **Lean-closed** (`HTGeometry/ComplexShiftLerch`, `CCMCircleDiracZetaDeterminant`, `CCMLogDiracRankOneDeterminant`, `CCMLogDiracDeterminantTheorem`) |
| T1 | CC 2020 Thm 1: `W_∞(g∗g*) ≥ Tr(ϑ(g)Sϑ(g)*)`, supp `g ⊆ [2^{-1/2},2^{1/2}]`, `ĝ(i/2)=ĝ(0)=0` | `−W(H) = Tr(ϑ(H)S) + Tr(ϑ(H)G)`, `G = 1−P−P̂−S`; T1 ⟺ `Re Tr(ϑ(g)Gϑ(g)†) ≥ 0` | **framework + cutoff-Λ trace formula + small-support domination Lean-closed** (`CCMArchimedeanSoninGenericDecomposition`, `CCMArchimedeanSoninCutoffTraceFormula`); the support-`log 2` inequality itself **open** (paper: numerical prolate input) |

## Gates
- [x] 0 → 1  in-progress: targets identified, attack per target sketched
- [ ] 2 → 3  formalized: each target's Lean theorem, `lake env lean` clean, axioms audited, wired

## Log
- 2026-10-21 — created; corpus survey: T2 has literal `X_S`, `F_S`, Def. 4.5 Sonin space
  (`FieldOneFiniteStageClassSonin`), θ-core/Euler identification; missing the isomorphism theorem.
- 2026-10-21 — T2 closed: `fieldOneFiniteStageSoninThetaEquiv S λ : Sonin_λ(ℝ) ≃L[ℂ] Sonin_λ(X_S)`,
  `fieldOneFiniteStageSemilocalSonin_eq_map_literalTheta`, whole-L² Fourier compatibility
  `fieldOneFiniteStageClassFourierUnitary_literalTheta`. Mechanism: `w_∞`, `w_S` carry both cutoffs to
  `1_{u≤λ}` (split point of `(k,u)` has module `u`); `1 − p^{-1/2}U_p^*` maps the closed vanishing
  space onto itself (restricted Neumann unit). Direct `lake env lean` clean; axioms
  `propext, Classical.choice, Quot.sound`; wired into `RHTower.lean`; olean built single-threaded.
  Open: T2b = finite-S dual Hardy–Titchmarsh square `υ_S ∘ E_S = ι'_S ∘ υ_∞` (one-prime case exists in
  `HardyTitchmarshSemilocalSquare`).
- 2026-10-21 — T4 closed. Oscillator triple `H = x∂+½, E = −iπx², F = −(i/4π)∂²` is `IsSl2Triple` on
  `𝓢(ℝ,ℂ)` (`ccmOscillator_isSl2Triple`); CCM elements `J = i(E+F)`, `N = (i/2)(E−F) − ¼`,
  `[J,N] = H` (`ccmOscillatorJacobi_eq`, `ccmOscillatorNumber_eq`, `ccmOscillator_lie_jacobi_number`);
  on normalized `ĥ_{2n}`, `J` is the Jacobi matrix with the forced coefficients and `N` the number
  operator. Sequence side: `J`, `N` realize the corpus formal actions; `[C,N] = J`, `[J,C] = −(4N+1)`;
  CCM triple `(2N+½, (J−C)/2, −(J+C)/2)` is `IsSl2Triple`; even Hermite synthesis intertwines it with
  the Cayley transform of `(H,E,F)` (`ccmMetaplectic_even_representation`); Hilbert basis/unitary
  `ℓ²(ℕ) ≃ L²(ℝ)^ev` (`ccmEvenHermiteUnitary`); spectral moments `⟨e₀,J^k e₀⟩ = Γ-moments`
  (`ccmMetaplecticJacobi_moment_eq_gamma`) with uniqueness (`..._momentFiber_eq_singleton`).
  Clean `lake env lean`, axioms `propext, Classical.choice, Quot.sound`, wired, oleans built.
- 2026-10-21 — T3 design. Corpus already has: literal matrix + displacement
  (`ccmPublishedRestrictedWeilMatrix_displacement`, η = constant boundary), source completion
  `A = D − |Dc⟩⟨η|` with `det(A−z) = −z·det(D−z)·⟨η,(D−z)⁻¹c⟩`
  (`ccmSourceCompletion_shift_det_eq_neg_mul_resolvent`), metric adjointness and full-charpoly
  real-rootedness of the canonical radical completion (`CCMSourceResponseDeterminantDichotomy`),
  Shannon factorization of the band-limited transform (`CCMShannonFourierFactorization`), real
  Lerch `exp(−ζ_H'(0,a)) = √(2π)/Γ(a)` (`HTGeometry/LerchHurwitzDerivative`), unbounded circle Dirac
  (`ccmCircleDirac`). Missing: complex Lerch; spectral ζ of `D₀ − z` (`d_n = πn/a`, `a = log λ`):
  `Z(s) = (π/a)^{-s}[ζ_H(s,−w) + e^{−iπs} ζ_H(s,1+w)]`, `w = az/π`, `Im z < 0`; `Z(0) = 0`;
  `exp(−Z'(0)) = 2π/(Γ(−w)Γ(1+w))·(−i e^{−iπw}) = 1 − e^{−2iaz}`; finite modification gives
  `det_reg(D_log − z) = (1 − λ^{−2iz})·Σ ξ_n/(d_n − z) = −iλ^{−iz} ξ̂(z)` with
  `ξ̂(z) = ∫_{−a}^{a} Σ ξ_n (−1)^n e^{iπnx/a} e^{−izx} dx`.
- 2026-10-21 — T1 analysis (no Lean yet). In the Mellin picture `S ↔ H² ∩ u·conj(H²)` (Toeplitz
  kernel of the Gamma ratio `u`); Halmos decomposition of `(ran Q, ran P̂)`: the three degenerate
  corners other than `S` vanish (uncertainty), so `1 − P − P̂ = S ⊕ G` with `G` the generic part,
  spectrum `±√λ_k` (λ_k even prolate eigenvalues), `Tr G = 0`. T1 ⟺
  `Σ_k √λ_k (‖ϑ(g)v_k^−‖² − ‖ϑ(g)v_k^+‖²) ≥ 0`. The paper closes this with finite numerics; an
  unconditional proof needs new analytic control of the dominant prolate modes.
- 2026-10-21 — T2b closed: `fieldOneFiniteStageClassHardyTitchmarshUnitary_literalTheta(_ae)`
  (`Υ_S θ_S f = c·σ_S·υ_∞ f`, `σ_S` the finite Euler symbol) and the Sonin-restricted form
  `..._soninThetaEquiv` (`FieldOneFiniteStageThetaHardyTitchmarsh`). Clean, axioms standard, wired.
- 2026-10-21 — T3 closed. (a) Complex-shift Lerch on the slit plane:
  `exp(−∂_sζ_H(0,b)) = √(2π)/Γ(b)` (`exp_neg_deriv_hurwitzZetaEMC_zero`, Euler–Maclaurin continuation,
  Binet extended by the identity theorem). (b) `det_ζ(D₀ − z) = 1 − e^{−2iaz}` for `Im z < 0`
  (`exp_neg_deriv_ccmLogDiracZeta_zero`), with `Z = Σ_{n∈ℤ}(d_n − z)^{−s}` for `Re s > 1`
  (`ccmLogDiracZeta_eq_tsum`, `summable_ccmLogDiracSpectrum`). (c) Rank-one algebra:
  `charpoly(D − |Dξ⟩⟨1|) = X·P_ξ`, `P_ξ = Σ ξ_i ∏_{j≠i}(X − d_j)` monic of degree `|n|−1`
  (`charpoly_ccmSourceCompletion_diagonal`); replacing block eigenvalues by `roots P_ξ` multiplies
  `det_ζ` by `Σ ξ_i/(d_i − z)` (`exp_neg_deriv_ccmRankOneModifiedZeta`). (d) Literal matrix: ground
  energy `ε = min spec W`, metric `T = W − ε` PSD and singular; spectral zeta of `D_log − z` equals
  the series over `{d_n : |n|>N} ∪ roots P_ξ` (`ccmLogDiracSpectralZeta_eq_series`);
  `det_reg(D_log − z) = −iλ^{−iz}ξ̂(z)` (`ccmLogDiracRegularizedDeterminant_eq`).
  Main theorem `ccmPublished_logDirac_theorem` (no premises beyond `a > 0`): either η-branch —
  normalized ground `ξ`, `T D_log = D_logᴴ T`, `D_log ξ = 0`, charpoly `X·P_ξ`, real quotient
  spectrum, `ξ̂` has only real zeros, determinant identity on `Im z < 0` — or the boundary-blind
  β-branch with metric-adjoint real-spectrum response completion. Published case
  `ccmPublished_logDirac_simpleEven`: ground level on the line of a reflection-even `v` ⇒ `Σv ≠ 0`
  and the η-branch holds for `ξ = v/Σv` (odd source cannot see `v`). All clean under `--json`,
  axioms `propext, Classical.choice, Quot.sound`, wired after `CCMPublishedRestrictedWeilMatrix`,
  oleans built single-threaded.
- 2026-10-21 — T1 framework closed, inequality open. Lean (`CCMArchimedeanSoninGenericDecomposition`,
  axioms standard, wired, olean built): `G := 1 − P − P̂ − S` on `L²(ℝ)^ev` (unit cutoffs, the corpus's
  source cutoff); `ϑ(g)G` trace class; **`−W(H) = Tr(ϑ(H)S) + Tr(ϑ(H)G)`**
  (`neg_ccmArchimedeanWeilDistribution_eq_sonin_add_generic`); T1 ⟺ `0 ≤ Re Tr(ϑ(H)G)`
  (`ccmSoninTraceDomination_iff`); `G = G† = FGF`, `GS = SG = 0`, `G² + (P−P̂)² = 1−S`,
  `G(P−P̂) = −(P−P̂)G`, `G² − G = PP̂ + P̂P`, hence `−W = Tr ϑS + Tr ϑG² − Tr ϑ(PP̂+P̂P)`.
  Paper analysis (not Lean): with prolate data `φ_n`, `μ_n = ⟨φ_n,Fφ_n⟩`, `G = Σ μ_n(|w⁻⟩⟨w⁻| − |w⁺⟩⟨w⁺|)`
  (`w^± ∝ φ_n ± Fφ_n`), `Tr G = 0`; `τ(u) := Tr(Gϑ(e^u))` is real, even, `τ(0)=0`, and for `u ≥ 0`
  `τ(u) = −2∫_1^{e^u} e^{−u/2} Z(ye^{−u},y) dy`, `Z` = kernel of `K(1−K²)^{−1}PF(1−P)`, `K = PFP`;
  on `|u| ≤ log 2` only `Z` on the little square `[1/2,1]×[1,2]` enters. `τ(u) = −κ|u| + O(u²)`,
  `κ = 2[(1−K²)^{−1} − 1](1,1) > 0` (= `−c∂_c log det(1−K_c)|_ev`, `c = 2π`), which is why `ĝ(0)=0` is
  needed. T1 ⟺ `∫∫ ḡ(s)g(t)τ(t−s) ≥ 0` on `L²(−½log2, ½log2) ∩ {ĝ(0)=ĝ(i/2)=0}`; equivalently
  `∫|ĝ|²(θ'/2π − σ) ≥ 0`, `σ` the Mellin density of the Sonin projection (`θ'/2π − σ ∈ L¹`, mean 0,
  tail `2κ/t²`) — the non-innerness defect of the quasi-inner Gamma ratio. Tried and failed as
  unconditional routes: (i) Pólya convexity of `τ` on `[0,log 2]` (would make `ĝ(i/2)=0` superfluous;
  not derivable without numerics); (ii) the sufficient condition `Re Tr(ϑ(g)(PP̂+P̂P)ϑ(g)†) ≤ 0`
  (fails for small support: by the explicit Si-formula `k(u) = Tr(ϑ(e^u)PP̂)` is smooth with
  `k''(0) < 0`, so the anticommutator term is positive on mean-zero tests); (iii) the Schur/Young
  criterion `∫_0^{log 2}|τ''| ≤ κ` (needs the size of `τ''` on `[0, log 2]`, unavailable without
  numerics); (iv) the cutoff transfer `Σ₁(g) ≤ Σ_{1/√2}(g★)`, which only reduces T1 to the harder
  positivity `Re Tr(ϑ(g)G_{1/√2}ϑ(g)†) ≥ ln 2·‖g‖²`.
  Status: the support-`log 2` inequality needs quantitative control of `Z` on the little square
  (the paper's numerical spectral input); no unconditional proof found. Positive survivor still to
  formalize: small-support T1 (∃ ℓ₀ > 0) from the kink `κ > 0` plus smoothness of `Z`.
- 2026-10-21 — T1 cutoff law and positive survivor in Lean (`CCMArchimedeanSoninCutoffTraceFormula`,
  0 messages under `--json`, axioms standard, wired after the generic decomposition, olean built).
  (a) Log coordinates: `log ∘ ϑ(g) = C_g ∘ log`, `C_g` the convolution kernel `g(t−s)`
  (`logEvenUnitary_ccmIntegratedScaling`). (b) Shell traces:
  `Tr(ϑ(g)(P_Λ−P₁)ϑ(g)†) = log Λ ∫|g|²` via `C_g 1_I C_g† = K K†` with the Schur kernel
  `g(t−s)1_I(s)` (`opTrace_ccmIntegratedScaling_physicalShell`); Fourier shell equal via
  `F ϑ(g) = ϑ(ǧ) F` (`opTrace_ccmIntegratedScaling_fourierShell`). (c) Test `g★⋆g`
  (`ccmSoninGramTest`, `ϑ(g★⋆g) = ϑ(g)†ϑ(g)`) and the **Sonin trace formula at every `Λ > 1`**:
  `−W(g★⋆g) = 2 log Λ‖g‖² + Tr(ϑ(g)S_Λϑ(g)†) + Tr(ϑ(g)G_Λϑ(g)†)`, `G_Λ = 1−P_Λ−P̂_Λ−S_Λ ∈ S₁`
  (`neg_ccmArchimedeanWeilDistribution_eq_cutoffAt`); domination at `Λ` ⟺
  `0 ≤ 2 log Λ‖g‖² + Re Tr(ϑ(g)G_Λϑ(g)†)` (`ccmSoninTraceDomination_cutoffAt_iff`). (d) Survivor:
  `|Tr(ϑ(g)G_Λϑ(g)†)| ≤ ‖G_Λ‖₁(∫|g|)²`, and `(∫|g|)² ≤ 2ε‖g‖²` on `|x| < ε`, hence domination for
  every test supported in `|log u| < log Λ/(‖G_Λ‖₁+1)`, without any vanishing condition
  (`exists_ccmSoninTraceDomination_cutoffAt_small_support`). For the paper's `Λ = √2` and support
  `½ log 2` this crude bound would need `‖G_{√2}‖₁ ≤ 1`, while `‖G_{√2}‖₁ = 2Σ|μ_n|` is about 8 by the Shannon count (heuristic, not proved); the gap is
  exactly the Mellin localisation of the negative eigenvectors of `G_{√2}` (prolate data), still open.
