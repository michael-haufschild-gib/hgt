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
| T2 | CCM 2023 Thm 4.6: `θ_S : Sonin_λ(ℝ) ≃ Sonin_λ(X_S)` for every finite `S`, Fourier compatible | `θ_S = w_S ∘ E_S`, `E_S = ∏_{p∈S}(1 − p^{-1/2}ϑ(p))` (Neumann-invertible, `‖p^{-1/2}ϑ(p)‖<1`); `E_S^{±1}` preserve `ran(1−P_λ)`; `F_S θ_S = θ_S F` ⇒ `Sonin_λ(X_S) = θ_S(Sonin_λ(ℝ))` | **Lean-closed** (`FieldOneFiniteStageThetaSoninIsomorphism`); finite-S Hardy–Titchmarsh square still to add (T2b) |
| T4 | CCM 2023 Thm 5.2(iv): Jacobi/Gamma data = even metaplectic representation | build sl₂ operators from Jacobi coefficients, identify on even Hermite basis | **Lean-closed** (`CCMMetaplecticOscillatorTriple`, `CCMMetaplecticRepresentationIdentification`) |
| T3 | CCM 2025 Thm 5.10: `D_log^{(λ,N)}` self-adjoint, `det_reg(D_log − z) = −i λ^{−iz} ξ̂(z)` | finite-rank perturbation of `diag(2πn/L)`; define regularized determinant explicitly; no simple-even premise laundering | open |
| T1 | CC 2020 Thm 1: `W_∞(g∗g*) ≥ Tr(ϑ(g)Sϑ(g)*)`, supp `g ⊆ [2^{-1/2},2^{1/2}]`, `ĝ(i/2)=ĝ(0)=0` | `1−P−P̂ = S + D`, `D = P∨P̂ − P − P̂` trace class; prove `Tr(ϑ(g)Dϑ(g)*) ≥ 0` analytically (paper uses numerics) | open |

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
