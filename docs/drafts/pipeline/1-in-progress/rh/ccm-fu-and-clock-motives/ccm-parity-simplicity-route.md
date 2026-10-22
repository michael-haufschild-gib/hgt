# Parity–simplicity route: Connes's even-simplicity is RH-sensitive

- **ID:** CCM-PS (loop rows 492, 505–514)
- **Stage:** 1-in-progress
- **Type:** CONJECTURE (C506), with a proved paper identity and numerics
- **Source:** rh-goal-loop-opus-2026-09-29 rows 505–514; computations/2026-10-06-planted-offline-separation
- **Statement:** RH ⟺ for every λ > 1 the minimal eigenvalue of the unconstrained restricted Weil form
  `QW_λ` is simple with an even eigenvector.

## Goal
- **Literature step.** Connes (arXiv 2602.04022 §6.6) and Connes–van Suijlekom (CMP 406 (2026) 312, Thm 6.1) treat even-simplicity as a technical first step; Zhu (arXiv 2608.24827) records it as verified only empirically.
- **Target theorem (⟸):** *if RH fails, the even and odd ground levels of QW_λ coincide for infinitely many λ.*
  - It would show that this step is RH-strength.
  - It would make RH a spectral-parity statement for an explicit operator family, with no convergence and no √X precision.
- **Direction (⟹):** RH ⇒ the even sector wins. Under RH the measured margin is μᵒ/μᵉ ≈ 10²–10³.

## Gates
- [x] 0 → 1  well-posed; numerics and mechanism in hand
- [ ] 1 → 2  complete paper proof of (⟸)
- [ ] 2 → 3  Lean
- [ ] 3 → 4  —

## Evidence (pod, Legendre Galerkin N = 40, 50 digits, converged a ≤ 0.8)
- **True form:** the even sector is lowest at every aperture in [0.40, 0.745], with μᵒ/μᵉ ≈ 80 → 10³.
- **Planted form:** the on-line pair ±γ₁ is replaced by the quartet ±γ₁ ± iδ (explicit-formula substitution, δ ∈ {0.05, 0.15, 0.30}).
  - The even sector crosses zero first (a ≈ 0.415–0.48) and the odd sector 0.03–0.06 later.
  - After that, the lower sector alternates E/O with half-period ≈ 0.11 = π/(2γ₁).
  - New real zeros of the ground state enter the zeta-zero-free window (0, γ₁).
- Data: `computations/2026-10-06-planted-offline-separation/parity.json`, `plant.out`.

## Proved on paper
1. **Sign-flip parity transfer.**
   - `f ↦ sign(x) f` is an isometry from the even sector of `L²[−a,a]` onto the odd sector, and it preserves the form domain (the log archimedean weight tolerates the jump).
   - For even f: `Q(sign·f) = Q(f) − 4H(f₊)`; for odd g: `Q(sign·g) = Q(g) + 4H(g₊)`.
   - Here `H(h) = ∫₀^a∫₀^a K(x+u)h(x)h(u)` is the Hankel form of the Weil kernel K.
   - Sandwich: `−4H(fᵉ₊)/‖fᵉ‖² ≥ μᵒ − μᵉ ≥ −4H(gᵒ₊)/‖gᵒ‖²`.
2. **Kernel split on s = x+u > 0:**
   - pole `2cosh(s/2)`: rank-2 positive Hankel, favors odd, measures edge mass;
   - archimedean `−2e^{−s/2}/(1−e^{−2s}) = −Σ_m 2e^{−(2m+½)(x+u)}`: a completely monotone Laplace kernel, so negative semidefinite, favors even;
   - primes `−ΣΛ(n)n^{−½}δ(s − log n)`: indefinite.
3. **Quartet in the zero-sum form.** An off-line quartet ±t₀ ± iδ contributes `4 Re F(γ₀)²` in both parity sectors: one negative square per sector (L366).

## Approach to (⟸)
- **Reduction.** The best sector states are `k_N(·,γ₀) ± k_N(·,−γ₀)` in the near-null space N_a (functions small at the on-line zeros below `T* = 2πe^{2a}`), so their energies differ by `K_N(γ₀,−γ₀)`.
- **Model.** `N_a ≈ Ψ·PW_{c(a)}`, with Ψ = Ξ with the quartet removed and `c(a)` the free exponential type at height t₀ (dc/da ≈ 1). Then `K_N(γ₀,−γ₀) ≈ Ψ(γ₀)Ψ(−γ₀)·sin(2c(a)t₀)/(2t₀)`, whose sign changes with half-period π/(2t₀), matching the numerics.
- **Final step.** Continuity of the sector ground energies plus evenness at small apertures turns each sign change into a degenerate aperture.
- **[OPEN CORE]** The near-null structure `N_a ≈ Ψ·PW_{c(a)}` with an error below `|K_N(γ₀,−γ₀)|`, under ¬RH, including other off-line zeros below T*. This is the same object as the CCM edge-mass core (row 508).

## No-go closure (partial)
- **Not a producer.** Even-dominance with margin is produced by positivity (row 512). Parity crossing counts are two-torsion (row 513).
- **Strongest positive survivor:** the sign-flip Hankel identity and sandwich, with paper proof complete.
  - Lean is pending: it needs the time-domain archimedean form on the full log-weighted form domain (`CCMArchimedeanWeilDistribution` covers only compact Schwartz tests).

## Log
- 2026-10-06 — created at stage 1 (Opus) from loop rows 505–514.
- 2026-10-06 — added (loop row 518), Hankel–explicit-formula bridge.
  - Identity: `H(f₊) = W(f₊∗f₊) = Σ_ρ F₊(γ_ρ)²` (squares of the half-function transform).
  - Under RH, the even ground state has `Re F₊(γ) ≈ 0` at every zero, so `H ≈ −Σ(Im F₊(γ))² < 0`: even dominance is the non-vanishing of the ground state's Hilbert transform at the zeros.
  - Under ¬RH, the resonance gives `F₊(γ₀) ≈ a/2` (an off-line square term ≈ a²/4 > 0) as the crossing driver.
  - Open core in explicit-formula form: compare the off-line square term with the on-line Hilbert energy near t₀, including the `e^{2it₀a}` corrections.
- 2026-10-06 — MUST-799 [L]: `Q(A, Ã) = Σ_q F_Ā(γ_q)²` and parity gap `= 4 Re Σ_q F_Ā(γ_q)²` on smooth interior sources (`CCMRestrictedWeilParityHankelBridge`). The Hankel/convolution-square bridge of rows 507/518 is formal; (⟸) remains open.
