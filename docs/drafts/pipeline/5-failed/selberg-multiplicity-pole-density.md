# Multiplicity × pole: can Frobenius multiplicity be combined with the Poincaré pole argument?

- **ID:** SELBERG-MULT-POLE
- **Stage:** 1-in-progress
- **Type:** CANDIDATE (research)
- **Source:** follow-up to `3-formalized/selberg-three-sixteenths-kloosterman.md` (λ₁ ≥ 3/16 closed in Lean).

## Why the 3/16 route stops (recorded 2026-09-25)
The pole argument needs the pairing ⟨P_m(·,s), u⟩ to be continued to s₀. Absolute convergence of
Σ_c S_N(m,n;c) c^{-2s} stops at Re s = 3/4 because Weil's √c is also the typical size of S. Continuing past 3/4
needs cancellation over the moduli c (Linnik–Selberg), and by Selberg's theorem the poles of the Kloosterman zeta
function are exactly the exceptional s_j. **Verdict for any single-form, pointwise-Kloosterman route: CIRCULAR.**

## Candidate: the whole exceptional eigenspace at once (paper, 2026-09-25)
At prime level p the exceptional eigenspace V has dim d ≥ (p−1)/2 (corpus `half_pred_le_finrank`).
For an orthonormal basis (u_j) of V and real s ∈ (1, 2], Bessel's inequality gives
  Σ_j |⟨P_m(·,s), u_j⟩|² ≤ ‖P_m(·,s)‖².
- Right side: unfolding plus the Fourier–Kloosterman expansion (`poincare_eq_Q`) gives
  ‖P_m(s)‖² = diagonal (p/4πm)^{2s−1}Γ(2s−1) + a Kloosterman part of relative size ≪ p^{1/2−2s+ε}.
- Left side: ⟨P_m(s), u_j⟩ = p ∫ y^{s−2} e^{−2πmy/p} a_{j,−m}(y) dy ≈ p α_j(m) Γ(s−s₀)(p/2πm)^{s−s₀}.
- So Σ_j |α_j(m)|² ≲ p^{−1−2(1−s₀)} m^{1−2s₀}·(1 + o(1)) for every m ≥ 1.
- **[OPEN CORE]** A lower bound for Σ_j Σ_{m≤M} |α_j(m)|² that grows with d. The natural route: Σ_j |u_j(z)|² is
  invariant under SL₂(ℤ) (G = PSL₂(F_p) acts on V by a unitary representation), so the eigenspace mass is spread
  evenly over all p-cusps. The missing piece is a lower bound on the share of that mass in the cusp region y ≥ 1,
  which is not automatic: the mass could sit in the compact part of the fundamental domain.
- If the open core holds with a mass fraction c₀ > 0, comparing both sides at s → 1⁺ gives an explicit upper
  bound on s₀ in terms of p. Whether it beats Sarnak–Xue's 5/36, or the 3/16 now in the corpus, is undetermined.

## Next
1. Decide the open core on paper: a lower bound on the cusp mass of Σ_j |u_j|² for exceptional
   G-representations. The corpus has `mass_tail_fraction` (an upper bound on the tail) and the SarnakXue inner-product
   and ONB machinery.
2. If it fails: build the P_m–P_n unfolding (Kuznetsov without the spectral theorem), which the density and
   large-sieve routes past 3/16 need anyway.

## Log
- 2026-09-25 — created; circularity of single-form Kloosterman continuation recorded; multiplicity–Bessel
  framework set up; open core isolated.

## Attack on the candidate (paper, 2026-09-25)
Normalize each u_j in L²(Γ(p)\ℍ) (volume ≍ p³). At s → 1⁺:
- ‖P_m‖² ≈ p ∫ y^{2s−2} e^{−4πmy/p} dy ≈ p²/(4πm).
- ⟨P_m, u_j⟩ ≈ p α_j(m) Γ(1−s₀)(p/2πm)^{1−s₀}.
- Bessel gives Σ_j |α_j(m)|² ≲ m^{−1}(m/p)^{2−2s₀}; summed over m ≤ p this is O(1). So the cusp mass of V at ∞ is
  ≲ p (strip width p).
- The mass expected from equidistribution is d·p/p³ ≍ p^{−1}.
The Bessel inequality against P_m loses a factor ≍ p² in the level. **Even if the open core holds, the route gives no
bound on s₀, at any p.**
**Verdict: FAILED (quantitatively insufficient).** A density argument needs a test kernel concentrated at scale
≍ 1 in the level (the Sarnak–Xue pretrace with counting), not a single Poincaré series.
**Positive survivor:** the leading-coefficient Bessel bound Σ_j |α_j(m)|² ≲ m^{−1}(m/p)^{2−2s₀}, a density bound for the
y^{1−s₀} coefficients of exceptional forms. Paper level only; not new in substance (the classical coefficient
large sieve for exceptional forms). Lean status: not formalized.
Status: moved to failed.
