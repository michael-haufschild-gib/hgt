# Planted off-line zero in the actual restricted Weil form

**What was computed.**
- Form: the unconstrained restricted Weil form with all actual primes and the archimedean term (Legendre Galerkin, N = 40, 50 digits; converged range a ≤ 0.8).
- Planting: through the explicit formula `Q(f) = Σ_ρ F(γ)F^#(γ)`, the contribution of the on-line pair ±γ₁ (γ₁ = 14.1347) was replaced by an off-line quartet ±γ₁ ± iδ, with δ ∈ {0.05, 0.15, 0.30}.
- Tracked: the ground energy, the parity of the ground state, its real zeros on (0, 40), and nested-aperture zero separation. Script `plant.py`, output `plant.out` (32 of 33 jobs; the last one was stopped).

**Outcome.**
- First contact (energy < 0) at a ≈ 0.48 (δ = 0.05), 0.44 (0.15), 0.42 (0.30).
- After contact the ground-state parity alternates even/odd from aperture to aperture. The two parity sectors' negative directions are nearly degenerate, as predicted in loop row 492.
- After contact, new zeros enter the zeta-zero-free window (0, γ₁): for example 3.41 (δ = 0.05, a = 0.65), 2.37 and 7.21 (a = 0.75), 3.45 (δ = 0.30, a = 0.55). For the true form, every zero stays above γ₁ at all apertures and approaches it from above (`computations/2026-10-06-ground-zero-monotonicity`).
- Nested-aperture separation was NOT violated (194, 196 and 160 checks, 0 violations). The new zeros enter the gap from below and only add zeros. So the continuous form does not reproduce the discrete separation failure in this range.

**Interpretation.**
- In the continuous setting the robust ¬RH signature is gap penetration: a ground-state zero below γ₁ (failure of zero domination x₁(a) ≥ γ₁) together with parity flipping. Separation (C502) is not the detector.
- Conjecture (refined C500): RH ⟺ x₁(a) ≥ γ₁ at every aperture, i.e. the real-rooted ground states never have a zero in the zeta-zero-free window.

## Even/odd sector energies (parity.py, one assembly per aperture, a = 0.400–0.745 step 0.015)

**Method.** Lowest eigenvalue of each parity block (the Legendre basis splits into even and odd blocks), for the true form and for the planted form with d ∈ {0.05, 0.15, 0.30}. Data: `parity.json`.

**True form.**
- The even sector is the ground state at every aperture, by a growing factor: μᵒ/μᵉ ≈ 81 (a = 0.400), 199 (0.505), 1.2e3 (0.655), 7.8e2 (0.745).
- Both sector energies stay positive.

**Planted form.**
- The even sector turns negative first; the odd sector follows 0.03–0.06 later in a (d = 0.30: even at 0.415, odd at 0.475).
- Once both are negative, which sector is lower alternates repeatedly as a grows:
  - d = 0.30: O on [0.475, 0.520], E on [0.535, 0.580], O on [0.595, 0.640], E on [0.655, 0.715], O from 0.730;
  - d = 0.15 and 0.05: the same pattern, shifted.
- The half-period ≈ 0.11 = π/(2γ₁) matches a cross term ∝ sin(2aγ₁) between the resonances at ±γ₁.

**Conclusion.** Under ¬RH the ground level is degenerate (μᵉ = μᵒ) at a sequence of apertures spaced π/(2t₀) apart (by continuity), so Connes's even-simplicity fails infinitely often. Under RH the even sector dominates by orders of magnitude.

Conjecture C506 (parity-simplicity route): RH ⟺ for every λ the minimal eigenvalue of QW_λ is simple with an even eigenvector.
