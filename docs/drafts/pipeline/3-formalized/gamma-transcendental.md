# A pole-counting transcendence criterion, and Γ transcendental over ℂ(s)

- **ID:** gamma-transcendental
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) — `[PROVED HERE]`, axiom-clean. First genuine theorem ABOUT Γ toward the hypertranscendence frontier (not just the definition).
- **General criterion (the sharper object):** `not_algebraic_of_infinite_poles (f) (hcont : Continuous f⁻¹) (Z infinite) (f⁻¹=0 on Z) (f≠0 punctured near Z) : ∀ nonzero p:ℂ[X][X], ∃ s, p.eval₂(evalRingHom s)(f s) ≠ 0`. A zero-free function whose reciprocal is continuous and vanishes on an infinite pole set is transcendental over ℂ(s). Abstracted from the Γ argument; reusable.
- **Instances:** `gamma_not_algebraic` (Γ, poles −ℕ) and `csc_not_algebraic` (1/sin, poles πℤ) — two distinct functions from one criterion.
- **Statement:** `gamma_not_algebraic (p : ℂ[X][X]) (hp : p ≠ 0) : ∃ s, p.eval₂ (evalRingHom s) (Γ s) ≠ 0`. The Gamma function satisfies no nonzero polynomial relation `P(s, Γ(s)) ≡ 0` — Γ is not an algebraic function.
- **Proof mechanism:** if `P(s,Γ(s))≡0`, divide by `Γ^deg` and let `s→−k` (a pole, where `Γ⁻¹→0`, using `differentiable_one_div_Gamma` + `Gamma_neg_nat_eq_zero`); the auxiliary `F(s)=∑ c_j(s)(Γ s)⁻¹^(d−j)` is continuous, vanishes off the poles, and at `−k` equals the leading coefficient `c_d(−k)`. So `c_d` vanishes at every `−k`; a nonzero polynomial cannot (`eq_zero_of_infinite_isRoot`). Contradiction.
- **Lean:** `formal/GaloisForLFunctions/GammaTranscendental.lean`. Axiom-clean, MainTheorems green.
- **Significance:** the base rung of `Hypertranscendental Complex.Gamma` (Hölder). The differential rungs (orders ≥1) remain the frontier; this discharges order 0 unconditionally, from Γ's pole structure alone.

## Log
- 2026-07-08 — created (order-0 Hölder, proven directly; the differential-order rungs are the open frontier).
