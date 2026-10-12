# No compactly carried analytic port from the cosine producer to Ξ

- **ID:** ptr-analytic-port-closure
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** PTR loop rows 285–287; unifies CANNOT-508/509/510
- **Statement:** For `h ≠ 0`, `ρ ∈ ℝ` and continuous linear functionals `L_{m,k}` on `C(D̄_ρ)`,
  `Σ_{m<M} t^m Σ_{k<K} L_{m,k}(w ↦ A_h^{(k)}(t + w)) ≠ Ξ(t)` for some real `t`.

## Goal
Close every port that is finite order in `t`, compactly carried in the shift variable (complex shifts, planar
averages) and finite order in derivatives, in one theorem. CANNOT-508 needed `h ∉ 2ℤ`; here only `h ≠ 0`.

## Approach
- **Symbol:** `L(w ↦ (FΨ)(t+w)) = F(Ψ ĝ_L)(t)` with `ĝ_L(z) = L(w ↦ e^{izw})` of exponential type `|ρ|`.
  This uses a Bochner interchange in `C(D̄_ρ)`.
- **Separation over exponential type:** cusp modes, then `IsExpType.eq_zero_of_superexp` (from the two-ray
  Paley–Wiener vanishing), a polynomial in `n²`, and the triangular top coefficient.
- **Leibniz coefficients and descent:** derivatives keep exponential type by Cauchy's estimate.
  Descent ends at `cosh(hz)·(…) ≡ 1`, false at `z = iπ/(2h)`.

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  fully-proven
- [x] 2 → 3  formalized: `RHTower/CosineProducerAnalyticPortObstruction.lean` (909 lines),
  `not_exists_analytic_port_cosineProducer`, `eq_zero_of_ker_eq_zero`. Standard axioms, olean built, wired,
  lint clean for the module.

## Result
- **CANNOT-511:** the port theorem.
- **MUST-1309 (positive survivor):** `Φ, Φ', Φ'', …` are linearly independent over entire functions of
  exponential type.
  - **Honest provenance:** this follows in substance from the natural boundary of `θ` along `Im u = ±π/4`.
    Independence over all entire coefficients holds by the same route, by local ODE continuation across the
    boundary. The novelty is only the elementary Lean proof.

**Consequence for PTR.** Every exact translation-invariant port `A_h → Ξ` has kernel symbol `sech(hu)`,
which is meromorphic with poles at `u = ±iπ/(2h)`. No compactly carried analytic functional, polynomial
weight or finite-order derivative combination reaches it.

**What is left of the frontier map's "Needs" line:**
- a port whose symbol has poles;
- an argument preserving the zero count under that port.

The corpus already has the exact port, the Poisson multiplier `cosh(hu)/cosh((h+d)u)`. The open part is
the zero count, which is RH.

## Log
- 2026-10-12 — created and formalized (PTR loop rows 286–287).
