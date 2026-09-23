# Cross-kernel mass/window/ceiling laws exclude weight design for (EG75)

Card `1-in-progress/zeta23-beyond-bandwidth-one-proportion.md`, open bridge "a direct bound for the
negative cross channel". The whole finite-Laplace weight-design option is now CLOSED, with its
positive survivors. Three Lean modules, all wired into `RHTower`, all axiom-clean.

Setup: weight `W(u) = Σ c_i e^{-b_i|u|}`; pairing two Ward responses at advance `A = a_q + a_{q'}`
gives the spatial cross kernel in `D = γ_q − γ_{q'}`
`K_A(D) = Σ_i 2 c_i β_i/(β_i² + D²)`, `β_i = A + b_i`.

1. `WardAnnulusCrossKernelMassRigidity.lean`
   - `(MASS)` `∫_ℝ K_A = 2π Σ c_i = 2π W(0)`, for every advance and all widths.
   - `setIntegral_annulusCrossKernel_le` — nonneg kernel deposits ≤ `2π W(0)` on any set.
   - baseline cancellation `W(0)=0` + nonneg ⟹ `K ≡ 0`; else `K` goes negative
     (`annulusCrossKernel_eq_zero_of_nonneg`, `exists_annulusCrossKernel_neg`,
     `wardBaselineCancellingNonnegativeCrossKernelRouteKilled`).

2. `WardAnnulusCrossKernelWindowMass.lean`
   - `(WINDOW)` `∫_{-ρ}^{ρ} K_A = 4 Σ_i c_i arctan(ρ/β_i)`; (MASS) is its `ρ→∞` limit.
   - `(RADIUS)` two-width `c=(1,−1)`: `K_A(D) = 2(β₁−β₀)(β₀β₁ − D²)/((β₀²+D²)(β₁²+D²))`, so
     `K_A ≥ 0 ⟺ D² ≤ β₀β₁`. Positivity radius is exactly `√(β₀β₁)` — proves, not observes, the
     locus in `wardAnnulusCrossKernel_eq`.
   - `sum_annulusCrossKernel_ge_diagonal` — LOCAL SURVIVOR: if all pairwise ordinate separations lie
     in `[-ρ,ρ]`, the quadratic form dominates its diagonal, so the fixed quantum applies verbatim
     on ordinate clusters of diameter `√(β₀β₁)` (≈ `log T/2π` mean gaps at a fixed Euler shift).

3. `WardAnnulusCrossKernelBudgetCeiling.lean`
   - `(CEILING)` `∫_{-ρ}^{ρ} K_A ≤ 2π Σ_i max(c_i,0)` — only the POSITIVE part of the coefficients
     appears. With `Σ c_i = 0` it reads `≤ π Σ|c_i|`. Baseline cancellation sets total mass to zero
     but leaves the window budget exactly that of the positive part.
   - `(SAT)` widths `ρ/r`, `ρ·r` (product `ρ²`, so radius exactly `ρ`):
     `∫_{-ρ}^{ρ} K_A = 8 arctan r − 2π < 2π`, saturating at `2π` = a SINGLE Lorentzian's mass.
     Buying radius drives the annulus into one exponential; the leak is formally zero at `u=0` but
     the usable budget tends to the uncancelled weight's.

**Verdict:** the two-parameter annulus family cannot give a global diagonal-domination bound for
`(EG75)`. Only the card's other option survives — a source-faithful trace/randomization — or a
weight class outside finite Laplace mixtures.

**Do not retry:** any finite-width weight design that cancels the Γ baseline and hopes for a
sign-definite or large-budget cross kernel, at any number of widths, any advance, any radius.

Corpus assets found first: `XiWardSourceWindowMultiplicity`, `XiWardCellRandomizedAnnulusCoercivity`
(`wardAnnulusCrossKernel_eq`), `XiWardFiniteWidthHighPassMassRigidity` (domination analogue),
`HTGeometry/HalfPlanePoissonKernel` (`integral_halfPlanePoisson`).
