# Elementary PNT with power-log error (infrastructure sub-project)

- **ID:** `elementary-pnt-power-log-error-infrastructure`
- **Stage:** 1-in-progress (formalization infrastructure)
- **Type:** `[BRIDGE]` infrastructure (classical, not candidate-new)
- **Purpose:** supply the single remaining input of
  `weighted-euler-tangent-global-graph-decoupling` (and reusable corpus-wide): primes in every
  short multiplicative window `[X, X(1+Θ(1/(c·log X)))]`, i.e.
  `ψ(x) = x + O(x/(log x)^A)` for every fixed `A` (Bombieri–Wirsing strength; `A ≈ B+2`
  suffices per consumer).  Consumer interface already formalized:
  `RHTower.exists_separated_primeLog_nodes` (needs one prime log per `η`-window) and
  `HTGeometry.norm_le_ray_of_sampled_decay` (node families).
- **Route (elementary, Selberg):**
  1. Dirichlet-algebra Leibniz rule: `(f * g)·log = (f·log) * g + f * (g·log)`.
  2. `Λ·log + Λ*Λ = μ * log²` (from `Λ * ζ = log`, mathlib has `vonMangoldt_mul_zeta`-form).
  3. Hyperbola-method estimate of `Σ_{n≤x} (μ*log²)(n)` → **Selberg symmetry formula**
     `ψ(x)log x + Σ_{n≤x} Λ(n)ψ(x/n) = 2x log x + O(x)`.
  4. Bootstrap the symmetry formula (Erdős–Selberg / Bombieri–Wirsing iteration) to
     `R(x) := ψ(x) − x = O(x/(log x)^A)`.
  5. Short-interval consequence: `ψ(x(1+δ)) − ψ(x) ≥ δx(1−o(1))` for `δ = 1/(log x)^{A−1}` ⇒
     prime (power) in the window; remove prime powers via Chebyshev θ/ψ comparison
     (corpus `MertensFirst.psi_theta_div_le` and mathlib Chebyshev).
- **Status log:**
  - 2026-07-23: card created; step 1 (Leibniz rule) starting.
  - 2026-07-23: **step 1+2 DONE** — `formal/GaloisForLFunctions/RHTower/DirichletLogDerivation.lean`
    (umbrella-registered, `lake build` clean, standard axioms): `pmul_log_mul` (the real-coefficient
    Leibniz rule; the corpus already had the ℂ-form `HTGeometry.logWeight_leibniz` in
    `OperatorTailDirichletMatroid.lean` — the real form is documented as its counterpart, needed
    because `Λ` and `ArithmeticFunction.log` are ℝ-valued), `zeta_pmul_log`, and
    **`vonMangoldt_pmul_log_add_mul_self`** (Selberg's identity `Λ·log + Λ*Λ = (log·log)*μ`).
    NEXT (step 3): summatory hyperbola estimate of `Σ_{n≤x}((log·log)*μ)(n)` toward the Selberg
    symmetry formula; reuse `RHTower.Mertens` summatory tooling (`log_summatory_eq`,
    `sum_log_le/ge`).
