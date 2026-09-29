# Lean programme: dyadic/Prüfer monodromy of disconnected Böttcher coordinates

- **ID:** `bottcher-dyadic-monodromy-lean-programme`
- **Stage:** 3-formalized (programme complete)
- **Type:** FORMALIZATION PROGRAMME
- **Consumers:** `2-fully-proven/01-bottcher-complex-dynamics/{bottcher-exact-pruefer-monodromy,
  bottcher-dyadic-monodromy-finite-type-absence, bottcher-pruefer-monodromy-no-finite-cover}.md`

## Route (no equilibrium measure, no coding map)

`ω := greenLogDeriv c = 2∂G_c` is holomorphic and single-valued on the basin `Ω_c`; on the escape
region it is `φ_c'/φ_c`.  Loops are `2π`-periodic `C¹` maps `γ : ℝ → Ω_c`; the period is
`P(γ) = ∫₀^{2π} ω(γ)γ'`.

1. **Wirtinger calculus.** `w(G) := ∂ₓG − i∂ᵧG`; chain rule `w(G∘h) = w(G)(h)·h'` for holomorphic
   `h`; `w(Re∘h) = h'`; `w(log‖·‖)(v) = 1/v`.  Hence: `ω = logDeriv φ_c` on the escape region;
   self-similarity `ω(f z)f'(z) = 2ω(z)` from `G∘f = 2G`; and **level sections**: if
   `G∘Σ = log‖·‖/2^j` then `ω(Σ v)Σ'(v) = 1/(2^j v)`.
2. **Upper bound.** For `N` large `f^N∘γ` lies in the escape region (compact image, `G∘f^N = 2^N G`);
   there `P(f^N∘γ)` is the winding integral of `φ_c∘f^N∘γ` about `0`, an integer multiple of `2πi`.
   So `P(γ) ∈ 2πi·2^{-N}ℤ`.
3. **Realization.** `exists_tower_deep` + `exists_subcritical_chain` give depth-`j` lobe sections
   `Σ_j` on a band below the critical level; `θ ↦ Σ_j(r e^{ikθ})` is a loop in `Ω_c` of period
   `2πi k/2^j`.
4. **Continuation.** A continuous `F` along `γ` that is locally `g∘γ` with `g' = ωg` satisfies
   `F(2π) = exp(P(γ))F(0)`; continuation of `φ_c` exists along every loop.  Scalar monodromy image
   `= μ_{2^∞}` exactly.
5. **Finite covers.** For a finite covering `π : Y → Ω_c` with `d`-point fibres, the lift of `γ^{d!}`
   closes (permutation order); a single-valued nonvanishing `F` with `d log F = π^*ω` would force
   `exp(d!·P(γ)) = 1`, false for `P(γ) = 2πi/2^n`, `2^n ∤ d!`.

## Progress
- 2026-09-29: steps 1–5 complete, unconditional (axioms `propext, Classical.choice, Quot.sound`).
  Modules `Bottcher/{GreenLogDerivCalculus, BottcherLogPeriods, BottcherContinuation,
  BottcherFiniteCoverMonodromy}` wired into `GaloisForLFunctions.Bottcher`.  Step 5 used lifts along
  `ℝ` (`existsUnique_continuousMap_lifts`, ℝ simply connected) and pigeonhole on lap endpoints
  instead of the permutation order `d!`; it also proves the Prüfer image survives every finite
  cover.  All three consumer cards moved to
  `3-formalized/not_new_scientific_knowledge/01-bottcher-complex-dynamics/`.
