# Fermi's Golden Rule — unconditional Lean formalization

- **ID:** fermi-golden-rule
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean)
- **Source:** user goal 2026-08-21
- **Statement:** In the Friedrichs model with bounded free Hamiltonian and bounded coupling, the
  first-order transition probability out of the unperturbed bound state grows linearly in time with
  rate `2 π λ² ρ(E₀)`, where `ρ` is the Lebesgue density of the form-factor spectral measure at the
  unperturbed energy; the true Schrödinger evolution agrees with the first-order amplitude up to
  `λ² ‖V‖² t² / 2`.

## Goal
A complete, hypothesis-honest, `sorry`/`axiom`-free Lean 4 proof of Fermi's golden rule, together
with the two mathlib gaps it forces:

1. `∫_ℝ sinc² = π`  (equivalently `∫_ℝ sin(a x)² / x² dx = π a`), and
2. the `sinc²` approximate-identity limit
   `t⁻¹ ∫_ℝ K_t(E − E₀) ρ(E) dE → 2π ρ(E₀)` for `ρ ∈ L¹(ℝ)` continuous at `E₀`,
   where `K_t(x) = t² sinc(x t / 2)² = 4 sin²(x t/2)/x²`.

## Gates
- [x] 0 → 1  in-progress
- [ ] 1 → 2  fully-proven on paper
- [ ] 2 → 3  formalized in Lean, `lake build` green, axiom audit clean
- [ ] 3 → 4  publication-ready

## Approach

### Layer A — the kernel normalization (mathlib gap)
`K_t` is `|𝓕 1_{[0,t]}|²` up to the `2π` convention.  The corpus already owns classical Plancherel
(`GaloisForLFunctions.RHTower.integral_norm_sq_fourier_eq`, and the packaged
`integral_norm_sq_compactFourier` for a compactly supported spectrum).  Taking the spectrum
`H ≡ 1` on `[-k, k]` gives `∫_ℝ sin²(2π k x)/(π² x²) dx = 2k`, i.e.
`∫_ℝ sin²(a x)/x² dx = π a` for `a ≥ 0`.  Hence `∫_ℝ K_t = 2π t` for `t ≥ 0`.

### Layer B — the golden-rule limit
Split `t⁻¹ ∫ K_t(x) ρ(E₀+x) dx` at `|x| = δ`.
* inside: `|ρ(E₀+x) − ρ(E₀)| ≤ ε` and `t⁻¹∫K_t = 2π`;
* outside: `K_t ≤ 4/x²`, so the tail is `≤ 4‖ρ‖₁/(t δ²)` and the missing mass of `K_t` is `≤ 8/(t δ)`.
No hypotheses beyond `Integrable ρ` and `ContinuousAt ρ E₀`.

### Layer C — the model and its exact dynamics
`𝓗 := WithLp 2 (ℂ × Lp ℂ 2 μ)`; free Hamiltonian `H₀ (z,f) = (E₀ z, ω · f)` with `ω` bounded
measurable (corpus `lpBoundedMulCLM`); coupling `V (z,f) = (⟪v,f⟫, z • v)`, rank two, self-adjoint;
`H = H₀ + λ V`, all bounded, so `U t = exp(-(t I) • H)` is the honest Schrödinger propagator.

* **Duhamel + remainder.**  `Φ(s) = U₀(t−s) U(s) ψ₀` has derivative `−i λ U₀(t−s) V U(s) ψ₀`;
  integrating and iterating once gives
  `‖U t ψ₀ − U₀ t ψ₀ − a t‖ ≤ λ² ‖V‖² t² / 2` with
  `a t := −i λ ∫_0^t U₀(t−s) V U₀(s) ψ₀ ds`.
* **Amplitude.**  `‖a t‖²` is computed *without* identifying the Bochner integral, by moving the
  inner product inside twice (`integral_inner`) and using Fubini:
  `‖a t‖² = λ² ∫ K_t(ω(E) − E₀) ‖v E‖² dμ(E)`.
* **Rate.**  Layer B with `ρ = ` the Lebesgue density of `‖v‖² dμ` gives
  `‖a t‖² / t → 2π λ² ρ(E₀)`.
* Since `ψ₀`-component of `a t` is `0` and `U₀ t ψ₀` is purely `ψ₀`-component, the *exact*
  transition probability into the continuum obeys the same asymptotics up to the `t²` remainder.

### Layer D — non-vacuity
A concrete instance with every hypothesis discharged: `μ = volume.restrict (Ioo a b)`,
`ω = clamp to [a,b]`, `v` continuous, `E₀ ∈ Ioo a b`; and the flat-band special case `v ≡ 1`
with rate exactly `2π λ²`.

## Log
- 2026-08-21 — created in 1-in-progress; corpus audit done (no prior Fermi-golden-rule asset;
  Plancherel, bounded `Lp` multipliers and strong multiplier continuity already owned).
