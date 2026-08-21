# Fermi's Golden Rule — unconditional Lean formalization

- **ID:** fermi-golden-rule
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** user goal 2026-08-21
- **Statement:** In the Friedrichs model with bounded free Hamiltonian and bounded coupling, the
  first-order transition probability out of the unperturbed bound state grows linearly in time with
  rate `2 π λ² ρ(E₀)`, where `ρ` is the Lebesgue density of the form-factor spectral measure at the
  unperturbed energy; the exact Schrödinger evolution agrees with the first-order Dyson term up to
  `λ² ‖V‖² t²`.

## Goal
A complete, `sorry`/`axiom`-free Lean 4 proof of Fermi's golden rule, together with the two mathlib
gaps it forces.

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  fully-proven on paper
- [x] 2 → 3  formalized in Lean, `lake build` green, axiom audit clean
- [ ] 3 → 4  publication-ready

## What was built

### Layer A — the sinc-square normalization (mathlib gap)
`formal/GaloisForLFunctions/HTGeometry/GoldenRuleSincIntegral.lean`
* `compactFourier_one_eq` — closed form of the flat compactly supported synthesis integral.
* `integral_sin_sq_div_sq : 0 ≤ a → ∫_ℝ sin(a x)²/x² dx = π a`.
* `integral_sinc_sq : ∫_ℝ sinc² = π`.
Route: Plancherel (corpus `integral_norm_sq_compactFourier`) applied to the flat spectrum `1` on
`[-k, k]`.  Mathlib defines `Real.sinc` but proves nothing about its integral.

### Layer B — the golden-rule kernel and its concentration (mathlib gap)
`GoldenRuleKernel.lean`, `GoldenRuleLimit.lean`
* `goldenRuleKernel t x = t² sinc(x t/2)² = 4 sin²(x t/2)/x²`, continuous at the resonance.
* `goldenRuleKernel_eq_normSq : K t x = ‖∫₀ᵗ exp (i s x) ds‖²`.
* `goldenRuleKernel_le_majorant : K t x ≤ (t² + 4)/(1 + x²)` — one integrable majorant for all `t`.
* `integral_goldenRuleKernel : 0 ≤ t → ∫_ℝ K t = 2 π t`.
* `tendsto_goldenRuleKernel_weight` / `tendsto_goldenRuleKernel_density`:
  `t⁻¹ ∫_ℝ K t (E − E₀) ρ(E) dE → 2 π ρ(E₀)` for `ρ ∈ L¹(ℝ)` continuous at `E₀`.
  No hypothesis beyond integrability and continuity at the single point `E₀`.

### Layer C — the dynamics
`SelfAdjointPropagator.lean`, `BoundedMultiplierCalculus.lean`, `GoldenRuleAmplitude.lean`
* `propagator H t = exp (t • (-i H))`: group law, derivative, adjoint, and unitarity for a bounded
  self-adjoint `H` (via `star_exp` and `exp_mem_unitary_of_mem_skewAdjoint`; no spectral theorem).
* `hasDerivAt_of_ae_mul`: a family of multiplication operators is differentiable *in operator norm*
  as soon as its symbols are uniformly second-order close — the reusable criterion behind both
  one-parameter families used here.
* `freeHamiltonian`, `freeGroup`: multiplication by a bounded real energy `ω` and by `exp(-i t ω)`,
  with self-adjointness, isometry, group law, commutation and the norm derivative `-i H₀ U₀ t`.
* `ampSymbol t Δ = t · exp(i t Δ/2) · sinc(t Δ/2)` — closed form of `∫₀ᵗ exp(i s Δ) ds` with no case
  split at the resonance; `ampSymbol_mul`, `normSq_ampSymbol : ‖A t Δ‖² = K t Δ`, `ampSymbol_taylor`.
* `integral_intOp` — the first-order Dyson integral evaluated in closed form by the FTC.

### Layer D — the Friedrichs model and the golden rule
`FermiGoldenRuleModel.lean`
* `FriedrichsModel`: a normalized bound state of `H₀` = multiplication by `ω` on `L²(μ)`, coupled to
  the continuum by the rank-two `V = |ψ₀⟩⟨v| + |v⟩⟨ψ₀|`; `H = H₀ + λ V`, all bounded.
* `duhamel` — the exact integral equation `U t − U₀ t = ∫₀ᵗ (-i λ) U₀(t−s) V U s ds`.
* `norm_evol_sub_freeProp_le` — `‖(U t − U₀ t) ψ₀‖ ≤ |λ| ‖V‖ t`.
* `firstOrder`, `firstOrder_eq` — the first-order Dyson term and its closed form.
* `norm_sub_firstOrder_le`, `abs_norm_sub_norm_firstOrder_le` — second-order remainder `λ² ‖V‖² t²`.
* `normSq_firstOrder : ‖a t‖² = λ² ∫ K t (ω x − E₀) ‖v x‖² dμ`.
* `tendsto_normSq_firstOrder` — **Fermi's golden rule**: `‖a t‖² / t → 2 π λ² ρ(E₀)`.

### Layer E — non-vacuity
`FermiGoldenRule.lean` builds the band model `μ = δ_{b+1} + Leb|_(a,b)`, `ω` = identity on the band
and `E₀` at the atom, bound state = the atom's indicator, form factor = `v` restricted to the band,
and discharges **every** hypothesis:
* `bandModel` — the `FriedrichsModel` instance (norm, eigenvector, orthogonality all proved);
* `bandModel_density` — the spectral measure of the form factor is literally `‖v‖² dE` on the band;
* `tendsto_bandModel_firstOrder` / `fermi_golden_rule` — for `a < E₀ < b` and continuous `v`,
  `‖a t‖² / t → 2 π λ² ‖v E₀‖²`, with the `λ² ‖V‖² t²` error control.

### Layer F — the energy-domain (Weisskopf–Wigner) face
`GoldenRuleSelfEnergy.lean`
* built on the corpus's own `halfPlanePoisson c t = c/(π(c²+t²))` (`HalfPlanePoissonKernel.lean`),
  which already supplies positivity, integrability, continuity, `∫ = 1` and the sup bound; only the
  tail estimates `halfPlanePoisson_le_of_tail`, `halfPlanePoisson_le_tail_majorant`,
  `setIntegral_halfPlanePoisson_compl_le`, `abs_setIntegral_halfPlanePoisson_compl_mul_le` are new;
* `tendsto_halfPlanePoisson_weight` / `tendsto_halfPlanePoisson_density`:
  `∫_ℝ P ε (E − E₀) ρ(E) dE → ρ(E₀)` as `ε ↓ 0`;
* `levelSelfEnergy ρ E₀ ε = ∫_ℝ ρ(E)/(E₀ + iε − E) dE` and
  `im_levelSelfEnergy : (Σ(E₀+iε)).im = −π ∫ P ε (E − E₀) ρ`;
* `tendsto_levelSelfEnergy_rate` — `Γ = −2 Im Σ(E₀ + i0⁺) = 2 π ρ(E₀)`.
* `goldenRule_rate_agreement` — **the two derivations give the same number**: the time-domain slope
  and the energy-domain boundary value both converge to `2 π ρ(E₀)`.

## Certificate
* `lake build GaloisForLFunctions.HTGeometry.FermiGoldenRule` and
  `lake build GaloisForLFunctions.HTGeometry.GoldenRuleSelfEnergy` — green.
* Wired into the `GaloisForLFunctions.HTGeometry` umbrella.
* `#print axioms` on every capstone: `[propext, Classical.choice, Quot.sound]` only — no `sorry`,
  no `axiom`, no added hypothesis.
* `scripts/formal_tools.py lint`: no proof debt from these modules (the reported unreachable-module
  errors are pre-existing and belong to other lanes).

## Log
- 2026-08-21 — created in 1-in-progress; corpus audit done (no prior Fermi-golden-rule asset).
- 2026-08-21 — all five layers formalized and built; promoted to 3-formalized.
- 2026-08-21 — Layer F added: the energy-domain face and the agreement of the two rates.
