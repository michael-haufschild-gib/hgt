# Lock phases of Herglotz producers: positivity, quantization and rigidity

- **ID:** weil-cone-lock-phase-rigidity
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** bohr-route-detection rows 33–47 · STATUS MUST-680, 681, 683–685, 687–692
- **Statement.** Let `G` be a Herglotz producer for `lam`, as in `weil-cone-herglotz-phase-lock-rigidity`. Write its lower-line lock as
  `G(1 − s) = κ₀ P(x) G(s)`, `s = ½ − 2ix`, `x > 0`, with `|P| = 1`, `P = e^{iθ}`.
  1. **Positivity law** (MUST-689, 691). `θ` is nondecreasing near every boundary non-zero of `G`. For `θ ∈ C¹`, `θ' ≥ 0` on `(0,∞)`.
  2. **Linear quantization** (MUST-688). If `θ = ηx + β₀C`, `C` monotone `O(x^α)`, `α < 1`, then `e^{−η/2} ∈ ℕ`. Profile form: any Lipschitz profile `Ψ(C(x))` in place of `e^{iβ₀C}`.
  3. **Rigidity** (MUST-683, 689, 691, 692). If `θ ∈ C¹` and `θ(x) = ηx + Θ(V(x))` with `Θ` Lipschitz and `V` monotone `O(x^α)`, then `η = 0`, `lam = Λ` and RH. This includes every `C¹` phase of sublinear growth.
  4. **Almost-periodic locks** (MUST-690). If `P = Σ_j p_j e^{iω_j x}` with `Σ|p_j|e^{|ω_j|/2} < ∞`, then some `ω_j` has `e^{−ω_j/2} ∈ ℕ`. If the spectrum meets `2 log ℚ_{>0}` only in `0`, then the Bohr mean `p₀ ≠ 0`, `lam = Λ` and RH.
  5. **Spectral forms** (MUST-680, 681, 684, 685, 687). Non-integer spectral mass, i.e. real atoms plus a diffuse part continuous to the line, of order `O(T^α)`, `α < 1`, forces `Λ` and RH. So do two-sided deviations `Σ dist(c_k, ℤ) = O(T^α)` and evaporation deficits `O(T^α)`. A positive uniform density cannot be added (`mixed_spectrum_no_uniform_density`).

## Goal
Classify which critical-line reflection phases a Herglotz producer can carry. Every phase whose deviation from a line has sublinear variation is rigid; the only escape is a deviation of linear total variation.

## Gates
- [x] 0 → 1, 1 → 2: Bohr card rows 33–47.
- [x] 2 → 3, `RHTower.AbelianTwist`, standard axioms throughout, wired into the RHTower umbrella. Modules and capstones:
  - `HamburgerRightEdgeKernel`, `HamburgerAbelianTwistContour`: right-edge kernel at real frequencies (`norm_integral_edge_exp_le`) and abstract contour shift (`setIntegral_Iic_radial_eq_of`);
  - `WeilAbelianTwistRigidity`, `WeilAbelianTwistPowerRigidity` (`abelian_twist_power_rigidity`);
  - `WeilFractionalMassSqrtGrowthRigidity`, `WeilMixedSpectrumRigidity` (`mixed_spectrum_power_rigidity`, `exists_producer_of_mixed_spectrum`), `WeilFractionalTwoSidedRigidity`;
  - `WeilLinearTwistQuantization` (`linear_twist_quantization_profile`, `mixed_spectrum_no_uniform_density`);
  - `WeilLinearTwistPositivity` (`linear_twist_rigidity`, `G_conj`, `exists_local_log`, `ae_ne_zero_of_ends`);
  - `WeilAlmostPeriodicLockRigidity` (`ap_lock_rigidity`, `ap_lock_impossible`);
  - `WeilLockPhasePositivity` (`lock_phase_rigidity`, `deriv_lock_phase_nonneg`);
  - `WeilLockPhaseVariationRigidity` (`lock_phase_variation_rigidity`);
  - `HTGeometry/HalfPlaneBoundaryPrimitive`.
- [ ] 3 → 4

## Proof mechanisms (as formalized)
- **Radial engine.** Hamburger's reflected identity: `ε J_{1_{t<0}φ*}(ε + im) → β/π ≠ 0` for every `m ≥ 1`. The lock turns `φ*` into `κ₀ P(−t)F(½+2it)`.
- **Analytic twists.** `e^{iηx}` is the boundary value of `W = e^{−(η/2)(s−½)}`. `W·F` is Dirichlet at the frequencies `log n + η/2`. The contour shift to `Re s = 3/2` resonates iff `m e^{−η/2} ∈ ℕ`. Off-resonant terms are `O(ε^{1−ν})`, and each twist is `O(e^{|η|/2})` uniformly in `ε`, which allows dominated convergence over almost-periodic spectra.
- **Monotone and Lipschitz twists.** A layer cake over the level function `C` with profile `Ψ = Ψ(u) + ∫ψ` turns the twisted far integral into truncated integrals, each `≪ ε^{1−ν}e^{bδ}`.
- **Positivity.** `G = G(2)e^P`, `P' = Φ`, so `Re Φ ≥ 0` makes the vertical phase monotone. Local continuous logarithms carry this to the line where `G ≠ 0`. A continuous plus monotone integer-valued function is monotone. Boundary zeros are null by Tonelli on `∫∫ Re Φ`; `G` vanishes on no far half-line (reflected limit); the real structure gives non-zeros at `±B`, so non-zeros are dense.

## External audit
The pure linear lock with full continuation is the Riemann functional equation with conductor `e^{−η/2}`. Integrality of degree-1 conductors in the extended Selberg class is classical (Kaczorowski–Perelli). The resonant solutions `(1 ± n₀^{½−s})ζ` are excluded here only by positivity. New: locks assumed only on the line; monotone, Lipschitz-profile and sublinear `C¹` twists; the positivity squeeze; multi-conductor almost-periodic locks.

## Reading
- **Must:** a producer other than `Λ` whose `G` is continuous to the line has a lock phase whose deviation from every line has at least linear total variation, and is not a non-resonant strip-analytic almost-periodic phase.
- **Wall:** spectral densities with positive mean and `L¹`-fluctuation of linear size (the quasicrystal core: Fourier support in `±log ℕ`). The method is intrinsically analytic: smoothing a non-analytic phase costs `√(log 1/ε)` against the mean of `|F|` on the line.

## Log
- 2026-10-03 — created at stage 3 (consolidates MUST-680–692)
- 2026-10-03 — Weil-cone bridges: MUST-693 (`vonMangoldt_and_riemannHypothesis_of_near_integer_atoms`, purely atomic `μ_lam`, no premise) and MUST-695 (`vonMangoldt_and_riemannHypothesis_of_mixed_spectrum`, premise `Φ_d` continuous to the line); modules `WeilConeNearIntegerAtomicRigidity`, `WeilConeMixedSpectrumRigidity`
- 2026-10-03 — L² settled locks: MUST-699 (`settled_lock_rigidity`; mean-square lock gap `O((log T)^{−κ²−η})` ⇒ `Λ ∧ RH` for `|lam| ≤ κ log n` with summable composite weight), via the Weil-cone Soundararajan mean square (`exists_setIntegral_exp_two_mul_le`); modules `WeilConeSoundararajanSplit`, `WeilConeSoundararajanLargeValues`, `WeilConeSoundararajanMoments`, `WeilConeSettledLockRigidity`
- 2026-10-03 — all cone moments (`exists_setIntegral_exp_mul_le`, every `k > 0`) and uniform settled locks: MUST-701 (`uniformly_settled_lock_rigidity`, sup-norm gap `O((log T)^{−κ²/4−η})`; common reduction `lock_rigidity_of_block_means`)
- 2026-10-03 — almost-periodic locks with a settling remainder: MUST-704 (`ap_settled_lock_rigidity` and Euler-class corollaries; module `WeilConeAlmostPeriodicSettledLock`); RH ⇒ Soundararajan moments as the Λ-instance: MUST-703 (`RiemannHypothesisSoundararajanMoments`)
- 2026-10-03 — power-rate settled locks for every producer (MUST-706, `power_settled_lock_rigidity`) and the spectral form for atomic `μ_lam` (MUST-708, `vonMangoldt_and_riemannHypothesis_of_settled_atomic_phase`, module `WeilConeSettledAtomicPhase`)
