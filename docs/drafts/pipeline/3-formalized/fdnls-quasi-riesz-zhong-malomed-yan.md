# FDNLS with the quasi-Riesz derivative (Zhong–Malomed–Yan, arXiv:2407.12441)

- **ID:** fdnls-quasi-riesz
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** arXiv:2407.12441v1, "Dynamics of discrete solitons in the fractional discrete nonlinear
  Schrödinger equation with the quasi-Riesz derivative", M. Zhong, B. A. Malomed, Z. Yan.
- **Statement:** Every analytical (non-numerical) statement of the paper is proved unconditionally
  in Lean 4 in `GaloisForLFunctions.HTGeometry.FDNLS`.

## Goal
The paper is a physics paper whose analytic core is a sharp, fully rigorous package: an exact
Fourier-multiplier definition of a discrete fractional Laplacian on `ℤ`, its coupling coefficients,
their closed forms at `α = 1, 2`, their large-distance asymptotics, an exact dispersion relation,
the conserved quantities, the anti-continuum limit and its Bogoliubov spectrum, a staggering
symmetry, a scaling reduction, and a dipolar-chain realization integral.  None of it was in the
corpus.  Formalizing it added a reusable discrete-Fourier-multiplier layer (lattice symbol,
absolute summability of the cosine coefficients of `|k|^α`, the Mellin transform of the sine) that
the corpus did not own.

## Inventory of formalization targets (paper equation numbers)

| # | Paper | Content | Lean name |
|---|---|---|---|
| T1 | (10) | `D_ℓ^{(α)} = (1/π)∫_0^π cos(ℓk) k^α dk`, evenness, `D_0 = π^α/(α+1)`, vanishing at `α = 0` | `quasiRieszCoupling`, `quasiRieszCoupling_neg`, `quasiRieszCoupling_zero_index`, `quasiRieszCoupling_alpha_zero` |
| T2 | (10') | integration-by-parts form | `quasiRieszCoupling_integration_by_parts` |
| T3 | (11) | `α = 2`: `D_0 = π²/3`, `D_ℓ = 2(-1)^ℓ/ℓ²` | `quasiRieszCoupling_two_eq`, `quasiRieszDeriv_two` |
| T4 | (14) | `α = 1`: `D_0 = π/2`, `D_ℓ = ((-1)^ℓ-1)/(πℓ²)`, even separations decouple | `quasiRieszCoupling_one_eq`, `quasiRieszCoupling_one_even`, `quasiRieszDeriv_one` |
| T5 | — | uniform decay bound and absolute summability of the coupling family | `abs_integral_sin_rpow`, `abs_quasiRieszCoupling_le`, `quasiRieszCoupling_summable_abs` |
| T6 | (9) | the convolution is the Fourier multiplier `|k|^α` | `quasiRieszDeriv_eq_fourierMultiplier` |
| T7 | (32)(33) | **the dispersion relation** `∑_ℓ D_ℓ^{(α)} cos(ℓk) = |k|^α` on `[-π,π]` | `hasSum_quasiRieszCoupling_cos`, `fdnlsDispersion_eq` |
| T8 | (34)(35)(38) | `ω(0)=0`, `ω(π)=Cπ^α`, band `0 ≤ ω ≤ Cπ^α` | `fdnlsDispersion_zero`, `fdnlsDispersion_pi`, `fdnlsDispersion_mem_band` |
| T9 | (36)(37) | the two classical sine series | `tendsto_sum_sine_div`, `tendsto_sum_alternating_sine_div` |
| T10 | (39) | group velocity and its blow-up at `k → 0` for `α < 1` | `hasDerivAt_fdnlsDispersion`, `fdnlsGroupVelocity_tendsto_atTop` |
| T11 | (17)(18) | conservation of power and Hamiltonian | `latticePower_const`, `latticeHamiltonian_const`, `quasiRiesz_conserved` |
| T12 | (21) | the staggering transform exchanges `σ` and `-σ` at `α = 1` | `quasiRiesz_stagger_solution_iff` |
| T13 | (27) | the scaling reduction to `ω = -1` | `stationary_scaling` |
| T14 | (40) | anti-continuum amplitudes | `antiContinuum_amplitude`, `antiContinuum_amplitude_phase` |
| T15 | (41) | anti-continuum Bogoliubov spectrum: nilpotent double zero / `λ = ±i` | `acMode_excited_eigenvalue_eq_zero`, `acMode_excited_jordan`, `acMode_empty_eigenvalue`, `acMode_empty_modes` |
| T16 | (28)–(30) | the Bogoliubov–de Gennes linearization is an exact derivative | `hasDerivAt_stationaryResidual`, `bdgResidual_first_order_vanishes` |
| T17 | (23)(24) | non-commutativity of the two limits | `dispersion_ne_shortRange`, `quasiRieszCoupling_two_two_ne_zero` |
| T18 | (12) | `α ∈ (0,1)`: `ℓ^{α+1}D_ℓ → -(αΓ(α)/π)sin(πα/2)` | `tendsto_quasiRieszCoupling_subcritical` |
| T19 | (13) | `α ∈ (1,2]`: `(-1)^ℓ ℓ² D_ℓ → απ^{α-2}` | `tendsto_quasiRieszCoupling_supercritical` |
| T20 | (31) | dipolar chain energy `E = -m₁m₂ sinθ₁ sinθ₂/(2πL²)` | `tendsto_integral_dipoleChainEnergy` |
| T21 | (42)(43) | the Peierls–Nabarro free-energy barrier | `pnBarrier_eq`, `latticeFreeEnergy_const` |

Cited-but-not-proved external inputs (MacKay–Aubry continuation [64], discrete Sturm–Liouville [71],
Krein-signature collision theory [78–80]) are results of other papers, not of this one, and are not
part of the target set.

## Infrastructure built along the way

* `MellinSine` — `∫_0^∞ x^{α-1} sin x dx = Γ(α) sin(πα/2)` for `0 < α < 1`, a mathlib gap.  Proved
  by `e^{-εx}` regularisation against the corpus's complex-scaled Euler integral
  (`ComplexScaledGammaIntegral.gammaScaledIntegral_eq`), with an `ε`-uniform tail bound obtained by
  one integration by parts against the decreasing weight `x^{α-1}e^{-εx}`.
* `CouplingDecay` — absolute summability of the cosine coefficients of `|k|^α` on the circle, via
  the split-at-`1/ℓ` estimate; this is what upgrades mathlib's `L²` Fourier theory to the pointwise
  identity (33).
* `Conservation` — the two real pairings `rePair`, `imPair` on `ℂ`, their calculus, and the
  antisymmetric-double-sum cancellation that drives both conservation laws for an arbitrary real
  symmetric kernel on a finite lattice.
* `DipolarRealization` — the closed primitive of `A r^{-3} + (Bx²+Cx+D) r^{-5}` and the resulting
  inverse-square chain–chain law.

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  fully-proven on paper
- [x] 2 → 3  formalized in Lean: 13 modules, 3552 lines, all wired into
  `GaloisForLFunctions.HTGeometry`; every capstone depends only on
  `propext, Classical.choice, Quot.sound`; the project lint gate reports no
  `sorry`/`admit`/`axiom`/`opaque`/`unsafe`.
- [ ] 3 → 4  publication-ready

## Log
- 2026-08-22 — created; paper read in full; corpus searched (no overlap; the sawtooth series (36)
  was already owned by `RHTower.SawtoothFourierSeries`, and the complex-scaled Euler integral by
  `HTGeometry.ComplexScaledGammaIntegral`).
- 2026-08-22 — all 21 targets formalized and audited; card promoted to 3-formalized.
