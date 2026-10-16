# CHMD far-field energy localization: negative Doob energy is confined to a compact window

- **ID:** chmd-far-field-energy-2026-10-16
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** CHMD route; continuation of chmd-pointwise-generator-threshold-weyl-2026-10-16 (which established `1/2 ∈ σ_ess(R)` via the cusp escape and left open "where can the spectrum above `1/2` live?")
- **Statement:** (1) for every `ε > 0` there are `R_ε, C_ε ≥ 0` with `E(p) ≥ −ε‖p‖²_μ − C_ε·∫_{|x|≤R_ε} p² dμ` for every vector `p` of the completed arithmetic Doob graph; (2) for every `μ > 1/2`, unit approximate eigenvectors of the arithmetic resolvent at level `μ` carry a definite amount of mass inside a fixed window, and unit sequences with `‖Re_n − μe_n‖ → 0` cannot escape to the cusp; (3) sharpness: the normalized primitive cusp escape is a unit family with `‖Re_n − e_n/2‖ → 0` and zero mass in every fixed window eventually.
- **Status:** STATUS MUST-1545, MUST-1546. Two leaves (`CHMDPrimeWindowTail` 34 declarations, `CHMDFarFieldEnergy` 41 declarations), all axioms propext/Classical.choice/Quot.sound; plain `lake env lean` audits clean; `lake build --old` green; wired once each into `GaloisForLFunctions/RHTower.lean`; index refreshed. Global lint exit 1 solely for other agents' unwired modules (CHMDStationary*, PaperThetaForced*, HTGeometry/BoundedVariationKernelIntegral, HTGeometry/EvenEntireWindowSource).

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  fully-proven (paper proof below = the Lean development)
- [x] 2 → 3  formalized: `exists_primeTail_bound`, `exists_primeKernelSum_two_sided`, `window_jump_lower`, `tsum_integral_shiftPair`, `tsum_phiDoobPrimeJump_window_lower`, `sourceEnergy_compactLift_window_lower`, `exists_window_energy_bound`, `exists_farField_energy_bound`, `exists_window_mass_resolvent`, `eventually_window_mass_of_weyl`, `threshold_escape_sequence`
- [ ] 3 → 4  publication-ready

## Obstacle addressed
In the CHMD dictionary RH ⟺ `E ≥ 0` on even primitives ⟺ `R ≤ 1/2` there (`R` the bounded arithmetic resolvent on
`L²(Θcosh(x/2)dx)`). The previous card showed `1/2` is essential spectrum (cusp escape), so the critical value is not
isolated; nothing said where a hypothetical off-line zero (a bound state of `R` above `1/2`) could live. The wall was
that the Doob form is a difference of two unbounded jump forms (`J_arith − J_polar`) with no structural reason for the
negative part to be confined. This card proves confinement: all negativity, up to an `ε‖·‖²` loss, sits inside a
compact window `|x| ≤ R_ε`. Equivalently, the compression of the Doob form to the far field is `≥ −ε`, and the
resolvent restricted to the far field is `≤ 1/2 + ε`. The structural input is arithmetic: the harmonic identity says
that the prime jumps from `x` carry exactly the polar rate `cosh(x/2)` (which is the mass density over `Θ`), and
Chebyshev's prefix bound grouped in log-shells says the jumps that leave a window of radius `R` carry only
`O(e^{−7R/2})` of it. No positivity of the Weil form is assumed; nothing is RH-equivalent; this is a new
unconditional law of the form.

## Paper proof
*Shell tail.* Let `a_n = Λ(n)/√n`, `Θ` Riemann's kernel (`Θ(x) ≤ Ce^{−4|x|}`). The corpus shell bound gives, for the
shell `⌊|x − log n|⌋ = k`, `Σ a_nΘ(x − log n) ≤ 34C e^{1/2} e^{x/2} r^k` with `r = e^{−7/2}`. Shifts landing outside
the window `|u| ≤ R` have `k ≥ ⌊R⌋`, so summing the geometric tail, `Σ_n a_n Θ(x − log n)1_{|x−log n|>R} ≤
34Ce^{1/2}e^{x/2} r^{⌊R⌋}/(1−r)`; the `+log n` side follows from `x ↦ −x`. Hence
`primeTail_R(x) ≤ A r^{⌊R⌋}(e^{x/2} + e^{−x/2}) ≤ 2A r^{⌊R⌋}cosh(x/2)` and `primeCross_R + primeTail_R = Σ a_n(Θ(x±log n))`.

*Two-sided bound.* By the harmonic identity `Σ a_n(Θ(x±log n)) = cosh(x/2) − 2cΘ(x) + ∫_0^∞ symArch`, and
`|2cΘ| ≤ 2|c|‖Θ‖_∞`, `|∫symArch| ≤ 2∫_0^∞ gammaSourceBound`, so `|Σ a_n(Θ(x±log n)) − cosh(x/2)| ≤ B`.

*Window inequality.* For `α, β ∈ {0,1}`, `δ > 0`: `(a−b)² ≥ βa² + αb² − δ⁻¹(αa² + βb²) − δ(a² + b²)`
(from `2ab ≤ δ⁻¹a² + δb²` and `2ab ≤ δa² + δ⁻¹b²`, four cases).

*Compact tests.* For `v ∈ C²_c`, `E(v) = J_arch(v) + Σ_n ∫ a_nΘ(x)Θ(x+log n)(v(x) − v(x+log n))²dx − ‖v‖²_μ ≥
Σ_n ∫(…) − ‖v‖²_μ`. Apply the window inequality with `a = v(x)`, `b = v(x+log n)`, `α = 1_{|x|≤R}`,
`β = 1_{|x+log n|≤R}`; the `b²` terms are shifted by `x ↦ x − log n`. Writing `m = v²Θ`, this gives per `n`
`∫ PJ_n ≥ ∫ m·a_n(Θ(x+log n)1_R(x+log n) + Θ(x−log n)1_R(x−log n)) − ∫ m(δ⁻¹1_R(x) + δ)·a_n(Θ(x+log n)+Θ(x−log n))`.
Summation and integration commute because on the support of `m` (`|x| ≤ R₀`) `Θ(x±log n) ≤ 2Ce^{4R₀}/n²` and
`Σ a_n/n² < ∞`. Hence `Σ∫PJ_n ≥ ∫ m·primeCross_R − ∫ m(δ⁻¹1_R + δ)·Σa_n(Θ(x±log n))`. With
`primeCross_R ≥ (1 − 2Ar^{⌊R⌋})cosh − B`, `Σa_n(Θ(x±log n)) ≤ cosh + B`, `∫m cosh = ‖v‖²_μ =: V`,
`∫ 1_R m cosh = nearMass_R(v) =: N`, `1_R m ≤ 1_R m cosh`, and `m ≤ 1_R m cosh + m cosh/cosh(R/2)` (since
`Θ ≤ Θcosh(x/2)/cosh(R/2)` for `|x| > R`), one gets
`E(v) ≥ −(K₁ + (1+δ)B/cosh(R/2) + δ)V − (B + δ⁻¹(1+B) + δB)N`, `K₁ = 2Ar^{⌊R⌋}`.

*Completion.* Given `ε`, take `δ = min(1, ε/3)` and `R` with `K₁ ≤ ε/3`, `2B/cosh(R/2) ≤ ε/3` (`cosh(R/2) ≥ (R/2+1)/2`).
`nearMass_R(p) = ‖1_R·p.fst‖²_μ` is continuous on the graph (bounded multiplier), `E` is continuous, compact
tests are dense (corpus), so the inequality holds on the whole completed graph.

*Confinement above `1/2`.* For `‖w‖ = 1`, `p = Riesz(w)` has `p.fst = Rw` and `E(p) = ⟨w,Rw⟩ − 2‖Rw‖²`. With
`ρ = ‖Rw − μw‖`: `‖Rw‖ ≥ μ − ρ`, `⟨w,Rw⟩ ≤ μ + ρ`. The theorem at `ε = (2μ−1)/(2μ)` gives
`C‖1_R Rw‖² ≥ (2−ε)‖Rw‖² − ⟨w,Rw⟩ ≥ (2μ+1)(μ−ρ)²/(2μ) − (μ+ρ) ≥ μ(2μ−1)/4 =: γ` once
`ρ ≤ min(μ, γ/(8μ(μ+1)))`. So `‖1_R Rw‖² ≥ γ/(C+1)`, and `‖1_R Rw‖ ≤ ρ + μ‖1_R w‖` transfers the window mass to `w`.

*Sharpness.* `e_n = source(normalized n)` (corpus escape) is unit with resolvent defect `→ 0` at level `1/2`
(corpus); `e_n = ‖·‖⁻¹·(profile(x − n)/Θ(x))` vanishes on `|x| ≤ R₀` once `n > R₀ + R_p`, so `1_{R₀}e_n = 0`.

## Lean modules (namespace `RHTower.CHMDPolar`)
1. `RHTower/CHMDPrimeWindowTail.lean` (260 lines) — `nearInd`, `farInd` and their algebra; `theta_le_mass_div_cosh`;
   `primeCross`, `primeTail`, summability, `primeCross_add_primeTail`; `shellRatio`, `sum_pow_shellRatio_le`,
   `primeTail_minus_le`, `exists_primeTail_bound`, `primeTail_le_cosh`, `shellRatio_pow_floor_tendsto`.
2. `RHTower/CHMDFarFieldEnergy.lean` (≈ 790 lines) — `exists_primeKernelSum_two_sided`, `window_jump_lower`,
   `shiftPair` (+ measurability/bounds), `integrable_mul_bounded`, `tsum_integral_shiftPair`,
   `thetaSq` toolkit, `integral_phiDoobPrimeJump_window_lower`, `tsum_phiDoobPrimeJump_window_lower`,
   `measurable_primeCross`, `measurable_primeKernelSum`, `nearMass`, `nearMul`, `nearMass_eq_norm_sq`,
   `continuous_nearMass`, `sourceEnergy_compactLift_window_lower`, `exists_window_energy_bound`,
   `exists_farField_energy_bound`, `exists_window_mass_resolvent`, `eventually_window_mass_of_weyl`,
   `nearMul_escape_eq_zero`, `threshold_escape_sequence`.

## Big picture
- The Doob form `E = J_arith − J_polar` is now known to be bounded below by `−ε‖·‖²` on the far field for every
  `ε`: the polar (negative) part is exactly cancelled at infinity by the prime jumps into the window. Negativity,
  i.e. off-line zeros, is a compact-window, finite-rank-looking phenomenon.
- Spectral consequence: spectrum of `R` above `1/2` is generated by window-confined vectors; `1/2` is the exact
  escape level. The remaining step to `σ_ess(R) ⊆ [0,1/2]` is local compactness of `1_R ∘ R` (a Rellich lemma on
  the Doob graph), which needs a logarithmic lower bound for the archimedean Lévy symbol
  `ψ(ξ) = 2∫_0^∞ ω(t)(1 − cos ξt)dt ≥ c log(2 + |ξ|) − C`; the corpus has only the upper bound
  (`EvenSectorWeightGrowth.abs_gammaBracket_le_log`). With it, eigenvalues of `R` in `(1/2,1]` would be isolated
  of finite multiplicity, i.e. the nonreal Xi orbits would be counted by a Birman–Schwinger principle.
- Walls catalogue: this is not a sign producer (no positivity is claimed); it is a structural confinement law
  that changes what an RH-core argument must do: rule out window-confined bound states only.

## Next conjectures
1. Rellich on the Doob graph: `{p : ‖p‖_graph ≤ 1}` has precompact image under `1_R ∘ sourceMap` in `L²(μ)`.
2. Lévy symbol log lower bound from the explicit `ω(t) = Σ_k ... e^{−(2k+1)t/2}`-type expansion in the corpus.
3. Birman–Schwinger count: `#σ(R) ∩ (1/2, 1]` (with multiplicity) = number of nonreal Xi zero orbits.
