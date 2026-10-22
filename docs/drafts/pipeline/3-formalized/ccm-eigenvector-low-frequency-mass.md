# Low-frequency content of CCM eigenvectors bounds the eigenvalue and forces RH

- **ID:** ccm-eigenvector-low-frequency-mass
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** RH goal loop (Opus) row 578; MUST-838 (`ccm-ground-energy-linear-zero-sum.md`)
- **Statement:** Let `u` be an eigenvector of the restricted Weil form at aperture `a` (`Q_a(u,s) = μ⟨u,s⟩` on smooth interior sources), with physical function `f` and transform `F(z) = ∫conj(f(t))e^{izt}dt`. Let `I_σ(F) = ∫F(s)e^{−σs²}b̂(−s)ds` be its low-frequency content at width `σ`, where `b ≥ 0` is a fixed bump. If `8σ ≤ a − 2` and `‖f‖₁e^{a}·2e^{−(a−2)²/16σ}·D ≤ |I_σ(F)|/2`, then `|μ| ≤ 2π(1 + C‖f‖₁e^{a/2−165σ/2}/|I_σ(F)|)`. Consequently, if nonzero full ground states at apertures `a_j → ∞` satisfy `‖f_j‖₁ ≤ Me^{a_j}|I_{a_j/40}(F_j)|`, the Riemann hypothesis holds.

## Goal
MUST-838 needs four hypotheses on the ground state: an even parity, real roots, nonzero mass with mass ratio `≤ Me^{Ka}`, and a linear inverse-square zero sum. This card replaces all four by one scalar condition. The ground transform must keep an `e^{−a}` share of its Paley–Wiener size `‖f‖₁` in a Gaussian window of width `≍ a^{−1/2}` around frequency `0`.

In the time domain, `I_σ(F) = √(π/σ)·conj∫f·k_σ` with the positive kernel `k_σ = b ⋆ e^{−t²/4σ}` of width `√σ ≍ √a`. So the condition says that `f` keeps an `e^{−a}` share of its `L¹` mass, weighted by `k_σ`, near the centre. Oscillation at frequency `≥ 9` destroys this mass at rate `e^{−81σ}`.

## Gates
- [x] 0 → 1  in-progress: mechanism identified (row 578)
- [x] 1 → 2  fully-proven: complete paper proof below
- [x] 2 → 3  formalized: `RHTower.riemannHypothesis_of_fullGrounds_lowFrequencyMass`, standard axioms

## Approach (paper proof)
Notation: `N = ‖f‖₁`, `κ = μ/2π`, `D = eigenDefectConst b (½) 0`, `K₀ = suzukiTestDecayConst b 1`, `S_Ξ = Σ_q 1/|γ_q|²`.

1. **Paley–Wiener.** `f` is supported in `[−a,a]`, so `|F(z)| ≤ N e^{a|Im z|}`. This gives `B = Ne^{a}` on `|Im z| < 1` and `|F(γ)| ≤ Ne^{a/2}` at every Xi zero (`|Im γ| < ½`).
2. **Smeared identity.** Smearing the exact shift identities over `|v| ≤ a − 2` against the Gaussian weight of width `σ` gives `|Z − κI| ≤ (1+|κ|)·B·τ_σ(a−2)·D`, with `τ_σ(R) ≤ 2e^{−R²/16σ}` for `R ≥ 8σ` (`norm_gaussWeightedDefect_le`, `gaussShiftTail_zero_le`). Here `Z = Σ_q F(γ_q)e^{−σγ_q²}b̂(−γ_q)` and `I = I_σ(F)`.
3. **Zero side.** `|e^{−σγ²}| = e^{−σ((Re γ)² − (Im γ)²)} ≤ e^{−σ(331/4 − 1/4)}` by the zero-free window `(Re γ)² > 331/4` (`xiSpectralPoint_re_sq_gt_floor`). With `|b̂(−γ)| ≤ 2K₀/|γ|²` this gives `|Z| ≤ Ne^{a/2}e^{−165σ/2}·2K₀S_Ξ`.
4. **Eigenvalue.** If `BτD ≤ |I|/2`, then `|κ||I| ≤ |Z| + (1+|κ|)|I|/2`, so `|κ| ≤ 1 + 2|Z|/|I|`, which is the single-aperture bound.
5. **RH.** Take `σ = a/40`. The hypothesis `N ≤ Me^{a}|I|` turns the tail condition into `2MD e^{2a − 5(a−2)²/2a} ≤ ½`, which holds for large `a`, and makes the bound `|μ_a| ≤ 2π(1 + CM)`, since `a + a/2 − 165a/80 < 0`. The ground energy is antitone in `a` and unbounded below under ¬RH (`exists_ccmRestrictedWeilGroundEnergy_lt_of_not_riemannHypothesis`). This is a contradiction.

## Relation to MUST-838 and reading
- MUST-838 bounds the zero side through the zero sum, using real roots, at width `σ = 6S`. This card bounds it through Paley–Wiener growth at width `σ ≍ a`, and pays with the low-frequency hypothesis.
- For mass ratios `e^{Ka}` with `K < 1`, MUST-838's hypotheses imply this card's [P]. With `S ≤ a/400` the window at `σ = a/40 ≥ 6S` sees `F ≈ F(0)`, so `|I| ≳ |F(0)|/√a ≥ ‖f‖₁e^{−Ka}/(M√a)`.
- Under RH the conjectured CCM picture (ground transform `≈ Ξ`) gives `|I| ≍ ‖f‖₁/√a`, a margin of `e^{a}` over the requirement.
- Under ¬RH, at every aperture where `μ_a` is very negative, the ground state has exponentially small central mass against `k_{a/40}`, even though its total mass `|∫f|` need not be small (row 571). The RH-sensitive datum is therefore oscillation, not edge growth: an `e^{δ|t|}` envelope alone costs only `e^{δa}`, `δ < ½`, which the `e^{a}` slack absorbs.
- No-slack check: the receiver has slack `e^{a}` in its hypothesis, but proving the hypothesis requires knowing the ground state, which is the CCM edge-mass core (row 508).

## Lean certificate (2026-10-09)

Module `RHTower/CCM/CCMEigenvectorLowFrequencyMassBound` (wired in `RHTower.lean` after `CCMGroundEnergyZeroSumBound`; `lake env lean` clean; `lake --old build` green). `#print axioms` gives `[propext, Classical.choice, Quot.sound]`.

| Claim | Lean |
|-|-|
| low-frequency content `I_σ(F)` | `lowFrequencyMass` |
| zero side `≤ Pe^{−165σ/2}·2K₀S_Ξ` under `\|G(γ_q)\| ≤ P` | `norm_zeroSide_gauss_le_of_bound` |
| single aperture, any eigenvector | `abs_eigenvalue_le_of_lowFrequencyMass` |
| nonzero form-domain vectors have positive `L¹` mass | `integral_norm_timeRep_pos`, `ccmArchimedeanFormToAperture_eq_zero_of_timeRep_ae_zero` |
| eventual tail condition at `σ = a/40` | `eventually_lowFrequency_tail_small` |
| **capstone** | `riemannHypothesis_of_fullGrounds_lowFrequencyMass` |
| any base test `b`: window `e^{−σs²}b̂(−s)` | `windowedMass`, `abs_eigenvalue_le_of_windowedMass`, `norm_zeroSide_gauss_le_of_bound b` |
| finite family of windows, one per aperture | `riemannHypothesis_of_fullGrounds_windowedMass` |
| **parity-free**: even window or odd window (`posBumpTest.derivTest`) | `riemannHypothesis_of_fullGrounds_evenOrOddWindow` |
| tail condition at `σ = cB`, `16c(1+η) < 1` | `eventually_lowFrequency_tail_small_rate` |
| **strip from the share rate** `\|Re ρ − ½\| ≤ max(0, η + ½ − 165c/2)/2` (MUST-843) | `abs_im_xiSpectralPoint_le_of_fullGrounds_lowFrequencyMass` |

## Graceful version (MUST-843)
If the share decays like `e^{−ηB}` at every large aperture, the single-aperture bound gives `μ_B ≥ −C e^{εB}` with `ε = max(0, η + ½ − 165c/2)`, where `16c(1+η) < 1` keeps the tail below the share. Then the sharp Bombieri–Yoshida cap (`abs_im_xiSpectralPoint_le_half_of_polarGroundEnergy_ge`, through `μ ≤ μ_polar`) gives `|Re ρ − ½| ≤ ε/2`. The corpus rate law `μ₀(B) ≤ −c′e^{2ΘB}/B³` (`ConstrainedWeilPolarGroundDecay`) shows that the factor `½` is sharp.

| share rate `η` | conclusion (current constants) |
|-|-|
| `< 1.53` | RH |
| `[1.53, 2.14)` | a strip of width `< ½` |
| `≥ 2.14` | nothing |

So the exponential decay rate of the ground states' low-frequency share controls `Θ − ½` continuously.

## Shape receiver (MUST-844)
Module `RHTower/CCM/CCMSymmetricDecreasingGroundStateRH` (wired after `CCMEigenvectorLowFrequencyMassBound`; `lake --old build` green; standard axioms).

1. **Time domain.** `I_σ(F) = √(π/σ)∫conj(f(t))k_σ(t)dt` with `k_σ(t) = ∫b(x)e^{−(t−x)²/4σ}dx` (`lowFrequencyMass_conjTransform_eq`). The proof is two applications of Fubini and `∫e^{isy}e^{−σs²}ds = √(π/σ)e^{−y²/4σ}` (`integral_cexp_mul_gaussian`, `integral_cexp_mul_lowFrequencyWeight`).
2. **Kernel.** `0 ≤ k_σ ≤ b̂(0)`, `k_σ` is continuous, and `k_σ(t) ≥ b̂(0)e^{−(r+1)²/4σ}` for `|t| ≤ r` (`lowFrequencyKernel_ge`).
3. **Central mass.** If `g ≥ 0` vanishes outside `[−A,A]` and is symmetric-decreasing, then `r∫g ≤ (r+A)∫_{[−r,r]}g` (`integral_le_mul_setIntegral_of_symmDecreasing`). The outer part is at most `2A·g(r)` and the inner part at least `2r·g(r)`.
4. **Share.** `√(π/σ)b̂(0)e^{−(r+1)²/4σ}·r‖f‖₁ ≤ (r+A)|I_σ(F)|` (`norm_lowFrequencyMass_ge`). At `σ = A/40`, `r = √σ`: `√π b̂(0)e^{−1}‖f‖₁ ≤ 2A|I_σ(F)| ≤ 2e^{A}|I_σ(F)|`.
5. **Capstone.** `riemannHypothesis_of_fullGrounds_symmDecreasing` feeds 4 into `riemannHypothesis_of_fullGrounds_lowFrequencyMass` along the tail `a_j ≥ 40`.

Reading: under RH the conjectured ground shape `Φ·1_{[−a,a]}` is positive, even and decreasing on `t > 0` (Pólya). The receiver says RH follows from Perron–Frobenius plus unimodality of the ground states. Positivity alone is insufficient (row 579).

## Log
- 2026-10-09 — created and formalized in one cycle (row 578).
- 2026-10-09 — strip version added (row 580, MUST-843).
- 2026-10-09 — shape receiver added (row 581, MUST-844).
- 2026-10-09 — generic base test and parity-free capstone (row 583).
