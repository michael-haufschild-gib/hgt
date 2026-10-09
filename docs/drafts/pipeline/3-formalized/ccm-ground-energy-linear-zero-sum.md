# Linear inverse-square zero sums of CCM ground states force RH

- **ID:** ccm-ground-energy-linear-zero-sum
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** RH goal loop (Opus) rows 565–572; MUST-833 (`riemannHypothesis_of_evenFullGrounds_zeroSum`)
- **Statement:** Let `u_a` be even full ground states of the restricted Weil form at apertures `a_j → ∞`, with real-rooted transforms, `∫u ≠ 0` and `‖u‖₁ ≤ Me^{Ka}|∫u|`. If the inverse-square zero sum satisfies `S_a = Σ_ρ 1/|ρ|² = ∫t²u/∫u ≤ c_K·a` with `c_K = 1/(100(K+2))`, then the ground energies `μ_{a_j}` are bounded, and so RH holds.

## Goal
MUST-833 needs a bounded zero sum. This card needs only a linear bound. Under ¬RH the resonance ground state is spread over the whole aperture and `S_a ≍ a²`, while the trivial bound is `S_a ≤ a²·(mass ratio)`. So RH follows from beating the trivial width `a` of the ground state by a factor `√a`: the effective width only has to be `≲ √a`. No Montel/Hurwitz limit is used. The theorem is a quantitative value correlation: the zero sum controls the ground energy.

## Gates
- [x] 0 → 1  in-progress: well-posed, mechanism identified (rows 570–572)
- [x] 1 → 2  fully-proven: complete paper proof below
- [x] 2 → 3  formalized: `RHTower.riemannHypothesis_of_evenFullGrounds_linearZeroSum`, standard axioms

## Approach (paper proof)
Notation: `F = conjTransform(u)`, `G = F/F(0) = P` (even Hadamard; `P` is the genus-one product over
the real zeros), `S ≥ 1` an upper bound for `Σ_ρ 1/|ρ|²`, `σ = 6S`, `κ = μ_a/2π`. `b` is a fixed
nonnegative even bump on `[−1,1]` with `b̂(0) > 0`, so that `|b̂| ≤ b̂(0)` and `b̂(s) ≥ b̂(0)(1 − s²/2)`.

1. **Exact smeared identity.** `norm_gaussWeightedDefect_le` at `c = u = 0`, `R = a − 2` gives
   `|Σ_q G(γ_q)b̂(−γ_q)e^{−σγ_q²} − κ∫G b̂ e^{−σs²}| ≤ (1+|κ|)·B·τ_σ(R)·D₀`, where
   `B = sup_{|Im|<1}|G| ≤ Me^{(K+1)a}` and `τ_σ(R) ≤ (4πσ)^{−½}(16σ/R)e^{−R²/8σ}` for `R ≥ 4σ`.
2. **Zero side is tiny.** `|G(z)| ≤ e^{2S|z|²}` (`canonicalProductE1Indexed_norm_le_exp_min`), so
   `|G(γ)e^{−σγ²}| ≤ e^{−4S x² + 8S y²} ≤ e^{2S − 4S·82}` using `(Re γ)² > 331/4`
   (`xiSpectralPoint_re_sq_gt_floor`). The zero sum is therefore `≤ b̂(0)·S_Ξ·e^{−300S}`.
3. **Line integral is large.** With `r = 1/(2√S)`:
   - on `|s| ≤ r`, `|G − 1| ≤ e^{Ss²} − 1 ≤ e^{¼} − 1 < 0.3` (`norm_canonicalProductE1Indexed_sub_one_le`; zeros satisfy `|ρ| ≥ 1/√S ≥ 2r`);
   - on `|s| > r`, `|G(s)| ≤ e^{Ss²/2}` (`norm_canonicalProductE1Indexed_ofReal_le`, real zeros).

   Hence `|∫G b̂ e^{−σs²}| ≥ b̂(0)[(0.875 − 0.3)∫_{|s|≤r}(1 − σs²) − ∫_{|s|>r}e^{−5.5Ss²}] ≥ b̂(0)(0.287 − 0.184)/√S`.
4. **Ground energy.** If `B τ D₀ ≤ |I|/2`, then `|κ| ≤ 1 + 2·tiny/|I|`, so `|μ_a| ≤ 2π(1 + 1)`.
   The condition holds when `(a−2)²/(48S) ≥ (K+1)a + O(log a)`, in particular for `S ≤ a/(100(K+2))`
   and `a` large.
5. **RH.** `μ_a` is antitone in `a` (`ccmRestrictedWeilGroundEnergy_antitone`). Under ¬RH it is
   unbounded below (`exists_ccmRestrictedWeilGroundEnergy_lt_of_not_riemannHypothesis`).

## Lean certificate (2026-10-09)

Modules `RHTower/CanonicalProductE1RealLineBounds`, `RHTower/CCMGroundEnergyZeroSumBound` (wired in
`RHTower.lean`; `lake env lean` clean on both; `lake --old build` green). `#print axioms` gives
`[propext, Classical.choice, Quot.sound]` for each item below.

| Claim | Lean |
|-|-|
| `\|(1−w)e^w\| ≤ e^{w²/2}`, real `w` | `norm_weierstrassE1_ofReal_le` |
| `\|P(s)\| ≤ e^{Ss²/2}` (real zeros); `\|P(z)−1\| ≤ e^{S\|z\|²}−1` | `norm_canonicalProductE1Indexed_ofReal_le`, `norm_canonicalProductE1Indexed_sub_one_le` |
| `\|G\| ≤ e^{2S\|z\|²}`, `\|G(s)−1\| ≤ e^{2Ss²}−1` | `norm_hadamardProduct_le_of_zeroSum`, `norm_hadamardProduct_ofReal_sub_one_le` |
| bump `b ≥ 0`: `\|b̂(z)\| ≤ b̂(0)e^{\|Im z\|}`, `Re b̂(s) ≥ b̂(0)(1−s²/2)` | `posBumpTest`, `norm_suzukiSmoothFourier_posBumpTest_le`, `re_suzukiSmoothFourier_posBumpTest_ge` |
| Gaussian tail `τ_σ(R) ≤ 2e^{−R²/16σ}` (`R ≥ 8σ`) | `gaussShiftTail_zero_le` |
| line integral `Re I ≥ b̂(0)√(π/S)/4` | `re_integral_gaussBump_ge` |
| zero side `≤ e^{−S}·2K₀S_Ξ` (uses `(Re γ)² > 331/4`) | `norm_zeroSide_gaussBump_le` |
| any even eigenvector: `\|μ\| ≤ μ_max` | `abs_eigenvalue_le_of_zeroSum` |
| single aperture: `\|μ_a\| ≤ μ_max` | `abs_ccmRestrictedWeilGroundEnergy_le_of_zeroSum` (constant `groundEnergyZeroSumConst`) |
| eventual tail condition for `S = a/(200(K+2))` | `eventually_gaussTail_small` |
| **capstone** | `riemannHypothesis_of_evenFullGrounds_linearZeroSum` |
| simple ground level (real roots automatic) | `riemannHypothesis_of_simpleEvenFullGrounds_linearZeroSum` |

The capstone takes even full ground states with real-rooted transforms, nonzero mass,
`‖u_j‖₁ ≤ Me^{Ka_j}|∫u_j|` (`K ≥ 0`) and `Σ_ρ1/|ρ|² ≤ a_j/(200(K+2))` along `a_j → ∞`, and
concludes RH. No limit is taken; the argument goes through the bounded ground energy, its
antitonicity, and `exists_ccmRestrictedWeilGroundEnergy_lt_of_not_riemannHypothesis`.

## Log
- 2026-10-09 — created; Module A compiled.
- 2026-10-09 — fully formalized; moved to 3-formalized (MUST-838).
