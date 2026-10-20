import GaloisForLFunctions.SquareRootThreshold.WeilPositivityForcesTheCriticalLine

/-!
# Unimodular two-bump tests decide the critical line

Positivity of the Weil form on all compactly supported tests is far more than the critical line
requires. Let `κ_γ` be the bump `κ_1` modulated to height `γ`. The family of unimodular two-bump
tests

`f_{γ,v,τ}(t) = κ_γ(t + v/2) + τ κ_γ(t − v/2)`,  `γ ∈ ℝ`, `v ≥ 0`, `|τ| = 1`,

three real parameters in all, already decides it (`onLine_iff_twoBump_nonneg`). A tempered
configuration has `Re W(f, f) ≥ 0` on every such test iff all its zeros lie on the critical line.
With the polar-free bump in place of `κ`, the same family lies in the Hodge class and decides
"every zero on the line or at `0, 1`" (`onLine_or_poles_iff_polarFree_twoBump_nonneg`).

The test `f_{γ,v,τ}` reads the `2 × 2` Toeplitz minor of the lag structure `S_γ` in the direction
`τ`. Positivity in every direction is the minor inequality
`|S_γ(v) + conj S_γ(−v)| ≤ 2 Re S_γ(0)` (`norm_lagStructure_le_of_twoBump_nonneg`). An off-line
zero breaks that inequality at its own height (`exists_minor_fails_modScaledBump`).

For `ζ` (`zeta_onLine_iff_twoBump_nonneg`): RH holds iff `Re W_ζ(f_{γ,v,τ}, f_{γ,v,τ}) ≥ 0` for
all `γ ∈ ℝ`, `v ≥ 0` and `|τ| = 1`.
-/

open MeasureTheory Complex Set Filter Topology
open scoped Real ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.SquareRootThreshold

open Zeta23 _root_.RHTower

/-- **Unimodular two-bump criterion.** A tempered configuration is Weil nonnegative on every test
`κ_γ(t + v/2) + τ κ_γ(t − v/2)`, `v ≥ 0`, `|τ| = 1`, iff all its zeros lie on the critical
line. -/
theorem onLine_iff_twoBump_nonneg (Z : ZeroConfig) (hZ : TemperedConfig Z) :
    (∀ (γ v : ℝ) (τ : ℂ), 0 ≤ v → ‖τ‖ = 1 →
      0 ≤ (Z.W (twoBump (modScaledBump 1 γ) v τ) (twoBump (modScaledBump 1 γ) v τ)).re) ↔
      ∀ ρ ∈ Z.carrier, ρ.re = 1 / 2 := by
  refine ⟨fun h ρ hρ => ?_, fun hon _ _ _ _ _ => weil_nonneg_of_onLine Z hon _⟩
  by_contra hre
  obtain ⟨γ, v, hv, hgt⟩ := exists_minor_fails_modScaledBump Z hZ hρ hre
  exact absurd (norm_lagStructure_le_of_twoBump_nonneg Z hZ (contDiff_modScaledBump_two 1 γ)
    (modScaledBump_support one_pos γ) v fun τ hτ => h γ v τ hv hτ) (not_le.mpr hgt)

/-- **Polar-free two-bump criterion.** A tempered configuration is Weil nonnegative on every test
`κ₂,γ(t + v/2) + τ κ₂,γ(t − v/2)`, `κ₂,γ` the polar-free bump modulated to `γ`, `v ≥ 0`, `|τ| = 1`,
iff each of its zeros lies on the critical line or at `s = 0, 1`. -/
theorem onLine_or_poles_iff_polarFree_twoBump_nonneg (Z : ZeroConfig) (hZ : TemperedConfig Z) :
    (∀ (γ v : ℝ) (τ : ℂ), 0 ≤ v → ‖τ‖ = 1 →
      0 ≤ (Z.W (twoBump (scaledBumpPolarFree 1 γ) v τ)
        (twoBump (scaledBumpPolarFree 1 γ) v τ)).re) ↔
      ∀ ρ ∈ Z.carrier, ρ.re = 1 / 2 ∨ ρ = 0 ∨ ρ = 1 := by
  refine ⟨fun h ρ hρ => ?_, fun hon γ v τ _ _ => ?_⟩
  · by_contra hcon
    push Not at hcon
    obtain ⟨γ, v, hv, hgt⟩ := exists_minor_fails_polarFree Z hZ hρ hcon.1 hcon.2.1 hcon.2.2
    exact absurd (norm_lagStructure_le_of_twoBump_nonneg Z hZ (contDiff_scaledBumpPolarFree 1 γ)
      (scaledBumpPolarFree_support one_pos γ) v fun τ hτ => h γ v τ hv hτ) (not_le.mpr hgt)
  · obtain ⟨hp, hn⟩ := paperFT_scaledBumpPolarFree_half one_pos γ
    have hbc := hasCompactSupport_of_support_subset_abs (scaledBumpPolarFree_support one_pos γ)
    have hc := (contDiff_scaledBumpPolarFree 1 γ).continuous
    refine re_W_nonneg_of_summand_nonneg Z fun ρ hρ => ?_
    rcases hon ρ hρ with h | h
    · exact re_Wsummand_nonneg_of_onLine Z _ h
    · rw [Wsummand_eq_zero_of_pole Z (paperFT_twoBump_eq_zero hc hbc v τ hp)
        (paperFT_twoBump_eq_zero hc hbc v τ hn) h, Complex.zero_re]

/-- **For `ζ`.** RH holds iff `Re W_ζ(f, f) ≥ 0` for every unimodular two-bump test
`f = κ_γ(t + v/2) + τ κ_γ(t − v/2)`. -/
theorem zeta_onLine_iff_twoBump_nonneg :
    (∀ (γ v : ℝ) (τ : ℂ), 0 ≤ v → ‖τ‖ = 1 →
      0 ≤ (zetaZeroConfig.W (twoBump (modScaledBump 1 γ) v τ)
        (twoBump (modScaledBump 1 γ) v τ)).re) ↔
      ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re = 1 / 2 :=
  onLine_iff_twoBump_nonneg _ temperedConfig_zetaZeroConfig

end GaloisForLFunctions.SquareRootThreshold
