import GaloisForLFunctions.SquareRootThreshold.RelaxedHodgeExponentOfOffLineLattices
import GaloisForLFunctions.RHTower.OffLineDensityWeilLowerBound

/-!
# The depth exponent of the depth–density lower bound is optimal

For a configuration all of whose zeros have depth `|β − ½| ≤ η` and whose off-line multiplicity
per unit window is at most `D`, every continuous test of aperture `a` satisfies

`Re W(f, f) ≥ −3500 (2a + 3) D e^{2η(a+2)} ∫|f|²`  (`RHTower.re_W_ge_of_depth_offLineDensity`).

**Optimality** (`depthDensity_exponent_optimal`). The exponent `2η` cannot be lowered, whatever the
constant in front: for every `δ ∈ (0, ½]`, every `θ < 2δ` and every `C > 0` the off-line lattice
`{½ ± δ + 2πik}` has depth exactly `δ`, off-line density at most `1/π + 2` per unit window
(`offLineLatticeConfig_offLineDensityBound`), and, at every large aperture `a`, a polar-constrained
test with `Re W(f, f) < −C e^{θa} ∫|f|²`.

The proof is the exact ground-state energy of the lattice: `L(n − √(S₊S₋))`, which decays like
`−e^{2δa}`.
-/

open MeasureTheory Complex Set Filter Topology
open scoped Real ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.SquareRootThreshold

open Zeta23 _root_.RHTower

/-- Every zero of the off-line lattice has depth exactly `δ`. -/
theorem offLineLatticeConfig_depth {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2) :
    ∀ ρ ∈ (offLineLatticeConfig hL hδ hδ').carrier, |ρ.re - 1 / 2| ≤ δ := by
  rintro _ (⟨k, rfl⟩ | ⟨k, rfl⟩) <;> simp [verticalLatticePoint, abs_of_pos hδ]

/-- **Off-line density of the lattice.** Every unit window carries off-line multiplicity at most
`L/π + 2`. -/
theorem offLineLatticeConfig_offLineDensityBound {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ)
    (hδ' : δ ≤ 1 / 2) : OffLineDensityBound (offLineLatticeConfig hL hδ hδ') (L / π + 2) := by
  set Z := offLineLatticeConfig hL hδ hδ' with hZ
  intro t s hs
  have hwin : (Z.window t (t + 1)).Finite := Z.finite_window t (t + 1)
  have hN : (Z.N t (t + 1) : ℝ) = (Z.window t (t + 1)).ncard := by
    unfold ZeroConfig.N
    exact_mod_cast finsum_one
  have himg : (s.image Subtype.val : Set ℂ) ⊆ Z.window t (t + 1) := by
    intro x hx
    rw [Finset.coe_image] at hx
    obtain ⟨ρ, hρ, rfl⟩ := hx
    exact ⟨ρ.2, hs ρ hρ⟩
  have hcard : (s.card : ℝ) ≤ (Z.window t (t + 1)).ncard := by
    have h1 := Set.ncard_le_ncard himg hwin
    rw [Set.ncard_coe_finset, Finset.card_image_of_injective _ Subtype.val_injective] at h1
    exact_mod_cast h1
  calc ∑ ρ ∈ s, offLineMult Z ρ ≤ ∑ _ρ ∈ s, (1 : ℝ) := by
        refine Finset.sum_le_sum fun ρ _ => ?_
        unfold offLineMult
        split_ifs
        · norm_num
        · simp [hZ, offLineLatticeConfig]
    _ = s.card := by simp
    _ ≤ (Z.window t (t + 1)).ncard := hcard
    _ = Z.N t (t + 1) := hN.symm
    _ ≤ L / π + 2 := offLineLatticeConfig_N_le hL hδ hδ' t

/-- **The depth exponent `2η` is optimal.** For every `δ ∈ (0, ½]`, `θ < 2δ` and `C > 0` there is a
configuration of depth `δ` and off-line density at most `1/π + 2` per unit window which, at every
large aperture `a`, has a polar-constrained test with `Re W(f, f) < −C e^{θa} ∫|f|²`. -/
theorem depthDensity_exponent_optimal {δ θ C : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2)
    (hθ : θ < 2 * δ) (hC : 0 < C) :
    ∃ Z : ZeroConfig, (∀ ρ ∈ Z.carrier, |ρ.re - 1 / 2| ≤ δ) ∧
      OffLineDensityBound Z (1 / π + 2) ∧ ∃ a₀ : ℝ, ∀ a ≥ a₀, ∃ f : ℝ → ℂ, ContDiff ℝ 2 f ∧
        tsupport f ⊆ Icc (-a) a ∧ paperFT f (I / 2) = 0 ∧ paperFT f (-(I / 2)) = 0 ∧
          (Z.W f f).re < -(C * Real.exp (θ * a) * ∫ u, ‖f u‖ ^ 2) := by
  refine ⟨offLineLatticeConfig one_pos hδ hδ', offLineLatticeConfig_depth one_pos hδ hδ',
    offLineLatticeConfig_offLineDensityBound one_pos hδ hδ', ?_⟩
  obtain ⟨a₀, ha₀⟩ := offLineLattice_not_relaxedHodge_eventually_of_lt one_pos hδ hδ' hθ hC
  exact ⟨a₀, fun a ha => (ha₀ a ha).1⟩

end GaloisForLFunctions.SquareRootThreshold
