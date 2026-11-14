import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.TheScalingSurface
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Exact two-test deficits for the real Weil pairing

The relative sign minimizing the energy of two real compact smooth tests is
explicit. Absolute-energy normalization makes the formula valid for every
test, including zero-energy tests. On positive-energy tests it is precisely
the normalized deficit `2(1-R)` in Corollary 5 of arXiv:2611.10726.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

/-- Absolute-energy normalization stays inside the actual real Weil test space. -/
def weilEnergyNormalize (f : realTests) : realTests :=
  (Real.sqrt |weilPair f f|)⁻¹ • f

/-- Scaling both test arguments scales the actual Weil pairing by the product. -/
theorem weilPair_two_smul (f g : realTests) (a b : ℝ) :
    weilPair (a • f) (b • g) = a * b * weilPair f g := by
  change weilPair (a • (f : ℝ → ℝ)) (b • (g : ℝ → ℝ)) = _
  rw [weilPair_smul_left, weilPair_comm (f : ℝ → ℝ), weilPair_smul_left,
    weilPair_comm (g : ℝ → ℝ)]
  ring

/-- The actual Weil energy along a two-test line is a binary quadratic form. -/
theorem weilPair_sub_smul_self (f g : realTests) (s : ℝ) :
    weilPair (f - s • g) (f - s • g) =
      weilPair f f - 2 * s * weilPair f g + s ^ 2 * weilPair g g := by
  rw [sub_eq_add_neg, ← neg_smul]
  change weilPair ((f : ℝ → ℝ) + (-s) • (g : ℝ → ℝ))
    ((f : ℝ → ℝ) + (-s) • (g : ℝ → ℝ)) = _
  have hg := realTests.smul_mem (-s) g.property
  have hsum := realTests.add_mem f.property hg
  rw [weilPair_add_left f.property hg hsum, weilPair_smul_left,
    weilPair_comm (f : ℝ → ℝ), weilPair_comm (g : ℝ → ℝ),
    weilPair_add_left f.property hg f.property,
    weilPair_add_left f.property hg g.property,
    weilPair_smul_left, weilPair_smul_left, weilPair_comm (g : ℝ → ℝ) f]
  ring

/-- The minimum over the two relative signs is attained, with no positivity assumption. -/
theorem weilPair_exists_sign_min (f g : realTests) :
    ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧
      weilPair (f - ε • g) (f - ε • g) =
        weilPair f f + weilPair g g - 2 * |weilPair f g| := by
  by_cases h : 0 ≤ weilPair f g
  · refine ⟨1, Or.inl rfl, ?_⟩
    rw [weilPair_sub_smul_self, abs_of_nonneg h]
    ring
  · refine ⟨-1, Or.inr rfl, ?_⟩
    rw [weilPair_sub_smul_self, abs_of_neg (lt_of_not_ge h)]
    ring

theorem weilPair_energyNormalize (f g : realTests) :
    weilPair (weilEnergyNormalize f) (weilEnergyNormalize g) =
      weilPair f g / (Real.sqrt |weilPair f f| * Real.sqrt |weilPair g g|) := by
  rw [weilEnergyNormalize, weilEnergyNormalize, weilPair_two_smul]
  ring

theorem weilPair_energyNormalize_self (f : realTests) :
    weilPair (weilEnergyNormalize f) (weilEnergyNormalize f) =
      weilPair f f / |weilPair f f| := by
  rw [weilPair_energyNormalize, ← sq, Real.sq_sqrt (abs_nonneg _)]

/-- The full normalized Weil deficit, including indefinite and zero-energy cases. -/
theorem weilPair_normalized_sign_min (f g : realTests) :
    ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧
      weilPair (weilEnergyNormalize f - ε • weilEnergyNormalize g)
        (weilEnergyNormalize f - ε • weilEnergyNormalize g) =
      weilPair f f / |weilPair f f| + weilPair g g / |weilPair g g| -
        2 * (|weilPair f g| / (Real.sqrt |weilPair f f| * Real.sqrt |weilPair g g|)) := by
  simpa only [weilPair_energyNormalize_self, weilPair_energyNormalize, abs_div,
    abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))] using
      weilPair_exists_sign_min (weilEnergyNormalize f) (weilEnergyNormalize g)

/-- Positive diagonal energies specialize the exact formula to `2(1-R)`. -/
theorem weilPair_positive_normalized_sign_min (f g : realTests)
    (hf : 0 < weilPair f f) (hg : 0 < weilPair g g) :
    ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧
      weilPair (weilEnergyNormalize f - ε • weilEnergyNormalize g)
        (weilEnergyNormalize f - ε • weilEnergyNormalize g) =
        2 * (1 - |weilPair f g| / Real.sqrt (weilPair f f * weilPair g g)) := by
  obtain ⟨ε, hε, he⟩ := weilPair_normalized_sign_min f g
  refine ⟨ε, hε, ?_⟩
  rw [abs_of_pos hf, abs_of_pos hg, div_self hf.ne', div_self hg.ne',
    ← Real.sqrt_mul hf.le] at he
  rw [he]
  ring

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri

#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.weilPair_normalized_sign_min
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.weilPair_positive_normalized_sign_min
