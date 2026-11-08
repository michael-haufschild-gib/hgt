import GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.NarainMeanFourierPositive
import GaloisForLFunctions.RHTower.Deninger.DeningerSchwartzOfDecay
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

/-!
# Schwartz regularity of the Narain boundary Fourier pair

Rapid decay on both rays and bounded derivatives give a Schwartz Fourier
profile by Landau interpolation. Pointwise Fourier inversion recovers the
actual scaled Mellin boundary as a Schwartz function.
-/

open Complex RHTower MeasureTheory Set Filter Topology
open scoped ContDiff
open GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap
set_option autoImplicit false
noncomputable section
namespace GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap

private theorem ray_bound_of_eventually_weighted_bound {f : ℝ → ℂ} (B : ℕ)
    (hbd : ∃ M : ℝ, ∀ x : ℝ, ‖f x‖ ≤ M)
    (htail : ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ x : ℝ in atTop, x ^ B * ‖f x‖ ≤ K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 1 ≤ x → ‖f x‖ ≤ C / x ^ B := by
  obtain ⟨M, hM⟩ := hbd
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  obtain ⟨K, hK, htail⟩ := htail
  obtain ⟨R, hR⟩ := eventually_atTop.mp htail
  let S : ℝ := max R 1
  have hS : 1 ≤ S := le_max_right _ _
  refine ⟨K + S ^ B * M, by positivity, ?_⟩
  intro x hx
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  apply (le_div_iff₀ (pow_pos hx0 B)).mpr
  rw [mul_comm]
  by_cases hRx : R ≤ x
  · exact (hR x hRx).trans (le_add_of_nonneg_right (by positivity))
  · have hxS : x ≤ S := (lt_of_not_ge hRx).le.trans (le_max_left _ _)
    have hp : x ^ B ≤ S ^ B := pow_le_pow_left₀ hx0.le hxS B
    exact (mul_le_mul hp (hM x) (norm_nonneg _) (by positivity)).trans
      (le_add_of_nonneg_left hK)

/-- Every inverse-power bound holds on the complete positive frequency ray. -/
theorem narainMeanBoundaryFourier_positive_rapid (Y Z : Height) (B : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ L : ℝ, 1 ≤ L →
      ‖narainMeanBoundaryFourier Y Z L‖ ≤ C / L ^ B := by
  have hbd : ∃ M : ℝ, ∀ L : ℝ, ‖narainMeanBoundaryFourier Y Z L‖ ≤ M := by
    simpa only [iteratedDeriv_zero] using exists_bound_narainMeanBoundaryFourier_iteratedDeriv Y Z 0
  apply ray_bound_of_eventually_weighted_bound B hbd
  obtain ⟨C, hC, hb⟩ := exists_narainMeanBoundaryFourier_positive_bound Y Z
  let D : ℝ := (Nat.factorial (B + 1) : ℝ) / (1 / 2 : ℝ) ^ (B + 1) * Real.exp (1 / 2)
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  refine ⟨C * D, mul_nonneg hC hD, ?_⟩
  filter_upwards [hb, eventually_ge_atTop (0 : ℝ)] with L hL hL0
  have hp := _root_.HTGeometry.one_add_pow_le_const_mul_exp hL0
    (show (0 : ℝ) < 1 / 2 by norm_num) (B + 1)
  change (1 + L) ^ (B + 1) ≤ D * Real.exp ((1 / 2 : ℝ) * L) at hp
  rw [show (1 / 2 : ℝ) * L = L / 2 by ring] at hp
  have hpoly : L ^ B * (1 + L) ≤ (1 + L) ^ (B + 1) := by
    rw [pow_succ]
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ hL0 (by linarith only [hL0]) B) (by positivity)
  have he : (1 + L) ^ (B + 1) * Real.exp (-(L / 2)) ≤ D := by
    calc
      _ ≤ (D * Real.exp (L / 2)) * Real.exp (-(L / 2)) :=
        mul_le_mul_of_nonneg_right hp (Real.exp_nonneg _)
      _ = D := by rw [mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
  calc
    _ ≤ L ^ B * (C * (1 + L) * Real.exp (-(L / 2))) :=
      mul_le_mul_of_nonneg_left hL (by positivity)
    _ = C * ((L ^ B * (1 + L)) * Real.exp (-(L / 2))) := by ring
    _ ≤ C * ((1 + L) ^ (B + 1) * Real.exp (-(L / 2))) := by gcongr
    _ ≤ _ := mul_le_mul_of_nonneg_left he hC

/-- Every inverse-power bound holds on the complete negative frequency ray. -/
theorem narainMeanBoundaryFourier_negative_rapid (Y Z : Height) (B : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ L : ℝ, 1 ≤ L →
      ‖narainMeanBoundaryFourier Y Z (-L)‖ ≤ C / L ^ B := by
  have hbd : ∃ M : ℝ, ∀ L : ℝ, ‖narainMeanBoundaryFourier Y Z (-L)‖ ≤ M := by
    obtain ⟨M, hM⟩ := exists_bound_narainMeanBoundaryFourier_iteratedDeriv Y Z 0
    exact ⟨M, fun L => by simpa only [iteratedDeriv_zero] using hM (-L)⟩
  apply ray_bound_of_eventually_weighted_bound B hbd
  refine ⟨1, zero_le_one, ?_⟩
  filter_upwards [(tendsto_pow_mul_narainMeanBoundaryFourier_neg Y Z B).eventually
    (gt_mem_nhds (zero_lt_one : (0 : ℝ) < 1))] with L hL
  exact hL.le

/-- The actual boundary Fourier profile is Schwartz by Landau interpolation. -/
def narainMeanFourierSchwartz (Y Z : Height) : SchwartzMap ℝ ℂ :=
  deningerSchwartzOfDecay (narainMeanBoundaryFourier Y Z)
    (contDiff_narainMeanBoundaryFourier Y Z)
    (exists_bound_narainMeanBoundaryFourier_iteratedDeriv Y Z)
    (narainMeanBoundaryFourier_positive_rapid Y Z)
    (narainMeanBoundaryFourier_negative_rapid Y Z)

@[simp] theorem narainMeanFourierSchwartz_apply (Y Z : Height) (L : ℝ) :
    narainMeanFourierSchwartz Y Z L = narainMeanBoundaryFourier Y Z L := rfl

/-- Inverse Fourier transport of the actual source profile. -/
def narainMeanBoundarySchwartz (Y Z : Height) : SchwartzMap ℝ ℂ :=
  FourierTransform.fourierInv (narainMeanFourierSchwartz Y Z)

/-- The Schwartz representative equals the literal Mellin boundary at every frequency. -/
theorem narainMeanBoundarySchwartz_apply (Y Z : Height) (t : ℝ) :
    narainMeanBoundarySchwartz Y Z t = narainMeanBoundaryFrequency Y Z t := by
  have hG : Integrable (narainMeanBoundaryFrequency Y Z) := by
    apply (integrable_narainMeanBoundaryFrequency_moment Y Z 0).mono'
      (continuous_narainMeanBoundaryFrequency Y Z).aestronglyMeasurable
    filter_upwards [] with x
    simp
  have hF : Integrable (FourierTransform.fourier (narainMeanBoundaryFrequency Y Z)) :=
    (narainMeanFourierSchwartz Y Z).integrable
  have h := (continuous_narainMeanBoundaryFrequency Y Z).fourierInv_fourier_eq hG hF
  change ((FourierTransform.fourierInv (narainMeanFourierSchwartz Y Z) : SchwartzMap ℝ ℂ) : ℝ → ℂ) t =
    narainMeanBoundaryFrequency Y Z t
  rw [SchwartzMap.fourierInv_coe]
  exact congrFun h t

#print axioms narainMeanBoundaryFourier_positive_rapid
#print axioms narainMeanBoundaryFourier_negative_rapid
#print axioms narainMeanFourierSchwartz
#print axioms narainMeanBoundarySchwartz_apply
end GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap
