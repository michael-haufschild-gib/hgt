import GaloisForLFunctions.RHTower.PaperCircleDyadicEnergy
import GaloisForLFunctions.HTGeometry.PaperFourierLLogL.Thermal.Positive

/-! # A finite convolution semigroup paid for by native circle energy

Nonnegative dyadic cell energies supply the spectral weights required by the source
positivity theorem. Their exponential Fourier coefficients form actual probability laws.
-/

open scoped BigOperators NNReal
open GaloisForLFunctions.HTGeometry.FourierLLogL
open GaloisForLFunctions.HTGeometry.FourierLLogL.Dyadic

namespace RHTower
noncomputable section
variable {ι : Type*} [Fintype ι]

/-- The probability law whose characteristic function is the energy Boltzmann factor. -/
def paperCircleGridHeat (a : ι → CCMCircleBoundedSymbol) (M : ℕ) (t : ℝ≥0) : Law (Grid M) :=
  ⟨Thermal.q ((t : ℝ) • paperCircleGridEnergy a M),
    Thermal.q_nonneg (fun x => mul_nonneg t.coe_nonneg (paperCircleGridEnergy_nonneg a M x)),
    Thermal.q_total _⟩

theorem paperCircleGridHeat_apply (a : ι → CCMCircleBoundedSymbol) (M : ℕ)
    (t : ℝ≥0) (x : Grid M) :
    paperCircleGridHeat a M t x = Thermal.q ((t : ℝ) • paperCircleGridEnergy a M) x := rfl

/-- Time zero is the point mass at the group identity. -/
theorem paperCircleGridHeat_zero (a : ι → CCMCircleBoundedSymbol) (M : ℕ) :
    paperCircleGridHeat a M 0 = Law.point 0 := by
  apply Law.ext
  intro x
  change Thermal.q ((0 : ℝ) • paperCircleGridEnergy a M) x = Law.point 0 x
  rw [zero_smul]
  simp only [Thermal.q, Thermal.boltz, Thermal.form_zero, neg_zero,
    Real.exp_zero, Complex.ofReal_one]
  rw [← funext chi_zero_left, fc_chi, Law.point_apply]
  by_cases h : x = 0 <;> simp [h, eq_comm]

/-- Addition of elapsed times is exactly convolution of the native energy laws. -/
theorem paperCircleGridHeat_convolution (a : ι → CCMCircleBoundedSymbol) (M : ℕ)
    (s t : ℝ≥0) (x : Grid M) :
    paperCircleGridHeat a M (s + t) x =
      ∑ y : Grid M, paperCircleGridHeat a M s y * paperCircleGridHeat a M t (x - y) := by
  change Thermal.q (((s : ℝ) + (t : ℝ)) • paperCircleGridEnergy a M) x = _
  rw [add_smul, Thermal.q_add]
  rfl

theorem paperCircleGridHeat_even (a : ι → CCMCircleBoundedSymbol) (M : ℕ) (t : ℝ≥0) :
    Function.Even (fun x => paperCircleGridHeat a M t x) := Thermal.q_even _

theorem paperCircleGridHeat_origin_pos (a : ι → CCMCircleBoundedSymbol) (M : ℕ) (t : ℝ≥0) :
    0 < paperCircleGridHeat a M t 0 := Thermal.q_origin_pos _

/-- Exact Fourier multiplier for every native family and every finite resolution. -/
theorem paperCircleGridHeat_characteristic (a : ι → CCMCircleBoundedSymbol) (M : ℕ)
    (t : ℝ≥0) (u : Grid M) :
    (paperCircleGridHeat a M t).Cx (chi u) =
      (Real.exp (-((t : ℝ) * Thermal.form (paperCircleGridEnergy a M) u)) : ℂ) := by
  let A : Thermal.Form M := (t : ℝ) • paperCircleGridEnergy a M
  have H := invert_fc (fun y : Grid M => (Thermal.boltz A y : ℂ)) u
  simp_rw [← Thermal.cq] at H
  change (∑ y : Grid M, (paperCircleGridHeat a M t y : ℂ) * chi u y) = _
  calc
    _ = ∑ y : Grid M, (Thermal.q A y : ℂ) * chi y u := by
      apply Finset.sum_congr rfl
      intro y _
      rw [paperCircleGridHeat_apply, chi_comm]
    _ = (Thermal.boltz A u : ℂ) := H
    _ = _ := by rw [Thermal.boltz, Thermal.form_smul]

/-- The convolution semigroup is continuous in its nonnegative time parameter. -/
theorem continuous_paperCircleGridHeat (a : ι → CCMCircleBoundedSymbol) (M : ℕ) (x : Grid M) :
    Continuous (fun t : ℝ≥0 => paperCircleGridHeat a M t x) := by
  change Continuous (fun t : ℝ≥0 => Thermal.q ((t : ℝ) • paperCircleGridEnergy a M) x)
  unfold Thermal.q fc expU
  simp only [Thermal.boltz, Thermal.form_smul, Complex.real_smul]
  fun_prop

end
end RHTower
