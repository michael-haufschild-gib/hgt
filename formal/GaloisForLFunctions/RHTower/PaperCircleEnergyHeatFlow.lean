import GaloisForLFunctions.RHTower.PaperCircleEnergyHeatKernel

/-! # Conservative finite heat evolution of native circle energy

The source probability semigroup acts on the actual dyadic energy profile. It preserves
mass, remains positive and bounded, and damps every Fourier mode by its exact Boltzmann
factor. All assertions hold for every native bounded-symbol family and resolution.
-/

open scoped BigOperators NNReal
open GaloisForLFunctions.HTGeometry.FourierLLogL
open GaloisForLFunctions.HTGeometry.FourierLLogL.Dyadic

namespace RHTower
noncomputable section
variable {ι : Type*} [Fintype ι]

/-- Evolve the actual dyadic family energy by its own probability heat law. -/
def paperCircleEnergyFlow (a : ι → CCMCircleBoundedSymbol) (M : ℕ) (t : ℝ≥0)
    (x : Grid M) : ℝ :=
  (paperCircleGridHeat a M t).Ex (fun y => paperCircleGridEnergy a M (x - y))

theorem paperCircleEnergyFlow_nonneg (a : ι → CCMCircleBoundedSymbol) (M : ℕ)
    (t : ℝ≥0) (x : Grid M) : 0 ≤ paperCircleEnergyFlow a M t x :=
  Law.Ex_nonneg _ fun y => paperCircleGridEnergy_nonneg a M (x - y)

theorem paperCircleEnergyFlow_le (a : ι → CCMCircleBoundedSymbol) (M : ℕ)
    (t : ℝ≥0) (x : Grid M) : paperCircleEnergyFlow a M t x ≤ ∑ i, (a i).bound ^ 2 :=
  (Law.Ex_mono _ fun y => paperCircleGridEnergy_le a M (x - y)).trans
    (Law.Ex_const _ _).le

theorem paperCircleEnergyFlow_zero (a : ι → CCMCircleBoundedSymbol) (M : ℕ) :
    paperCircleEnergyFlow a M 0 = paperCircleGridEnergy a M := by
  funext x
  simp [paperCircleEnergyFlow, paperCircleGridHeat_zero]

/-- Smoothing retains exactly the integrated native family energy. -/
theorem expU_paperCircleEnergyFlow (a : ι → CCMCircleBoundedSymbol) (M : ℕ) (t : ℝ≥0) :
    expU (paperCircleEnergyFlow a M t) = paperCircleFamilyEnergy a := by
  unfold paperCircleEnergyFlow
  rw [expU_ex, Law.Ex_swap]
  have H (y : Grid M) :
      (Law.uniform (Grid M)).Ex (fun x => paperCircleGridEnergy a M (x - y)) =
        paperCircleFamilyEnergy a := by
    rw [← expU_ex]
    simpa only [sub_eq_add_neg, add_comm] using
      (expU_translate (paperCircleGridEnergy a M) (-y)).trans (expU_paperCircleGridEnergy a M)
  simp_rw [H, Law.Ex_const]

/-- Evolution through two elapsed times is iteration of the same averaging law. -/
theorem paperCircleEnergyFlow_add (a : ι → CCMCircleBoundedSymbol) (M : ℕ)
    (s t : ℝ≥0) (x : Grid M) :
    paperCircleEnergyFlow a M (s + t) x =
      (paperCircleGridHeat a M s).Ex (fun y => paperCircleEnergyFlow a M t (x - y)) := by
  unfold paperCircleEnergyFlow Law.Ex
  simp_rw [paperCircleGridHeat_convolution, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  symm
  apply Fintype.sum_equiv (Equiv.addLeft y)
  intro z
  change paperCircleGridHeat a M s y *
      (paperCircleGridHeat a M t z * paperCircleGridEnergy a M (x - y - z)) =
    (paperCircleGridHeat a M s y * paperCircleGridHeat a M t (y + z - y)) *
      paperCircleGridEnergy a M (x - (y + z))
  rw [add_sub_cancel_left, show x - (y + z) = x - y - z by ring]
  ring

/-- Each finite Fourier mode has the exact source exponential damping factor. -/
theorem fc_paperCircleEnergyFlow (a : ι → CCMCircleBoundedSymbol) (M : ℕ)
    (t : ℝ≥0) (u : Grid M) :
    fc (fun x => (paperCircleEnergyFlow a M t x : ℂ)) u =
      (Real.exp (-((t : ℝ) * Thermal.form (paperCircleGridEnergy a M) u)) : ℂ) *
        fc (fun x => (paperCircleGridEnergy a M x : ℂ)) u := by
  have H (y : Grid M) : fc (fun x => (paperCircleGridEnergy a M (x - y) : ℂ)) u =
      chi (-u) y * fc (fun x => (paperCircleGridEnergy a M x : ℂ)) u :=
    fc_right_translate (fun x => (paperCircleGridEnergy a M x : ℂ)) y u
  simp_rw [paperCircleEnergyFlow, Law.Ex, Complex.ofReal_sum, Complex.ofReal_mul,
    fc_sum, fc_lmul, H, ← mul_assoc]
  rw [← Finset.sum_mul]
  change (paperCircleGridHeat a M t).Cx (chi (-u)) * _ = _
  rw [paperCircleGridHeat_characteristic, Thermal.form_even]

theorem norm_fc_paperCircleEnergyFlow (a : ι → CCMCircleBoundedSymbol) (M : ℕ)
    (t : ℝ≥0) (u : Grid M) :
    ‖fc (fun x => (paperCircleEnergyFlow a M t x : ℂ)) u‖ =
      Real.exp (-((t : ℝ) * Thermal.form (paperCircleGridEnergy a M) u)) *
        ‖fc (fun x => (paperCircleGridEnergy a M x : ℂ)) u‖ := by
  rw [fc_paperCircleEnergyFlow, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]

/-- Fourier magnitudes decrease after any additional nonnegative elapsed time. -/
theorem norm_fc_paperCircleEnergyFlow_add_le (a : ι → CCMCircleBoundedSymbol) (M : ℕ)
    (s t : ℝ≥0) (u : Grid M) :
    ‖fc (fun x => (paperCircleEnergyFlow a M (s + t) x : ℂ)) u‖ ≤
      ‖fc (fun x => (paperCircleEnergyFlow a M t x : ℂ)) u‖ := by
  rw [norm_fc_paperCircleEnergyFlow, norm_fc_paperCircleEnergyFlow]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  apply Real.exp_le_exp.mpr
  change -(((s : ℝ) + (t : ℝ)) * _) ≤ -((t : ℝ) * _)
  have H := Thermal.form_nonneg (fun x => paperCircleGridEnergy_nonneg a M x) u
  nlinarith [mul_nonneg s.coe_nonneg H]

/-- The finite squared L² size of the energy profile never increases. -/
theorem expU_sq_paperCircleEnergyFlow_add_le (a : ι → CCMCircleBoundedSymbol) (M : ℕ)
    (s t : ℝ≥0) :
    expU (fun x => paperCircleEnergyFlow a M (s + t) x ^ 2) ≤
      expU (fun x => paperCircleEnergyFlow a M t x ^ 2) := by
  have H (r : ℝ≥0) :
      expU (fun x => paperCircleEnergyFlow a M r x ^ 2) =
        ∑ u, ‖fc (fun x => (paperCircleEnergyFlow a M r x : ℂ)) u‖ ^ 2 := by
    rw [fc_parseval]
    congr 1
    funext x
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [H, H]
  apply Finset.sum_le_sum
  intro u _
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_fc_paperCircleEnergyFlow_add_le a M s t u) 2

/-- The finite evolution is continuous at every elapsed time, including zero. -/
theorem continuous_paperCircleEnergyFlow (a : ι → CCMCircleBoundedSymbol) (M : ℕ)
    (x : Grid M) : Continuous (fun t : ℝ≥0 => paperCircleEnergyFlow a M t x) := by
  unfold paperCircleEnergyFlow Law.Ex
  exact continuous_finsetSum _ fun y _ => (continuous_paperCircleGridHeat a M y).mul continuous_const

end
end RHTower
