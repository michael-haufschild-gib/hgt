import GaloisForLFunctions.HTGeometry.LoopEisenstein.UnipotentCoefficientGroup
import GaloisForLFunctions.RHTower.Deninger.DeningerBigWittGhost

/-!
# Finite dependence of unipotent matrix coefficients

The lower-right coefficient through degree `N` depends on upper-left and
lower-left coefficients through `N`, but upper-right coefficients only
below `N`. The missing boundary term vanishes because the lower-left
constant coefficient is zero. The multiplication defects consequently
have the strict-prefix dependence of triangular coordinates.
-/

namespace GaloisForLFunctions.HTGeometry.LoopEisenstein
open Matrix
noncomputable section
variable {R : Type*} [CommRing R]

private theorem coeff_mul_congr_through (N : ℕ) {a b c d : PowerSeries R}
    (ha : ∀ n ≤ N, PowerSeries.coeff n a = PowerSeries.coeff n c)
    (hb : ∀ n ≤ N, PowerSeries.coeff n b = PowerSeries.coeff n d) :
    PowerSeries.coeff N (a * b) = PowerSeries.coeff N (c * d) := by
  rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
  apply Finset.sum_congr rfl
  intro p hp
  have he := Finset.mem_antidiagonal.mp hp
  rw [ha p.1 (by omega), hb p.2 (by omega)]

/-- A zero right constant removes the left coefficient at the current degree. -/
theorem coeff_mul_congr_zero_right (N : ℕ) {a b c d : PowerSeries R}
    (hb : PowerSeries.constantCoeff b = 0) (hd : PowerSeries.constantCoeff d = 0)
    (ha : ∀ n < N, PowerSeries.coeff n a = PowerSeries.coeff n c)
    (hbd : ∀ n ≤ N, PowerSeries.coeff n b = PowerSeries.coeff n d) :
    PowerSeries.coeff N (a * b) = PowerSeries.coeff N (c * d) := by
  rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
  apply Finset.sum_congr rfl
  intro p hp
  have he := Finset.mem_antidiagonal.mp hp
  by_cases hz : p.2 = 0
  · simp only [hz, PowerSeries.coeff_zero_eq_constantCoeff, hb, hd, mul_zero]
  · rw [ha p.1 (by omega), hbd p.2 (by omega)]

/-- A zero left constant removes the right coefficient at the current degree. -/
theorem coeff_mul_congr_zero_left (N : ℕ) {a b c d : PowerSeries R}
    (ha : PowerSeries.constantCoeff a = 0) (hc : PowerSeries.constantCoeff c = 0)
    (hac : ∀ n ≤ N, PowerSeries.coeff n a = PowerSeries.coeff n c)
    (hb : ∀ n < N, PowerSeries.coeff n b = PowerSeries.coeff n d) :
    PowerSeries.coeff N (a * b) = PowerSeries.coeff N (c * d) := by
  rw [mul_comm a b, mul_comm c d]
  exact coeff_mul_congr_zero_right N ha hc hb hac

/-- Two zero constants remove both current-degree boundary terms. -/
theorem coeff_mul_congr_zero_constants (N : ℕ) {a b c d : PowerSeries R}
    (ha : PowerSeries.constantCoeff a = 0) (hb : PowerSeries.constantCoeff b = 0)
    (hc : PowerSeries.constantCoeff c = 0) (hd : PowerSeries.constantCoeff d = 0)
    (hac : ∀ n < N, PowerSeries.coeff n a = PowerSeries.coeff n c)
    (hbd : ∀ n < N, PowerSeries.coeff n b = PowerSeries.coeff n d) :
    PowerSeries.coeff N (a * b) = PowerSeries.coeff N (c * d) := by
  rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
  apply Finset.sum_congr rfl
  intro p hp
  have he := Finset.mem_antidiagonal.mp hp
  by_cases hz : p.1 = 0
  · simp only [hz, PowerSeries.coeff_zero_eq_constantCoeff, ha, hc, zero_mul]
  · by_cases hw : p.2 = 0
    · simp only [hw, PowerSeries.coeff_zero_eq_constantCoeff, hb, hd, mul_zero]
    · rw [hac p.1 (by omega), hbd p.2 (by omega)]

/-- The determinant determines the fourth entry by principal-unit inversion. -/
theorem unipotentCoefficient_lowerRight (g : unipotentCoefficientGroup R) :
    g.1 1 1 = PowerSeries.invOfUnit (g.1 0 0) 1 * (1 + g.1 0 1 * g.1 1 0) := by
  have h := congrArg (fun q : unipotentCoefficientGroup R => q.1 1 1)
    ((unipotentCoefficientEquiv R).symm_apply_apply g)
  exact h.symm

/-- The fourth entry needs one fewer upper-right coefficient than the other two entries. -/
theorem unipotentCoefficient_lowerRight_congr (g h : unipotentCoefficientGroup R) (N : ℕ)
    (ha : ∀ n ≤ N, PowerSeries.coeff n (g.1 0 0) = PowerSeries.coeff n (h.1 0 0))
    (hb : ∀ n < N, PowerSeries.coeff n (g.1 0 1) = PowerSeries.coeff n (h.1 0 1))
    (hc : ∀ n ≤ N, PowerSeries.coeff n (g.1 1 0) = PowerSeries.coeff n (h.1 1 0)) :
    PowerSeries.coeff N (g.1 1 1) = PowerSeries.coeff N (h.1 1 1) := by
  rw [unipotentCoefficient_lowerRight, unipotentCoefficient_lowerRight]
  apply coeff_mul_congr_through N
  · intro n hn
    exact RHTower.deningerBigWittInvOfUnit_coeff_congr (fun m hm => ha m (hm.trans hn))
  · intro n hn
    simp only [map_add]
    congr 1
    apply coeff_mul_congr_zero_right n
      ((mem_unipotentCoefficientGroup R g).mp g.property).2.1
      ((mem_unipotentCoefficientGroup R h).mp h.property).2.1
    · exact fun m hm => hb m (lt_of_lt_of_le hm hn)
    · exact fun m hm => hc m (hm.trans hn)

/-- The upper-right multiplication defect has one zero-constant factor in each term. -/
theorem unipotentCoefficient_upperRight_defect (g h : unipotentCoefficientGroup R) :
    (g * h).1 0 1 - g.1 0 1 - h.1 0 1 =
      (g.1 0 0 - 1) * h.1 0 1 + g.1 0 1 * (h.1 1 1 - 1) := by
  change (g.1 * h.1) 0 1 - g.1 0 1 - h.1 0 1 = _
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  ring

/-- Both factors in each lower-left multiplication defect have zero constant. -/
theorem unipotentCoefficient_lowerLeft_defect (g h : unipotentCoefficientGroup R) :
    (g * h).1 1 0 - g.1 1 0 - h.1 1 0 =
      g.1 1 0 * (h.1 0 0 - 1) + (g.1 1 1 - 1) * h.1 1 0 := by
  change (g.1 * h.1) 1 0 - g.1 1 0 - h.1 1 0 = _
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  ring

/-- The upper-left defect separates principal-unit and off-diagonal products. -/
theorem unipotentCoefficient_upperLeft_defect (g h : unipotentCoefficientGroup R) :
    (g * h).1 0 0 - g.1 0 0 - h.1 0 0 + 1 =
      (g.1 0 0 - 1) * (h.1 0 0 - 1) + g.1 0 1 * h.1 1 0 := by
  change (g.1 * h.1) 0 0 - g.1 0 0 - h.1 0 0 + 1 = _
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  ring

end
end GaloisForLFunctions.HTGeometry.LoopEisenstein

#print axioms GaloisForLFunctions.HTGeometry.LoopEisenstein.unipotentCoefficient_lowerRight_congr
#print axioms GaloisForLFunctions.HTGeometry.LoopEisenstein.unipotentCoefficient_upperLeft_defect
