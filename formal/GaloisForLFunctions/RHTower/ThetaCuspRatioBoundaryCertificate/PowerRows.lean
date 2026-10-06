import GaloisForLFunctions.RHTower.ThetaCuspRatioBoundaryCertificate.CoefficientForms

namespace HTGeometry.ThetaRatioInfinity
noncomputable section
open HTGeometry.EvenCompactBernstein

def boundaryTermPowerRow77 (c : ℝ) (a p j e : ℕ) (x : ℕ → ℝ) : ℝ :=
  ∑ l ∈ Finset.range (j+1), ∑ m ∈ Finset.range (l+1),
    if e=a+2*l+m then boundaryTermScalar77 c j l m*x (p+j+l) else 0

theorem boundaryTermForm77_power_rows (c : ℝ) (a p j A : ℕ) (x : ℕ → ℝ)
    (ha : a+3*j≤96) :
    boundaryTermForm77 c a p j A x=
      ∑ e ∈ Finset.range 97,
        boundaryH77^e*degreeElevationCoefficient 96 e A*
          boundaryTermPowerRow77 c a p j e (fun q => boundaryS77^q*x q) := by
  unfold boundaryTermForm77 boundaryTermPowerRow77
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l hl
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m hm
  have hl' : l≤j := by have := Finset.mem_range.mp hl; omega
  have hm' : m≤l := by have := Finset.mem_range.mp hm; omega
  have he : a+2*l+m∈Finset.range 97 := by
    apply Finset.mem_range.mpr
    omega
  simp only [mul_ite,mul_zero]
  rw [Finset.sum_ite_eq']
  simp only [he,if_true]
  ring

theorem boundaryTermPowerRow77_zero_clock (c : ℝ) (a p j e : ℕ) (x : ℕ → ℝ)
    (he : e<a) : boundaryTermPowerRow77 c a p j e x=0 := by
  unfold boundaryTermPowerRow77
  apply Finset.sum_eq_zero
  intro l hl
  apply Finset.sum_eq_zero
  intro m hm
  have hn : e≠a+2*l+m := by omega
  simp only [hn,if_false]


theorem boundaryTermPowerRow77_zero_above (c : ℝ) (a p j e : ℕ) (x : ℕ → ℝ)
    (he : a+3*j<e) : boundaryTermPowerRow77 c a p j e x=0 := by
  unfold boundaryTermPowerRow77
  apply Finset.sum_eq_zero
  intro l hl
  apply Finset.sum_eq_zero
  intro m hm
  have hl' : l≤j := by have := Finset.mem_range.mp hl; omega
  have hm' : m≤l := by have := Finset.mem_range.mp hm; omega
  have hn : e≠a+2*l+m := by omega
  simp only [hn,if_false]


theorem boundaryTermPowerRow77_single_sum (c : ℝ) (a p j e : ℕ) (x : ℕ → ℝ) :
    boundaryTermPowerRow77 c a p j e x=
      ∑ l ∈ Finset.range (j+1),
        if a+2*l≤e ∧ e≤a+3*l then
          boundaryTermScalar77 c j l (e-(a+2*l))*x (p+j+l)
        else 0 := by
  unfold boundaryTermPowerRow77
  apply Finset.sum_congr rfl
  intro l hl
  by_cases he : a+2*l≤e ∧ e≤a+3*l
  · simp only [if_pos he]
    rw [Finset.sum_eq_single (e-(a+2*l))]
    · have heq : e=a+2*l+(e-(a+2*l)) := by omega
      rw [if_pos heq]
    · intro m hm hne
      have hn : e≠a+2*l+m := by omega
      simp only [hn,if_false]
    · intro hn
      have hm : e-(a+2*l)∈Finset.range (l+1) := by
        apply Finset.mem_range.mpr
        omega
      exact (hn hm).elim
  · simp only [if_neg he]
    apply Finset.sum_eq_zero
    intro m hm
    have hm' : m≤l := by have := Finset.mem_range.mp hm; omega
    have hn : e≠a+2*l+m := by omega
    simp only [hn,if_false]

end
end HTGeometry.ThetaRatioInfinity
