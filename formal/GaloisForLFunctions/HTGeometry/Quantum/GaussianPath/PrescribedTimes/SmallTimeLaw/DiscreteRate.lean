import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.SmallTimeLaw.PowerIdentity
import GaloisForLFunctions.HTGeometry.RootGrowthEngine

/-! # Exact small-deadline exponent on the inverse-square-root mesh -/
open MeasureTheory ProbabilityTheory Filter Real Topology
namespace GaloisForLFunctions.HTGeometry.PrescribedTimes.SmallTimeLaw
noncomputable section
variable {ι : Type*} [Fintype ι]

private theorem jacobian_root (m : ℕ) :
    Tendsto (fun n : ℕ => ((sqrt ((n:ℝ)+1))^m)^((n:ℝ)⁻¹)) atTop (𝓝 1) := by
  simp_rw [←one_div]
  apply tendsto_rpow_inv_of_polynomial_bounds (C₁:=1) (C₂:=(2:ℝ)^m) (B:=(m:ℝ)) zero_lt_one (by positivity)
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hn' : 1 ≤ (n:ℝ) := by exact_mod_cast hn
    rw [one_mul]
    exact (rpow_le_one_of_one_le_of_nonpos hn' (by positivity)).trans
      (one_le_pow₀ (one_le_sqrt.mpr (by linarith only [hn'])) )
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hn' : 1 ≤ (n:ℝ) := by exact_mod_cast hn
    rw [rpow_natCast,←mul_pow]
    apply pow_le_pow_left₀ (sqrt_nonneg _) _ _
    apply sqrt_le_iff.mpr ⟨by positivity,?_⟩
    nlinarith only [hn',sq_nonneg ((n:ℝ)-1)]

/-- Taking the inverse-square-time root removes the dilation Jacobian.
The remaining constant is the essential supremum of the Boltzmann weight
on the unit-deadline event. -/
theorem gaussian_discrete_passage_rate (F : (ι → ℝ) → ℝ) (hf : Measurable F)
    (hom : ∀ a > (0:ℝ), ∀ x, a*F (a • x)=F x) :
    let μ := Measure.pi fun _ : ι => gaussianReal 0 1
    Tendsto (fun n : ℕ =>
      (μ.real {x | F x ≤ (sqrt ((n:ℝ)+1))⁻¹})^((n:ℝ)⁻¹))
      atTop (𝓝 (essSup (unitWeight F) μ)) := by
  intro μ
  have h := (gaussian_passage_power_mean F hf hom).mul (jacobian_root (Fintype.card ι))
  rw [mul_one] at h
  apply h.congr
  intro n
  let q := sqrt ((n:ℝ)+1)
  have hq : 0 < q := sqrt_pos.mpr (by positivity)
  let p := μ.real {x | F x ≤ q⁻¹}
  change (p/q^Fintype.card ι)^((n:ℝ)⁻¹)*(q^Fintype.card ι)^((n:ℝ)⁻¹)=p^((n:ℝ)⁻¹)
  rw [←mul_rpow (div_nonneg measureReal_nonneg (pow_nonneg hq.le _)) (pow_nonneg hq.le _),
    div_mul_cancel₀ _ (pow_ne_zero _ hq.ne')]

#print axioms gaussian_discrete_passage_rate
end
end GaloisForLFunctions.HTGeometry.PrescribedTimes.SmallTimeLaw
