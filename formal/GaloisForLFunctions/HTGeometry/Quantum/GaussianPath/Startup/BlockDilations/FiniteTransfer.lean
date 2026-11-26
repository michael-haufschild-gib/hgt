import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.BlockDilations.PatternMass

/-! # From a uniform packet count to a Gaussian probability bound -/

open MeasureTheory ProbabilityTheory Finset
namespace GaloisForLFunctions.HTGeometry.BlockDilations
noncomputable section
variable {ι J : Type*} [Fintype ι] [DecidableEq ι] [Fintype J]

/-- For any measurable event, bound its mass by the largest number of
selective dilations landing in it. The loss is at most the full
Jacobian, even when different patterns dilate different coordinates. -/
theorem gaussian_pattern_cap (S : J→Finset ι) {a : ℝ} (ha : 1≤a)
    {E : Set (ι→ℝ)} (hE : MeasurableSet E) :
    open Classical in
    let μ := Measure.pi fun _ : ι => gaussianReal 0 1
    ∀ M : ℝ, 0≤M →
      (∀ x, ((univ.filter fun j => expand (S j) a x∈E).card:ℝ)≤M) →
      μ.real E*(Fintype.card J:ℝ)≤a^Fintype.card ι*M := by
  classical
  intro μ M hM hcount
  let d := Fintype.card ι
  let v := a^d
  let c (x : ι→ℝ) : ℝ := (univ.filter fun j => expand (S j) a x∈E).card
  have hv : 0<v := pow_pos (zero_lt_one.trans_le ha) _
  have hw (j : J) : v⁻¹≤(a^(S j).card)⁻¹ :=
    inv_anti₀ (pow_pos (zero_lt_one.trans_le ha) _)
      (pow_le_pow_right₀ ha (card_le_univ _))
  have hsum : (Fintype.card J:ℝ)*v⁻¹≤∑ j, (a^(S j).card)⁻¹ := by
    simpa only [sum_const,card_univ,nsmul_eq_mul] using sum_le_sum (s:=univ) (fun j _ => hw j)
  have hcap : ∫ x, c x ∂μ ≤ M := by
    by_cases hi : Integrable c μ
    · simpa using (integral_mono hi (integrable_const (μ:=μ) M) hcount)
    · rw [integral_undef hi]
      exact hM
  have h := (mul_le_mul_of_nonneg_left hsum ENNReal.toReal_nonneg).trans
    ((gaussian_pattern_mass S ha hE).trans hcap)
  rw [←mul_assoc,←div_eq_mul_inv,div_le_iff₀ hv,mul_comm M] at h
  exact h

#print axioms gaussian_pattern_cap
end
end GaloisForLFunctions.HTGeometry.BlockDilations
