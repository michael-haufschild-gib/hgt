import GaloisForLFunctions.HTGeometry.GaussianRadialPolarLaw

/-! # Gaussian bounds about the mode of a chi density -/
open Real MeasureTheory Set
namespace GaloisForLFunctions.HTGeometry.WeakBonds.GuardedSegments
noncomputable section

private theorem chi_ratio {k : ℕ} {a r : ℝ} (ha : 0<a) (hr : 0<r) :
    gaussianRadialDensity (k+1) r = gaussianRadialDensity (k+1) a *
      exp ((k:ℝ)*log (r/a)-(r^2-a^2)/2) := by
  let c := (2:ℝ)^(1-((k+1:ℕ):ℝ)/2)/Gamma (((k+1:ℕ):ℝ)/2)
  change c*r^k*exp (-r^2/2)=c*a^k*exp (-a^2/2)*_
  rw [sub_eq_add_neg ((k:ℝ)*_),exp_add,exp_nat_mul,exp_log (div_pos hr ha)]
  have h : a^k*(r/a)^k=r^k := by rw [div_pow]; field_simp
  calc c*r^k*exp (-r^2/2) = c*(a^k*(r/a)^k)*(exp (-a^2/2)*exp (-((r^2-a^2)/2))) := by
         rw [h,←exp_add,show -a^2/2 + -((r^2-a^2)/2) = -r^2/2 by ring]
       _ = _ := by ring

private theorem density_pos (k : ℕ) {a : ℝ} (ha : 0<a) : 0<gaussianRadialDensity (k+1) a := by
  unfold gaussianRadialDensity
  have hg : 0<Gamma (((k+1:ℕ):ℝ)/2) := Gamma_pos_of_pos (by positivity)
  positivity

/-- Up to a centered Gaussian envelope, the mode captures the entire
radial mass. On its right the density also has a Gaussian lower envelope.
Both shapes are independent of the dimension. -/
theorem chi_mode_profile {k : ℕ} (hk : 0<k) {r : ℝ} (hr : 0<r) :
    let a := sqrt (k:ℝ)
    gaussianRadialDensity (k+1) r ≤ gaussianRadialDensity (k+1) a * exp (-((r-a)^2)/2) ∧
    (a≤r → gaussianRadialDensity (k+1) a * exp (-3*(r-a)^2/2) ≤ gaussianRadialDensity (k+1) r) := by
  intro a
  have ha : 0<a := sqrt_pos.mpr (Nat.cast_pos.mpr hk)
  have hs : (k:ℝ)=a^2 := (sq_sqrt (Nat.cast_nonneg k)).symm
  have hρ := (density_pos k ha).le
  rw [chi_ratio ha hr]
  constructor
  · apply mul_le_mul_of_nonneg_left (exp_le_exp.mpr _) hρ
    have h := mul_le_mul_of_nonneg_left (log_le_sub_one_of_pos (div_pos hr ha)) (Nat.cast_nonneg k)
    rw [hs] at h ⊢
    calc a^2*log (r/a)-(r^2-a^2)/2 ≤ a^2*(r/a-1)-(r^2-a^2)/2 := sub_le_sub_right h _
         _ = _ := by field_simp [ha.ne']; ring
  · intro har
    apply mul_le_mul_of_nonneg_left (exp_le_exp.mpr _) hρ
    have h := mul_le_mul_of_nonneg_left (one_sub_inv_le_log_of_pos (div_pos hr ha)) (Nat.cast_nonneg k)
    rw [hs,inv_div] at h
    rw [hs]
    calc -3*(r-a)^2/2 ≤ -((r-a)^2)*(r+2*a)/(2*r) := by
           apply (le_div_iff₀ (by positivity)).mpr
           nlinarith only [mul_le_mul_of_nonneg_left har (sq_nonneg (r-a))]
         _ = a^2*(1-a/r)-(r^2-a^2)/2 := by field_simp [hr.ne']; ring
         _ ≤ _ := sub_le_sub_right h _

#print axioms chi_mode_profile
end
end GaloisForLFunctions.HTGeometry.WeakBonds.GuardedSegments
