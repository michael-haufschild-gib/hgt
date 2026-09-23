import GaloisForLFunctions.HTGeometry.HypergeometricTaylorEndpointBounds

/-! Quantitative multiplication and the native inverse-square-root endpoint Jacobian. -/
namespace GaloisForLFunctions.HTGeometry
open Complex Set
noncomputable section
set_option autoImplicit false

/-- Multiplication preserves a second-order remainder with an explicit coefficient bound. -/
theorem quadratic_endpoint_product_bound {f g a₀ a₁ b₀ b₁ : ℂ} {z C D : ℝ}
    (hz : z ∈ Icc (0:ℝ) 1) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hf : ‖f-a₀-a₁*(z:ℂ)‖ ≤ C*z^(2 : ℕ))
    (hg : ‖g-b₀-b₁*(z:ℂ)‖ ≤ D*z^(2 : ℕ)) :
    ‖f*g-a₀*b₀-(a₀*b₁+a₁*b₀)*(z:ℂ)‖ ≤
      (C*(‖b₀‖+‖b₁‖+D)+(‖a₀‖+‖a₁‖)*D+‖a₁‖*‖b₁‖)*z^(2 : ℕ) := by
  have hz0 := hz.1
  have hz1 := hz.2
  have hz2 : z^(2 : ℕ) ≤ 1 := by nlinarith
  have hnz : ‖(z:ℂ)‖=z := by simp [Complex.norm_real,abs_of_nonneg hz0]
  have hbg : ‖g‖ ≤ ‖b₀‖+‖b₁‖+D := by
    calc
      _ ≤ ‖g-b₀-b₁*(z:ℂ)‖+‖b₀+b₁*(z:ℂ)‖ := by
        have hh := norm_sub_norm_le g (b₀+b₁*(z:ℂ))
        rw [← sub_sub] at hh
        linarith
      _ ≤ D*z^(2 : ℕ)+(‖b₀‖+‖b₁‖*z) := by
        gcongr
        simpa only [norm_mul,hnz] using norm_add_le b₀ (b₁*(z:ℂ))
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hz2 hD,mul_le_mul_of_nonneg_left hz1 (norm_nonneg b₁)]
  have hba : ‖a₀+a₁*(z:ℂ)‖ ≤ ‖a₀‖+‖a₁‖ := by
    calc
      _ ≤ ‖a₀‖+‖a₁‖*z := by simpa only [norm_mul,hnz] using norm_add_le a₀ (a₁*(z:ℂ))
      _ ≤ _ := by nlinarith [norm_nonneg a₁]
  rw [show f*g-a₀*b₀-(a₀*b₁+a₁*b₀)*(z:ℂ)=
      (f-a₀-a₁*(z:ℂ))*g+(a₀+a₁*(z:ℂ))*(g-b₀-b₁*(z:ℂ))+a₁*b₁*(z:ℂ)^(2 : ℕ) by ring]
  calc
    _ ≤ ‖(f-a₀-a₁*(z:ℂ))*g‖+‖(a₀+a₁*(z:ℂ))*(g-b₀-b₁*(z:ℂ))‖+‖a₁*b₁*(z:ℂ)^(2 : ℕ)‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ = ‖f-a₀-a₁*(z:ℂ)‖*‖g‖+‖a₀+a₁*(z:ℂ)‖*‖g-b₀-b₁*(z:ℂ)‖+‖a₁‖*‖b₁‖*z^(2 : ℕ) := by
      simp only [norm_mul,norm_pow,hnz]
    _ ≤ (C*z^(2 : ℕ))*(‖b₀‖+‖b₁‖+D)+(‖a₀‖+‖a₁‖)*(D*z^(2 : ℕ))+‖a₁‖*‖b₁‖*z^(2 : ℕ) := by gcongr
    _ = _ := by ring

/-- The literal radial Jacobian has its first two coefficients and a uniform quadratic remainder. -/
theorem inverse_sqrt_jacobian_second_bound {z : ℝ} (hz : z ∈ Icc (0:ℝ) (1/2)) :
    ‖(1/(2*(Real.sqrt (1-z):ℂ)))-(1/2:ℂ)-(1/4:ℂ)*(z:ℂ)‖ ≤ 2*z^(2 : ℕ) := by
  have hz0 := hz.1
  have hz1 := hz.2
  let r := Real.sqrt (1-z)
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hr2 : r^(2 : ℕ)=1-z := Real.sq_sqrt (by linarith)
  have hrl : 1/2 ≤ r := by nlinarith
  have hru : r ≤ 1 := by nlinarith
  have hrp : 0 < r := by linarith
  have hrn : r ≠ 0 := ne_of_gt hrp
  have hr1 : 1+r ≠ 0 := by positivity
  have he : 1/(2*r)-1/2-z/4=z^(2 : ℕ)*((r+2)/(4*r*(1+r)^(2 : ℕ))) := by
    have hzEq : z=1-r^(2 : ℕ) := by linarith
    rw [hzEq]
    field_simp [hrn,hr1]
    ring
  have hfac0 : 0 ≤ (r+2)/(4*r*(1+r)^(2 : ℕ)) := by positivity
  have hfac2 : (r+2)/(4*r*(1+r)^(2 : ℕ)) ≤ 2 := by
    apply (div_le_iff₀ (by positivity)).mpr
    have hs : 1 ≤ (1+r)^(2 : ℕ) := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ 4*r)]
  have hec : (1/(2*(r:ℂ)))-(1/2:ℂ)-(1/4:ℂ)*(z:ℂ)=((1/(2*r)-1/2-z/4:ℝ):ℂ) := by push_cast; ring
  rw [hec,Complex.norm_real,Real.norm_eq_abs,he,abs_of_nonneg (by positivity)]
  exact mul_le_mul_of_nonneg_left hfac2 (sq_nonneg z) |>.trans_eq (by ring)

end
end GaloisForLFunctions.HTGeometry
