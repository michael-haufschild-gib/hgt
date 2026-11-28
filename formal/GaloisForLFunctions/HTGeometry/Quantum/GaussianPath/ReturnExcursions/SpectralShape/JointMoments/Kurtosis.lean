import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.SpectralShape.MomentStability

/-! # Stability of both normalized moments of a winding -/

open Finset
open scoped BigOperators
namespace GaloisForLFunctions.HTGeometry.ReturnExcursions.SpectralShape
open private pointwise_change moment_change from
  GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.SpectralShape.MomentStability
noncomputable section
variable {I : Type*} [Fintype I] [Nonempty I]

/-- The normalized fourth moment of a centered template. -/
def kurtosis (u : I → ℝ) : ℝ := moment 4 u/(moment 2 u)^2

private theorem fourth_change {x y δ : ℝ} (h : |y-x|≤δ) (hd : δ≤1) :
    |y^4-x^4|≤δ*(3*x^4+8*x^2+4) := by
  have hn := (abs_nonneg _).trans h
  have ha : |y|≤|x|+1 := calc
    _ = |y-x+x| := by rw [sub_add_cancel]
    _ ≤ |y-x|+|x| := abs_add_le ..
    _ ≤ _ := by linarith only [h,hd]
  have hb := pow_le_pow_left₀ (abs_nonneg y) ha 2
  have hs : y^2+x^2≤3*x^2+2 := by
    nlinarith only [hb,sq_abs x,sq_abs y,sq_nonneg (|x|-1)]
  rw [show y^4-x^4=(y^2-x^2)*(y^2+x^2) by ring,abs_mul,
    abs_of_nonneg (add_nonneg (sq_nonneg y) (sq_nonneg x))]
  exact (mul_le_mul (pointwise_change h hd).1 hs (by positivity) (by positivity)).trans_eq (by ring)

/-- Unit variance and fourth moment at most 43 control both coordinates
under the same levelwise perturbation. No higher moment is required. -/
theorem joint_shape_stability (u v : I → ℝ) {δ : ℝ} (hd₀ : 0≤δ) (hd : δ≤1/8)
    (h : ∀ i, |v i-u i|≤δ) (hu : moment 2 u=1) (hu₄ : moment 4 u≤43) :
    |moment 3 u^2-shape v|≤8000*δ ∧ |moment 4 u-kurtosis v|≤2000*δ := by
  refine ⟨(shape_stability u v hd₀ hd h hu hu₄).2,?_⟩
  have h₁ : δ≤1 := hd.trans (by norm_num)
  let V := moment 2 v
  have hv := (moment_change u v h₁ h hu).1
  have hl : 1/2≤V := by linarith only [(abs_le.mp hv).1,hd]
  have hr : V≤3/2 := by linarith only [(abs_le.mp hv).2,hd]
  have hdiff : |moment 4 v-moment 4 u|≤141*δ := by
    unfold moment
    rw [←expect_sub_distrib]
    apply (abs_expect_le _ _).trans ((expect_le_expect (fun i _ => fourth_change (h i) h₁)).trans ?_)
    rw [←mul_expect,expect_add_distrib,expect_add_distrib,←mul_expect,←mul_expect,Fintype.expect_const]
    change δ*(3*moment 4 u+8*moment 2 u+4)≤_
    rw [hu]
    nlinarith only [mul_le_mul_of_nonneg_left hu₄ hd₀]
  have hV : |V^2-1|≤8*δ := by
    rw [show V^2-1=(V-1)*(V+1) by ring,abs_mul,abs_of_nonneg (by linarith only [hl] : 0≤V+1)]
    nlinarith only [mul_le_mul hv (show V+1≤5/2 by linarith only [hr]) (by linarith only [hl]) (by positivity),hd₀]
  have hu₀ : 0≤moment 4 u := expect_nonneg fun i _ => by positivity
  have hnum : |moment 4 u*V^2-moment 4 v|≤485*δ := by
    rw [show moment 4 u*V^2-moment 4 v=moment 4 u*(V^2-1)+(moment 4 u-moment 4 v) by ring]
    apply (abs_add_le ..).trans
    rw [abs_mul,abs_of_nonneg hu₀,abs_sub_comm (moment 4 u) (moment 4 v)]
    linarith only [mul_le_mul hu₄ hV (abs_nonneg _) (by norm_num),hdiff]
  have hVp : 0<V^2 := sq_pos_of_pos (by linarith only [hl])
  change |moment 4 u-moment 4 v/V^2|≤_
  rw [show moment 4 u-moment 4 v/V^2=(moment 4 u*V^2-moment 4 v)/V^2 by
    field_simp [hVp.ne'],abs_div,abs_of_pos hVp]
  apply (div_le_iff₀ hVp).mpr
  have hlow := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤1/2) hl 2
  nlinarith only [hnum,mul_le_mul_of_nonneg_left hlow hd₀,hd₀]

#print axioms joint_shape_stability
end
end GaloisForLFunctions.HTGeometry.ReturnExcursions.SpectralShape
