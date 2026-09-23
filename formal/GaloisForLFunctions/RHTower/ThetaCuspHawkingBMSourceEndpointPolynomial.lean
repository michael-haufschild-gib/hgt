import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMRealSourceCoercivity

/-! The original horizon-contact quartic has no zeros in the entire physical strip. -/
namespace RHTower.D4BMJointSource
open Complex Set
noncomputable section
set_option autoImplicit false

def nonstationarySourceEndpointPolynomial (v : ℂ) : ℂ :=
  30*v^(4 : ℕ)+81*v^(3 : ℕ)+80*v^(2 : ℕ)+19*v-6

theorem nonstationarySourceEndpointPolynomial_ne_zero (v : ℂ)
    (hv : v.re ∈ Icc (-(1/2):ℝ) 0) :
    nonstationarySourceEndpointPolynomial v ≠ 0 := by
  let t := -v.re
  let y := v.im
  let F : ℝ := 19-160*t+243*t^(2 : ℕ)-120*t^(3 : ℕ)
  let H : ℝ := -180*t^(2 : ℕ)+243*t-80
  let P : ℝ := 30*t^(4 : ℕ)-81*t^(3 : ℕ)+80*t^(2 : ℕ)-19*t-6
  have ht0 : 0 ≤ t := by dsimp only [t]; linarith [hv.2]
  have ht1 : t ≤ 1/2 := by dsimp only [t]; linarith [hv.1]
  have hP : P ≤ -(15/4) := by
    obtain ⟨hA,hB⟩ := realSourceCoefficient_bounds (v.re-1)
      (by constructor <;> linarith [hv.1,hv.2])
    dsimp only [realSourceCoefficientA,realSourceCoefficientB] at hA hB
    dsimp only [P,t]
    nlinarith only [hA,hB]
  have hre : (nonstationarySourceEndpointPolynomial v).re=P+y^(2 : ℕ)*(30*y^(2 : ℕ)+H) := by
    dsimp only [nonstationarySourceEndpointPolynomial,P,H,t,y]
    norm_num [pow_succ,Complex.mul_re,Complex.mul_im]
    ring
  have him : (nonstationarySourceEndpointPolynomial v).im=y*(F-(81-120*t)*y^(2 : ℕ)) := by
    dsimp only [nonstationarySourceEndpointPolynomial,F,t,y]
    norm_num [pow_succ,Complex.mul_re,Complex.mul_im]
    ring
  intro hz
  have hi := congrArg Complex.im hz
  rw [him,Complex.zero_im] at hi
  have hcor : y^(2 : ℕ)*(30*y^(2 : ℕ)+H) ≤ 0 := by
    rcases mul_eq_zero.mp hi with hy | hy
    · simp [hy]
    · have he : (81-120*t)*y^(2 : ℕ)=F := by linarith only [hy]
      have hF : F ≤ 19-(137/2)*t := by
        have hp := mul_nonneg (mul_nonneg ht0 (show 0 ≤ 1/2-t by linarith))
          (show 0 ≤ 183-120*t by linarith)
        dsimp only [F]
        nlinarith only [hp]
      have hF0 : 0 ≤ F := by
        rw [← he]
        exact mul_nonneg (by linarith) (sq_nonneg y)
      have ht3 : t ≤ 1/3 := by linarith only [hF,hF0]
      have hy2 : y^(2 : ℕ) ≤ 1/2 := by
        have hmul := mul_le_mul_of_nonneg_right
          (show (41:ℝ) ≤ 81-120*t by linarith only [ht3]) (sq_nonneg y)
        rw [he] at hmul
        linarith only [hmul,hF,ht0]
      have hH : H ≤ -19 := by
        have hp := mul_nonpos_of_nonpos_of_nonneg
          (show t-1/3 ≤ 0 by linarith only [ht3])
          (show 0 ≤ 183-180*t by linarith only [ht3])
        dsimp only [H]
        nlinarith only [hp]
      exact mul_nonpos_of_nonneg_of_nonpos (sq_nonneg y) (by linarith only [hy2,hH])
  have hr := congrArg Complex.re hz
  rw [hre,Complex.zero_re] at hr
  linarith only [hr,hP,hcor]

end
end RHTower.D4BMJointSource
