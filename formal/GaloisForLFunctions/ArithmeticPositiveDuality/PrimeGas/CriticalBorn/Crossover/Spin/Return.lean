import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Crossover.Spin.Fidelity

/-! # Orthogonalization by the limiting prime Hamiltonian -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Crossover.Spin

open Filter Real Dynamics
open GaloisForLFunctions.HTGeometry.SchafferExl
open scoped Topology

private theorem clock_norm (θ : ℝ) : ‖clockPhase θ 1‖=1 := by
  simp [clockPhase,Complex.norm_exp]

private theorem kernel_zero (c d θ : ℝ) :
    1+(exp ((c+d)/2):ℂ)*clockPhase θ 1=0 ↔ c+d=0 ∧ clockPhase θ 1= -1 := by
  constructor
  · intro h
    have prod : (exp ((c+d)/2):ℂ)*clockPhase θ 1= -1 := by linear_combination h
    have mag := congrArg (fun w : ℂ => ‖w‖) prod
    simp only [norm_mul,clock_norm,mul_one,Complex.norm_real,Real.norm_of_nonneg (exp_pos _).le,
      norm_neg,norm_one] at mag
    have mid := (Real.exp_eq_one_iff _).mp mag
    rw [mag,Complex.ofReal_one,one_mul] at prod
    exact ⟨by linarith only [mid],prod⟩
  · rintro ⟨h,p⟩
    rw [h,zero_div,exp_zero,Complex.ofReal_one,one_mul,p,add_neg_cancel]

/-- Complete orthogonality criterion in temperature and time. -/
theorem orthogonal_iff (c d t h k : ℝ) :
    Tendsto (transitionProbability c d t h k) atTop (𝓝 0) ↔
      c+d=0 ∧ ∃ n : ℤ, h-k=π+n*(2*π) := by
  have eq : profile c d h k=0 ↔ c+d=0 ∧ ∃ n : ℤ, h-k=π+n*(2*π) := by
    rw [profile,div_eq_iff (by positivity),zero_mul,sq_eq_zero_iff,norm_eq_zero,kernel_zero,negative_phase_iff]
  constructor
  · intro hz
    exact eq.mp (tendsto_nhds_unique (probability_limit c d t h k) hz)
  · intro hz
    simpa only [eq.mpr hz] using probability_limit c d t h k

private theorem norm_response (x θ : ℝ) : ‖1+(x:ℂ)*clockPhase θ 1‖^2 =
    1+x^2+2*x*cos θ := by
  have hr : (clockPhase θ 1).re=cos θ := by simp [clockPhase,Complex.exp_re]
  have hi : (clockPhase θ 1).im=sin θ := by simp [clockPhase,Complex.exp_im]
  rw [←Complex.normSq_eq_norm_sq,Complex.normSq_apply]
  simp only [Complex.add_re,Complex.add_im,Complex.one_re,Complex.one_im,Complex.mul_re,Complex.mul_im,
    Complex.ofReal_re,Complex.ofReal_im,hr,hi,zero_mul,sub_zero,add_zero,zero_add]
  have trig := congrArg (fun z : ℝ => x^2*z) (sin_sq_add_cos_sq θ)
  change x^2*(sin θ^2+cos θ^2)=x^2*1 at trig
  nlinarith only [trig]

/-- Return probability on a fixed temperature latitude. -/
theorem return_profile (c θ : ℝ) : profile c c θ 0 =
    1-4*(Bulk.bulkWeight c:ℝ)*(1-(Bulk.bulkWeight c:ℝ))*sin (θ/2)^2 := by
  rw [profile,sub_zero,show (c+c)/2=c by ring,norm_response]
  have tr := cos_two_mul (θ/2)
  rw [show 2*(θ/2)=θ by ring] at tr
  have ht : cos θ=1-2*sin (θ/2)^2 := by nlinarith only [tr,sin_sq_add_cos_sq (θ/2)]
  rw [ht]
  change _ = 1-4*(1/(1+exp c))*(1-1/(1+exp c))*sin (θ/2)^2
  field_simp [(show 0<1+exp c by positivity).ne']
  ring

/-- The sharp return probability is attained after half a rescaled clock turn. -/
theorem least_return (c : ℝ) :
    IsLeast (Set.range (fun θ : ℝ => profile c c θ 0)) (tanh (c/2)^2) := by
  have edge : tanh (c/2)^2=1-4*(Bulk.bulkWeight c:ℝ)*(1-(Bulk.bulkWeight c:ℝ)) := by
    rw [←spinLatitude_exp_tanh,show 2*(c/2)=c by ring]
    change _ = 1-4*(1/(1+exp c))*(1-1/(1+exp c))
    field_simp [(show 0<1+exp c by positivity).ne']
    ring
  constructor
  · refine ⟨π,?_⟩
    change profile c c π 0 = _
    rw [return_profile,sin_pi_div_two,one_pow,mul_one,edge]
  · rintro y ⟨θ,rfl⟩
    change _ ≤ profile c c θ 0
    rw [return_profile,edge]
    have hs : sin (θ/2)^2≤1 := by nlinarith only [sin_sq_add_cos_sq (θ/2),sq_nonneg (cos (θ/2))]
    have pos : 0≤4*(Bulk.bulkWeight c:ℝ)*(1-(Bulk.bulkWeight c:ℝ)) :=
      mul_nonneg (mul_nonneg (by norm_num) (Bulk.bulkWeight c).property.1)
        (sub_nonneg.mpr (Bulk.bulkWeight c).property.2)
    exact sub_le_sub_left (mul_le_of_le_one_right pos hs) 1

/-- Only the central transition state can be made orthogonal to itself
by a change of clock time alone. -/
theorem time_orthogonal_iff (c t : ℝ) :
    (∃ θ : ℝ, Tendsto (transitionProbability c c t θ 0) atTop (𝓝 0)) ↔ c=0 := by
  constructor
  · rintro ⟨θ,h⟩
    have hc := ((orthogonal_iff c c t θ 0).mp h).1
    linarith only [hc]
  · rintro rfl
    exact ⟨π,(orthogonal_iff 0 0 t π 0).mpr ⟨by ring,0,by simp⟩⟩

#print axioms orthogonal_iff
#print axioms return_profile
#print axioms least_return
#print axioms time_orthogonal_iff

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Crossover.Spin
