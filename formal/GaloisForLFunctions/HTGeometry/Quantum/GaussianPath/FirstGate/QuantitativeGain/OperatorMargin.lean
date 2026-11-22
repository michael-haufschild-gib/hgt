import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.FirstGate.QuantitativeGain.UniformMargin

/-! # Uniform operator-norm gain for a two-endpoint contact -/
open ContinuousLinearMap
open scoped InnerProductSpace
namespace GaloisForLFunctions.HTGeometry.FirstGate.QuantitativeGain
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The endpoint motion controls the actual operator norm at a prescribed
angle. Only the real-part gap to the spectator levels enters the bound. -/
theorem quadratic_operator_gain (U V K : E →L[ℂ] E) (p : E→E) (ε γ b : ℝ)
    (hγ : 0≤γ) (hγ' : γ≤2) (hb : 0≤b) (hb' : b≤4)
    (hU : ∀ v, ‖U v‖=‖v‖) (hV : ∀ v, ‖V v‖=‖v‖) (hK : ‖K‖≤2)
    (hpy : ∀ v, ‖p v‖^2+‖v-p v‖^2=‖v‖^2)
    (hface : ∀ v, ‖v‖=1 → 1-ε^2/2+γ*‖v-p v‖^2 ≤ (⟪U v,v⟫_ℂ).re)
    (hdir : ∀ v, (⟪U (p v),K (p v)⟫_ℂ).re=b*‖p v‖^2) :
    let t := γ*b/64
    ‖V-ContinuousLinearMap.id ℂ E-(t:ℂ) • K‖ ≤ 2*t^2 →
      ‖U-V‖ ≤ Real.sqrt (ε^2-t*b) := by
  intro t hrem
  have ht : 0≤t := by dsimp [t]; positivity
  apply ContinuousLinearMap.opNorm_le_of_unit_norm (Real.sqrt_nonneg _)
  intro v hv
  let r := ‖v-p v‖
  have hr : 0≤r := norm_nonneg _
  have hpy' : ‖p v‖^2+r^2=1 := by simpa only [hv,one_pow,r] using hpy v
  have hp : ‖p v‖≤1 := by nlinarith only [hpy',sq_nonneg r,norm_nonneg (p v)]
  have hr' : r≤1 := by nlinarith only [hpy',sq_nonneg ‖p v‖,hr]
  have hquad : b*r^2≤4*r := (mul_le_mul_of_nonneg_right hb' (sq_nonneg r)).trans
    (mul_le_mul_of_nonneg_left (by nlinarith only [mul_nonneg hr (sub_nonneg.mpr hr')] : r^2≤r) (by norm_num))
  have hd := variation_restriction U K hU hK v (p v) hv hp
  rw [hdir] at hd
  have hvar : b-8*r ≤ (⟪U v,K v⟫_ℂ).re := by
    change b*‖p v‖^2-4*r ≤ _ at hd
    nlinarith only [hd,hquad,congrArg (b*·) hpy']
  let A := V-ContinuousLinearMap.id ℂ E-(t:ℂ) • K
  have hR : |(⟪U v,A v⟫_ℂ).re| ≤ 2*t^2 := by
    refine (Complex.abs_re_le_norm _).trans ((norm_inner_le_norm _ _).trans ?_)
    rw [hU,hv,one_mul]
    exact (A.le_opNorm v).trans (by simpa only [hv,mul_one] using hrem)
  have he : V v=v+(t:ℂ) • K v+A v := by
    simp only [A,sub_apply,ContinuousLinearMap.id_apply,smul_apply]
    abel
  have hh : (⟪U v,V v⟫_ℂ).re=(⟪U v,v⟫_ℂ).re+t*(⟪U v,K v⟫_ℂ).re+(⟪U v,A v⟫_ℂ).re := by
    conv_lhs => rw [he]
    rw [inner_add_right,inner_add_right,inner_smul_right]
    simp only [Complex.add_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  apply Real.le_sqrt_of_sq_le
  rw [sub_apply,norm_sub_sq (𝕜 := ℂ),hU,hV,hv]
  have hbase := hface v hv
  change 1-ε^2/2+γ*r^2 ≤ _ at hbase
  have hm : t*b/2 ≤ γ*r^2+t*(b-8*r)-2*t^2 := uniform_contact_margin hγ hγ'
  change 1^2-2*(⟪U v,V v⟫_ℂ).re+1^2 ≤ ε^2-t*b
  linarith only [hh,hbase,hm,mul_le_mul_of_nonneg_left hvar ht,(abs_le.mp hR).1]

#print axioms quadratic_operator_gain
end
end GaloisForLFunctions.HTGeometry.FirstGate.QuantitativeGain
