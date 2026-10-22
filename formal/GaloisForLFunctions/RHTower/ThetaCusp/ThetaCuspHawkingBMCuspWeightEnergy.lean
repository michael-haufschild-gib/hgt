import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMCuspWeightGraph

/-! Exact weighted energy identity for the original completed joint wave domain. -/
namespace RHTower.D4BMJointWave
open Complex MeasureTheory
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

private theorem complex_self_re {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (x : E) :
    (inner ℂ x x).re = ‖x‖^(2 : ℕ) := inner_self_eq_norm_sq (𝕜 := ℂ) x

private theorem complex_self_im {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (x : E) :
    (inner ℂ x x).im = 0 := inner_self_im (𝕜 := ℂ) x

private theorem double_weight_inner (N : ℝ) (hN : 0 < N) (u v : SpatialSpace) :
    inner ℂ (cuspSpatialMultiply N hN (cuspSpatialMultiply N hN u)) v =
      inner ℂ (cuspSpatialMultiply N hN u) (cuspSpatialMultiply N hN v) :=
  cuspSpatialMultiply_inner N hN (cuspSpatialMultiply N hN u) v

private theorem vertical_weight_identity (N : ℝ) (hN : 0 < N) (g v : SpatialSpace) :
    (inner ℂ
      (cuspSpatialMultiply N hN (cuspSpatialMultiply N hN g+
        cuspSpatialLogSlope N hN (cuspSpatialMultiply N hN v))+
        cuspSpatialLogSlope N hN (cuspSpatialMultiply N hN (cuspSpatialMultiply N hN v))) g).re =
      ‖cuspSpatialMultiply N hN g+cuspSpatialLogSlope N hN (cuspSpatialMultiply N hN v)‖^(2 : ℕ)-
        ‖cuspSpatialLogSlope N hN (cuspSpatialMultiply N hN v)‖^(2 : ℕ) := by
  rw [← cuspSpatialMultiply_logSlope_commute N hN (cuspSpatialMultiply N hN v),map_add]
  simp only [inner_add_left,Complex.add_re]
  rw [double_weight_inner,cuspSpatialMultiply_inner N hN
    (cuspSpatialLogSlope N hN (cuspSpatialMultiply N hN v)) g]
  rw [complex_self_re,norm_add_sq (𝕜 := ℂ)]
  have hc : (inner ℂ (cuspSpatialLogSlope N hN (cuspSpatialMultiply N hN v))
      (cuspSpatialMultiply N hN g)).re =
      (inner ℂ (cuspSpatialMultiply N hN g) (cuspSpatialLogSlope N hN (cuspSpatialMultiply N hN v))).re :=
    inner_re_symm (𝕜 := ℂ) _ _
  change _ = ‖cuspSpatialMultiply N hN g‖^(2 : ℕ)+
    2*(inner ℂ (cuspSpatialMultiply N hN g) (cuspSpatialLogSlope N hN (cuspSpatialMultiply N hN v))).re+
    ‖cuspSpatialLogSlope N hN (cuspSpatialMultiply N hN v)‖^(2 : ℕ)-_
  rw [hc]
  ring

/-- Testing with the squared actual multiplier subtracts exactly its retained gradient error. -/
theorem jointCuspWeight_energy (N : ℝ) (hN : 0 < N) (u : jointDomain) :
    (inner ℂ (jointCuspWeight N hN (jointCuspWeight N hN u)) u).re =
      ‖jointCuspWeight N hN u‖^(2 : ℕ)-
        ‖cuspSpatialLogSlope N hN (cuspSpatialMultiply N hN (jointEmbedding u))‖^(2 : ℕ) := by
  have hn : ‖jointCuspWeight N hN u‖^(2 : ℕ) =
      (inner ℂ (jointCuspWeight N hN u) (jointCuspWeight N hN u)).re := by
    simp only [complex_self_re]
  rw [hn,joint_inner_decomposition,joint_inner_decomposition]
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero,jointCuspWeight_mass]
  let M := cuspSpatialMultiply N hN
  let R := cuspSpatialLogSlope N hN
  let v := jointEmbedding u
  let a := (u : JointEnergySpace) 1
  let b := (u : JointEnergySpace) 2
  let c := (u : JointEnergySpace) 3
  change (inner ℂ (M (M v)) v+
      (inner ℂ (M (M a)) a+(inner ℂ (M (M b)) b+
        inner ℂ (M (M c+R (M v))+R (M (M v))) c))).re =
    (inner ℂ (M v) (M v)+(inner ℂ (M a) (M a)+(inner ℂ (M b) (M b)+
      inner ℂ (M c+R (M v)) (M c+R (M v))))).re-‖R (M v)‖^(2 : ℕ)
  have hv := vertical_weight_identity N hN c v
  simp only [Complex.add_re]
  dsimp only [M,R] at *
  simp only [double_weight_inner,complex_self_re]
  linarith

/-- The original wave form evaluated on its squared cusp test retains the exact derivative defect. -/
theorem jointCuspWeight_wave_identity (N : ℝ) (hN : 0 < N) (w : ℂ)
    (F : SpatialSpace) (u : jointDomain) (hu : JointWaveSolution w F u) :
    ‖jointCuspWeight N hN u‖^(2 : ℕ)+
      ((w^(2 : ℕ)).re-1)*‖cuspSpatialMultiply N hN (jointEmbedding u)‖^(2 : ℕ)-
      ‖cuspSpatialLogSlope N hN (cuspSpatialMultiply N hN (jointEmbedding u))‖^(2 : ℕ) =
      (inner ℂ (cuspSpatialMultiply N hN (jointEmbedding u)) (cuspSpatialMultiply N hN F)).re := by
  have he := hu (jointCuspWeight N hN (jointCuspWeight N hN u))
  change inner ℂ (jointCuspWeight N hN (jointCuspWeight N hN u)) u+
      (w^(2 : ℕ)-1)*inner ℂ (jointEmbedding (jointCuspWeight N hN (jointCuspWeight N hN u)))
        (jointEmbedding u) = inner ℂ (jointEmbedding (jointCuspWeight N hN (jointCuspWeight N hN u))) F at he
  have hr := congrArg Complex.re he
  simp only [jointCuspWeight_mass,double_weight_inner,Complex.add_re] at hr
  rw [jointCuspWeight_energy] at hr
  simp only [Complex.mul_re,Complex.sub_re,Complex.sub_im,Complex.one_re,Complex.one_im,
    complex_self_re,complex_self_im,mul_zero,sub_zero] at hr
  linarith

/-- Uniform weighted mass bound for the actual original response, before removing the truncation. -/
theorem jointWaveResponse_cuspWeight_bound (N : ℝ) (hN : 0 < N) (w : ℂ)
    (hw : 0 < w.re) (hd : 9/4 < (w^(2 : ℕ)).re) (F : SpatialSpace) :
    ‖cuspSpatialMultiply N hN (jointEmbedding (jointWaveResponse w hw F))‖ ≤
      ‖cuspSpatialMultiply N hN F‖/((w^(2 : ℕ)).re-9/4) := by
  let u := jointWaveResponse w hw F
  let v := cuspSpatialMultiply N hN (jointEmbedding u)
  have he := jointCuspWeight_wave_identity N hN w F u (jointWaveResponse_spec w hw F)
  have hg : ‖v‖^(2 : ℕ) ≤ ‖jointCuspWeight N hN u‖^(2 : ℕ) := by
    apply pow_le_pow_left₀ (norm_nonneg _) _ 2
    simpa only [jointCuspWeight_mass] using jointEmbedding_norm_le (jointCuspWeight N hN u)
  have hs := cuspSpatialLogSlope_bound N hN v
  have hs2 : ‖cuspSpatialLogSlope N hN v‖^(2 : ℕ) ≤ (9/4:ℝ)*‖v‖^(2 : ℕ) := by
    have hsq := pow_le_pow_left₀ (norm_nonneg _) hs 2
    nlinarith only [hsq]
  have hi : (inner ℂ v (cuspSpatialMultiply N hN F)).re ≤ ‖v‖*‖cuspSpatialMultiply N hN F‖ :=
    (Complex.re_le_norm _).trans (norm_inner_le_norm _ _)
  have hd0 : 0 < (w^(2 : ℕ)).re-9/4 := by linarith
  apply (le_div_iff₀ hd0).mpr
  by_cases hv : ‖v‖ = 0
  · change ‖v‖*((w^(2 : ℕ)).re-9/4) ≤ _
    rw [hv,zero_mul]
    exact norm_nonneg _
  · have hv0 : 0 < ‖v‖ := lt_of_le_of_ne (norm_nonneg v) (Ne.symm hv)
    have he' : ((w^(2 : ℕ)).re-9/4)*‖v‖^(2 : ℕ) ≤ ‖v‖*‖cuspSpatialMultiply N hN F‖ := by
      change ‖jointCuspWeight N hN u‖^(2 : ℕ)+((w^(2 : ℕ)).re-1)*‖v‖^(2 : ℕ)-
        ‖cuspSpatialLogSlope N hN v‖^(2 : ℕ) = _ at he
      nlinarith
    change ‖v‖*((w^(2 : ℕ)).re-9/4) ≤ _
    nlinarith

end
end RHTower.D4BMJointWave
