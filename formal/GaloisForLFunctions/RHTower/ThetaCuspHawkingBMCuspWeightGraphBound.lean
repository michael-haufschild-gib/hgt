import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMCuspWeightLimit

/-! Uniform control of the complete original cusp-weighted differential graph. -/
open Complex MeasureTheory
open scoped ComplexConjugate
namespace RHTower.D4BMJointWave
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- The actual causal response has uniformly bounded full weighted energy, including its radial derivative. -/
theorem jointWaveResponse_cuspGraph_uniform (w : ℂ) (hw : 0 < w.re)
    (hd : 3/2 < w.re) (F : SpatialSpace)
    (hF : MemLp (fun p : ℝ × UpperHalfPlane => (cuspWeightLimit p.2.im:ℂ)*F p)
      2 (radialMeasure.prod D4BMModularCore.measure)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℝ, ∀ hN : 0 < N,
      ‖jointCuspWeight N hN (jointWaveResponse w hw F)‖ ≤ C := by
  let K := w.re*‖w‖/((w.re^(2 : ℕ)+w.im^(2 : ℕ))*(w.re^(2 : ℕ)-9/4))
  let B := ‖hF.toLp _‖
  let V := K*B
  let A := ‖w‖*V*B+(9/4)*w.re*V^(2 : ℕ)
  let D := (2*w.re*A+9*w.im^(2 : ℕ)*V^(2 : ℕ))/w.re^(2 : ℕ)
  have hδ : 0 < w.re^(2 : ℕ)-(9/4:ℝ) := by nlinarith
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hB : 0 ≤ B := norm_nonneg _
  have hV : 0 ≤ V := mul_nonneg hK hB
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  refine ⟨Real.sqrt D,Real.sqrt_nonneg _,?_⟩
  intro N hN
  let u := jointWaveResponse w hw F
  let v := cuspSpatialMultiply N hN (jointEmbedding u)
  let r := cuspSpatialLogSlope N hN v
  let d := (jointCuspWeight N hN u : JointEnergySpace) 3
  let X := ‖jointCuspWeight N hN u‖
  have hX : 0 ≤ X := norm_nonneg _
  have hsource : ‖cuspSpatialMultiply N hN F‖ ≤ B := cuspSpatialMultiply_norm_le_limit N hN F hF
  have hv : ‖v‖ ≤ V :=
    (jointWaveResponse_cuspWeight_rotated_bound N hN w hw hd F).trans
      (mul_le_mul_of_nonneg_left hsource hK)
  have hr : ‖r‖ ≤ (3/2)*V := (cuspSpatialLogSlope_bound N hN v).trans
    (mul_le_mul_of_nonneg_left hv (by norm_num))
  have hr2 : ‖r‖^(2 : ℕ) ≤ (9/4)*V^(2 : ℕ) := by
    have h := pow_le_pow_left₀ (norm_nonneg _) hr 2
    nlinarith only [h]
  have hdX : ‖d‖ ≤ X := PiLp.norm_apply_le (jointCuspWeight N hN u : JointEnergySpace) 3
  have hi : |(inner ℂ r d).im| ≤ (3/2)*V*X := by
    apply ((Complex.abs_im_le_norm _).trans (norm_inner_le_norm _ _)).trans
    exact mul_le_mul hr hdX (norm_nonneg _) (by positivity)
  have hc : -3*|w.im| *V*X ≤ 2*w.im*(inner ℂ r d).im := by
    have h := mul_le_mul_of_nonneg_left hi (abs_nonneg w.im)
    have hn := neg_abs_le (w.im*(inner ℂ r d).im)
    rw [abs_mul] at hn
    nlinarith only [h,hn]
  have hright : (conj w*inner ℂ v (cuspSpatialMultiply N hN F)).re ≤ ‖w‖*V*B := by
    calc
      _ ≤ ‖conj w*inner ℂ v (cuspSpatialMultiply N hN F)‖ := Complex.re_le_norm _
      _ = ‖w‖*‖inner ℂ v (cuspSpatialMultiply N hN F)‖ := by rw [norm_mul,Complex.norm_conj]
      _ ≤ ‖w‖*(‖v‖*‖cuspSpatialMultiply N hN F‖) :=
        mul_le_mul_of_nonneg_left (norm_inner_le_norm _ _) (norm_nonneg _)
      _ = ‖w‖*‖v‖*‖cuspSpatialMultiply N hN F‖ := by ring
      _ ≤ _ := by gcongr
  have he := jointCuspWeight_rotated_identity N hN w F u (jointWaveResponse_spec w hw F)
  change w.re*X^(2 : ℕ)+w.re*(w.re^(2 : ℕ)+w.im^(2 : ℕ)-1)*‖v‖^(2 : ℕ)-w.re*‖r‖^(2 : ℕ)+
    2*w.im*(inner ℂ r d).im = _ at he
  have hdrop : 0 ≤ w.re*(w.re^(2 : ℕ)+w.im^(2 : ℕ)-1)*‖v‖^(2 : ℕ) := by
    have hs : 0 ≤ w.re^(2 : ℕ)+w.im^(2 : ℕ)-1 := by nlinarith [sq_nonneg w.im]
    positivity
  have hb : w.re*X^(2 : ℕ) ≤ A+3*|w.im| *V*X := by
    have hr' := mul_le_mul_of_nonneg_left hr2 hw.le
    dsimp [A]
    nlinarith only [he,hdrop,hr',hc,hright]
  have hx2 : X^(2 : ℕ) ≤ D := by
    apply (le_div_iff₀ (sq_pos_of_pos hw)).mpr
    have hb' := mul_le_mul_of_nonneg_left hb (show 0 ≤ 2*w.re by positivity)
    have hsq := sq_nonneg (w.re*X-3*|w.im| *V)
    simp only [sub_sq,mul_pow,sq_abs] at hsq
    nlinarith only [hb',hsq]
  apply (sq_le_sq₀ hX (Real.sqrt_nonneg D)).mp
  rwa [Real.sq_sqrt hD]

end
end RHTower.D4BMJointWave
