import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMCuspWeightEnergy

/-! Retaining the imaginary commutator gives cusp admission at every imaginary frequency. -/
namespace RHTower.D4BMJointWave
open Complex MeasureTheory
open scoped ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

private theorem self_re {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (u : E) : (inner ℂ u u).re = ‖u‖^(2 : ℕ) :=
  inner_self_eq_norm_sq (𝕜 := ℂ) u
private theorem self_im {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (u : E) : (inner ℂ u u).im = 0 :=
  inner_self_im (𝕜 := ℂ) u

private theorem vertical_complex (N : ℝ) (hN : 0 < N) (g v : SpatialSpace) :
    inner ℂ (cuspSpatialMultiply N hN (cuspSpatialMultiply N hN g+
        cuspSpatialLogSlope N hN (cuspSpatialMultiply N hN v))+
      cuspSpatialLogSlope N hN (cuspSpatialMultiply N hN (cuspSpatialMultiply N hN v))) g =
    inner ℂ (cuspSpatialMultiply N hN g+cuspSpatialLogSlope N hN (cuspSpatialMultiply N hN v))
      (cuspSpatialMultiply N hN g+cuspSpatialLogSlope N hN (cuspSpatialMultiply N hN v))-
    inner ℂ (cuspSpatialLogSlope N hN (cuspSpatialMultiply N hN v))
      (cuspSpatialLogSlope N hN (cuspSpatialMultiply N hN v))+
    inner ℂ (cuspSpatialLogSlope N hN (cuspSpatialMultiply N hN v))
      (cuspSpatialMultiply N hN g+cuspSpatialLogSlope N hN (cuspSpatialMultiply N hN v))-
    inner ℂ (cuspSpatialMultiply N hN g+cuspSpatialLogSlope N hN (cuspSpatialMultiply N hN v))
      (cuspSpatialLogSlope N hN (cuspSpatialMultiply N hN v)) := by
  rw [← cuspSpatialMultiply_logSlope_commute N hN (cuspSpatialMultiply N hN v),map_add]
  simp only [inner_add_left,inner_add_right]
  rw [cuspSpatialMultiply_inner N hN (cuspSpatialMultiply N hN g) g,
    cuspSpatialMultiply_inner N hN (cuspSpatialLogSlope N hN (cuspSpatialMultiply N hN v)) g]
  ring

/-- The squared test retains the full skew cross term of the original vertical derivative. -/
theorem jointCuspWeight_energy_complex (N : ℝ) (hN : 0 < N) (u : jointDomain) :
    inner ℂ (jointCuspWeight N hN (jointCuspWeight N hN u)) u =
      inner ℂ (jointCuspWeight N hN u) (jointCuspWeight N hN u)-
        inner ℂ (cuspSpatialLogSlope N hN (cuspSpatialMultiply N hN (jointEmbedding u)))
          (cuspSpatialLogSlope N hN (cuspSpatialMultiply N hN (jointEmbedding u)))+
        inner ℂ (cuspSpatialLogSlope N hN (cuspSpatialMultiply N hN (jointEmbedding u)))
          ((jointCuspWeight N hN u : JointEnergySpace) 3)-
        inner ℂ ((jointCuspWeight N hN u : JointEnergySpace) 3)
          (cuspSpatialLogSlope N hN (cuspSpatialMultiply N hN (jointEmbedding u))) := by
  rw [joint_inner_decomposition,joint_inner_decomposition]
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero,jointCuspWeight_mass]
  let M := cuspSpatialMultiply N hN
  let R := cuspSpatialLogSlope N hN
  let v := jointEmbedding u
  let a := (u : JointEnergySpace) 1
  let b := (u : JointEnergySpace) 2
  let c := (u : JointEnergySpace) 3
  change inner ℂ (M (M v)) v+(inner ℂ (M (M a)) a+(inner ℂ (M (M b)) b+
      inner ℂ (M (M c+R (M v))+R (M (M v))) c)) =
    (inner ℂ (M v) (M v)+(inner ℂ (M a) (M a)+(inner ℂ (M b) (M b)+
      inner ℂ (M c+R (M v)) (M c+R (M v)))))-inner ℂ (R (M v)) (R (M v))+
      inner ℂ (R (M v)) (M c+R (M v))-inner ℂ (M c+R (M v)) (R (M v))
  have hc := vertical_complex N hN c v
  rw [cuspSpatialMultiply_inner N hN (M v) v,
    cuspSpatialMultiply_inner N hN (M a) a,cuspSpatialMultiply_inner N hN (M b) b]
  change inner ℂ (M v) (M v)+(inner ℂ (M a) (M a)+(inner ℂ (M b) (M b)+_)) = _
  linear_combination hc

private theorem mass_vertical_le (u : jointDomain) :
    ‖jointEmbedding u‖^(2 : ℕ)+‖(u : JointEnergySpace) 3‖^(2 : ℕ) ≤ ‖u‖^(2 : ℕ) := by
  have he := congrArg Complex.re (joint_inner_decomposition u u)
  have hs : (inner ℂ u u).re = ‖u‖^(2 : ℕ) := inner_self_eq_norm_sq (𝕜 := ℂ) u
  rw [hs] at he
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero,Complex.add_re,self_re] at he
  change ‖u‖^(2 : ℕ) = ‖jointEmbedding u‖^(2 : ℕ)+(‖(u : JointEnergySpace) 1‖^(2 : ℕ)+
    (‖(u : JointEnergySpace) 2‖^(2 : ℕ)+‖(u : JointEnergySpace) 3‖^(2 : ℕ))) at he
  nlinarith only [he,sq_nonneg ‖(u : JointEnergySpace) 1‖,sq_nonneg ‖(u : JointEnergySpace) 2‖]

/-- Rotation by the actual conjugate frequency preserves the complete derivative commutator. -/
theorem jointCuspWeight_rotated_identity (N : ℝ) (hN : 0 < N) (w : ℂ)
    (F : SpatialSpace) (u : jointDomain) (hu : JointWaveSolution w F u) :
    w.re*‖jointCuspWeight N hN u‖^(2 : ℕ)+
      w.re*(w.re^(2 : ℕ)+w.im^(2 : ℕ)-1)*‖cuspSpatialMultiply N hN (jointEmbedding u)‖^(2 : ℕ)-
      w.re*‖cuspSpatialLogSlope N hN (cuspSpatialMultiply N hN (jointEmbedding u))‖^(2 : ℕ)+
      2*w.im*(inner ℂ (cuspSpatialLogSlope N hN (cuspSpatialMultiply N hN (jointEmbedding u)))
        ((jointCuspWeight N hN u : JointEnergySpace) 3)).im =
    (conj w*inner ℂ (cuspSpatialMultiply N hN (jointEmbedding u)) (cuspSpatialMultiply N hN F)).re := by
  have he := hu (jointCuspWeight N hN (jointCuspWeight N hN u))
  change inner ℂ (jointCuspWeight N hN (jointCuspWeight N hN u)) u+
      (w^(2 : ℕ)-1)*inner ℂ (jointEmbedding (jointCuspWeight N hN (jointCuspWeight N hN u)))
        (jointEmbedding u) = inner ℂ (jointEmbedding (jointCuspWeight N hN (jointCuspWeight N hN u))) F at he
  simp only [jointCuspWeight_mass] at he
  rw [cuspSpatialMultiply_inner N hN (cuspSpatialMultiply N hN (jointEmbedding u)) (jointEmbedding u),
    cuspSpatialMultiply_inner N hN (cuspSpatialMultiply N hN (jointEmbedding u)) F,
    jointCuspWeight_energy_complex] at he
  let r := cuspSpatialLogSlope N hN (cuspSpatialMultiply N hN (jointEmbedding u))
  let d := ((jointCuspWeight N hN u : JointEnergySpace) 3)
  have hr : (inner ℂ r d).re = (inner ℂ d r).re := inner_re_symm (𝕜 := ℂ) r d
  have hi : (inner ℂ d r).im = -(inner ℂ r d).im := by
    have hc : conj (inner ℂ r d) = inner ℂ d r := inner_conj_symm d r
    exact (congrArg Complex.im hc).symm
  have hsR : (inner ℂ (jointCuspWeight N hN u) (jointCuspWeight N hN u)).re =
      ‖jointCuspWeight N hN u‖^(2 : ℕ) := self_re (jointCuspWeight N hN u)
  have hsI : (inner ℂ (jointCuspWeight N hN u) (jointCuspWeight N hN u)).im = 0 :=
    self_im (jointCuspWeight N hN u)
  have hc := congrArg (fun z : ℂ => (conj w*z).re) he
  simp only [Complex.mul_re,Complex.add_re,Complex.sub_re,Complex.mul_im,Complex.add_im,
    Complex.sub_im,Complex.conj_re,Complex.conj_im,Complex.one_re,Complex.one_im,
    hsR,hsI,self_re,self_im,mul_zero,sub_zero] at hc
  dsimp [r,d] at hr hi
  rw [hi,← hr] at hc
  simp only [pow_two,Complex.mul_re,Complex.mul_im] at hc
  simp only [Complex.mul_re,Complex.conj_re,Complex.conj_im]
  nlinarith only [hc]

/-- Causal weighted response bound uniform over the entire imaginary-frequency axis. -/
theorem jointWaveResponse_cuspWeight_rotated_bound (N : ℝ) (hN : 0 < N) (w : ℂ)
    (hw : 0 < w.re) (ha : 3/2 < w.re) (F : SpatialSpace) :
    ‖cuspSpatialMultiply N hN (jointEmbedding (jointWaveResponse w hw F))‖ ≤
      (w.re*‖w‖/((w.re^(2 : ℕ)+w.im^(2 : ℕ))*(w.re^(2 : ℕ)-9/4)))*‖cuspSpatialMultiply N hN F‖ := by
  let u := jointWaveResponse w hw F
  let v := cuspSpatialMultiply N hN (jointEmbedding u)
  let r := cuspSpatialLogSlope N hN v
  let d := (jointCuspWeight N hN u : JointEnergySpace) 3
  let S := w.re^(2 : ℕ)+w.im^(2 : ℕ)
  have hS : 0 < S := by dsimp [S]; nlinarith [sq_nonneg w.im]
  have hδ : 0 < w.re^(2 : ℕ)-(9/4:ℝ) := by nlinarith
  have he := jointCuspWeight_rotated_identity N hN w F u (jointWaveResponse_spec w hw F)
  have hg : ‖v‖^(2 : ℕ)+‖d‖^(2 : ℕ) ≤ ‖jointCuspWeight N hN u‖^(2 : ℕ) :=
    mass_vertical_le (jointCuspWeight N hN u)
  have hs : ‖r‖^(2 : ℕ) ≤ (9/4:ℝ)*‖v‖^(2 : ℕ) := by
    have h := pow_le_pow_left₀ (norm_nonneg _) (cuspSpatialLogSlope_bound N hN v) 2
    nlinarith only [h]
  have hi : |(inner ℂ r d).im| ≤ ‖r‖*‖d‖ :=
    (Complex.abs_im_le_norm _).trans (norm_inner_le_norm _ _)
  have hm : -(|w.im| *‖r‖*‖d‖) ≤ w.im*(inner ℂ r d).im := by
    have hb := mul_le_mul_of_nonneg_left hi (abs_nonneg w.im)
    have hn := neg_abs_le (w.im*(inner ℂ r d).im)
    rw [abs_mul] at hn
    nlinarith only [hb,hn]
  have hiR : (conj w*inner ℂ v (cuspSpatialMultiply N hN F)).re ≤
      ‖w‖*‖v‖*‖cuspSpatialMultiply N hN F‖ := by
    calc
      _ ≤ ‖conj w*inner ℂ v (cuspSpatialMultiply N hN F)‖ := Complex.re_le_norm _
      _ = ‖w‖*‖inner ℂ v (cuspSpatialMultiply N hN F)‖ := by rw [norm_mul,Complex.norm_conj]
      _ ≤ _ := by
        have h := mul_le_mul_of_nonneg_left (norm_inner_le_norm (𝕜 := ℂ) v (cuspSpatialMultiply N hN F)) (norm_nonneg w)
        nlinarith only [h]
  have hc : S*(w.re^(2 : ℕ)-9/4)*‖v‖^(2 : ℕ) ≤ w.re*‖w‖*‖v‖*‖cuspSpatialMultiply N hN F‖ := by
    have h1 := mul_le_mul_of_nonneg_left hg (sq_nonneg w.re)
    have h2 := mul_le_mul_of_nonneg_left hs hS.le
    have h3 := mul_le_mul_of_nonneg_left hm (show 0 ≤ 2*w.re by positivity)
    have h4 := mul_le_mul_of_nonneg_left hiR hw.le
    have he' := congrArg (fun x : ℝ => w.re*x) he
    have hsq := sq_nonneg (w.re*‖d‖-|w.im| *‖r‖)
    simp only [sub_sq,mul_pow,sq_abs] at hsq
    change w.re*(w.re*‖jointCuspWeight N hN u‖^(2 : ℕ)+w.re*(S-1)*‖v‖^(2 : ℕ)-
      w.re*‖r‖^(2 : ℕ)+2*w.im*(inner ℂ r d).im) = _ at he'
    dsimp only [S] at h2 ⊢
    change w.re*(w.re*‖jointCuspWeight N hN u‖^(2 : ℕ)+w.re*(w.re^(2 : ℕ)+w.im^(2 : ℕ)-1)*‖v‖^(2 : ℕ)-
      w.re*‖r‖^(2 : ℕ)+2*w.im*(inner ℂ r d).im) =
      w.re*(conj w*inner ℂ v (cuspSpatialMultiply N hN F)).re at he' 
    nlinarith only [h1,h2,h3,h4,he',hsq]
  by_cases hz : ‖v‖ = 0
  · change ‖v‖ ≤ _
    rw [hz]
    positivity
  · have hv : 0 < ‖v‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    change ‖v‖ ≤ (w.re*‖w‖/(S*(w.re^(2 : ℕ)-9/4)))*‖cuspSpatialMultiply N hN F‖
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (mul_pos hS hδ)).mpr
    nlinarith only [hc,hv]

end
end RHTower.D4BMJointWave
