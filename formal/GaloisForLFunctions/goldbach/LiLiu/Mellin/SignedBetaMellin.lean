import GaloisForLFunctions.goldbach.LiLiu.Mellin.ProfileBeta
import GaloisForLFunctions.goldbach.LiLiu.Mellin.BetaFactorization
import GaloisForLFunctions.goldbach.LiLiu.Mellin.SignedMellin
import GaloisForLFunctions.goldbach.LiLiu.Mellin.VerticalLine

/-! # The signed Beta–Mellin identity on the product contour -/

namespace GaloisForLFunctions.Goldbach.LiLiu
open _root_.Complex MeasureTheory Set Filter Asymptotics
open scoped Topology
noncomputable section

private theorem oriented_convergent (φ : TestWeight) {d : ℝ} (hd : d^2=1) {w : ℂ} (hw : 0 < w.re) :
    MellinConvergent (orientedProfile φ d) w := by
  have hcont := (sumProfile_smooth φ).continuous
  have hc : Continuous (orientedProfile φ d) := by
    rcases sq_eq_one_iff.mp hd with rfl | rfl
    · rw [show orientedProfile φ 1 = _ from funext (orientedProfile_add φ)]
      exact continuous_ofReal.comp hcont
    · rw [show orientedProfile φ (-1) = _ from funext (orientedProfile_sub φ)]
      exact continuous_ofReal.comp (hcont.comp (continuous_const.sub continuous_id))
  have hzero : orientedProfile φ d =ᶠ[atTop] fun _ => 0 := by
    filter_upwards [eventually_gt_atTop (2:ℝ)] with y hy
    rcases sq_eq_one_iff.mp hd with rfl | rfl
    · rw [orientedProfile_add,sumProfile_zero φ (fun h => by linarith only [h.2,hy]),Complex.ofReal_zero]
    · rw [orientedProfile_sub,sumProfile_zero φ (fun h => by linarith only [h.1,hy]),Complex.ofReal_zero]
  apply mellinConvergent_of_isBigO_rpow (a := w.re+1) (b := 0)
    (hc.continuousOn.locallyIntegrableOn measurableSet_Ioi)
    (hzero.isBigO.trans (isBigO_zero _ _)) (by linarith only) _ hw
  simpa only [neg_zero, Real.rpow_zero] using
    (hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).isBigO_one ℝ

private theorem profileMellin_orientations (φ : TestWeight) {w : ℂ} (hw : 0 < w.re) :
    profileMellin φ w = 2*mellin (orientedProfile φ (-1)) w - mellin (orientedProfile φ 1) w := by
  have h₁ := oriented_convergent φ (d := -1) (by norm_num) hw
  have h₂ := oriented_convergent φ (d := 1) (by norm_num) hw
  simp only [MellinConvergent,smul_eq_mul] at h₁ h₂
  have he (x : ℝ) : (x:ℂ)^(w-1) * (signedProfile φ x : ℂ) =
      2*((x:ℂ)^(w-1) * orientedProfile φ (-1) x) - ((x:ℂ)^(w-1) * orientedProfile φ 1 x) := by
    simp only [orientedProfile_add,orientedProfile_sub,signedProfile,ofReal_sub,ofReal_mul,ofReal_ofNat]
    ring
  simp only [profileMellin,mellin,smul_eq_mul,he, integral_sub (h₁.const_mul 2) h₂, integral_const_mul]

/-- Formula (7.8). Reflection of the first difference integral about Im(w)/2
produces the Beta term in the other Mellin variable. -/
theorem signedBeta_mellin_identity (φ : TestWeight) {σ : ℝ} (hσ : 0 < σ) (hσ' : σ < 1/2)
    {w : ℂ} (hw : w.re = 2*σ) :
    profileMellin φ w = (1/(2*Real.pi) : ℂ) * ∫ t : ℝ,
      mellin (companion φ) (mellinLine σ t) * mellin (companion φ) (w-mellinLine σ t) *
        signedBeta (mellinLine σ t) (w-mellinLine σ t) := by
  let s := mellinLine σ
  let M := mellin (companion φ)
  let F (d t : ℝ) := M (w-s t) * shapeBeta d w (s t) * M (s t)
  have hw0 : 0 < w.re := by linarith only [hw,hσ]
  have htop : w.re < 1/2+σ := by linarith only [hw,hσ']
  have H (d : ℝ) (hd : d^2=1) : Integrable (F d) ∧
      mellin (orientedProfile φ d) w = (1/(2*Real.pi):ℂ) * ∫ t, F d t :=
    orientedProfile_mellin_beta φ hd hσ' hw0 htop
  obtain ⟨hC,eC⟩ := H (-1) (by norm_num)
  obtain ⟨hJ,eJ⟩ := H 1 (by norm_num)
  have he (t : ℝ) : F (-1) t + F (-1) (w.im-t) - F 1 t =
      M (s t)*M (w-s t)*signedBeta (s t) (w-s t) := by
    have hR : s (w.im-t) = w-s t := mellinLine_reflect hw t
    simp only [F,hR,sub_sub_cancel,signedBeta,shapeBeta,eq_self,ite_true,if_neg (by norm_num : (-1:ℝ) ≠ 1),
      show s t+(w-s t)=w by ring, show 1/2+s t-w = 1/2-(w-s t) by ring]
    ring
  change profileMellin φ w = _ * ∫ t, M (s t)*M (w-s t)*signedBeta (s t) (w-s t)
  simp_rw [← he]
  have hboth : Integrable (fun t => F (-1) t + F (-1) (w.im-t)) := hC.add (hC.comp_sub_left w.im)
  rw [integral_sub hboth hJ,integral_add hC (hC.comp_sub_left w.im),
    integral_sub_left_eq_self,profileMellin_orientations φ hw0,eC,eJ]
  ring

#print axioms signedBeta_mellin_identity
end
end GaloisForLFunctions.Goldbach.LiLiu
