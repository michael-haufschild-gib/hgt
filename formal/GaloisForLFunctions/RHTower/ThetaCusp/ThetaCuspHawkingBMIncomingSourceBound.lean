import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMIncomingSourceTransport
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMLaplaceHorizonGaussBound

/-! Uniform endpoint control of the actual incoming Green quotient transport. -/
namespace RHTower.D4BMLaplaceRadial
open Complex Filter Topology Set Metric GaloisForLFunctions.HTGeometry D4BMModularCore
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

private theorem transport_denominator_bound {z C : ℝ} {H : ℂ}
    (hz : z ∈ Icc (0:ℝ) (1/2)) (hC : 0 ≤ C)
    (he : ‖H-1‖ ≤ C*z) (hl : 1/2 ≤ ‖H‖) (hu : ‖H‖ ≤ 3/2) :
    let D : ℂ := 2*(Real.sqrt (1-z):ℂ)*H^(2 : ℕ)
    ‖D⁻¹‖ ≤ 4 ∧ ‖D⁻¹-(1/2:ℂ)‖ ≤ (10*C+4)*z := by
  have hz0 := hz.1
  have hz1 := hz.2
  let r := Real.sqrt (1-z)
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hr2 : r^(2 : ℕ)=1-z := Real.sq_sqrt (by linarith)
  have hrl : 1/2 ≤ r := by nlinarith
  have hru : r ≤ 1 := by nlinarith
  have hrz : |r-1| ≤ z := by rw [abs_of_nonpos (by linarith)]; nlinarith
  let D : ℂ := 2*(r:ℂ)*H^(2 : ℕ)
  have hDn : ‖D‖=2*r*‖H‖^(2 : ℕ) := by
    simp only [D,norm_mul,norm_pow,Complex.norm_real,Real.norm_of_nonneg hr0]
    norm_num
  have hDl : 1/4 ≤ ‖D‖ := by
    rw [hDn]
    nlinarith [sq_nonneg (‖H‖-1/2)]
  have hD0 : D ≠ 0 := norm_pos_iff.mp (by linarith)
  have hi : ‖D⁻¹‖ ≤ 4 := by
    rw [norm_inv,inv_eq_one_div]
    exact (div_le_iff₀ (by linarith : 0 < ‖D‖)).mpr (by linarith)
  have hHp : ‖H+1‖ ≤ 5/2 := by
    have ht := norm_add_le H (1:ℂ)
    rw [norm_one] at ht
    linarith
  have hH2 : ‖H^(2 : ℕ)-1‖ ≤ (5/2)*C*z := by
    rw [show H^(2 : ℕ)-1=(H-1)*(H+1) by ring,norm_mul]
    calc
      _ ≤ (C*z)*(5/2) := mul_le_mul he hHp (norm_nonneg _) (by positivity)
      _ = _ := by ring
  have hD2 : ‖D-2‖ ≤ (5*C+2)*z := by
    have hh : D-2=2*(r:ℂ)*(H^(2 : ℕ)-1)+2*((r:ℂ)-1) := by dsimp [D]; ring
    rw [hh]
    calc
      _ ≤ ‖2*(r:ℂ)*(H^(2 : ℕ)-1)‖+‖2*((r:ℂ)-1)‖ := norm_add_le _ _
      _ = 2*r*‖H^(2 : ℕ)-1‖+2*|r-1| := by
        simp only [norm_mul,Complex.norm_real,Real.norm_of_nonneg hr0]
        rw [← Complex.ofReal_one,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
        norm_num
      _ ≤ 2*1*((5/2)*C*z)+2*z := by gcongr
      _ = _ := by ring
  refine ⟨hi,?_⟩
  have heq : D⁻¹-(1/2:ℂ)=(2-D)*D⁻¹/2 := by field_simp [hD0]
  rw [heq,norm_div,norm_mul,norm_sub_rev]
  rw [show ‖(2:ℂ)‖=(2:ℝ) by norm_num]
  calc
    _ ≤ ((5*C+2)*z)*4/2 := by gcongr
    _ = _ := by ring

/-- The actual transport differs from its derived horizon value by one power, uniformly in frequency. -/
theorem incomingSourceTransport_uniform_first_bound (s chi a J K w : ℂ)
    (hw : w.im ≠ 0) (hwr : -2 < w.re) (hs : w-2*s ≠ 0) :
    ∃ R b C : ℝ, 0 < R ∧ 0 < b ∧ b ≤ 1/2 ∧ 0 ≤ C ∧
      ∀ u ∈ ball w R, ∀ z ∈ Ioc (0:ℝ) b,
        ‖incomingSourceTransport s chi a J K u z-
          sourceRemainder s u a J K 1 0*(1/(u-2*s)+onsetCorrection (2*s) u)/(2*(u+1))‖ ≤ C*z := by
  obtain ⟨RG,b,CG,hRG,hb,hbhalf,hCG,hG⟩ := horizonGauss_uniform_nonzero w chi hw
  obtain ⟨RF,CF,hRF,hCF,_,hF⟩ := horizonMellinCore_uniform_first_bound s chi a J K w hw
    (by norm_num : (0:ℝ) < 1/2) (by norm_num : (1/2:ℝ) < 1)
  let A := fun u : ℂ => 1/(u-2*s)+onsetCorrection (2*s) u
  let U := fun u : ℂ => horizonMellinCore s chi a J K u 0/(u+1)
  let MA := ‖A w‖+1
  let MU := ‖U w‖+1
  let β := (w.re-2)/2
  have hβ : -2 < β := by dsimp [β]; linarith
  have hβ2 : 0 < β+2 := by linarith
  have hAc : ContinuousAt A w :=
    ((analyticAt_const.div (analyticAt_id.sub analyticAt_const) hs).add
      ((onsetCorrection_entire (2*s)).analyticAt w)).continuousAt
  have hw1 : w+1 ≠ 0 := by intro h; apply hw; have hi := congrArg Complex.im h; simpa using hi
  have hUc : ContinuousAt U w := by
    have hc := (sourceRemainder_frequency_entire s a J K 1 0).continuous.continuousAt (x := w)
    have he : U = ((fun v => sourceRemainder s v a J K 1 0)/(id+fun _ => (1:ℂ))) := by
      funext v
      simp only [U,horizonMellinCore,Complex.ofReal_zero,gaussFactor_zero,one_mul,
        Pi.div_apply,Pi.add_apply,id_eq]
    rw [he]
    exact hc.div (continuousAt_id.add continuousAt_const) hw1
  have hMA : ∀ᶠ u in 𝓝 w, ‖A u‖ < MA := hAc.norm.eventually_lt continuousAt_const (by dsimp [MA]; linarith)
  have hMU : ∀ᶠ u in 𝓝 w, ‖U u‖ < MU := hUc.norm.eventually_lt continuousAt_const (by dsimp [MU]; linarith)
  have hreal : ∀ᶠ u : ℂ in 𝓝 w, β < u.re :=
    continuousAt_const.eventually_lt Complex.continuous_re.continuousAt (by dsimp [β]; linarith)
  obtain ⟨R,hR,hall⟩ := Metric.eventually_nhds_iff.mp (hMA.and (hMU.and hreal))
  let R0 := min R (min RG RF)
  let C := 4*MA*CF/(β+2)+MU*MA*(10*CG+4)
  have hMA0 : 0 ≤ MA := by dsimp [MA]; positivity
  have hMU0 : 0 ≤ MU := by dsimp [MU]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨R0,b,C,lt_min hR (lt_min hRG hRF),hb,hbhalf,hC,?_⟩
  intro u hu z hz
  have hz0 := hz.1.le
  have huR : u ∈ ball w R := ball_subset_ball (min_le_left _ _) hu
  have huG : u ∈ ball w RG := ball_subset_ball ((min_le_right _ _).trans (min_le_left _ _)) hu
  have huF : u ∈ ball w RF := ball_subset_ball ((min_le_right _ _).trans (min_le_right _ _)) hu
  obtain ⟨hAu,hUu,hru⟩ := hall (mem_ball.mp huR)
  obtain ⟨hGe,hGl,hGu⟩ := hG u huG z ⟨hz.1.le,hz.2⟩
  have hM := normalizedFirstEndpointMellin_uniform_bound hz.1 hCF hβ hru.le
    (horizonMellinCore_measurable s chi a J K u)
    (fun t ht => hF u huF t ⟨ht.1.le,ht.2.trans (hz.2.trans hbhalf)⟩)
  obtain ⟨hDi,hDe⟩ := transport_denominator_bound ⟨hz.1.le,hz.2.trans hbhalf⟩ hCG hGe hGl hGu
  let M := normalizedFirstEndpointMellin (horizonMellinCore s chi a J K) u z
  let D : ℂ := 2*(Real.sqrt (1-z):ℂ)*(gaussFactor u chi false (z:ℂ))^(2 : ℕ)
  have hv : sourceRemainder s u a J K 1 0*A u/(2*(u+1))=U u*A u/2 := by
    simp only [U,horizonMellinCore,Complex.ofReal_zero,gaussFactor_zero,one_mul,div_mul_eq_div_div]
    ring
  rw [incomingSourceTransport_eq_regular s chi a J K u hz.1]
  change ‖M*A u/D-sourceRemainder s u a J K 1 0*A u/(2*(u+1))‖ ≤ C*z
  rw [hv,show M*A u/D-U u*A u/2=(M-U u)*A u*D⁻¹+U u*A u*(D⁻¹-1/2) by ring]
  calc
    _ ≤ ‖(M-U u)*A u*D⁻¹‖+‖U u*A u*(D⁻¹-1/2)‖ := norm_add_le _ _
    _ = ‖M-U u‖*‖A u‖*‖D⁻¹‖+‖U u‖*‖A u‖*‖D⁻¹-1/2‖ := by simp only [norm_mul]
    _ ≤ (CF*z/(β+2))*MA*4+MU*MA*((10*CG+4)*z) := by gcongr
    _ = C*z := by dsimp [C]; ring

/-- Spatial continuity of the actual transport follows from the restored Mellin endpoint derivative. -/
theorem incomingSourceTransport_continuousAt (s chi a J K w : ℂ)
    (hw : w.im ≠ 0) (hwr : -2 < w.re) {z : ℝ} (hz : z ∈ Ioo 0 1)
    (hh : horizon w chi z ≠ 0) :
    ContinuousAt (incomingSourceTransport s chi a J K w) z := by
  obtain ⟨R,C,hR,_,_,hbound⟩ := horizonMellinCore_uniform_first_bound s chi a J K w hw hz.1 hz.2
  have hw1 : w+1 ≠ 0 := by intro h; apply hw; have hi := congrArg Complex.im h; simpa using hi
  have hgc := (gaussFactor_derivatives_continued (w := w) (chi := chi) false
    (enorm_ofReal_lt_one hz.1 hz.2)).1.comp_ofReal.continuousAt
  have hcore : ContinuousAt (horizonMellinCore s chi a J K w) z :=
    hgc.mul (sourceRemainder_continuous s w a J K 1).continuousAt
  have hm := (firstEndpointMellin_hasDerivAt hz.1 hwr hw1
    (horizonMellinCore_measurable s chi a J K w) hcore
    (fun t ht => hbound w (mem_ball_self hR) t ⟨ht.1.le,ht.2⟩)).continuousAt
  have hH := (horizon_derivatives_continued (w := w) (chi := chi) hz).1.continuousAt
  have hs : (Real.sqrt (1-z):ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
    (ne_of_gt (Real.sqrt_pos.mpr (sub_pos.mpr hz.2)))
  have hd : ContinuousAt (fun t : ℝ => 2*(t:ℂ)*(Real.sqrt (1-t):ℂ)*(horizon w chi t)^(2 : ℕ)) z := by
    exact ((continuousAt_const.mul Complex.continuous_ofReal.continuousAt).mul
      (by fun_prop)).mul (hH.pow 2)
  exact (hm.mul_const _).div hd (mul_ne_zero
    (mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr (ne_of_gt hz.1))) hs)
    (pow_ne_zero _ hh))

end
end RHTower.D4BMLaplaceRadial

namespace RHTower.D4BMJointSource
open Complex Set Metric
open D4BMLaplaceRadial D4BMModularCore
noncomputable section
set_option autoImplicit false

/-- Both actual Xi fundamental sources have a uniform linear transport remainder at the original horizon. -/
theorem physical_fundamental_incomingSourceTransport_uniform_bound (q : XiZeroCopy)
    (branch side : Bool) (a : ℂ) :
    let w := physicalFundamentalFrequency q side
    let chi := physicalRadialFrequency q
    let s := physicalRate q branch
    let K := reducedGreenGradient chi s 1
    ∃ R b C : ℝ, 0 < R ∧ 0 < b ∧ b ≤ 1/2 ∧ 0 ≤ C ∧
      ∀ u ∈ ball w R, ∀ z ∈ Ioc (0:ℝ) b,
        ‖incomingSourceTransport s chi a 1 K u z-
          sourceRemainder s u a 1 K 1 0*(1/(u-2*s)+onsetCorrection (2*s) u)/(2*(u+1))‖ ≤ C*z := by
  dsimp only
  exact incomingSourceTransport_uniform_first_bound _ _ _ _ _ _
    (physicalFundamentalFrequency_strip q side).1
    (abs_lt.mp (physicalFundamentalFrequency_strip q side).2).1
    (physicalFundamentalFrequency_sub_sourceRate_ne_zero q branch side)

end
end RHTower.D4BMJointSource
