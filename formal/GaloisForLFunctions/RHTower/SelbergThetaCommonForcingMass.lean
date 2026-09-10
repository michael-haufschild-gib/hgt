import GaloisForLFunctions.RHTower.SelbergThetaCommonForcingGram

/-!
# Retained native mass of the centered common-forcing source

The literal positive theta periodization has a reciprocal-height cusp bound.
Every nonidentity row is retained: its cubic seed bound gains one reciprocal
height against the bounded complete quadratic row sum. Positivity and cusp
regions of positive native measure rule out an almost-everywhere constant.

The centered forcing is therefore nonzero. The existing native graph equation
then proves nonvanishing of every centered common-forcing response and permits
unit normalization in that same domain. The normalized equation retains its
full arithmetic forcing; no vanishing residual or RH assertion is made.
-/

open Complex Set Filter Topology MeasureTheory UpperHalfPlane ModularGroup
open GaloisForLFunctions.HTGeometry
set_option autoImplicit false
namespace RHTower.SelbergThetaCommonForcingMass
open D4BMModularCore D4BMGlobalAngularResponse SelbergThetaNativeSource
open SelbergThetaCommonForcing SelbergThetaCommonForcingGram SelbergNativeConstantMode
noncomputable section

private theorem profile_pos (y : ℝ) : 0 < positiveProfile y :=
  mul_pos (Real.exp_pos _) (thetaCuspFullSource_pos_all _)

/-- The complete positive forcing decays at the cusp, with every primitive row retained. -/
theorem positiveSource_cusp_bound : ∃ C : ℝ, 0 < C ∧ ∀ z : UpperHalfPlane,
    1/2 ≤ z.im → positiveSource z ≤ C / z.im := by
  classical
  obtain ⟨A,hA,ha⟩ := positiveProfile_power_bound (-1)
  obtain ⟨B,hB,hb⟩ := positiveProfile_power_bound 3
  obtain ⟨D,hD,hd⟩ := SelbergResummedSource.nonparabolic_quadratic_bound
  refine ⟨A+B*D,by positivity,fun z hz => ?_⟩
  have hquad : Summable (fun v : gammaSetHalf => (gammaSetMatrix v.1 • z).im^2) := by
    simpa only [Real.rpow_two] using positiveCuspRows_summable 2 (by norm_num) z
  have hs : Summable (fun v : gammaSetHalf => positiveProfile (gammaSetMatrix v.1 • z).im) := by
    obtain ⟨E,hE,he⟩ := positiveProfile_power_bound 2
    apply (hquad.mul_left E).of_nonneg_of_le (fun v => (profile_pos _).le)
    intro v
    simpa only [Real.rpow_two] using he _ (gammaSetMatrix v.1 • z).im_pos
  have hn : Summable (fun v : gammaSetHalf => if v=cuspIdentityRow then (0:ℝ)
      else positiveProfile (gammaSetMatrix v.1 • z).im) :=
    hs.of_nonneg_of_le (fun v => by split_ifs <;> first | exact le_rfl | exact (profile_pos _).le)
      (fun v => by split_ifs <;> first | exact le_rfl | exact (profile_pos _).le)
  have hq : Summable (fun v : gammaSetHalf => if v=cuspIdentityRow then (0:ℝ)
      else (gammaSetMatrix v.1 • z).im^2) :=
    hquad.of_nonneg_of_le (fun v => by split_ifs <;> positivity)
      (fun v => by split_ifs <;> first | exact le_rfl | positivity)
  have hle := hn.tsum_le_tsum (fun v => show
      (if v=cuspIdentityRow then (0:ℝ) else positiveProfile (gammaSetMatrix v.1 • z).im) ≤
      (B/z.im)*(if v=cuspIdentityRow then 0 else (gammaSetMatrix v.1 • z).im^2) from by
    split_ifs with hv
    · simp
    · have hp := hb _ (gammaSetMatrix v.1 • z).im_pos
      have hr := cuspRow_nonparabolic_height_le v hv z
      rw [show (3:ℝ) = (3:ℕ) from rfl, Real.rpow_natCast] at hp
      calc
        _ ≤ B*(gammaSetMatrix v.1 • z).im^3 := hp
        _ ≤ (B/z.im)*(gammaSetMatrix v.1 • z).im^2 := by
          have hm := mul_le_mul_of_nonneg_left hr
            (show 0 ≤ B*(gammaSetMatrix v.1 • z).im^2 by positivity)
          calc
            _ = (B*(gammaSetMatrix v.1 • z).im^2)*(gammaSetMatrix v.1 • z).im := by ring
            _ ≤ (B*(gammaSetMatrix v.1 • z).im^2)*(1/z.im) := hm
            _ = _ := by ring) (hq.mul_left (B/z.im))
  rw [tsum_mul_left] at hle
  have hs' := hs.tsum_eq_add_tsum_ite cuspIdentityRow
  have hq' := hquad.tsum_eq_add_tsum_ite cuspIdentityRow
  rw [cuspIdentityRow_height] at hs' hq'
  change positiveSource z = _ at hs'
  have heq : (∑' v : gammaSetHalf, (gammaSetMatrix v.1 • z).im^2) = positiveCuspRows 2 z := by
    simp only [positiveCuspRows, Real.rpow_two]
  rw [heq] at hq'
  have hr : (∑' v : gammaSetHalf, if v=cuspIdentityRow then (0:ℝ)
      else (gammaSetMatrix v.1 • z).im^2) ≤ D := by linarith [hd z hz]
  have hi : positiveProfile z.im ≤ A/z.im := by
    simpa only [Real.rpow_neg_one, div_eq_mul_inv] using ha z.im z.im_pos
  have hrest := hle.trans (mul_le_mul_of_nonneg_left hr (by positivity : 0 ≤ B/z.im))
  rw [hs']
  calc
    _ ≤ A/z.im+(B/z.im)*D := add_le_add hi hrest
    _ = (A+B*D)/z.im := by ring

private theorem exists_high_of_ae (Y : ℝ) {p : UpperHalfPlane → Prop}
    (hp : ∀ᵐ z ∂angularMeasure, p z) :
    ∃ z : UpperHalfPlane, 2 < z.im ∧ Y < z.im ∧ p z := by
  let U : Set UpperHalfPlane := {z | 2 < z.im ∧ Y < z.im ∧ |z.re| < 1/2}
  have hU : IsOpen U :=
    (isOpen_lt continuous_const UpperHalfPlane.continuous_im).inter
      ((isOpen_lt continuous_const UpperHalfPlane.continuous_im).inter
        (isOpen_lt UpperHalfPlane.continuous_re.abs continuous_const))
  have hne : U.Nonempty := by
    let z : UpperHalfPlane := ⟨⟨0,max Y 2+1⟩,by linarith [le_max_right Y 2]⟩
    refine ⟨z,?_⟩
    change 2 < max Y 2+1 ∧ Y < max Y 2+1 ∧ |(0:ℝ)| < 1/2
    constructor
    · linarith [le_max_right Y 2]
    constructor
    · linarith [le_max_left Y 2]
    · norm_num
  have hsub : U ⊆ fd := by
    intro z hz
    refine ⟨?_,hz.2.2.le⟩
    change 1 ≤ z.re*z.re+z.im*z.im
    nlinarith [hz.1,sq_nonneg z.re]
  have ha : ∀ᵐ z ∂volume.restrict U, p z :=
    ae_restrict_of_ae_restrict_of_subset hsub hp
  obtain ⟨z,hz,hp⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    (hU.measure_pos volume hne).ne' ha
  exact ⟨z,hz.1,hz.2.1,hp⟩

/-- The complete positive forcing has a genuine nonconstant native component. -/
theorem positiveSource_not_ae_constant (c : ℂ) :
    ¬ ((fun z => (positiveSource z:ℂ)) =ᵐ[angularMeasure] (fun _ => c)) := by
  intro he
  obtain ⟨z,_,_,hz⟩ := exists_high_of_ae 0 he
  have hc : 0 < c.re := by
    have hr := congrArg Complex.re hz
    simp only [Complex.ofReal_re] at hr
    rw [← hr]
    exact positiveSource_pos z
  obtain ⟨C,hC,hb⟩ := positiveSource_cusp_bound
  obtain ⟨w,hw,hy,heq⟩ := exists_high_of_ae (C/c.re) he
  have hr := congrArg Complex.re heq
  simp only [Complex.ofReal_re] at hr
  have ht : C/w.im < c.re := by
    apply (div_lt_iff₀ w.im_pos).mpr
    have h := (div_lt_iff₀ hc).mp hy
    nlinarith
  have h := hb w (by linarith)
  rw [hr] at h
  exact (not_lt_of_ge h) ht

/-- Orthogonal centering preserves a nonzero part of the literal full theta forcing. -/
theorem centered_nativePositive_ne_zero : centered nativePositive ≠ 0 := by
  intro hz
  have he : nativePositive = constantComponent nativePositive := sub_eq_zero.mp hz
  let c : ℂ := inner ℂ constantVector nativePositive / inner ℂ constantVector constantVector
  apply positiveSource_not_ae_constant c
  have hP : (nativePositive : UpperHalfPlane → ℂ) =ᵐ[angularMeasure]
      (fun z => (positiveSource z:ℂ)) := positiveSource_memLp.ofReal.coeFn_toLp
  filter_upwards [hP,constantVector_coe,Lp.coeFn_smul c constantVector] with z hP h1 hs
  change nativePositive z = (positiveSource z:ℂ) at hP
  have hv : nativePositive = c • constantVector := he
  rw [hv] at hP
  simp only [Pi.smul_apply,smul_eq_mul] at hs
  rw [hs,h1,mul_one] at hP
  exact hP.symm

/-- The shared forcing in the original centered graph is nonzero. -/
theorem forcing_ne_zero : SelbergThetaCommonForcingGram.forcing ≠ 0 := by
  apply smul_ne_zero
  · norm_num
  · exact centered_nativePositive_ne_zero

/-- Every actual common-forcing response retains native mass after centering. -/
theorem vector_ne_zero (q : XiZeroCopy) : vector q ≠ 0 := by
  intro hz
  have hd : centeredDomain q = 0 := Subtype.ext hz
  have hi : SelbergThetaCommonForcingGram.image q = 0 := by
    unfold SelbergThetaCommonForcingGram.image
    rw [hd]
    exact energyOperator.map_zero
  have he := image_eq q
  rw [hz,smul_zero,zero_add,hi] at he
  exact forcing_ne_zero he.symm

theorem vector_norm_pos (q : XiZeroCopy) : 0 < ‖vector q‖ :=
  norm_pos_iff.mpr (vector_ne_zero q)

/-- Actual unit normalization stays in the original closed native operator domain. -/
def unitDomain (q : XiZeroCopy) : energyOperator.domain :=
  ((‖vector q‖⁻¹:ℝ):ℂ) • centeredDomain q

theorem unitDomain_norm (q : XiZeroCopy) : ‖(unitDomain q : Space)‖ = 1 := by
  change ‖((‖vector q‖⁻¹:ℝ):ℂ) • vector q‖ = 1
  rw [norm_smul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr (vector_norm_pos q))]
  exact inv_mul_cancel₀ (vector_norm_pos q).ne'

/-- The unit vector retains the exact full forcing term in the native graph. -/
theorem unitDomain_equation (q : XiZeroCopy) :
    energyOperator (unitDomain q)-energy q • (unitDomain q : Space) =
      ((‖vector q‖⁻¹:ℝ):ℂ) • SelbergThetaCommonForcingGram.forcing := by
  have h := congrArg (fun v : Space => ((‖vector q‖⁻¹:ℝ):ℂ) • v)
    (centeredDomain_equation q)
  change ((‖vector q‖⁻¹:ℝ):ℂ) •
    (energyOperator (centeredDomain q)-energy q • vector q) =
      ((‖vector q‖⁻¹:ℝ):ℂ) • SelbergThetaCommonForcingGram.forcing at h
  unfold unitDomain
  rw [energyOperator.map_smul]
  change ((‖vector q‖⁻¹:ℝ):ℂ) • energyOperator (centeredDomain q)-
    energy q • (((‖vector q‖⁻¹:ℝ):ℂ) • vector q) = _
  rw [smul_comm (energy q) ((‖vector q‖⁻¹:ℝ):ℂ) (vector q)]
  exact (smul_sub _ _ _).symm.trans h

end
end RHTower.SelbergThetaCommonForcingMass

