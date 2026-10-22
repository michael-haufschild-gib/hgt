import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspCurvatureDefectGrowthCenterModularJets
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspExactCompletedC5SeamFarTail
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspGlobalReflectedRiccati

/-! The literal theta source has positive sixth logarithmic center jet.
Its radial third-curvature numerator is negative near zero and positive
eventually. These source signs obstruct a pointwise projection producer. -/

noncomputable section
open Set Filter Topology
namespace RHTower.ThetaRadial
open ThetaCuspDefect

private theorem center_sixth_numerator_neg {X : ℝ} (hX : 191/10 ≤ X) :
    centerSixthNumerator X < 0 := by
  have h (y : ℝ) (hy : 0 ≤ y) : 0 < -centerSixthNumerator (191/10+y) := by
    unfold centerSixthNumerator centerRawJet
    simp only [centerMassJet, Nat.reduceAdd]
    ring_nf (config := {mode := .raw})
    simp only [Mathlib.Tactic.RingNF.nnrat_rawCast, Mathlib.Tactic.RingNF.nat_rawCast_1,
      Mathlib.Tactic.RingNF.nat_rawCast_2, pow_one]
    positivity
  have hn := h (X-191/10) (sub_nonneg.mpr hX)
  rw [show (191/10:ℝ)+(X-191/10)=X by ring] at hn
  linarith

/-- The actual sixth logarithmic source jet has the opposite sign to the
second and fourth jets at the modular center. -/
theorem log_six_center_pos : 0 < iteratedDeriv 6 thetaCuspLogSource 0 := by
  let m := (thetaCuspModularODEState .H 0).re
  let X := thetaCuspSelfDualModularScale^2
  have hraw :
      -thetaCuspFullSource 0^2*iteratedDeriv 6 thetaCuspFullSource 0+
        15*thetaCuspFullSource 0*iteratedDeriv 2 thetaCuspFullSource 0*
          iteratedDeriv 4 thetaCuspFullSource 0-
        30*(iteratedDeriv 2 thetaCuspFullSource 0)^3 = m^3*centerSixthNumerator X := by
    have h0 := thetaSource_centerRawJet 0 (by omega)
    have h2 := thetaSource_centerRawJet 1 (by omega)
    have h4 := thetaSource_centerRawJet 2 (by omega)
    have h6 := thetaSource_centerRawJet 3 (by omega)
    norm_num only [Nat.reduceMul, iteratedDeriv_zero] at h0 h2 h4 h6
    rw [h0,h2,h4,h6]
    dsimp only [m,X,centerSixthNumerator]
    ring
  have hbell :
      -thetaCuspFullSource 0^2*iteratedDeriv 6 thetaCuspFullSource 0+
        15*thetaCuspFullSource 0*iteratedDeriv 2 thetaCuspFullSource 0*
          iteratedDeriv 4 thetaCuspFullSource 0-
        30*(iteratedDeriv 2 thetaCuspFullSource 0)^3 =
      -thetaCuspFullSource 0^3*iteratedDeriv 6 thetaCuspLogSource 0 := by
    have h1 := iteratedDeriv_thetaCuspLogSource_zero_of_odd (m := 1) ⟨0,rfl⟩
    have h3 := iteratedDeriv_thetaCuspLogSource_zero_of_odd (m := 3) ⟨1,rfl⟩
    have h5 := iteratedDeriv_thetaCuspLogSource_zero_of_odd (m := 5) ⟨2,rfl⟩
    have he : Real.exp (thetaCuspLogSource 0)=thetaCuspFullSource 0 := by
      rw [thetaCuspLogSource, Real.exp_log (thetaCuspFullSource_pos_all 0)]
    rw [iteratedDeriv_two_thetaCuspFullSource_eq_logExponentialJet,
      iteratedDeriv_four_thetaCuspFullSource_eq_logExponentialJet,
      iteratedDeriv_six_thetaCuspFullSource_eq_logExponentialJet]
    unfold thetaCuspLogExponentialJetTwo thetaCuspLogExponentialJetFour
      thetaCuspLogExponentialJetSix thetaCuspLogExponentialJetZero
    rw [he,h1,h3,h5]
    ring
  have hn := mul_neg_of_pos_of_neg (pow_pos (thetaCuspModularODEState_H_re_pos 0) 3)
    (center_sixth_numerator_neg thetaCuspSelfDualModularScale_sq_gt_nineteen_point_one.le)
  change m^3*centerSixthNumerator X < 0 at hn
  rw [← hraw,hbell] at hn
  have hp := pow_pos (thetaCuspFullSource_pos_all 0) 3
  by_contra h
  have hbad := mul_nonneg (neg_nonneg.mpr (le_of_not_gt h)) hp.le
  nlinarith only [hn,hbad]

/-- Numerator of the third derivative of `-log(k(sqrt u)/k(0))`. -/
def radialDefect (x : ℝ) : ℝ :=
  -x^2*iteratedDeriv 3 thetaCuspLogSource x+
    3*x*iteratedDeriv 2 thetaCuspLogSource x-3*iteratedDeriv 1 thetaCuspLogSource x

private def radialAux (x : ℝ) : ℝ :=
  iteratedDeriv 3 thetaCuspLogSource x-x*iteratedDeriv 4 thetaCuspLogSource x

private theorem radialAux_hasDerivAt (x : ℝ) :
    HasDerivAt radialAux (-x*iteratedDeriv 5 thetaCuspLogSource x) x := by
  convert! (hasDerivAt_iteratedDeriv_thetaCuspLogSource 3 x).sub
    ((hasDerivAt_id x).mul (hasDerivAt_iteratedDeriv_thetaCuspLogSource 4 x)) using 1
  simp only [id_eq]
  ring

theorem radialDefect_hasDerivAt (x : ℝ) :
    HasDerivAt radialDefect
      (x*(iteratedDeriv 3 thetaCuspLogSource x-x*iteratedDeriv 4 thetaCuspLogSource x)) x := by
  convert! (((((hasDerivAt_id x).pow 2).mul
    (hasDerivAt_iteratedDeriv_thetaCuspLogSource 3 x)).neg).add
    (((hasDerivAt_id x).mul (hasDerivAt_iteratedDeriv_thetaCuspLogSource 2 x)).const_mul 3)).sub
    ((hasDerivAt_iteratedDeriv_thetaCuspLogSource 1 x).const_mul 3) using 1
  · funext t
    simp only [radialDefect, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Pi.mul_apply, Pi.pow_apply, id_eq]
    ring
  · simp only [Pi.pow_apply, id_eq, Nat.cast_ofNat]
    ring

private theorem radialAux_zero : radialAux 0 = 0 := by
  simp only [radialAux, zero_mul, sub_zero,
    iteratedDeriv_thetaCuspLogSource_zero_of_odd (m := 3) ⟨1,rfl⟩]

theorem radialDefect_zero : radialDefect 0 = 0 := by
  simp only [radialDefect, zero_pow (by norm_num : 2 ≠ 0), zero_mul, neg_zero,
    mul_zero, zero_add, zero_sub,
    iteratedDeriv_thetaCuspLogSource_zero_of_odd (m := 1) ⟨0,rfl⟩]

/-- The actual radial third-curvature numerator is strictly negative on a
punctured right neighborhood of the center. -/
theorem radialDefect_neg_near_center :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ Ioo 0 δ, radialDefect x < 0 := by
  have he : ∀ᶠ x : ℝ in 𝓝 0, 0 < iteratedDeriv 6 thetaCuspLogSource x :=
    (hasDerivAt_iteratedDeriv_thetaCuspLogSource 6 0).continuousAt.eventually
      (isOpen_Ioi.mem_nhds log_six_center_pos)
  obtain ⟨a,b,hab,hb⟩ := mem_nhds_iff_exists_Ioo_subset.mp he
  have h6 {x : ℝ} (hx : x ∈ Ioo 0 b) : 0 < iteratedDeriv 6 thetaCuspLogSource x :=
    hb ⟨lt_trans hab.1 hx.1,hx.2⟩
  have hmono : StrictMonoOn (iteratedDeriv 5 thetaCuspLogSource) (Icc 0 b) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
      (fun x _ => (hasDerivAt_iteratedDeriv_thetaCuspLogSource 5 x).continuousAt.continuousWithinAt)
    intro x hx
    rw [(hasDerivAt_iteratedDeriv_thetaCuspLogSource 5 x).deriv]
    exact h6 (by simpa only [interior_Icc] using hx)
  have h5 {x : ℝ} (hx : x ∈ Ioo 0 b) : 0 < iteratedDeriv 5 thetaCuspLogSource x := by
    have h := hmono ⟨le_refl 0,hab.2.le⟩ ⟨hx.1.le,hx.2.le⟩ hx.1
    simpa only [iteratedDeriv_thetaCuspLogSource_zero_of_odd (m := 5) ⟨2,rfl⟩] using h
  have hanti : StrictAntiOn radialAux (Icc 0 b) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc _ _)
      (fun x _ => (radialAux_hasDerivAt x).continuousAt.continuousWithinAt)
    intro x hx
    have hx' : x ∈ Ioo 0 b := by simpa only [interior_Icc] using hx
    rw [(radialAux_hasDerivAt x).deriv]
    exact mul_neg_of_neg_of_pos (neg_neg_of_pos hx'.1) (h5 hx')
  have hu {x : ℝ} (hx : x ∈ Ioo 0 b) : radialAux x < 0 := by
    have h := hanti ⟨le_refl 0,hab.2.le⟩ ⟨hx.1.le,hx.2.le⟩ hx.1
    simpa only [radialAux_zero] using h
  have ht : StrictAntiOn radialDefect (Icc 0 b) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc _ _)
      (fun x _ => (radialDefect_hasDerivAt x).continuousAt.continuousWithinAt)
    intro x hx
    have hx' : x ∈ Ioo 0 b := by simpa only [interior_Icc] using hx
    rw [(radialDefect_hasDerivAt x).deriv]
    exact mul_neg_of_pos_of_neg hx'.1 (hu hx')
  refine ⟨b,hab.2,fun x hx => ?_⟩
  have h := ht ⟨le_refl 0,hab.2.le⟩ ⟨hx.1.le,hx.2.le⟩ hx.1
  simpa only [radialDefect_zero] using h

/-- The actual far-tail source jets force the opposite radial sign. -/
theorem radialDefect_pos_eventually : ∀ᶠ x : ℝ in atTop, 0 < radialDefect x := by
  let q : ℝ → ℝ := fun x =>
    (-iteratedDeriv 3 thetaCuspLogSource x)/thetaCuspSingleAtomReflectionScale 1 x-
      3*((-iteratedDeriv 2 thetaCuspLogSource x)/thetaCuspSingleAtomReflectionScale 1 x)*x⁻¹
  have hlim : Tendsto q atTop (𝓝 8) := by
    simpa only [mul_zero, sub_zero] using
      thetaCuspC5FarTail_neg_logJetThree_div_scale_tendsto_eight.sub
        ((thetaCuspC5FarTail_neg_logJetTwo_div_scale_tendsto_four.const_mul 3).mul
          tendsto_inv_atTop_zero)
  have he := (tendsto_order.1 hlim).1 0 (by norm_num)
  filter_upwards [he,eventually_ge_atTop (1:ℝ)] with x hx hx1
  have hx0 : 0 < x := by linarith
  have hs : 0 < thetaCuspSingleAtomReflectionScale 1 x := by
    unfold thetaCuspSingleAtomReflectionScale
    positivity
  have h := mul_pos (mul_pos (sq_pos_of_pos hx0) hs) hx
  have heq : x^2*thetaCuspSingleAtomReflectionScale 1 x*q x =
      -x^2*iteratedDeriv 3 thetaCuspLogSource x+3*x*iteratedDeriv 2 thetaCuspLogSource x := by
    dsimp only [q]
    field_simp [hs.ne',hx0.ne']
    ring
  rw [heq] at h
  have hp := thetaCuspLogDecaySlope_nonneg hx0.le
  dsimp only [thetaCuspLogDecaySlope] at hp
  dsimp only [radialDefect]
  linarith only [h,hp]

/-- Negative central and positive far-tail source regions have a genuine
positive radial-curvature zero between them. -/
theorem exists_pos_radialDefect_zero : ∃ x : ℝ, 0 < x ∧ radialDefect x = 0 := by
  obtain ⟨δ,hδ,hn⟩ := radialDefect_neg_near_center
  obtain ⟨a,ha⟩ := eventually_atTop.mp radialDefect_pos_eventually
  let u := δ/2
  let v := max a δ+1
  have hu : u ∈ Ioo 0 δ := by dsimp [u]; constructor <;> linarith
  have hav : a ≤ v := by dsimp [v]; linarith [le_max_left a δ]
  have huv : u ≤ v := by dsimp [u,v]; linarith [le_max_right a δ]
  have hc : ContinuousOn radialDefect (Icc u v) :=
    fun x _ => (radialDefect_hasDerivAt x).continuousAt.continuousWithinAt
  obtain ⟨x,hx,hzero⟩ := intermediate_value_Icc huv hc ⟨(hn u hu).le,(ha v hav).le⟩
  exact ⟨x,lt_of_lt_of_le hu.1 hx.1,hzero⟩

private def fourPointJet (n : ℕ) (x : ℝ) : ℝ :=
  2*iteratedDeriv n thetaCuspLogSource x+
    (2:ℝ)^n*iteratedDeriv n thetaCuspLogSource (2*x)-
    (2*(Real.sqrt 3)^n)*iteratedDeriv n thetaCuspLogSource (Real.sqrt 3*x)-
    (if n=0 then thetaCuspLogSource 0 else 0)

private theorem fourPointJet_hasDerivAt (n : ℕ) (x : ℝ) :
    HasDerivAt (fourPointJet n) (fourPointJet (n+1) x) x := by
  have h1 := hasDerivAt_iteratedDeriv_thetaCuspLogSource n x
  have h2 := (hasDerivAt_iteratedDeriv_thetaCuspLogSource n (2*x)).comp x
    ((hasDerivAt_id x).const_mul 2)
  have h3 := (hasDerivAt_iteratedDeriv_thetaCuspLogSource n (Real.sqrt 3*x)).comp x
    ((hasDerivAt_id x).const_mul (Real.sqrt 3))
  convert! (((h1.const_mul 2).add (h2.const_mul ((2:ℝ)^n))).sub
    (h3.const_mul (2*(Real.sqrt 3)^n))).sub_const
    (if n=0 then thetaCuspLogSource 0 else 0) using 1
  simp only [fourPointJet, if_neg (show n+1 ≠ 0 by omega), sub_zero, pow_succ, mul_one]
  ring

private theorem fourPointJet_zero (n : ℕ) (hn : n < 6) : fourPointJet n 0 = 0 := by
  have h1 := iteratedDeriv_thetaCuspLogSource_zero_of_odd (m := 1) ⟨0,rfl⟩
  have h3 := iteratedDeriv_thetaCuspLogSource_zero_of_odd (m := 3) ⟨1,rfl⟩
  have h5 := iteratedDeriv_thetaCuspLogSource_zero_of_odd (m := 5) ⟨2,rfl⟩
  have hs : Real.sqrt 3^2 = 3 := Real.sq_sqrt (by norm_num)
  have hs4 : Real.sqrt 3^4 = 9 := by
    calc
      Real.sqrt 3^4 = (Real.sqrt 3^2)^2 := by ring
      _ = 9 := by rw [hs]; norm_num
  interval_cases n <;> norm_num [fourPointJet,h1,h3,h5,hs,hs4] <;> ring

private theorem fourPointJet_six_center_pos : 0 < fourPointJet 6 0 := by
  have hs : Real.sqrt 3^6 = 27 := by
    calc
      Real.sqrt 3^6 = (Real.sqrt 3^2)^3 := by ring
      _ = 27 := by rw [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)]; norm_num
  have he : fourPointJet 6 0 = 12*iteratedDeriv 6 thetaCuspLogSource 0 := by
    norm_num [fourPointJet,hs]
    ring
  rw [he]
  exact mul_pos (by norm_num) log_six_center_pos

private theorem fourPointJet_pos_of_next {n : ℕ} (hn : n < 6) {δ : ℝ} (hδ : 0 < δ)
    (hp : ∀ x ∈ Ioo 0 δ, 0 < fourPointJet (n+1) x) :
    ∀ x ∈ Ioo 0 δ, 0 < fourPointJet n x := by
  have hm : StrictMonoOn (fourPointJet n) (Icc 0 δ) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
      (fun x _ => (fourPointJet_hasDerivAt n x).continuousAt.continuousWithinAt)
    intro x hx
    rw [(fourPointJet_hasDerivAt n x).deriv]
    exact hp x (by simpa only [interior_Icc] using hx)
  intro x hx
  have h := hm ⟨le_refl 0,hδ.le⟩ ⟨hx.1.le,hx.2.le⟩ hx.1
  simpa only [fourPointJet_zero n hn] using h

/-- The proposed literal four-point source comparison has strict reverse
orientation at every sufficiently small positive equispaced pair. -/
theorem four_point_reverse_near_center :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ Ioo 0 δ,
      thetaCuspFullSource 0*(thetaCuspFullSource (Real.sqrt 3*x))^2 <
        thetaCuspFullSource x^2*thetaCuspFullSource (2*x) := by
  have he : ∀ᶠ x : ℝ in 𝓝 0, 0 < fourPointJet 6 x :=
    (fourPointJet_hasDerivAt 6 0).continuousAt.eventually
      (isOpen_Ioi.mem_nhds fourPointJet_six_center_pos)
  obtain ⟨a,b,hab,hb⟩ := mem_nhds_iff_exists_Ioo_subset.mp he
  have h6 : ∀ x ∈ Ioo 0 b, 0 < fourPointJet 6 x :=
    fun x hx => hb ⟨lt_trans hab.1 hx.1,hx.2⟩
  have hj : ∀ j : ℕ, j ≤ 6 → ∀ x ∈ Ioo 0 b, 0 < fourPointJet (6-j) x := by
    intro j
    induction j with
    | zero => intro _; simpa only [Nat.sub_zero] using h6
    | succ j ih =>
      intro hj
      have hi := ih (by omega)
      have hidx : 6-(j+1)+1 = 6-j := by omega
      exact fourPointJet_pos_of_next (by omega) hab.2 (by simpa only [hidx] using hi)
  refine ⟨b,hab.2,fun x hx => ?_⟩
  have hd := hj 6 (le_refl 6) x hx
  norm_num only [Nat.sub_self, fourPointJet, pow_zero, mul_one, if_true,
    iteratedDeriv_zero] at hd
  have hlog : Real.log (thetaCuspFullSource 0*(thetaCuspFullSource (Real.sqrt 3*x))^2) <
      Real.log (thetaCuspFullSource x^2*thetaCuspFullSource (2*x)) := by
    rw [Real.log_mul (thetaCuspFullSource_pos_all 0).ne'
      (pow_ne_zero 2 (thetaCuspFullSource_pos_all _).ne'),
      Real.log_mul (pow_ne_zero 2 (thetaCuspFullSource_pos_all x).ne')
        (thetaCuspFullSource_pos_all _).ne', Real.log_pow, Real.log_pow]
    dsimp only [thetaCuspLogSource] at hd
    norm_num only [Nat.cast_ofNat]
    linarith only [hd]
  exact (Real.log_lt_log_iff
    (mul_pos (thetaCuspFullSource_pos_all 0) (sq_pos_of_pos (thetaCuspFullSource_pos_all _)))
    (mul_pos (sq_pos_of_pos (thetaCuspFullSource_pos_all x)) (thetaCuspFullSource_pos_all _))).mp hlog

theorem not_universal_four_point_source_comparison :
    ¬ ∀ t : ℝ, 0 < t → ∀ z : ℝ, 0 < z →
      thetaCuspFullSource t*thetaCuspFullSource (t+z)*thetaCuspFullSource z <
        thetaCuspFullSource 0*(thetaCuspFullSource (Real.sqrt (t^2+t*z+z^2)))^2 := by
  intro h
  obtain ⟨δ,hδ,hrev⟩ := four_point_reverse_near_center
  let x := δ/2
  have hx : x ∈ Ioo 0 δ := by dsimp [x]; constructor <;> linarith
  have hr := hrev x hx
  have hf := h x hx.1 x hx.1
  have hs : Real.sqrt (x^2+x*x+x^2)=Real.sqrt 3*x := by
    have he : (Real.sqrt 3*x)^2=x^2+x*x+x^2 := by
      rw [mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)]
      ring
    have h0 : 0 ≤ x^2+x*x+x^2 := by nlinarith [sq_nonneg x]
    have h1 : 0 ≤ Real.sqrt (x^2+x*x+x^2) := by positivity
    have h2 : 0 ≤ Real.sqrt 3*x := by positivity
    nlinarith [Real.sq_sqrt h0]
  rw [hs,show x+x=2*x by ring] at hf
  nlinarith only [hr,hf]

end RHTower.ThetaRadial
