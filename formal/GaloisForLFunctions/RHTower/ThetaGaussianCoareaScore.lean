import GaloisForLFunctions.RHTower.ThetaTailGaussianSubmodular
import Mathlib.Analysis.Calculus.Deriv.Slope

/-! The actual coarea covariance score has a positive mass-boundary derivative.
Its exact defect is a strictly positive integral of the source curvature jet. -/

noncomputable section
open Set MeasureTheory Filter Topology
namespace RHTower.ThetaGaussianCoarea

local notation "p" => thetaCuspLogDecaySlope
local notation "c" => thetaCuspLogCurvature
local notation "v" => thetaCuspLogCurvatureJet
local notation "a" => thetaCuspLogCurvatureJetTwo

private theorem p_zero : p 0=0 := by
  simp only [thetaCuspLogDecaySlope,
    iteratedDeriv_thetaCuspLogSource_zero_of_odd (m := 1) ⟨0,rfl⟩,neg_zero]
private theorem cont_p : Continuous p := continuous_iff_continuousAt.mpr
  fun t => (hasDerivAt_thetaCuspLogDecaySlope t).continuousAt
private theorem cont_c : Continuous c := continuous_iff_continuousAt.mpr
  fun t => (hasDerivAt_thetaCuspLogCurvature t).continuousAt
private theorem cont_a : Continuous a := continuous_iff_continuousAt.mpr
  fun t => (hasDerivAt_thetaCuspLogCurvatureJetTwo t).continuousAt

/-- Endpoint differentiation of the amplitude divided by its endpoint. -/
def covarianceScore (y u : ℝ) : ℝ := amplitude y u*(1+y*leftDerivative y 0 u)

def leftMassJet (x y u : ℝ) : ℝ :=
  (length x y u*((x+y+shift x y u)*c (x+shift x y u)-
    shift x y u*c (y+shift x y u))-
    (x+y)*(p (x+shift x y u)+p (y+shift x y u)))/length x y u^3

def covarianceScoreMassJet (y u : ℝ) : ℝ :=
  amplitude y u*((massRate 0 0 u-massRate 0 y u)*(1+y*leftDerivative y 0 u)+
    y*leftMassJet y 0 u)

def scoreBoundaryDefect (y : ℝ) : ℝ := c 0+c y-2*p y/y

/-- Exact positive curvature quadrature exposed by the score obstruction. -/
theorem scoreBoundaryDefect_eq_curvatureIntegral {y : ℝ} (hy : 0 < y) :
    scoreBoundaryDefect y=(∫ s in (0:ℝ)..y, s*(y-s)*a s)/y := by
  have hd (s : ℝ) : HasDerivAt
      (fun r => r*(y-r)*v r-(y-2*r)*c r-2*p r) (s*(y-s)*a s) s := by
    convert! ((((hasDerivAt_id s).mul ((hasDerivAt_id s).const_sub y)).mul
      (hasDerivAt_thetaCuspLogCurvatureJet s)).sub
      (((hasDerivAt_id s).const_mul 2).const_sub y |>.mul
        (hasDerivAt_thetaCuspLogCurvature s))).sub
      ((hasDerivAt_thetaCuspLogDecaySlope s).const_mul 2) using 1
    dsimp
    ring
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s (_ : s ∈ uIcc (0:ℝ) y) => hd s)
    ((continuous_id.mul (continuous_const.sub continuous_id) |>.mul cont_a).intervalIntegrable 0 y)
  rw [hi]
  simp only [sub_self,mul_zero,zero_mul,p_zero,sub_zero]
  unfold scoreBoundaryDefect
  field_simp [hy.ne']
  ring

theorem scoreBoundaryDefect_pos {y : ℝ} (hy : 0 < y) : 0 < scoreBoundaryDefect y := by
  rw [scoreBoundaryDefect_eq_curvatureIntegral hy]
  apply div_pos _ hy
  apply intervalIntegral.intervalIntegral_pos_of_pos_on
    ((continuous_id.mul (continuous_const.sub continuous_id) |>.mul cont_a).intervalIntegrable 0 y)
    _ hy
  intro s hs
  exact mul_pos (mul_pos hs.1 (sub_pos.mpr hs.2)) (thetaCuspLogCurvatureJetTwo_pos_all s)

private theorem length_hasDerivAt_mass (x y : ℝ) {u : ℝ} (hu : 0 < u) :
    HasDerivAt (length x y) (2/length x y u) u := by
  have hd := (((hasDerivAt_id u).const_mul 4).const_add ((x+y)^2)).sqrt
    (ne_of_gt (by nlinarith [sq_nonneg (x+y)] : 0 < (x+y)^2+4*u))
  convert! hd using 1
  dsimp only [length,id_eq]
  field_simp [(length_pos x y hu).ne']
  ring

theorem leftDerivative_hasDerivAt_mass (x y : ℝ) {u : ℝ} (hu : 0 < u) :
    HasDerivAt (leftDerivative x y) (leftMassJet x y u) u := by
  have ht := shift_hasDerivAt_mass x y hu
  have hX := (hasDerivAt_thetaCuspLogDecaySlope (x+shift x y u)).comp u (ht.const_add x)
  have hY := (hasDerivAt_thetaCuspLogDecaySlope (y+shift x y u)).comp u (ht.const_add y)
  convert! (hX.sub_const (p x)).sub
    ((ht.mul (hX.add hY)).div (length_hasDerivAt_mass x y hu) (length_pos x y hu).ne') using 1
  dsimp only [leftMassJet,Pi.add_apply,Pi.mul_apply,Function.comp_apply,id_eq]
  field_simp [(length_pos x y hu).ne']
  rw [length_eq x y u]
  ring

theorem covarianceScore_eq_amplitude_sub_deriv (y : ℝ) {u : ℝ} (hu : 0 < u) :
    covarianceScore y u=amplitude y u-y*deriv (fun z => amplitude z u) y := by
  have he : (fun z => amplitude z u)=
      (fun z => Real.exp (potential 0 0 u-potential z 0 u)) := by
    funext z
    rw [amplitude,potential_comm 0 z u]
  have hd := ((potential_hasDerivAt_left y 0 hu).const_sub (potential 0 0 u)).exp
  rw [he,hd.deriv]
  unfold covarianceScore amplitude
  rw [potential_comm 0 y u]
  ring

theorem covarianceScore_hasDerivAt_mass (y : ℝ) {u : ℝ} (hu : 0 < u) :
    HasDerivAt (covarianceScore y) (covarianceScoreMassJet y u) u := by
  have hA := ((potential_hasDerivAt_mass 0 0 hu).sub
    (potential_hasDerivAt_mass 0 y hu)).exp
  convert! hA.mul (((leftDerivative_hasDerivAt_mass y 0 hu).const_mul y).const_add 1) using 1
  dsimp only [covarianceScoreMassJet,amplitude,Pi.sub_apply]
  ring

private theorem length_zero {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) : length x y 0=x+y := by
  simp only [length,mul_zero,add_zero,Real.sqrt_sq (add_nonneg hx hy)]

private theorem length_cont (x y : ℝ) : Continuous (length x y) := by
  unfold length
  fun_prop
private theorem shift_cont (x y : ℝ) : Continuous (shift x y) := by
  unfold shift
  exact (((length_cont x y).sub continuous_const).sub continuous_const).div_const 2

private theorem rate_cont_zero {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hs : x+y ≠ 0) :
    ContinuousAt (massRate x y) 0 := by
  apply ((cont_p.comp (continuous_const.add (shift_cont x y))).add
    (cont_p.comp (continuous_const.add (shift_cont x y)))).continuousAt.div
    (length_cont x y).continuousAt
  simpa only [length_zero hx hy] using hs

private theorem left_cont_zero {y : ℝ} (hy : 0 < y) :
    ContinuousAt (leftDerivative y 0) 0 := by
  have ht := shift_cont y 0
  apply ((cont_p.comp (continuous_const.add ht)).sub continuous_const).continuousAt.sub
    ((ht.mul ((cont_p.comp (continuous_const.add ht)).add
      (cont_p.comp (continuous_const.add ht)))).continuousAt.div (length_cont y 0).continuousAt _)
  simpa only [length_zero hy.le (le_refl (0:ℝ)),add_zero] using hy.ne'

private theorem leftJet_cont_zero {y : ℝ} (hy : 0 < y) :
    ContinuousAt (leftMassJet y 0) 0 := by
  have ht := shift_cont y 0
  apply (((length_cont y 0).mul
    (((continuous_const.add ht).mul (cont_c.comp (continuous_const.add ht))).sub
      (ht.mul (cont_c.comp (continuous_const.add ht))))).sub
    (continuous_const.mul ((cont_p.comp (continuous_const.add ht)).add
      (cont_p.comp (continuous_const.add ht))))).continuousAt.div
    ((length_cont y 0).pow 3).continuousAt
  change length y 0 0^3 ≠ 0
  simpa only [length_zero hy.le (le_refl (0:ℝ)),add_zero] using pow_ne_zero 3 hy.ne'

private theorem centerRate_square {z : ℝ} (hz : 0 < z) : massRate 0 0 (z^2)=p z/z := by
  have hl : length 0 0 (z^2)=2*z := by
    unfold length
    rw [show ((0:ℝ)+0)^2+4*z^2=(2*z)^2 by ring,Real.sqrt_sq (by positivity : 0 ≤ 2*z)]
  have hs : shift 0 0 (z^2)=z := by rw [shift,hl]; ring
  simp only [massRate,hs,hl,zero_add]
  field_simp [hz.ne']
  ring

/-- The derivative score is positive at arbitrarily small positive coarea masses. -/
theorem covarianceScoreMassJet_boundary_limit {y : ℝ} (hy : 0 < y) :
    Tendsto (fun z => covarianceScoreMassJet y (z^2)) (𝓝[>] 0) (𝓝 (scoreBoundaryDefect y)) := by
  have hz : Tendsto (fun z : ℝ => z^2) (𝓝[>] 0) (𝓝 (0:ℝ)) := by
    have h : Tendsto (fun z : ℝ => z^2) (𝓝 (0:ℝ)) (𝓝 ((0:ℝ)^2)) :=
      (show Continuous (fun z : ℝ => z^2) by fun_prop).tendsto 0
    simpa only [zero_pow (by norm_num : 2 ≠ 0)] using h.mono_left nhdsWithin_le_nhds
  have hA := (amplitude_continuous y).continuousAt.tendsto.comp hz
  have hM := (rate_cont_zero (le_refl (0:ℝ)) hy.le (by simpa using hy.ne')).tendsto.comp hz
  have hL := (left_cont_zero hy).tendsto.comp hz
  have hJ := (leftJet_cont_zero hy).tendsto.comp hz
  have h0 : Tendsto (fun z => massRate 0 0 (z^2)) (𝓝[>] 0) (𝓝 (c 0)) := by
    have hp := (hasDerivAt_thetaCuspLogDecaySlope 0).tendsto_slope_zero_right
    have he : (fun z => massRate 0 0 (z^2)) =ᶠ[𝓝[>] 0] (fun z => p z/z) := by
      filter_upwards [self_mem_nhdsWithin] with z hz
      exact centerRate_square hz
    apply Filter.Tendsto.congr' he.symm
    simpa only [zero_add,p_zero,sub_zero,smul_eq_mul,inv_mul_eq_div] using hp
  have h := hA.mul (((h0.sub hM).mul ((tendsto_const_nhds (x := (1:ℝ))).add
    ((tendsto_const_nhds (x := y)).mul hL))).add
    ((tendsto_const_nhds (x := y)).mul hJ))
  convert! h using 1
  simp only [amplitude_zero hy.le,massRate,leftDerivative,leftMassJet,
    shift_zero (le_refl (0:ℝ)) hy.le,shift_zero hy.le (le_refl (0:ℝ)),
    length_zero (le_refl (0:ℝ)) hy.le,length_zero hy.le (le_refl (0:ℝ)),
    zero_add,add_zero,p_zero,mul_zero,zero_mul,zero_div,sub_self,sub_zero,one_mul]
  unfold scoreBoundaryDefect
  field_simp [hy.ne']
  ring

theorem covarianceScoreMassJet_eventually_pos {y : ℝ} (hy : 0 < y) :
    ∀ᶠ z : ℝ in 𝓝[>] 0, 0 < covarianceScoreMassJet y (z^2) :=
  (covarianceScoreMassJet_boundary_limit hy).eventually (lt_mem_nhds (scoreBoundaryDefect_pos hy))

/-- Decreasing-amplitude covariance cannot be applied separately after endpoint differentiation. -/
theorem covarianceScore_not_antitone {y : ℝ} (hy : 0 < y) :
    ¬AntitoneOn (covarianceScore y) (Ioi 0) := by
  intro hanti
  have hpos : ∀ᶠ z : ℝ in 𝓝[>] 0, 0 < z := self_mem_nhdsWithin
  obtain ⟨z,hz,hjet⟩ := (hpos.and (covarianceScoreMassJet_eventually_pos hy)).exists
  have hz2 : 0 < z^2 := pow_pos hz 2
  have hn := hanti.derivWithin_nonpos (x := z^2)
  rw [derivWithin_of_isOpen isOpen_Ioi hz2,(covarianceScore_hasDerivAt_mass y hz2).deriv] at hn
  exact (not_lt_of_ge hn) hjet

/-- The actual two-mass covariance kernel has strictly adverse values. -/
theorem exists_negative_covarianceScore_pair {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    ∃ u w : ℝ, 0 < u ∧ u < w ∧
      (amplitude x w-amplitude x u)*(covarianceScore y w-covarianceScore y u) < 0 := by
  have h := covarianceScore_not_antitone hy
  unfold AntitoneOn at h
  push Not at h
  obtain ⟨u,hu,w,hv,huv,hs⟩ := h
  change 0 < u at hu
  change 0 < w at hv
  have huv' : u < w := lt_of_le_of_ne huv (by intro he; subst w; exact hs.ne rfl)
  exact ⟨u,w,hu,huv',mul_neg_of_neg_of_pos
    (sub_neg.mpr (amplitude_strictAnti hx (show u ∈ Ici 0 from hu.le)
      (show w ∈ Ici 0 from hv.le) huv'))
    (sub_pos.mpr hs)⟩

end RHTower.ThetaGaussianCoarea
