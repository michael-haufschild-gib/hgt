import GaloisForLFunctions.RHTower.ThetaGaussianCoareaScore
import Mathlib.Analysis.Calculus.LHopital

/-! Quadratic amplitude and score defects for the literal coarea covariance.
Uniform source-time envelopes retain the whole positive mass half-line. -/

noncomputable section
open Set Filter Topology
namespace RHTower.ThetaGaussianCoarea

local notation "p" => thetaCuspLogDecaySlope
local notation "c" => thetaCuspLogCurvature

private theorem p_zero : p 0=0 := by
  simp only [thetaCuspLogDecaySlope,
    iteratedDeriv_thetaCuspLogSource_zero_of_odd (m := 1) ⟨0,rfl⟩,neg_zero]

private theorem c_mono : MonotoneOn c (Ici 0) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ici _)
  · intro t _; exact (hasDerivAt_thetaCuspLogCurvature t).continuousAt.continuousWithinAt
  · intro t _; exact (hasDerivAt_thetaCuspLogCurvature t).differentiableAt.differentiableWithinAt
  · intro t ht
    rw [(hasDerivAt_thetaCuspLogCurvature t).deriv]
    exact (thetaCuspLogCurvatureJet_pos_of_pos
      (by simpa only [interior_Ici,mem_Ioi] using ht)).le

private theorem p_mono : Monotone p := by
  apply monotone_of_deriv_nonneg
  · exact fun t => (hasDerivAt_thetaCuspLogDecaySlope t).differentiableAt
  · intro t
    rw [(hasDerivAt_thetaCuspLogDecaySlope t).deriv]
    exact (thetaCuspLogCurvature_pos t).le

private theorem slope_chord {s r : ℝ} (hs : 0 ≤ s) (hsr : s ≤ r) :
    p r-p s ≤ (r-s)*c r := by
  have hd (z : ℝ) : HasDerivAt (fun w => w*c r-p w) (c r-c z) z := by
    convert! ((hasDerivAt_id z).mul_const (c r)).sub (hasDerivAt_thetaCuspLogDecaySlope z) using 1
    ring
  have hm : MonotoneOn (fun w => w*c r-p w) (Icc s r) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
    · intro z _; exact (hd z).continuousAt.continuousWithinAt
    · intro z _; exact (hd z).differentiableAt.differentiableWithinAt
    · intro z hz
      have hz' : z ∈ Ioo s r := by simpa only [interior_Icc] using hz
      rw [(hd z).deriv]
      exact sub_nonneg.mpr (c_mono (hs.trans hz'.1.le) (hs.trans hsr) hz'.2.le)
  have h := hm (left_mem_Icc.mpr hsr) (right_mem_Icc.mpr hsr) hsr
  linarith only [h]

private theorem slope_upper {s r : ℝ} (hs : 0 ≤ s) (hsr : s ≤ r) : p s ≤ s*c r := by
  have h := slope_chord (le_refl (0:ℝ)) hs
  simp only [p_zero,sub_zero] at h
  exact h.trans (mul_le_mul_of_nonneg_left (c_mono hs (hs.trans hsr) hsr) hs)

private theorem center_shift {t : ℝ} (ht : 0 ≤ t) : shift 0 0 (t^2)=t := by
  convert! shift_coordinate (le_refl (0:ℝ)) (le_refl (0:ℝ)) ht using 1
  simp only [coordinate,add_zero,pow_two]

private theorem center_length {t : ℝ} (ht : 0 ≤ t) : length 0 0 (t^2)=2*t := by
  rw [length_eq,center_shift ht]
  ring

theorem amplitude_hasDerivAt_endpoint (x : ℝ) {u : ℝ} (hu : 0 < u) :
    HasDerivAt (fun z => amplitude z u) (-amplitude x u*leftDerivative x 0 u) x := by
  have he : (fun z => amplitude z u)=
      (fun z => Real.exp (potential 0 0 u-potential z 0 u)) := by
    funext z
    rw [amplitude,potential_comm 0 z u]
  rw [he]
  convert! ((potential_hasDerivAt_left x 0 hu).const_sub (potential 0 0 u)).exp using 1
  simp only [amplitude,potential_comm 0 x u]
  ring

theorem leftDerivative_endpoint_bound {x t : ℝ} (hx : 0 ≤ x) (ht : 0 < t) :
    |leftDerivative x 0 (t^2)| ≤ x*c (t+x) := by
  let s := shift x 0 (t^2)
  let r := x+s
  have hs : 0 < s := shift_pos hx (le_refl (0:ℝ)) (pow_pos ht 2)
  have hr : 0 < r := by dsimp only [r]; linarith
  have hsr : s ≤ r := by dsimp only [r]; linarith
  have hst : s ≤ t := by
    have he := coordinate_shift (sq_nonneg t) (x := x) (y := 0)
    change s*(s+x+0)=t^2 at he
    nlinarith only [he,mul_nonneg hx hs.le,ht,hs]
  have hrT : r ≤ t+x := by dsimp only [r]; linarith
  have hL : length x 0 (t^2)=r+s := by rw [length_eq]; dsimp only [r,s]; ring
  have hLpos : 0 < r+s := add_pos hr hs
  have hpx := thetaCuspLogDecaySlope_nonneg hx
  have hps := thetaCuspLogDecaySlope_nonneg hs.le
  have hpr := p_mono hsr
  have hch := slope_chord hs.le hsr
  have hup := slope_upper hs.le hsr
  have hxp := slope_upper hx (show x ≤ r by dsimp only [r]; linarith)
  have hn0 : 0 ≤ r*p r-s*p s := by
    have h1 := mul_nonneg hr.le (sub_nonneg.mpr hpr)
    have h2 := mul_nonneg (sub_nonneg.mpr hsr) hps
    nlinarith only [h1,h2]
  have hn1 : r*p r-s*p s ≤ x*(r+s)*c r := by
    have h1 := mul_le_mul_of_nonneg_left hch hr.le
    have h2 := mul_le_mul_of_nonneg_left hup (sub_nonneg.mpr hsr)
    have he : r-s=x := by dsimp only [r]; ring
    rw [he] at h1 h2
    nlinarith only [h1,h2]
  have he : leftDerivative x 0 (t^2)=(r*p r-s*p s)/(r+s)-p x := by
    unfold leftDerivative
    rw [hL]
    simp only [zero_add]
    change p r-p x-s*(p r+p s)/(r+s)=(r*p r-s*p s)/(r+s)-p x
    field_simp [hLpos.ne']
    dsimp only [r]
    ring
  have hb : |leftDerivative x 0 (t^2)| ≤ x*c r := by
    rw [he,abs_le]
    constructor
    · have hnn := div_nonneg hn0 hLpos.le
      linarith only [hnn,hxp]
    · have hdiv : (r*p r-s*p s)/(r+s) ≤ x*c r :=
        (div_le_iff₀ hLpos).mpr (by nlinarith only [hn1])
      linarith only [hdiv,hpx]
  exact hb.trans (mul_le_mul_of_nonneg_left (c_mono hr.le (hr.le.trans hrT) hrT) hx)

def quadraticProfile (t : ℝ) : ℝ := (c t+p t/t-2*c 0)/4
def amplitudeDefect (x t : ℝ) : ℝ := (1-amplitude x (t^2))/x^2
def scoreDefect (x t : ℝ) : ℝ := (covarianceScore x (t^2)-1)/x^2

theorem leftDerivative_endpoint_zero {t : ℝ} (ht : 0 < t) : leftDerivative 0 0 (t^2)=0 := by
  simp only [leftDerivative,center_shift ht.le,center_length ht.le,zero_add,p_zero,sub_zero]
  field_simp [ht.ne']
  ring

theorem leftDerivative_hasDerivAt_endpoint_zero {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun x => leftDerivative x 0 (t^2)) (2*quadraticProfile t) 0 := by
  have hs : HasDerivAt (fun x => shift x 0 (t^2)) (-(1/2:ℝ)) 0 := by
    convert! shift_hasDerivAt_left 0 0 (pow_pos ht 2) using 1
    rw [center_shift ht.le,center_length ht.le]
    field_simp [ht.ne']
  have hl : HasDerivAt (fun x => length x 0 (t^2)) 0 0 := by
    simpa only [zero_add,zero_div] using length_hasDerivAt_left 0 0 (pow_pos ht 2)
  have hr := (hasDerivAt_thetaCuspLogDecaySlope (0+shift 0 0 (t^2))).comp 0
    ((hasDerivAt_id (0:ℝ)).add hs)
  have hp := (hasDerivAt_thetaCuspLogDecaySlope (0+shift 0 0 (t^2))).comp 0 (hs.const_add 0)
  convert! (hr.sub (hasDerivAt_thetaCuspLogDecaySlope 0)).sub
    ((hs.mul (hr.add hp)).div hl (length_pos 0 0 (pow_pos ht 2)).ne') using 1
  simp only [quadraticProfile,center_shift ht.le,center_length ht.le,zero_add,
    Pi.add_apply,Pi.mul_apply,Function.comp_apply,id_eq]
  field_simp [ht.ne']
  ring

private theorem quadratic_limit {f g : ℝ → ℝ} {d : ℝ}
    (hf : ∀ x, HasDerivAt f (g x) x) (hg : HasDerivAt g d 0) (hz : g 0=0) :
    Tendsto (fun x => (f x-f 0)/x^2) (𝓝[>] 0) (𝓝 (d/2)) := by
  have hq : Tendsto (fun x => g x/x) (𝓝[>] 0) (𝓝 d) := by
    simpa only [zero_add,hz,sub_zero,smul_eq_mul,inv_mul_eq_div] using hg.tendsto_slope_zero_right
  have hq' : Tendsto (fun x => g x/(2*x)) (𝓝[>] 0) (𝓝 (d/2)) := by
    convert! hq.div_const 2 using 1
    funext x; ring
  apply HasDerivAt.lhopital_zero_nhdsGT
    (Eventually.of_forall fun x => (hf x).sub_const (f 0))
    (Eventually.of_forall fun x => by
      convert! (hasDerivAt_id x).pow 2 using 1; simp only [id_eq]; ring)
    ?_ ?_ ?_ hq'
  · filter_upwards [self_mem_nhdsWithin] with x hx
    exact mul_ne_zero (by norm_num) (ne_of_gt hx)
  · simpa only [sub_self] using ((hf 0).continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds).sub_const (f 0)
  · simpa using (tendsto_id : Tendsto (fun x : ℝ => x) (𝓝[>] 0) (𝓝[>] 0)).mono_right
      nhdsWithin_le_nhds |>.pow 2

theorem amplitudeDefect_limit {t : ℝ} (ht : 0 < t) :
    Tendsto (fun x => amplitudeDefect x t) (𝓝[>] 0) (𝓝 (quadraticProfile t)) := by
  have hf := fun x => amplitude_hasDerivAt_endpoint x (pow_pos ht 2)
  have hg : HasDerivAt (fun x => -amplitude x (t^2)*leftDerivative x 0 (t^2))
      (-2*quadraticProfile t) 0 := by
    convert! (hf 0).neg.mul (leftDerivative_hasDerivAt_endpoint_zero ht) using 1
    simp only [Pi.neg_apply,amplitude,sub_self,Real.exp_zero,leftDerivative_endpoint_zero ht,mul_zero,zero_add]
    ring
  have h := quadratic_limit hf hg (by rw [leftDerivative_endpoint_zero ht,mul_zero])
  have he : amplitude 0 (t^2)=1 := by simp only [amplitude,sub_self,Real.exp_zero]
  have heq : (fun x => amplitudeDefect x t)=(fun x => -((amplitude x (t^2)-amplitude 0 (t^2))/x^2)) := by
    funext x; rw [amplitudeDefect,he]; ring
  rw [heq]
  convert! h.neg using 1
  ring

theorem scoreDefect_limit {t : ℝ} (ht : 0 < t) :
    Tendsto (fun x => scoreDefect x t) (𝓝[>] 0) (𝓝 (quadraticProfile t)) := by
  have hA : Tendsto (fun x => amplitude x (t^2)) (𝓝[>] 0) (𝓝 (1:ℝ)) := by
    simpa only [amplitude,sub_self,Real.exp_zero] using
      ((amplitude_hasDerivAt_endpoint 0 (pow_pos ht 2)).continuousAt.tendsto.mono_left
        nhdsWithin_le_nhds)
  have hL : Tendsto (fun x => leftDerivative x 0 (t^2)/x) (𝓝[>] 0)
      (𝓝 (2*quadraticProfile t)) := by
    simpa only [zero_add,leftDerivative_endpoint_zero ht,sub_zero,smul_eq_mul,inv_mul_eq_div] using
      (leftDerivative_hasDerivAt_endpoint_zero ht).tendsto_slope_zero_right
  have h := (amplitudeDefect_limit ht).neg.add (hA.mul hL)
  have he : (fun x => scoreDefect x t) =ᶠ[𝓝[>] 0]
      (fun x => -amplitudeDefect x t+amplitude x (t^2)*(leftDerivative x 0 (t^2)/x)) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    unfold scoreDefect amplitudeDefect covarianceScore
    field_simp [(show (0:ℝ) < x from hx).ne']
    ring
  apply Filter.Tendsto.congr' he.symm
  convert! h using 1
  ring

theorem amplitudeDefect_bound {x t : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) (ht : 0 < t) :
    |amplitudeDefect x t| ≤ c (t+1) := by
  have hbound (z : ℝ) (hz : z ∈ Icc (0:ℝ) x) :
      ‖-amplitude z (t^2)*leftDerivative z 0 (t^2)‖ ≤ x*c (t+1) := by
    have hA : amplitude z (t^2) ≤ 1 := by
      rcases eq_or_lt_of_le hz.1 with he | hp
      · rw [← he]; simp only [amplitude,sub_self,Real.exp_zero,le_refl]
      · exact amplitude_le_one hp (sq_nonneg t)
    rw [Real.norm_eq_abs,abs_mul,abs_neg,abs_of_pos (amplitude_pos z (t^2))]
    calc
      _ ≤ |leftDerivative z 0 (t^2)| := mul_le_of_le_one_left (abs_nonneg _) hA
      _ ≤ z*c (t+z) := leftDerivative_endpoint_bound hz.1 ht
      _ ≤ x*c (t+1) := mul_le_mul hz.2
        (c_mono (by linarith [hz.1] : 0 ≤ t+z) (by linarith : 0 ≤ t+1) (by linarith [hz.2]))
        (thetaCuspLogCurvature_pos (t+z)).le hx.le
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun z (_ : z ∈ Icc (0:ℝ) x) => (amplitude_hasDerivAt_endpoint z (pow_pos ht 2)).hasDerivWithinAt)
    hbound (convex_Icc 0 x) (left_mem_Icc.mpr hx.le) (right_mem_Icc.mpr hx.le)
  simp only [Real.norm_eq_abs,amplitude,sub_self,Real.exp_zero,sub_zero,abs_of_pos hx] at h
  rw [amplitudeDefect,abs_div,abs_pow,abs_of_pos hx]
  apply (div_le_iff₀ (pow_pos hx 2)).mpr
  rw [abs_sub_comm]
  change |amplitude x (t^2)-1| ≤ c (t+1)*x^2
  convert! h using 1
  ring

theorem scoreDefect_bound {x t : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) (ht : 0 < t) :
    |scoreDefect x t| ≤ 2*c (t+1) := by
  have he : scoreDefect x t=-amplitudeDefect x t+
      amplitude x (t^2)*(leftDerivative x 0 (t^2)/x) := by
    unfold scoreDefect amplitudeDefect covarianceScore
    field_simp [hx.ne']
    ring
  have hL : |leftDerivative x 0 (t^2)/x| ≤ c (t+1) := by
    rw [abs_div,abs_of_pos hx]
    apply (div_le_iff₀ hx).mpr
    calc
      _ ≤ x*c (t+x) := leftDerivative_endpoint_bound hx.le ht
      _ ≤ c (t+1)*x := by
        have hm := c_mono (by linarith : 0 ≤ t+x) (by linarith : 0 ≤ t+1) (by linarith)
        nlinarith only [mul_le_mul_of_nonneg_left hm hx.le]
  rw [he]
  have h := abs_add_le (-amplitudeDefect x t)
    (amplitude x (t^2)*(leftDerivative x 0 (t^2)/x))
  rw [abs_neg,abs_mul,abs_of_pos (amplitude_pos x (t^2))] at h
  have hm := mul_le_of_le_one_left (abs_nonneg (leftDerivative x 0 (t^2)/x))
    (amplitude_le_one hx (sq_nonneg t))
  linarith only [h,hm,hL,amplitudeDefect_bound hx hx1 ht]

theorem quadraticProfile_continuousOn : ContinuousOn quadraticProfile (Ioi 0) := by
  have hp : Continuous p := continuous_iff_continuousAt.mpr
    fun t => (hasDerivAt_thetaCuspLogDecaySlope t).continuousAt
  have hc : Continuous c := continuous_iff_continuousAt.mpr
    fun t => (hasDerivAt_thetaCuspLogCurvature t).continuousAt
  exact ((hc.continuousOn.add (hp.continuousOn.div continuousOn_id
    (fun _ ht => ne_of_gt ht))).sub continuousOn_const).div_const 4

theorem quadraticProfile_strictMono : StrictMonoOn quadraticProfile (Ioi 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioi _) quadraticProfile_continuousOn
  intro t ht
  have ht0 : 0 < t := by simpa only [interior_Ioi,mem_Ioi] using ht
  have hd : HasDerivAt quadraticProfile
      ((thetaCuspLogCurvatureJet t+(t*c t-p t)/t^2)/4) t := by
    convert! ((hasDerivAt_thetaCuspLogCurvature t).add
      ((hasDerivAt_thetaCuspLogDecaySlope t).div (hasDerivAt_id t) ht0.ne')).sub_const
        (2*c 0) |>.div_const 4 using 1
    simp only [id_eq,mul_one]
    ring
  rw [hd.deriv]
  apply div_pos _ (by norm_num)
  exact add_pos_of_pos_of_nonneg (thetaCuspLogCurvatureJet_pos_of_pos ht0)
    (div_nonneg (sub_nonneg.mpr (slope_upper ht0.le le_rfl)) (sq_nonneg t))

theorem eventually_small_positive_nodes : ∀ᶠ x : ℝ in 𝓝[>] 0, 0 < x ∧ x ≤ 1 := by
  have h : Tendsto (fun x : ℝ => x) (𝓝[>] 0) (𝓝 (0:ℝ)) :=
    tendsto_id.mono_right nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin,h.eventually (gt_mem_nhds (show (0:ℝ) < 1 by norm_num))]
    with x hx hx1
  exact ⟨hx,hx1.le⟩

theorem quadraticProfile_bound {t : ℝ} (ht : 0 < t) : |quadraticProfile t| ≤ c (t+1) := by
  apply le_of_tendsto (amplitudeDefect_limit ht).abs
  filter_upwards [eventually_small_positive_nodes] with x hx
  exact amplitudeDefect_bound hx.1 hx.2 ht

end RHTower.ThetaGaussianCoarea
