import GaloisForLFunctions.RHTower.ThetaTwoNodePortBoundaryClassification
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Topology.Order.MonotoneConvergence

/-! Exact signed scalar energy for the actual two-node theta source span. -/

noncomputable section
open MeasureTheory Filter Topology Set

namespace RHTower.ThetaSturm

def secant (x z t : ℝ) : ℝ :=
  (thetaCuspLogDecaySlope (z+t)-thetaCuspLogDecaySlope (x+t))/(z-x)

def intercept (x z t : ℝ) : ℝ :=
  ((x+t)*thetaCuspLogDecaySlope (z+t)-(z+t)*thetaCuspLogDecaySlope (x+t))/(z-x)

def secantJet (x z t : ℝ) : ℝ :=
  (-iteratedDeriv 2 thetaCuspLogSource (z+t)+iteratedDeriv 2 thetaCuspLogSource (x+t))/(z-x)

def reciprocal (x z t : ℝ) : ℝ := 1/secant x z t

def reciprocalJet (x z t : ℝ) : ℝ := -secantJet x z t/(secant x z t)^2

def density (x z t : ℝ) : ℝ := 2*(intercept x z t/secant x z t)+reciprocalJet x z t

def packet (x z a b t : ℝ) : ℝ := a*thetaCuspFullSource (x+t)+b*thetaCuspFullSource (z+t)

def coordinatePacket (x z a b t : ℝ) : ℝ :=
  a*(x+t)*thetaCuspFullSource (x+t)+b*(z+t)*thetaCuspFullSource (z+t)

def energy (x z a b : ℝ) : ℝ :=
  a^2*thetaTailFirstMomentKernel x x + 2*a*b*thetaTailFirstMomentKernel x z +
    b^2*thetaTailFirstMomentKernel z z

private theorem slope_hasDerivAt (x : ℝ) :
    HasDerivAt thetaCuspLogDecaySlope (-iteratedDeriv 2 thetaCuspLogSource x) x :=
  (hasDerivAt_iteratedDeriv_thetaCuspLogSource 1 x).neg

private theorem slope_continuous : Continuous thetaCuspLogDecaySlope :=
  continuous_iff_continuousAt.mpr fun x => (slope_hasDerivAt x).continuousAt

theorem secant_pos {x z : ℝ} (hxz : x < z) (t : ℝ) : 0 < secant x z t := by
  have h := ThetaPortBoundary.slopeSecant_pos (show x+t < z+t by linarith)
  simpa only [secant, ThetaPortBoundary.slopeSecant, add_sub_add_right_eq_sub] using h

theorem secant_hasDerivAt (x z t : ℝ) :
    HasDerivAt (secant x z) (secantJet x z t) t := by
  have hz := (slope_hasDerivAt (z+t)).comp t ((hasDerivAt_id t).const_add z)
  have hx := (slope_hasDerivAt (x+t)).comp t ((hasDerivAt_id t).const_add x)
  convert! (hz.sub hx).div_const (z-x) using 1
  simp only [secantJet, mul_one]
  ring

theorem secantJet_pos {x z : ℝ} (hx : 0 ≤ x) (hxz : x < z) {t : ℝ} (ht : 0 ≤ t) :
    0 < secantJet x z t := by
  have hm := ThetaPort.strictConvexOn_slope.strictMonoOn_deriv
    (fun y _ => (slope_hasDerivAt y).differentiableAt)
  have h := hm (show x+t ∈ Ici 0 by change 0 ≤ x+t; linarith)
    (show z+t ∈ Ici 0 by change 0 ≤ z+t; linarith) (show x+t < z+t by linarith)
  rw [(slope_hasDerivAt (x+t)).deriv, (slope_hasDerivAt (z+t)).deriv] at h
  exact div_pos (by linarith) (sub_pos.mpr hxz)

theorem reciprocal_hasDerivAt {x z : ℝ} (hxz : x < z) (t : ℝ) :
    HasDerivAt (reciprocal x z) (reciprocalJet x z t) t := by
  convert! (secant_hasDerivAt x z t).inv (secant_pos hxz t).ne' using 1
  funext u
  simp only [reciprocal, Pi.inv_apply, one_div]

theorem reciprocalJet_neg {x z : ℝ} (hx : 0 ≤ x) (hxz : x < z)
    {t : ℝ} (ht : 0 ≤ t) : reciprocalJet x z t < 0 :=
  div_neg_of_neg_of_pos (neg_neg_of_pos (secantJet_pos hx hxz ht))
    (sq_pos_of_pos (secant_pos hxz t))

theorem reciprocal_antitoneOn {x z : ℝ} (hx : 0 ≤ x) (hxz : x < z) :
    AntitoneOn (reciprocal x z) (Ici 0) := by
  apply (strictAntiOn_of_deriv_neg (convex_Ici 0)
    (fun t _ => (reciprocal_hasDerivAt hxz t).continuousAt.continuousWithinAt) ?_).antitoneOn
  intro t ht
  rw [(reciprocal_hasDerivAt hxz t).deriv]
  have ht' : 0 < t := by simpa only [interior_Ici, mem_Ioi] using ht
  exact reciprocalJet_neg hx hxz ht'.le

theorem reciprocal_limit_exists {x z : ℝ} (hx : 0 ≤ x) (hxz : x < z) :
    ∃ l : ℝ, Tendsto (reciprocal x z) atTop (𝓝 l) := by
  let g : ℝ → ℝ := fun t => reciprocal x z (max 0 t)
  have ha : Antitone g := by
    intro a b hab
    exact reciprocal_antitoneOn hx hxz (show max 0 a ∈ Ici 0 from le_max_left 0 a)
      (show max 0 b ∈ Ici 0 from le_max_left 0 b) (max_le_max (le_refl 0) hab)
  have hb : BddBelow (range g) := ⟨0, by
    rintro _ ⟨t,rfl⟩
    exact (one_div_pos.mpr (secant_pos hxz (max 0 t))).le⟩
  refine ⟨_, (tendsto_atTop_ciInf ha hb).congr' ?_⟩
  filter_upwards [eventually_ge_atTop (0:ℝ)] with t ht
  simp only [g, max_eq_right ht]

/-- The decreasing reciprocal secant has integrable derivative on the actual half-line. -/
theorem reciprocalJet_integrable {x z : ℝ} (hx : 0 ≤ x) (hxz : x < z) :
    IntegrableOn (reciprocalJet x z) (Ioi 0) := by
  obtain ⟨l,hl⟩ := reciprocal_limit_exists hx hxz
  exact integrableOn_Ioi_deriv_of_nonpos' (fun t _ => reciprocal_hasDerivAt hxz t)
    (fun t ht => (reciprocalJet_neg hx hxz ht.le).le) hl

private theorem slope_zero : thetaCuspLogDecaySlope 0 = 0 := by
  simp only [thetaCuspLogDecaySlope,
    iteratedDeriv_thetaCuspLogSource_zero_of_odd (m := 1) ⟨0,rfl⟩, neg_zero]

theorem intercept_nonneg {x z : ℝ} (hx : 0 ≤ x) (hxz : x < z)
    {t : ℝ} (ht : 0 ≤ t) : 0 ≤ intercept x z t := by
  rcases (show 0 ≤ x+t by linarith).eq_or_lt with he | he
  · simp only [intercept, ← he, slope_zero, zero_mul, mul_zero, sub_self, zero_div]
    exact le_refl 0
  · have h := (ThetaPortBoundary.slopeIntercept_pos he (show x+t < z+t by linarith)).le
    simpa only [intercept, ThetaPortBoundary.slopeIntercept, add_sub_add_right_eq_sub] using h

theorem intercept_div_le {x z : ℝ} (hx : 0 ≤ x) (hxz : x < z)
    {t : ℝ} (ht : 0 ≤ t) : intercept x z t/secant x z t ≤ x+t := by
  have he : intercept x z t = (x+t)*secant x z t-thetaCuspLogDecaySlope (x+t) := by
    dsimp [intercept, secant]
    field_simp [sub_ne_zero.mpr hxz.ne']
    ring
  rw [div_le_iff₀ (secant_pos hxz t), he]
  have hp := thetaCuspLogDecaySlope_nonneg (show 0 ≤ x+t by linarith)
  linarith

/-- The scalar density is genuinely negative at a center-anchored endpoint. -/
theorem density_center_neg {z : ℝ} (hz : 0 < z) : density 0 z 0 < 0 := by
  have hj : intercept 0 z 0 = 0 := by simp [intercept, slope_zero]
  simpa only [density, hj, zero_div, mul_zero, zero_add] using
    reciprocalJet_neg (le_refl (0:ℝ)) hz (le_refl (0:ℝ))

private theorem secant_continuous (x z : ℝ) : Continuous (secant x z) :=
  continuous_iff_continuousAt.mpr fun t => (secant_hasDerivAt x z t).continuousAt

private theorem intercept_continuous (x z : ℝ) : Continuous (intercept x z) := by
  unfold intercept
  exact (((continuous_const.add continuous_id).mul
    (slope_continuous.comp (continuous_const.add continuous_id))).sub
    ((continuous_const.add continuous_id).mul
      (slope_continuous.comp (continuous_const.add continuous_id)))).div_const _

private theorem reciprocalJet_continuous {x z : ℝ} (hxz : x < z) :
    Continuous (reciprocalJet x z) := by
  have hc : Continuous (secantJet x z) := by
    unfold secantJet
    exact ((continuous_iteratedDeriv_two_thetaCuspLogSource.comp
      (continuous_const.add continuous_id)).neg.add
      (continuous_iteratedDeriv_two_thetaCuspLogSource.comp
        (continuous_const.add continuous_id))).div_const _
  exact hc.neg.div ((secant_continuous x z).pow 2)
    (fun t => pow_ne_zero 2 (secant_pos hxz t).ne')

private theorem source_continuous : Continuous thetaCuspFullSource :=
  thetaCuspSchwartzReal.continuous

private theorem packet_continuous (x z a b : ℝ) : Continuous (packet x z a b) :=
  ((source_continuous.comp (continuous_const.add continuous_id)).const_mul a).add
    ((source_continuous.comp (continuous_const.add continuous_id)).const_mul b)

private theorem source_deriv_eq (t : ℝ) :
    deriv thetaCuspFullSource t = -thetaCuspLogDecaySlope t * thetaCuspFullSource t := by
  have h : iteratedDeriv 1 thetaCuspLogSource t =
      deriv thetaCuspFullSource t / thetaCuspFullSource t := by
    simpa only [iteratedDeriv_one] using (hasDerivAt_thetaCuspLogSource t).deriv
  dsimp only [thetaCuspLogDecaySlope]
  rw [h]
  field_simp [(thetaCuspFullSource_pos_all t).ne']

theorem packet_hasDerivAt {x z : ℝ} (hxz : x < z) (a b t : ℝ) :
    HasDerivAt (packet x z a b)
      (intercept x z t*packet x z a b t-secant x z t*coordinatePacket x z a b t) t := by
  have hk (u : ℝ) : HasDerivAt thetaCuspFullSource (deriv thetaCuspFullSource u) u :=
    thetaCuspSchwartzReal.hasDerivAt u
  have hx := (hk (x+t)).comp t ((hasDerivAt_id t).const_add x)
  have hz := (hk (z+t)).comp t ((hasDerivAt_id t).const_add z)
  convert! (hx.const_mul a).add (hz.const_mul b) using 1
  simp only [intercept, secant, packet, coordinatePacket, source_deriv_eq, mul_one]
  field_simp [sub_ne_zero.mpr hxz.ne']
  ring

private def weighted (f : SchwartzMap ℝ ℝ) : SchwartzMap ℝ ℝ :=
  SchwartzMap.smulLeftCLM ℝ (fun t : ℝ => t) f

private theorem weighted_apply (f : SchwartzMap ℝ ℝ) (t : ℝ) : weighted f t = t*f t := by
  have hg : (fun t : ℝ => t).HasTemperateGrowth := by fun_prop
  simp only [weighted, SchwartzMap.smulLeftCLM_apply_apply hg, smul_eq_mul]

private theorem shifted_integrable (f : SchwartzMap ℝ ℝ) (x : ℝ) :
    Integrable (fun t => f (x+t)) := by
  simpa only [add_comm] using f.integrable.comp_add_right x

private theorem weighted_shift_integrable (f : SchwartzMap ℝ ℝ) (x : ℝ) :
    Integrable (fun t => t*f (x+t)) := by
  have h := (shifted_integrable (weighted f) x).sub ((shifted_integrable f x).const_mul x)
  simp only [weighted_apply] at h
  convert! h using 1
  ext t
  dsimp
  ring

private theorem linear_product_integrable (f g : SchwartzMap ℝ ℝ) (x z C D : ℝ) :
    Integrable (fun t => (C+D*t)*f (x+t)*g (z+t)) := by
  have h := ((shifted_integrable f x).const_mul C).add
    ((weighted_shift_integrable f x).const_mul D)
  have hp := h.mul_bdd (g.continuous.comp (continuous_const.add continuous_id)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun t => g.norm_le_seminorm ℝ (z+t))
  convert! hp using 1
  ext t
  dsimp
  ring

private theorem linear_packet_square_integrable (x z a b C D : ℝ) :
    Integrable (fun t => (C+D*t)*(packet x z a b t)^2) := by
  have h := (((linear_product_integrable thetaCuspSchwartzReal thetaCuspSchwartzReal x x C D).const_mul
    (a^2)).add ((linear_product_integrable thetaCuspSchwartzReal thetaCuspSchwartzReal x z C D).const_mul
      (2*a*b))).add
    ((linear_product_integrable thetaCuspSchwartzReal thetaCuspSchwartzReal z z C D).const_mul (b^2))
  convert! h using 1
  ext t
  simp only [packet, Pi.add_apply, thetaCuspSchwartzReal_apply]
  ring

private theorem packet_bounded (x z a b : ℝ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ t, ‖packet x z a b t‖ ≤ C := by
  let K := SchwartzMap.seminorm ℝ 0 0 thetaCuspSchwartzReal
  have hK (u : ℝ) : ‖thetaCuspFullSource u‖ ≤ K := thetaCuspSchwartzReal.norm_le_seminorm ℝ u
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK 0)
  refine ⟨(|a|+|b|)*K, mul_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _)) hK0, ?_⟩
  intro t
  calc
    ‖packet x z a b t‖ ≤ ‖a*thetaCuspFullSource (x+t)‖+‖b*thetaCuspFullSource (z+t)‖ :=
      norm_add_le _ _
    _ = |a| * ‖thetaCuspFullSource (x+t)‖ + |b| * ‖thetaCuspFullSource (z+t)‖ := by
      rw [norm_mul, norm_mul, Real.norm_eq_abs a, Real.norm_eq_abs b]
    _ ≤ |a| * K + |b| * K := add_le_add
      (mul_le_mul_of_nonneg_left (hK _) (abs_nonneg _))
      (mul_le_mul_of_nonneg_left (hK _) (abs_nonneg _))
    _ = (|a|+|b|)*K := by ring

private theorem packet_zero_limit (x z a b : ℝ) : Tendsto (packet x z a b) atTop (𝓝 0) := by
  have hk (u : ℝ) : Tendsto (fun t => thetaCuspFullSource (u+t)) atTop (𝓝 0) :=
    (thetaCuspSchwartzReal.tendsto_cocompact.mono_left atTop_le_cocompact).comp
      (tendsto_atTop_add_const_left atTop u tendsto_id)
  change Tendsto (fun t => a*thetaCuspFullSource (x+t)+b*thetaCuspFullSource (z+t)) atTop (𝓝 0)
  simpa only [mul_zero, add_zero] using ((hk x).const_mul a).add ((hk z).const_mul b)

/-- The signed density is integrable against every squared two-translate packet,
including packets at nodes other than the defining secant nodes. -/
theorem density_square_integrable {x z : ℝ} (hx : 0 ≤ x) (hxz : x < z) (u v a b : ℝ) :
    IntegrableOn (fun t => density x z t*(packet u v a b t)^2) (Ioi 0) := by
  have hc := (intercept_continuous x z).div (secant_continuous x z) (fun t => (secant_pos hxz t).ne')
  have hmain : IntegrableOn (fun t => 2*(intercept x z t/secant x z t)*(packet u v a b t)^2)
      (Ioi 0) := by
    apply (linear_packet_square_integrable u v a b (2*x) 2).integrableOn.mono'
      ((hc.const_mul 2).mul ((packet_continuous u v a b).pow 2)).aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    change ‖2*(intercept x z t/secant x z t)*(packet u v a b t)^2‖ ≤ _
    have hn := div_nonneg (intercept_nonneg hx hxz ht.le) (secant_pos hxz t).le
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (mul_nonneg (by positivity) hn) (sq_nonneg _))]
    have h := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (intercept_div_le hx hxz ht.le) (by positivity : (0:ℝ) ≤ 2))
      (sq_nonneg (packet u v a b t))
    nlinarith only [h]
  obtain ⟨C,hC,hbound⟩ := packet_bounded u v a b
  have htail : IntegrableOn (fun t => reciprocalJet x z t*(packet u v a b t)^2) (Ioi 0) := by
    apply (reciprocalJet_integrable hx hxz).mul_bdd
      ((packet_continuous u v a b).pow 2).aestronglyMeasurable
    filter_upwards [] with t
    change ‖(packet u v a b t)^2‖ ≤ C^2
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (hbound t) 2
  convert! hmain.add htail using 1
  ext t
  dsimp [density]
  ring

private theorem energy_integrand_integrable (x z a b : ℝ) :
    Integrable (fun t => 2*packet x z a b t*coordinatePacket x z a b t) := by
  have h := (((integrable_thetaTailCommonTranslationIntegrand x x).const_mul (a^2)).add
    ((integrable_thetaTailCommonTranslationIntegrand x z).const_mul (2*a*b))).add
    ((integrable_thetaTailCommonTranslationIntegrand z z).const_mul (b^2))
  convert! h using 1
  ext t
  dsimp [packet, coordinatePacket, thetaTailCommonTranslationIntegrand]
  ring

theorem energy_eq_integral (x z a b : ℝ) :
    energy x z a b = ∫ t in Ioi 0, 2*packet x z a b t*coordinatePacket x z a b t := by
  have hH (u v : ℝ) : (∫ t in Ioi 0, thetaTailCommonTranslationIntegrand u v t) =
      thetaTailFirstMomentKernel u v := by
    simpa only [add_zero] using (thetaTailFirstMomentKernel_commonShift_eq_tail 0 u v).symm
  have h₁ : IntegrableOn (fun t => a^2*thetaTailCommonTranslationIntegrand x x t) (Ioi 0) :=
    ((integrable_thetaTailCommonTranslationIntegrand x x).const_mul (a^2)).integrableOn
  have h₂ : IntegrableOn (fun t => 2*a*b*thetaTailCommonTranslationIntegrand x z t) (Ioi 0) :=
    ((integrable_thetaTailCommonTranslationIntegrand x z).const_mul (2*a*b)).integrableOn
  have h₃ : IntegrableOn (fun t => b^2*thetaTailCommonTranslationIntegrand z z t) (Ioi 0) :=
    ((integrable_thetaTailCommonTranslationIntegrand z z).const_mul (b^2)).integrableOn
  have he : (fun t => 2*packet x z a b t*coordinatePacket x z a b t) =
      (fun t => a^2*thetaTailCommonTranslationIntegrand x x t+
        2*a*b*thetaTailCommonTranslationIntegrand x z t+b^2*thetaTailCommonTranslationIntegrand z z t) := by
    funext t
    dsimp [packet, coordinatePacket, thetaTailCommonTranslationIntegrand]
    ring
  have h₁₂ : IntegrableOn (fun t => a^2*thetaTailCommonTranslationIntegrand x x t+
      2*a*b*thetaTailCommonTranslationIntegrand x z t) (Ioi 0) := h₁.add h₂
  rw [he, integral_add h₁₂ h₃, integral_add h₁ h₂]
  simp only [integral_const_mul, hH, energy]

private theorem boundary_hasDerivAt {x z : ℝ} (hxz : x < z) (a b t : ℝ) :
    HasDerivAt (fun t => reciprocal x z t*(packet x z a b t)^2)
      (density x z t*(packet x z a b t)^2-2*packet x z a b t*coordinatePacket x z a b t) t := by
  convert! (reciprocal_hasDerivAt hxz t).mul ((packet_hasDerivAt hxz a b t).pow 2) using 1
  simp only [density, reciprocal, Pi.pow_apply]
  field_simp [(secant_pos hxz t).ne']
  ring

/-- Exact signed scalar energy, with its source boundary term retained. -/
theorem energy_eq_boundary_add_signed_integral {x z : ℝ} (hx : 0 ≤ x) (hxz : x < z)
    (a b : ℝ) :
    energy x z a b = (packet x z a b 0)^2/secant x z 0 +
      ∫ t in Ioi 0, density x z t*(packet x z a b t)^2 := by
  obtain ⟨l,hl⟩ := reciprocal_limit_exists hx hxz
  have hb : Tendsto (fun t => reciprocal x z t*(packet x z a b t)^2) atTop (𝓝 0) := by
    simpa using hl.mul ((packet_zero_limit x z a b).pow 2)
  have hi := density_square_integrable hx hxz x z a b
  have he := (energy_integrand_integrable x z a b).integrableOn (s := Ioi 0)
  have h := integral_Ioi_of_hasDerivAt_of_tendsto'
    (a := 0) (fun t _ => boundary_hasDerivAt hxz a b t) (hi.sub he) hb
  rw [integral_sub hi he, ← energy_eq_integral] at h
  simp only [zero_sub, reciprocal, div_eq_mul_inv] at h ⊢
  nlinarith only [h]

def determinant (x z : ℝ) : ℝ :=
  thetaTailFirstMomentKernel x x*thetaTailFirstMomentKernel z z-thetaTailFirstMomentKernel x z^2

/-- The first coefficient of the actual inverse-Gram source representer. -/
def representerLeft (x z : ℝ) : ℝ :=
  (thetaTailFirstMomentKernel z z*thetaCuspFullSource x-
    thetaTailFirstMomentKernel x z*thetaCuspFullSource z)/determinant x z

/-- The second coefficient of the actual inverse-Gram source representer. -/
def representerRight (x z : ℝ) : ℝ :=
  (thetaTailFirstMomentKernel x x*thetaCuspFullSource z-
    thetaTailFirstMomentKernel x z*thetaCuspFullSource x)/determinant x z

def feedback (x z : ℝ) : ℝ :=
  representerLeft x z*thetaCuspFullSource x+representerRight x z*thetaCuspFullSource z

def representer (x z : ℝ) : ℝ → ℝ := packet x z (representerLeft x z) (representerRight x z)

/-- The coefficients satisfy the literal two-node source projection equations. -/
theorem representer_equations {x z : ℝ} (hxz : x < z) :
    (thetaTailFirstMomentKernel x x*representerLeft x z+
      thetaTailFirstMomentKernel x z*representerRight x z = thetaCuspFullSource x) ∧
    (thetaTailFirstMomentKernel x z*representerLeft x z+
      thetaTailFirstMomentKernel z z*representerRight x z = thetaCuspFullSource z) := by
  have hD : determinant x z ≠ 0 := (ThetaTailTwoPoint.kernel_two_point_det_pos hxz.ne).ne'
  constructor <;> dsimp only [representerLeft, representerRight] <;>
    rw [← mul_div_assoc, ← mul_div_assoc, ← add_div, div_eq_iff hD] <;>
    dsimp only [determinant] <;> ring

theorem feedback_pos {x z : ℝ} (hxz : x < z) : 0 < feedback x z := by
  have hD := ThetaTailTwoPoint.kernel_two_point_det_pos hxz.ne
  have hxx : 0 < thetaTailFirstMomentKernel x x := by
    rw [ThetaTailTwoPoint.kernel_diag_eq_cut]
    exact ThetaSourceWard.thetaPrimeGammaCutEnergy_pos x
  have hn : 0 < thetaTailFirstMomentKernel z z*thetaCuspFullSource x^2-
      2*thetaTailFirstMomentKernel x z*thetaCuspFullSource x*thetaCuspFullSource z+
      thetaTailFirstMomentKernel x x*thetaCuspFullSource z^2 := by
    have hp := mul_pos hD (sq_pos_of_pos (thetaCuspFullSource_pos_all x))
    have hs := sq_nonneg (thetaTailFirstMomentKernel x x*thetaCuspFullSource z-
      thetaTailFirstMomentKernel x z*thetaCuspFullSource x)
    have hh : 0 < (thetaTailFirstMomentKernel z z*thetaCuspFullSource x^2-
        2*thetaTailFirstMomentKernel x z*thetaCuspFullSource x*thetaCuspFullSource z+
        thetaTailFirstMomentKernel x x*thetaCuspFullSource z^2)*thetaTailFirstMomentKernel x x := by
      nlinarith only [hp,hs]
    exact (mul_pos_iff.mp hh).resolve_right (fun h => (not_lt_of_ge hxx.le) h.2) |>.1
  have he : feedback x z = (thetaTailFirstMomentKernel z z*thetaCuspFullSource x^2-
      2*thetaTailFirstMomentKernel x z*thetaCuspFullSource x*thetaCuspFullSource z+
      thetaTailFirstMomentKernel x x*thetaCuspFullSource z^2)/determinant x z := by
    dsimp [feedback, representerLeft, representerRight]
    ring
  rw [he]
  exact div_pos hn hD

theorem representer_energy {x z : ℝ} (hxz : x < z) :
    energy x z (representerLeft x z) (representerRight x z) = feedback x z := by
  obtain ⟨h₁,h₂⟩ := representer_equations hxz
  dsimp only [energy, feedback]
  linear_combination representerLeft x z*h₁ + representerRight x z*h₂

/-- The actual inverse-Gram feedback excess is exactly a signed source energy.
This preserves the inverse-matrix term without assuming its sign. -/
theorem feedback_sub_secant_eq_signed_energy {x z : ℝ} (hx : 0 ≤ x) (hxz : x < z) :
    feedback x z-secant x z 0 = -(secant x z 0/feedback x z)*
      ∫ t in Ioi 0, density x z t*(representer x z t)^2 := by
  have h := energy_eq_boundary_add_signed_integral hx hxz (representerLeft x z) (representerRight x z)
  rw [representer_energy hxz] at h
  have hz : packet x z (representerLeft x z) (representerRight x z) 0 = feedback x z := by
    simp only [packet, feedback, add_zero]
  rw [hz] at h
  change feedback x z = feedback x z^2/secant x z 0+
    ∫ t in Ioi 0, density x z t*(representer x z t)^2 at h
  field_simp [(secant_pos hxz 0).ne'] at h
  field_simp [(feedback_pos hxz).ne']
  nlinarith only [h]

end RHTower.ThetaSturm
