import GaloisForLFunctions.ExclusionOfTheCriticalState.Index.TheMellinHeatMomentsOfTheOrdinateTail

/-!
# Coalescing heat measurements at the finite-layer threshold

The two rates may converge to the same positive value at any speed.
Dividing by their separation then recovers the derivative of the
logarithmic heat response. Without division their difference vanishes.
-/
noncomputable section
open MeasureTheory Set Filter Topology Zeta23
open GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
open GaloisForLFunctions.ArithmeticCastelnuovoSeveri _root_.RHTower
namespace GaloisForLFunctions.ExclusionOfTheCriticalState

open private bounded_weighted_tail ordinate_tail_antitone_nonneg mellin_heat_integrable mellin_density_mass
  from GaloisForLFunctions.ExclusionOfTheCriticalState.Index.TheMellinHeatMomentsOfTheOrdinateTail

/-- A dominated family of filters may vary with the observation scale.
Its pointwise limit determines the full physical-space tail integral. -/
theorem inverse_tail_moving_test_limit {f : ℝ → ℝ} {C : ℝ}
    (hp : ∀ x,0≤f x) (ha : Antitone f) (h : Tendsto (fun x : ℝ => x*f x) atTop (𝓝 C))
    {w : ℝ → ℝ → ℝ} {w₀ M : ℝ → ℝ} (hM : IntegrableOn M (Ioi 0))
    (hm : ∀ L,AEStronglyMeasurable (w L) (volume.restrict (Ioi 0)))
    (hb : ∀ᶠ L in atTop,∀ᵐ z ∂volume.restrict (Ioi 0),‖w L z‖≤M z)
    (hc : ∀ᵐ z ∂volume.restrict (Ioi 0),Tendsto (fun L => w L z) atTop (𝓝 (w₀ z))) :
    Tendsto (fun L : ℝ => ∫ x in Ioi 0,f x*((x/L)*w L (x/L))) atTop
      (𝓝 (C*∫ z in Ioi 0,w₀ z)) := by
  obtain ⟨B,hB⟩ := bounded_weighted_tail hp ha h
  have hB₀ : 0≤B := (mul_nonneg zero_le_one (hp 1)).trans (hB 1 zero_lt_one)
  let g (L z : ℝ) := (L*z)*f (L*z)*w L z
  have hg (L : ℝ) : AEStronglyMeasurable (g L) (volume.restrict (Ioi 0)) :=
    (((measurable_const.mul measurable_id).mul
      (ha.measurable.comp (measurable_const.mul measurable_id))).aestronglyMeasurable).mul (hm L)
  have hle : ∀ᶠ L in atTop,∀ᵐ z ∂volume.restrict (Ioi 0),‖g L z‖≤B*M z := by
    filter_upwards [eventually_gt_atTop (0:ℝ),hb] with L hL hdom
    filter_upwards [ae_restrict_mem measurableSet_Ioi,hdom] with z hz hw
    have hx := mul_pos hL (show 0<z from hz)
    dsimp only [g]
    rw [norm_mul,Real.norm_of_nonneg (mul_nonneg hx.le (hp _))]
    exact mul_le_mul (hB _ hx) hw (norm_nonneg _) hB₀
  have hlim : ∀ᵐ z ∂volume.restrict (Ioi 0),Tendsto (fun L => g L z) atTop (𝓝 (C*w₀ z)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi,hc] with z hz hw
    exact (h.comp (tendsto_id.atTop_mul_const (show 0<z from hz))).mul hw
  have ht := tendsto_integral_filter_of_dominated_convergence (fun z => B*M z)
    (.of_forall hg) hle (hM.const_mul B) hlim
  rw [integral_const_mul] at ht
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with L hL
  let G := fun x : ℝ => f x*((x/L)*w L (x/L))
  have hr := integral_comp_mul_left_Ioi G 0 hL
  rw [mul_zero,smul_eq_mul] at hr
  calc
    (∫ z in Ioi (0:ℝ),g L z) = ∫ z in Ioi (0:ℝ),L*G (L*z) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro z _
      simp only [g,G,mul_div_cancel_left₀ _ hL.ne']; ring
    _ = _ := by rw [integral_const_mul,hr,←mul_assoc,mul_inv_cancel₀ hL.ne',one_mul]

/-- The cusp coefficient is strictly positive for a critical ground state at the infimum. -/
theorem ordinateCuspConstant_pos {W : ℝ} (hW : 0<W)
    (ht : (⨅ (A : ℝ) (_ : 0≤A),windowThreshold A)=(W:EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W F) : 0<ordinateCuspConstant W F := by
  have hn := isConfinedNullVector_of_groundState hW ht hF
  have he : (∫ u : ℝ, F u^2*Real.exp (-(8*u)))=criticalHalfLineExponentialPair F F := by
    unfold criticalHalfLineExponentialPair
    exact integral_congr_ae (.of_forall fun u => by ring)
  unfold ordinateCuspConstant
  rw [he]
  exact div_pos (mul_pos (mul_pos (by norm_num) (criticalAliasCoefficient_positive hW))
    (exponentialPair_self_pos (criticalHalfLineEnergyDomain_of_groundState hF) hn.2.1)) Real.pi_pos

private def secant (a b t : ℝ) := (Real.exp (-a*t)-Real.exp (-b*t))/(b-a)

private theorem secant_bounds {a b t : ℝ} (h : a<b) :
    t*Real.exp (-b*t) ≤ secant a b t ∧ secant a b t ≤ t*Real.exp (-a*t) := by
  have h₁ := mul_le_mul_of_nonneg_right (Real.add_one_le_exp ((b-a)*t)) (Real.exp_pos (-b*t)).le
  have h₂ := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (-(b-a)*t)) (Real.exp_pos (-a*t)).le
  rw [←Real.exp_add,show (b-a)*t+-b*t= -a*t by ring] at h₁
  rw [←Real.exp_add,show -(b-a)*t+-a*t= -b*t by ring] at h₂
  exact ⟨(le_div_iff₀ (sub_pos.mpr h)).mpr (by linarith only [h₁]),
    (div_le_iff₀ (sub_pos.mpr h)).mpr (by linarith only [h₂])⟩

private theorem secant_limit {a b : ℝ → ℝ} {r : ℝ} (ha : Tendsto a atTop (𝓝 r))
    (hb : Tendsto b atTop (𝓝 r)) (hab : ∀ᶠ L in atTop,a L<b L) (t : ℝ) :
    Tendsto (fun L => secant (a L) (b L) t) atTop (𝓝 (t*Real.exp (-r*t))) := by
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    ((hb.neg.mul_const t).rexp.const_mul t) ((ha.neg.mul_const t).rexp.const_mul t)
    (hab.mono fun _ h => (secant_bounds h).1) (hab.mono fun _ h => (secant_bounds h).2)

/-- A derivative measurement with arbitrarily varying, coalescing positive rates.
For arbitrary separation b(L)-a(L)>0 the normalized signal has the
same nonzero limit C/(pr) as a single derivative reading at r. -/
theorem critical_ordinate_coalescing_heat_rates {W : ℝ} (hW : 0<W)
    (ht : (⨅ (A : ℝ) (_ : 0≤A),windowThreshold A)=(W:EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W F) (hf : BacklundConverse.FiniteOffLine)
    {p r : ℝ} (hp : 0<p) (hr : 0<r) {a b : ℝ → ℝ}
    (ha : Tendsto a atTop (𝓝 r)) (hb : Tendsto b atTop (𝓝 r))
    (hab : ∀ᶠ L in atTop,a L<b L) :
    Tendsto (fun L : ℝ => (∫ x in Ioi 0,ordinateTailMass F x*
        (Real.exp (-a L*(x/L)^p)-Real.exp (-b L*(x/L)^p)))/(b L-a L)) atTop
      (𝓝 (ordinateCuspConstant W F/(p*r))) := by
  let w := fun L z : ℝ => secant (a L) (b L) (z^p)/z
  let M := fun z : ℝ => z^(p-1)*Real.exp (-(r/2)*z^p)
  let w₀ := fun z : ℝ => z^(p-1)*Real.exp (-r*z^p)
  have hpower {z : ℝ} (hz : 0<z) : z^p/z=z^(p-1) := by rw [Real.rpow_sub hz,Real.rpow_one]
  have hm (L : ℝ) : AEStronglyMeasurable (w L) (volume.restrict (Ioi 0)) := by
    have hmeas : Measurable (w L) := by dsimp only [w,secant]; fun_prop
    exact hmeas.aestronglyMeasurable
  have hdom : ∀ᶠ L in atTop,∀ᵐ z ∂volume.restrict (Ioi 0),‖w L z‖≤M z := by
    filter_upwards [hab,ha.eventually_const_lt (show r/2<r by linarith)] with L h hr'
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
    have hz' : 0<z := hz
    have hzpow := Real.rpow_pos_of_pos hz' p
    have hsec := secant_bounds (t:=z^p) h
    have hn := (mul_nonneg hzpow.le (Real.exp_pos _).le).trans hsec.1
    have he := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (neg_le_neg hr'.le) hzpow.le)
    dsimp only [w,M]
    rw [Real.norm_of_nonneg (div_nonneg hn hz'.le),←hpower hz']
    calc
      _ ≤ (z^p*Real.exp (-a L*z^p))/z := div_le_div_of_nonneg_right hsec.2 hz'.le
      _ = z^p/z*Real.exp (-a L*z^p) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left he (div_nonneg hzpow.le hz'.le)
  have hc : ∀ᵐ z ∂volume.restrict (Ioi (0:ℝ)),Tendsto (fun L => w L z) atTop (𝓝 (w₀ z)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
    have h := (secant_limit ha hb hab (z^p)).div_const z
    dsimp only [w,w₀]
    rwa [←hpower hz,show z^p/z*Real.exp (-r*z^p)=z^p*Real.exp (-r*z^p)/z by ring]
  obtain ⟨hanti,hpos⟩ := ordinate_tail_antitone_nonneg
    (domain_zeroParseval_of_finiteOffLine (criticalHalfLineEnergyDomain_of_groundState hF) hf).1
  have htail : Tendsto (fun x : ℝ => x*ordinateTailMass F x) atTop (𝓝 (ordinateCuspConstant W F)) :=
    criticalState_criticalLine_tail_asymptotic hW ht hF hf
  have hI := inverse_tail_moving_test_limit hpos hanti htail
    (show IntegrableOn M (Ioi 0) from mellin_heat_integrable hp (half_pos hr) hp) hm hdom hc
  have hmass : (∫ z in Ioi 0,w₀ z)=r⁻¹/p := mellin_density_mass hp hr
  rw [hmass,show ordinateCuspConstant W F*(r⁻¹/p)=ordinateCuspConstant W F/(p*r) by ring] at hI
  apply hI.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with L hL
  rw [←integral_div]
  exact setIntegral_congr_fun measurableSet_Ioi fun x hx => by
    have hpos' := div_pos (show 0<x from hx) hL
    dsimp only [w,secant]
    rw [mul_div_cancel₀ _ hpos'.ne']
    ring

/-- An unnormalized difference at coalescing rates vanishes for every
surviving ground state. Such vanishing cannot exclude a finite layer. -/
theorem critical_ordinate_coalescing_heat_difference {W : ℝ} (hW : 0<W)
    (ht : (⨅ (A : ℝ) (_ : 0≤A),windowThreshold A)=(W:EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W F) (hf : BacklundConverse.FiniteOffLine)
    {p r : ℝ} (hp : 0<p) (hr : 0<r) {a b : ℝ → ℝ}
    (ha : Tendsto a atTop (𝓝 r)) (hb : Tendsto b atTop (𝓝 r))
    (hab : ∀ᶠ L in atTop,a L<b L) :
    Tendsto (fun L : ℝ => ∫ x in Ioi 0,ordinateTailMass F x*
        (Real.exp (-a L*(x/L)^p)-Real.exp (-b L*(x/L)^p))) atTop (𝓝 0) := by
  have h := (critical_ordinate_coalescing_heat_rates hW ht hF hf hp hr ha hb hab).mul (hb.sub ha)
  rw [sub_self,mul_zero] at h
  exact h.congr' (hab.mono fun L hL => div_mul_cancel₀ _ (sub_ne_zero.mpr hL.ne'))

/-- For ordered rates converging to r, exact collisions are the only
obstruction to reading the positive wall constant with a divided difference. -/
theorem coalescing_heat_limit_iff_eventually_separated {W : ℝ} (hW : 0<W)
    (ht : (⨅ (A : ℝ) (_ : 0≤A),windowThreshold A)=(W:EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W F) (hf : BacklundConverse.FiniteOffLine)
    {p r : ℝ} (hp : 0<p) (hr : 0<r) {a b : ℝ → ℝ}
    (ha : Tendsto a atTop (𝓝 r)) (hb : Tendsto b atTop (𝓝 r))
    (hab : ∀ᶠ L in atTop,a L≤b L) :
    Tendsto (fun L : ℝ => (∫ x in Ioi 0,ordinateTailMass F x*
        (Real.exp (-a L*(x/L)^p)-Real.exp (-b L*(x/L)^p)))/(b L-a L)) atTop
      (𝓝 (ordinateCuspConstant W F/(p*r))) ↔ ∀ᶠ L in atTop,a L<b L := by
  refine ⟨fun h => ?_,critical_ordinate_coalescing_heat_rates hW ht hF hf hp hr ha hb⟩
  have hc := ordinateCuspConstant_pos hW ht hF
  filter_upwards [hab,h.eventually_const_lt (div_pos hc (mul_pos hp hr))] with L hle hpos
  refine lt_of_le_of_ne hle ?_
  intro heq
  simpa only [heq,sub_self,div_zero,lt_self_iff_false] using hpos

end GaloisForLFunctions.ExclusionOfTheCriticalState
