import GaloisForLFunctions.ExclusionOfTheCriticalState.Index.TheConditionalOrdinateLawOnMultiplicativeBands
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# Finite heat moments of the critical ordinate tail

De Nitti–Ignat–Quirós, Lemma 7.1, identify the logarithmic Gaussian
profile at the inverse-distance threshold. A weight vanishing at zero
removes that logarithm. Every positive Mellin moment of a stretched
Gaussian then has a finite limit, for the actual ordinate tail of a
critical ground state.
-/
noncomputable section
open MeasureTheory Set Filter Topology Zeta23
open GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
open GaloisForLFunctions.ArithmeticCastelnuovoSeveri _root_.RHTower
namespace GaloisForLFunctions.ExclusionOfTheCriticalState

private theorem bounded_weighted_tail {f : ℝ → ℝ} {C : ℝ} (hp : ∀ x, 0≤f x)
    (ha : Antitone f) (h : Tendsto (fun x : ℝ => x*f x) atTop (𝓝 C)) :
    ∃ B:ℝ, ∀ x>0, x*f x≤B := by
  obtain ⟨R,hR⟩ := eventually_atTop.mp (h.eventually_lt_const (show C<C+1 by linarith))
  refine ⟨max (C+1) (max R 0*f 0),fun x hx => ?_⟩
  rcases le_or_gt R x with hr|hr
  · exact (hR _ hr).le.trans (le_max_left _ _)
  · exact (mul_le_mul (hr.le.trans (le_max_left _ _)) (ha hx.le) (hp _) (le_max_right _ _)).trans (le_max_right _ _)

/-- Every integrable profile w against the multiplicatively rescaled
density x f(x) has the full weak limit. The physical-space formula
allows kernels that vanish arbitrarily slowly at the origin. -/
theorem inverse_tail_test_limit {f : ℝ → ℝ} {C : ℝ} (hp : ∀ x, 0≤f x) (ha : Antitone f)
    (h : Tendsto (fun x : ℝ => x*f x) atTop (𝓝 C)) {w : ℝ → ℝ}
    (hw : IntegrableOn w (Ioi 0)) :
    Tendsto (fun L : ℝ => ∫ x in Ioi 0, f x*((x/L)*w (x/L))) atTop
      (𝓝 (C*∫ z in Ioi 0,w z)) := by
  obtain ⟨B,hB⟩ := bounded_weighted_tail hp ha h
  let g (L z : ℝ) := (L*z)*f (L*z)*w z
  have hm (L : ℝ) : AEStronglyMeasurable (g L) (volume.restrict (Ioi 0)) :=
    (((measurable_const.mul measurable_id).mul
      (ha.measurable.comp (measurable_const.mul measurable_id))).aestronglyMeasurable).mul hw.aestronglyMeasurable
  have hb : ∀ᶠ L : ℝ in atTop, ∀ᵐ z ∂volume.restrict (Ioi 0), ‖g L z‖ ≤ B*‖w z‖ := by
    filter_upwards [eventually_gt_atTop (0:ℝ)] with L hL
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
    have hx := mul_pos hL (show 0<z from hz)
    dsimp only [g]
    rw [norm_mul,Real.norm_of_nonneg (mul_nonneg hx.le (hp _))]
    exact mul_le_mul_of_nonneg_right (hB _ hx) (norm_nonneg _)
  have hc : ∀ᵐ z ∂volume.restrict (Ioi (0:ℝ)), Tendsto (fun L => g L z) atTop (𝓝 (C*w z)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
    exact (h.comp (tendsto_id.atTop_mul_const (show 0<z from hz))).mul_const (w z)
  have ht := tendsto_integral_filter_of_dominated_convergence (fun z => B*‖w z‖)
    (.of_forall hm) hb (hw.norm.const_mul B) hc
  rw [integral_const_mul] at ht
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with L hL
  let G := fun x : ℝ => f x*((x/L)*w (x/L))
  have hr := integral_comp_mul_left_Ioi G 0 hL
  rw [mul_zero,smul_eq_mul] at hr
  calc
    (∫ z in Ioi (0:ℝ),g L z) = ∫ z in Ioi (0:ℝ),L*G (L*z) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro z _
      simp only [g,G,mul_div_cancel_left₀ _ hL.ne']; ring
    _ = _ := by rw [integral_const_mul,hr,←mul_assoc,mul_inv_cancel₀ hL.ne',one_mul]

/-- After multiplication by any integrable density, the rescaled inverse
tail converges in L¹. Consequently even moving measurable cells can be
used to observe its limiting mass. -/
theorem inverse_tail_weighted_variation {f : ℝ → ℝ} {C : ℝ}
    (hp : ∀ x, 0≤f x) (ha : Antitone f) (h : Tendsto (fun x : ℝ => x*f x) atTop (𝓝 C))
    {w : ℝ → ℝ} (hw : IntegrableOn w (Ioi 0)) :
    Tendsto (fun L : ℝ => ∫ z in Ioi 0, abs ((L*z)*f (L*z)-C) * ‖w z‖) atTop (𝓝 0) := by
  obtain ⟨B,hB⟩ := bounded_weighted_tail hp ha h
  let G := fun L z : ℝ => abs ((L*z)*f (L*z)-C) * ‖w z‖
  have hm (L : ℝ) : AEStronglyMeasurable (G L) (volume.restrict (Ioi 0)) := by
    apply AEStronglyMeasurable.mul _ hw.aestronglyMeasurable.norm
    exact ((((measurable_const.mul measurable_id).mul
      (ha.measurable.comp (measurable_const.mul measurable_id))).sub measurable_const).abs).aestronglyMeasurable
  have hb : ∀ᶠ L : ℝ in atTop,∀ᵐ z ∂volume.restrict (Ioi 0),
      ‖G L z‖≤(B+|C|)*‖w z‖ := by
    filter_upwards [eventually_gt_atTop (0:ℝ)] with L hL
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
    have hpz := mul_pos hL (show 0<z from hz)
    have hsize := abs_sub ((L*z)*f (L*z)) C
    rw [abs_of_nonneg (mul_nonneg hpz.le (hp _))] at hsize
    exact (Real.norm_of_nonneg (mul_nonneg (abs_nonneg _) (norm_nonneg _))).le.trans
      (mul_le_mul_of_nonneg_right (hsize.trans (add_le_add (hB _ hpz) le_rfl)) (norm_nonneg _))
  have hc : ∀ᵐ z ∂volume.restrict (Ioi (0:ℝ)), Tendsto (fun L => G L z) atTop (𝓝 0) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
    have hh := (((h.comp (tendsto_id.atTop_mul_const (show 0<z from hz))).sub_const C).abs).mul_const ‖w z‖
    simpa only [G,Function.comp_apply,id_eq,sub_self,abs_zero,zero_mul] using hh
  have ht := tendsto_integral_filter_of_dominated_convergence (fun z => (B+|C|)*‖w z‖)
    (.of_forall hm) hb (hw.norm.const_mul _) hc
  simpa only [integral_zero] using ht

private theorem ordinate_tail_antitone_nonneg {F : ℝ → ℝ} (hs : Summable (fun q : onLineCopies => zeroValueMass F q)) :
    Antitone (ordinateTailMass F) ∧ ∀ u, 0≤ordinateTailMass F u := by
  have hn := zeroValueMass_nonneg F
  have hi (u : ℝ) : Summable (fun q : onLineCopies =>
      if u < |(centredZero q).im| then zeroValueMass F q else 0) :=
    hs.of_nonneg_of_le (fun q => by split <;> first | exact le_rfl | exact hn q) (fun q => by split <;> first | exact le_rfl | exact hn q)
  refine ⟨fun x y hxy => (hi y).tsum_le_tsum (fun q => ?_) (hi x),fun _ => tsum_nonneg fun q => by split <;> first | exact le_rfl | exact hn q⟩
  split_ifs with hy hx
  · exact le_rfl
  · exact (hx (hxy.trans_lt hy)).elim
  · exact hn q
  · exact le_rfl

private theorem mellin_heat_integrable {s a p : ℝ} (hs : 0<s) (ha : 0<a) (hp : 0<p) :
    IntegrableOn (fun z : ℝ => z^(s-1)*Real.exp (-a*z^p)) (Ioi 0) := by
  by_contra hbad
  have he := integral_rpow_mul_exp_neg_mul_rpow (q:=s-1) hp (by linarith) ha
  rw [integral_undef hbad,sub_add_cancel] at he
  exact (mul_pos (mul_pos (Real.rpow_pos_of_pos ha _) (one_div_pos.mpr hp))
    (Real.Gamma_pos_of_pos (div_pos hs hp))).ne' he.symm

/-- Sharp Gamma moment at every positive order, scale and stretch
exponent. For a Gaussian and order 2j+2 the coefficient is a factorial. -/
theorem critical_ordinate_mellin_heat_moment {W : ℝ} (hW : 0<W)
    (ht : (⨅ (A : ℝ) (_ : 0≤A), windowThreshold A)=(W:EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W F) (hf : BacklundConverse.FiniteOffLine)
    {s a p : ℝ} (hs : 0<s) (ha : 0<a) (hp : 0<p) :
    Tendsto (fun L : ℝ => ∫ x in Ioi 0,
      ordinateTailMass F x*(x/L)^s*Real.exp (-a*(x/L)^p)) atTop
      (𝓝 (ordinateCuspConstant W F * a^(-s/p)/p * Real.Gamma (s/p))) := by
  obtain ⟨hanti,hpos⟩ := ordinate_tail_antitone_nonneg
    (domain_zeroParseval_of_finiteOffLine (criticalHalfLineEnergyDomain_of_groundState hF) hf).1
  have hlim : Tendsto (fun x : ℝ => x*ordinateTailMass F x) atTop (𝓝 (ordinateCuspConstant W F)) :=
    criticalState_criticalLine_tail_asymptotic hW ht hF hf
  have hq : -1<s-1 := by linarith
  let w := fun z : ℝ => z^(s-1)*Real.exp (-a*z^p)
  have he : (∫ z in Ioi 0, w z)=a^(-s/p)*(1/p)*Real.Gamma (s/p) := by
    simpa only [w,sub_add_cancel] using integral_rpow_mul_exp_neg_mul_rpow (p:=p) (q:=s-1) hp hq ha
  have hwi : IntegrableOn w (Ioi 0) := mellin_heat_integrable hs ha hp
  have hz := inverse_tail_test_limit hpos hanti hlim hwi
  rw [he,show ordinateCuspConstant W F*(a^(-s/p)*(1/p)*Real.Gamma (s/p))=
      ordinateCuspConstant W F*a^(-s/p)/p*Real.Gamma (s/p) by ring] at hz
  apply hz.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with L hL
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  have hx' := div_pos (show 0<x from hx) hL
  have hpow : x/L*(x/L)^(s-1)=(x/L)^s := by
    rw [Real.rpow_sub hx',Real.rpow_one,mul_comm,div_mul_cancel₀ _ hx'.ne']
  dsimp only [w]
  rw [←mul_assoc (x/L),hpow,mul_assoc]

/-- The continuum of Mellin readings comes from total variation
convergence of the heat-weighted rescaled ordinate density. This controls
every measurable collection of bands at once. -/
theorem critical_ordinate_heat_density_variation {W : ℝ} (hW : 0<W)
    (ht : (⨅ (A : ℝ) (_ : 0≤A), windowThreshold A)=(W:EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W F) (hf : BacklundConverse.FiniteOffLine)
    {s a p : ℝ} (hs : 0<s) (ha : 0<a) (hp : 0<p) :
    Tendsto (fun L : ℝ => ∫ z in Ioi 0,
      abs ((L*z)*ordinateTailMass F (L*z)-ordinateCuspConstant W F) *
        (z^(s-1)*Real.exp (-a*z^p))) atTop (𝓝 0) := by
  obtain ⟨hanti,hpos⟩ := ordinate_tail_antitone_nonneg
    (domain_zeroParseval_of_finiteOffLine (criticalHalfLineEnergyDomain_of_groundState hF) hf).1
  have hlim : Tendsto (fun x : ℝ => x*ordinateTailMass F x) atTop (𝓝 (ordinateCuspConstant W F)) :=
    criticalState_criticalLine_tail_asymptotic hW ht hF hf
  let w := fun z : ℝ => z^(s-1)*Real.exp (-a*z^p)
  have hwi : IntegrableOn w (Ioi 0) := mellin_heat_integrable hs ha hp
  apply (inverse_tail_weighted_variation hpos hanti hlim hwi).congr'
  exact .of_forall fun L => setIntegral_congr_fun measurableSet_Ioi fun z hz => by
    rw [Real.norm_of_nonneg (show 0≤w z from mul_nonneg (Real.rpow_nonneg hz.le _) (Real.exp_pos _).le)]

/-- The quadratic Gaussian reading gives a finite, positive observation
whenever a critical state survives a finite outer layer. -/
theorem critical_ordinate_gaussian_pulse {W : ℝ} (hW : 0<W)
    (ht : (⨅ (A : ℝ) (_ : 0≤A), windowThreshold A)=(W:EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W F) (hf : BacklundConverse.FiniteOffLine) :
    Tendsto (fun L : ℝ => ∫ x in Ioi 0,
      ordinateTailMass F x*(x/L)^2*Real.exp (-((x/L)^2))) atTop (𝓝 (ordinateCuspConstant W F/2)) := by
  have h := critical_ordinate_mellin_heat_moment hW ht hF hf (s:=2) (a:=1) (p:=2)
    (by norm_num) (by norm_num) (by norm_num)
  norm_num [Real.rpow_two] at h ⊢
  exact h

private def heatBand (p a b z : ℝ) :=
  ∫ v in Ioc a b, z^(p-1)*Real.exp (-v*z^p)

private theorem heat_band_at_pos {p a b z : ℝ} (hz : 0<z) (hab : a≤b) :
    z*heatBand p a b z=Real.exp (-a*z^p)-Real.exp (-b*z^p) := by
  have hsq : z*z^(p-1)=z^p := by
    rw [Real.rpow_sub hz,Real.rpow_one,mul_comm,div_mul_cancel₀ _ hz.ne']
  have hd (v : ℝ) : HasDerivAt (fun t : ℝ => -Real.exp (-t*z^p))
      (z*z^(p-1)*Real.exp (-v*z^p)) v := by
    have h := ((((hasDerivAt_id' v).neg.mul_const (z^p)).exp).neg)
    rw [hsq]
    refine h.congr_deriv ?_
    change -(Real.exp (-v*z^p)*(-1*z^p))=z^p*Real.exp (-v*z^p)
    ring
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t)
    (Continuous.intervalIntegrable (by fun_prop) a b)
  rw [intervalIntegral.integral_of_le hab] at h
  unfold heatBand
  rw [←integral_const_mul]
  simpa only [←mul_assoc,neg_sub_neg] using h

private theorem mellin_density_mass {p a : ℝ} (hp : 0<p) (ha : 0<a) :
    (∫ z in Ioi (0:ℝ),z^(p-1)*Real.exp (-a*z^p))=a⁻¹/p := by
  have h := integral_rpow_mul_exp_neg_mul_rpow (p:=p) (q:=p-1) hp (by linarith) ha
  rw [sub_add_cancel,neg_div,div_self hp.ne',Real.rpow_neg_one,Real.Gamma_one,mul_one] at h
  simpa only [div_eq_mul_inv,one_mul] using h

private theorem heat_band_mass {p a b : ℝ} (hp : 0<p) (ha : 0<a) (hab : a≤b) :
    IntegrableOn (heatBand p a b) (Ioi 0) ∧
      (∫ z in Ioi 0,heatBand p a b z)=Real.log (b/a)/p := by
  let U := Ioi (0:ℝ)
  let V := Ioc a b
  let μ := volume.restrict U
  let ν := volume.restrict V
  let k := fun z v : ℝ => z^(p-1)*Real.exp (-v*z^p)
  have hmajor : Integrable (fun z : ℝ => k z a) μ := by
    by_contra hh
    have he := mellin_density_mass hp ha
    change (∫ z, k z a ∂μ)=_ at he
    rw [integral_undef hh] at he
    exact (div_pos (inv_pos.mpr ha) hp).ne' he.symm
  have h1 : Integrable (fun _ : ℝ => (1:ℝ)) ν :=
    integrableOn_const (C:=1) (hs:=measure_Ioc_lt_top.ne)
  have hprod : Integrable (Function.uncurry k) (μ.prod ν) := by
    apply (hmajor.mul_prod h1).mono' (by dsimp only [k,Function.uncurry];fun_prop)
    change ∀ᵐ z ∂(volume.restrict U).prod (volume.restrict V), _
    rw [Measure.prod_restrict]
    filter_upwards [ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Ioc)] with z hz
    obtain ⟨hz,hv⟩ := hz
    have hpp := Real.rpow_pos_of_pos (show 0<z.1 from hz) p
    dsimp only [k,Function.uncurry]
    rw [Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg hz.le _) (Real.exp_pos _).le),mul_one]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_right (neg_le_neg hv.1.le) hpp.le)) (Real.rpow_nonneg hz.le _)
  refine ⟨hprod.integral_prod_left,?_⟩
  change (∫ z, ∫ v, k z v ∂ν ∂μ)=_
  rw [integral_integral_swap hprod]
  calc
    _ = ∫ v in Ioc a b,v⁻¹/p := setIntegral_congr_fun measurableSet_Ioc fun v hv =>
      mellin_density_mass hp (ha.trans hv.1)
    _ = _ := by rw [integral_div,←intervalIntegral.integral_of_le hab,
      integral_inv_of_pos ha (ha.trans_le hab)]

/-- Two heat rates recover the wall constant from one unnormalized
difference, although either individual reading may diverge logarithmically.
The exact response is logarithmic in the ratio, for every stretch p>0. -/
theorem critical_ordinate_heat_band {W : ℝ} (hW : 0<W)
    (ht : (⨅ (A : ℝ) (_ : 0≤A), windowThreshold A)=(W:EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W F) (hf : BacklundConverse.FiniteOffLine)
    {p a b : ℝ} (hp : 0<p) (ha : 0<a) (hab : a≤b) :
    Tendsto (fun L : ℝ => ∫ x in Ioi 0, ordinateTailMass F x*
      (Real.exp (-a*(x/L)^p)-Real.exp (-b*(x/L)^p)))
      atTop (𝓝 (ordinateCuspConstant W F*Real.log (b/a)/p)) := by
  obtain ⟨hanti,hpos⟩ := ordinate_tail_antitone_nonneg
    (domain_zeroParseval_of_finiteOffLine (criticalHalfLineEnergyDomain_of_groundState hF) hf).1
  have hlim : Tendsto (fun x : ℝ => x*ordinateTailMass F x) atTop (𝓝 (ordinateCuspConstant W F)) :=
    criticalState_criticalLine_tail_asymptotic hW ht hF hf
  obtain ⟨hi,hm⟩ := heat_band_mass hp ha hab
  have h := inverse_tail_test_limit hpos hanti hlim hi
  rw [hm,←mul_div_assoc] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with L hL
  exact setIntegral_congr_fun measurableSet_Ioi fun x hx =>
    congrArg (ordinateTailMass F x * ·) (heat_band_at_pos (div_pos hx hL) hab)

/-- On the finite-layer branch a single sequence of vanishing two-rate
readings of the positive tail is equivalent to excluding a ground state.
No logarithmic normalization or tuning of the two heat rates is required. -/
theorem finite_layer_exclusion_iff_two_heat_rates {p a b : ℝ} (hp : 0<p) (ha : 0<a) (hab : a<b) :
    (BacklundConverse.FiniteOffLine → RiemannHypothesis) ↔
      (BacklundConverse.FiniteOffLine → ∀ (W : ℝ) (F : ℝ → ℝ),0<W →
        (⨅ (A : ℝ) (_ : 0≤A),windowThreshold A)=(W:EReal) →
        IsCriticalHalfLineGroundState W F → ∃ L : ℕ → ℝ, Tendsto L atTop atTop ∧
        Tendsto (fun n => ∫ x in Ioi 0,ordinateTailMass F x*
          (Real.exp (-a*(x/L n)^p)-Real.exp (-b*(x/L n)^p))) atTop (𝓝 0)) := by
  have hc : (BacklundConverse.FiniteOffLine → RiemannHypothesis) ↔
    (BacklundConverse.FiniteOffLine → ¬∃ (W : ℝ) (F : ℝ → ℝ),0<W ∧
      (⨅ (A : ℝ) (_ : 0≤A),windowThreshold A)=(W:EReal) ∧ IsCriticalHalfLineGroundState W F) :=
    finiteLayer_ecs_b13_tfae.out 0 1
  rw [hc]
  constructor
  · intro h hf W F hW ht hF
    exact (h hf ⟨W,F,hW,ht,hF⟩).elim
  · rintro h hf ⟨W,F,hW,ht,hF⟩
    obtain ⟨L,hL,hvan⟩ := h hf W F hW ht hF
    have heq := tendsto_nhds_unique ((critical_ordinate_heat_band hW ht hF hf hp ha hab.le).comp hL) hvan
    have hn := isConfinedNullVector_of_groundState hW ht hF
    have he : (∫ u : ℝ, F u^2*Real.exp (-(8*u)))=criticalHalfLineExponentialPair F F := by
      unfold criticalHalfLineExponentialPair
      exact integral_congr_ae (.of_forall fun u => by ring)
    have hC : 0<ordinateCuspConstant W F := by
      unfold ordinateCuspConstant
      rw [he]
      exact div_pos (mul_pos (mul_pos (by norm_num) (criticalAliasCoefficient_positive hW))
        (exponentialPair_self_pos (criticalHalfLineEnergyDomain_of_groundState hF) hn.2.1)) Real.pi_pos
    exact (div_pos (mul_pos hC (Real.log_pos ((one_lt_div ha).mpr hab))) hp).ne' heq

#print axioms finite_layer_exclusion_iff_two_heat_rates
#print axioms critical_ordinate_heat_band

#print axioms inverse_tail_weighted_variation
#print axioms critical_ordinate_heat_density_variation
#print axioms inverse_tail_test_limit
#print axioms critical_ordinate_mellin_heat_moment
#print axioms critical_ordinate_gaussian_pulse
end GaloisForLFunctions.ExclusionOfTheCriticalState
