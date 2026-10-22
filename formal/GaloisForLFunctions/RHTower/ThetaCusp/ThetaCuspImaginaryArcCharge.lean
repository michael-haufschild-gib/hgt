import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspImaginaryEndpoint
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Exact signed charges and an interior zero of the literal theta source

The complex Ward identity and flat odd-cusp endpoint give two exact arc charges.
Their positive survivor is the signed charge law. The negative sine charge and
positive source value at zero force an interior imaginary source zero, excluding
an exponential representation on the whole source strip. These statements do
not locate any zero of Xi and do not prove or falsify RH.
-/

open Complex Filter Topology Set MeasureTheory
noncomputable section
namespace RHTower.ThetaImaginaryArc

private theorem intervalIntegrable_of_flat_endpoint {f : ℝ → ℂ}
    (hc : ContinuousOn f (Ico 0 arcEnd))
    (ht : Tendsto f (𝓝[<] arcEnd) (𝓝 0)) :
    IntervalIntegrable f volume 0 arcEnd := by
  classical
  have hF : ContinuousOn (Function.update f arcEnd 0) (Icc 0 arcEnd) := by
    rw [continuousOn_update_iff, Icc_sdiff_right]
    exact ⟨hc, fun _ => ht.mono_left (nhdsWithin_mono _ Ico_subset_Iio_self)⟩
  apply (hF.intervalIntegrable_of_Icc arcEnd_pos.le).congr_uIoo
  intro t ht
  rw [uIoo_of_lt arcEnd_pos] at ht
  exact Function.update_of_ne ht.2.ne _ _

theorem continuousOn_axis_source :
    ContinuousOn (fun t : ℝ => thetaCuspStripSource ((t:ℂ)*Complex.I)) (Ico 0 arcEnd) := by
  intro t ht
  exact ((differentiableAt_thetaCuspStripSource (axis_mem_strip ht.1 ht.2)).continuousAt.comp (f := fun u : ℝ => (u:ℂ)*Complex.I)
    (by fun_prop : ContinuousAt (fun u : ℝ => (u:ℂ)*Complex.I) t)).continuousWithinAt

theorem intervalIntegrable_axisSource_weight (w : ℝ → ℂ) (hw : Continuous w) :
    IntervalIntegrable (fun t => w t*thetaCuspStripSource ((t:ℂ)*Complex.I)) volume 0 arcEnd := by
  apply intervalIntegrable_of_flat_endpoint (hw.continuousOn.mul continuousOn_axis_source)
  change Tendsto (fun t => w t*thetaCuspStripSource ((t:ℂ)*Complex.I)) _ _
  simpa only [mul_zero] using
    ((hw.tendsto arcEnd).mono_left nhdsWithin_le_nhds).mul tendsto_source_axis_zero

private theorem hasDerivAt_axis_potential {t : ℝ} (ht0 : 0≤t) (htL : t<arcEnd) :
    HasDerivAt (fun u : ℝ => Potential ((u:ℂ)*Complex.I))
      (Complex.I*deriv Potential ((t:ℂ)*Complex.I)) t := by
  have haxis := ((hasDerivAt_id t).ofReal_comp).mul_const Complex.I
  have hh := ((analytic_potential _ (axis_mem_strip ht0 htL)).differentiableAt.hasDerivAt).scomp t haxis
  simpa! only [Function.comp_def,Complex.ofReal_one,one_mul,smul_eq_mul,id_eq] using hh

private theorem hasDerivAt_axis_deriv {t : ℝ} (ht0 : 0≤t) (htL : t<arcEnd) :
    HasDerivAt (fun u : ℝ => deriv Potential ((u:ℂ)*Complex.I))
      (Complex.I*deriv (deriv Potential) ((t:ℂ)*Complex.I)) t := by
  have haxis := ((hasDerivAt_id t).ofReal_comp).mul_const Complex.I
  have hh := ((analytic_potential.deriv _ (axis_mem_strip ht0 htL)).differentiableAt.hasDerivAt).scomp t haxis
  simpa! only [Function.comp_def,Complex.ofReal_one,one_mul,smul_eq_mul,id_eq] using hh

private def cosineFlux (t : ℝ) : ℂ :=
  (Real.cos (t/2):ℂ)*Complex.I*deriv Potential ((t:ℂ)*Complex.I) +
  (Real.sin (t/2):ℂ)/2*Potential ((t:ℂ)*Complex.I)

private def sineFlux (t : ℝ) : ℂ :=
  (Real.sin (t/2):ℂ)*Complex.I*deriv Potential ((t:ℂ)*Complex.I) -
  (Real.cos (t/2):ℂ)/2*Potential ((t:ℂ)*Complex.I)

private theorem hasDerivAt_cosineFlux {t : ℝ} (ht0 : 0≤t) (htL : t<arcEnd) :
    HasDerivAt cosineFlux (-2*((Real.cos (t/2):ℂ)*thetaCuspStripSource ((t:ℂ)*Complex.I))) t := by
  have hc := (((hasDerivAt_id t).div_const (2:ℝ)).cos).ofReal_comp
  have hs := (((hasDerivAt_id t).div_const (2:ℝ)).sin).ofReal_comp
  have hh := ((hc.mul_const Complex.I).mul (hasDerivAt_axis_deriv ht0 htL)).add
    ((hs.div_const 2).mul (hasDerivAt_axis_potential ht0 htL))
  apply hh.congr_deriv
  rw [source_complex_ward (axis_mem_strip ht0 htL)]
  simp only [id_eq,Complex.ofReal_mul,Complex.ofReal_neg,Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat]
  linear_combination (Real.cos (t/2):ℂ)*deriv (deriv Potential) ((t:ℂ)*Complex.I)*Complex.I_sq

private theorem hasDerivAt_sineFlux {t : ℝ} (ht0 : 0≤t) (htL : t<arcEnd) :
    HasDerivAt sineFlux (-2*((Real.sin (t/2):ℂ)*thetaCuspStripSource ((t:ℂ)*Complex.I))) t := by
  have hc := (((hasDerivAt_id t).div_const (2:ℝ)).cos).ofReal_comp
  have hs := (((hasDerivAt_id t).div_const (2:ℝ)).sin).ofReal_comp
  have hh := ((hs.mul_const Complex.I).mul (hasDerivAt_axis_deriv ht0 htL)).sub
    ((hc.div_const 2).mul (hasDerivAt_axis_potential ht0 htL))
  apply hh.congr_deriv
  rw [source_complex_ward (axis_mem_strip ht0 htL)]
  simp only [id_eq,Complex.ofReal_mul,Complex.ofReal_neg,Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat]
  linear_combination (Real.sin (t/2):ℂ)*deriv (deriv Potential) ((t:ℂ)*Complex.I)*Complex.I_sq

private theorem tendsto_fluxes :
    Tendsto cosineFlux (𝓝[<] arcEnd) (𝓝 0) ∧ Tendsto sineFlux (𝓝[<] arcEnd) (𝓝 0) := by
  have hc : Tendsto (fun t : ℝ => (Real.cos (t/2):ℂ)) (𝓝[<] arcEnd)
      (𝓝 (Real.cos (arcEnd/2):ℂ)) :=
    ((by fun_prop : Continuous (fun t : ℝ => (Real.cos (t/2):ℂ))).tendsto _).mono_left nhdsWithin_le_nhds
  have hs : Tendsto (fun t : ℝ => (Real.sin (t/2):ℂ)) (𝓝[<] arcEnd)
      (𝓝 (Real.sin (arcEnd/2):ℂ)) :=
    ((by fun_prop : Continuous (fun t : ℝ => (Real.sin (t/2):ℂ))).tendsto _).mono_left nhdsWithin_le_nhds
  have hj := tendsto_potential_jets
  constructor
  · unfold cosineFlux
    simpa only [cosineFlux,mul_zero,add_zero] using
      ((hc.mul_const Complex.I).mul hj.2.1).add ((hs.div_const 2).mul hj.1)
  · unfold sineFlux
    simpa only [sineFlux,mul_zero,sub_zero] using
      ((hs.mul_const Complex.I).mul hj.2.1).sub ((hc.div_const 2).mul hj.1)

private theorem deriv_potential_zero : deriv Potential 0 = 0 := by
  have hh := deriv_potential_real 0
  norm_num [realJet,thetaCuspTailDerivative_one_zero] at hh ⊢
  exact hh

private theorem cosineFlux_zero : cosineFlux 0 = 0 := by
  simp [cosineFlux,deriv_potential_zero]

private theorem sineFlux_zero : sineFlux 0 = -Potential 0/2 := by
  simp [sineFlux]
  ring

/-- The exact cosine charge of the literal source is zero. -/
theorem cosine_arc_charge :
    (∫ t in (0:ℝ)..arcEnd, (Real.cos (t/2):ℂ)*thetaCuspStripSource ((t:ℂ)*Complex.I)) = 0 := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto arcEnd_pos
    (fun t ht => hasDerivAt_cosineFlux ht.1.le ht.2)
    ((intervalIntegrable_axisSource_weight (fun t => (Real.cos (t/2):ℂ)) (by fun_prop)).const_mul (-2))
    (((hasDerivAt_cosineFlux (le_refl 0) arcEnd_pos).continuousAt.tendsto).mono_left nhdsWithin_le_nhds)
    tendsto_fluxes.1
  rw [cosineFlux_zero,sub_zero,intervalIntegral.integral_const_mul] at h
  exact (mul_eq_zero.mp h).resolve_left (by norm_num)

/-- The exact sine charge retains the initial potential, with a negative sign. -/
theorem sine_arc_charge :
    (∫ t in (0:ℝ)..arcEnd, (Real.sin (t/2):ℂ)*thetaCuspStripSource ((t:ℂ)*Complex.I)) = -Potential 0/4 := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto arcEnd_pos
    (fun t ht => hasDerivAt_sineFlux ht.1.le ht.2)
    ((intervalIntegrable_axisSource_weight (fun t => (Real.sin (t/2):ℂ)) (by fun_prop)).const_mul (-2))
    (((hasDerivAt_sineFlux (le_refl 0) arcEnd_pos).continuousAt.tendsto).mono_left nhdsWithin_le_nhds)
    tendsto_fluxes.2
  rw [sineFlux_zero,intervalIntegral.integral_const_mul] at h
  linear_combination -h/2

/-- The initial theta potential is strictly positive. -/
theorem potential_zero_re_pos : 0<(Potential 0).re := by
  have ht : 0≤thetaCuspTailDerivative 0 0 := by
    unfold thetaCuspTailDerivative
    apply tsum_nonneg
    intro n
    simp only [thetaCuspTailDerivativePolynomial,thetaCuspPolynomialAtom,Polynomial.eval_one,mul_one]
    positivity
  have hp := potential_real 0
  norm_num [realJet] at hp
  rw [hp]
  simpa using (show 0<2*thetaCuspTailDerivative 0 0+1 by linarith)

/-- The source is positive at the real-axis seam. -/
theorem source_zero_re_pos : 0<(thetaCuspStripSource 0).re := by
  have hall : ∀n,0≤thetaCuspSourceTerm 0 n := by
    intro n
    cases n with
    | zero => simp [thetaCuspSourceTerm,thetaCuspSeed]
    | succ n =>
      have hn : (1:ℝ)≤n.succ := by exact_mod_cast n.succ_pos
      have hs : 0<thetaCuspSeed (n.succ:ℝ) := by
        apply thetaCuspSeed_pos
        nlinarith [Real.pi_gt_three]
      simpa [thetaCuspSourceTerm] using hs.le
  have h1 : 0<thetaCuspSourceTerm 0 1 := by
    have hs : 0<thetaCuspSeed 1 := by
      apply thetaCuspSeed_pos
      nlinarith [Real.pi_gt_three]
    simpa [thetaCuspSourceTerm] using hs
  have hp : 0<thetaCuspFullSource 0 := (summable_thetaCuspSourceTerm 0).tsum_pos hall 1 h1
  have he := thetaCuspStripSource_ofReal 0
  norm_num at he
  rw [he]
  exact hp

/-- Strictly negative sine charge forces a negative value in the open arc. -/
theorem exists_negative_axis_source :
    ∃ t : ℝ, 0<t ∧ t<arcEnd ∧ (thetaCuspStripSource ((t:ℂ)*Complex.I)).re<0 := by
  have hi := intervalIntegrable_axisSource_weight (fun t => (Real.sin (t/2):ℂ)) (by fun_prop)
  have hr := intervalIntegral.intervalIntegral_re hi
  change (∫t in (0:ℝ)..arcEnd,
    ((Real.sin (t/2):ℂ)*thetaCuspStripSource ((t:ℂ)*Complex.I)).re) =
    (∫t in (0:ℝ)..arcEnd,
    (Real.sin (t/2):ℂ)*thetaCuspStripSource ((t:ℂ)*Complex.I)).re at hr
  rw [sine_arc_charge] at hr
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] at hr
  have hire : IntervalIntegrable (fun t =>
      Real.sin (t/2)*(thetaCuspStripSource ((t:ℂ)*Complex.I)).re) volume 0 arcEnd := by
    simpa only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] using
      (show IntervalIntegrable (fun t =>
        ((Real.sin (t/2):ℂ)*thetaCuspStripSource ((t:ℂ)*Complex.I)).re) volume 0 arcEnd from
        ⟨hi.1.re,hi.2.re⟩)
  by_contra hn
  push Not at hn
  have hnonneg : 0≤∫t in (0:ℝ)..arcEnd,
      Real.sin (t/2)*(thetaCuspStripSource ((t:ℂ)*Complex.I)).re := by
    have hh := intervalIntegral.integral_mono_on_of_le_Ioo arcEnd_pos.le
      (intervalIntegrable_const (c := (0:ℝ))) hire (fun t ht => by
        have hs : 0≤Real.sin (t/2) := Real.sin_nonneg_of_mem_Icc (by
          dsimp [arcEnd] at ht
          constructor <;> linarith [ht.1,ht.2,Real.pi_pos])
        exact mul_nonneg hs (hn t ht.1 ht.2))
    simpa only [intervalIntegral.integral_zero] using hh
  have hp := potential_zero_re_pos
  rw [hr] at hnonneg
  norm_num [Complex.div_re,Complex.normSq] at hnonneg
  linarith

/-- The literal theta source has a zero strictly inside its holomorphic strip. -/
theorem exists_imaginary_source_zero :
    ∃ t : ℝ, 0<t ∧ t<arcEnd ∧ thetaCuspStripSource ((t:ℂ)*Complex.I)=0 := by
  obtain ⟨u,hu0,huL,huneg⟩ := exists_negative_axis_source
  have hc : ContinuousOn (fun t : ℝ => (thetaCuspStripSource ((t:ℂ)*Complex.I)).re) (Icc 0 u) := by
    apply (Complex.continuous_re.comp_continuousOn continuousOn_axis_source).mono
    intro t ht
    exact ⟨ht.1,ht.2.trans_lt huL⟩
  have hzero : 0<(thetaCuspStripSource (((0:ℝ):ℂ)*Complex.I)).re := by
    simpa using source_zero_re_pos
  obtain ⟨t,ht,he⟩ := intermediate_value_Icc' hu0.le hc ⟨huneg.le,hzero.le⟩
  have ht0 : 0<t := by
    refine lt_of_le_of_ne ht.1 ?_
    intro h
    subst t
    linarith
  have htL : t<arcEnd := ht.2.trans_lt huL
  refine ⟨t,ht0,htL,?_⟩
  apply Complex.ext
  · simpa using he
  · simpa using source_axis_im ht0.le htL

/-- Even an unrestricted exponential representation fails on the whole source strip. -/
theorem no_strip_exponential_representation :
    ¬∃ g : ℂ → ℂ, ∀z∈thetaCuspStrip, Complex.exp (g z)=thetaCuspStripSource z := by
  rintro ⟨g,hg⟩
  obtain ⟨t,ht0,htL,hz⟩ := exists_imaginary_source_zero
  exact Complex.exp_ne_zero (g ((t:ℂ)*Complex.I))
    ((hg _ (axis_mem_strip ht0.le htL)).trans hz)

end RHTower.ThetaImaginaryArc
