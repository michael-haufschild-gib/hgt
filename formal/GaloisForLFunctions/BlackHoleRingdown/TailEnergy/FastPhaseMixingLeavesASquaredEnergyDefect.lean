import GaloisForLFunctions.BlackHoleRingdown.TailEnergy.PolarizationAndPositivity
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma

/-!
# Persistent quadratic oscillation in a rapidly mixed receiver

Di Fratta–Slastikov (arXiv:2611.17543, Theorem 2.3) separate weak
density convergence from a nonzero squared deviation. In a modular
receiver the analogous defect is exactly twice the squared cross
energy. It is measured from scalar tail energies using a relative
phase that winds faster and faster as a function of the cutoff.
-/

noncomputable section
open Complex MeasureTheory Filter Topology Set
namespace GaloisForLFunctions.BlackHoleRingdown

/-- Continuity of the complex cross energy in the cutoff time. -/
theorem continuous_tailCrossEnergy (g h : CompactPulse) : Continuous (tailCrossEnergy g h) := by
  have he (p : CompactPulse) : Continuous (tailEnergy p) :=
    continuous_iff_continuousAt.mpr fun t => (hasDerivAt_tailEnergy p t).continuousAt
  simp_rw [show tailCrossEnergy g h = _ from funext (tailCrossEnergy_eq_polarization g h)]
  fun_prop

/-- Difference between the mixed reading and the sum of the two
single-channel readings at the same cutoff. -/
def phaseSweepError (g h : CompactPulse) (n t : ℝ) :=
  tailEnergy (CompactPulse.phaseMix (2*Real.pi*t*n) g h) t-tailEnergy g t-tailEnergy h t

/-- Unit phase at frequency n and cutoff t. -/
def phaseSweepCarrier (n t : ℝ) := Complex.exp (-I*((2*Real.pi*t*n:ℝ):ℂ))

theorem phaseSweepError_eq_carrier (g h : CompactPulse) (n t : ℝ) :
    phaseSweepError g h n t = 2*(phaseSweepCarrier n t*tailCrossEnergy g h t).re := by
  rw [phaseSweepError,tailEnergy_phaseMix]
  dsimp only [phaseSweepCarrier]
  rw [neg_mul]
  ring

private theorem carrier_unit (n t : ℝ) : ‖phaseSweepCarrier n t‖=1 := by
  unfold phaseSweepCarrier
  rw [show -I*((2*Real.pi*t*n:ℝ):ℂ)=((-(2*Real.pi*t*n):ℝ):ℂ)*I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

private theorem carrier_sq (n t : ℝ) : phaseSweepCarrier n t^2=phaseSweepCarrier (2*n) t := by
  unfold phaseSweepCarrier
  rw [pow_two,← Complex.exp_add]
  congr 1
  push_cast
  ring

private theorem dephase (f : ℝ → ℂ) :
    Tendsto (fun n : ℝ => ∫ t : ℝ, phaseSweepCarrier n t*f t) (cocompact ℝ) (𝓝 0) := by
  have h := Real.tendsto_integral_exp_smul_cocompact f
  apply h.congr
  intro n
  apply integral_congr_ae (Eventually.of_forall fun t => ?_)
  rw [Circle.smul_def,Real.fourierChar_apply]
  change Complex.exp _ * f t = Complex.exp _ * f t
  congr 2
  push_cast
  ring

theorem continuous_phaseSweepCarrier (n : ℝ) : Continuous (phaseSweepCarrier n) := by unfold phaseSweepCarrier; fun_prop

private theorem dephase_real_cocompact {f : ℝ → ℂ} (hc : Continuous f) (hk : HasCompactSupport f) :
    Tendsto (fun n : ℝ => ∫ t : ℝ, (phaseSweepCarrier n t*f t).re) (cocompact ℝ) (𝓝 0) := by
  have hr := Complex.continuous_re.continuousAt.tendsto.comp (dephase f)
  rw [Complex.zero_re] at hr
  apply hr.congr
  intro n
  exact (Complex.reCLM.integral_comp_comm (((continuous_phaseSweepCarrier n).mul hc).integrable_of_hasCompactSupport
    hk.mul_left)).symm

private theorem dephase_real {f : ℝ → ℂ} (hc : Continuous f) (hk : HasCompactSupport f) :
    Tendsto (fun n : ℝ => ∫ t : ℝ, (phaseSweepCarrier n t*f t).re) atTop (𝓝 0) :=
  (dephase_real_cocompact hc hk).mono_left (by rw [cocompact_eq_atBot_atTop]; exact le_sup_right)

/-- A signed sweep leaves its static term exactly at speed zero. -/
theorem signed_phase_sweep_integral {f : ℝ → ℂ} (hc : Continuous f) (hk : HasCompactSupport f)
    (v : ℝ) :
    Tendsto (fun n : ℝ => ∫ t : ℝ, (phaseSweepCarrier (v*n) t*f t).re) atTop
      (𝓝 (if v=0 then ∫ t : ℝ, (f t).re else 0)) := by
  by_cases hv : v=0
  · subst v
    simpa only [phaseSweepCarrier,zero_mul,mul_zero,Complex.ofReal_zero,Complex.exp_zero,one_mul,if_pos rfl,if_true]
      using (tendsto_const_nhds : Tendsto (fun _ : ℝ => ∫ t : ℝ, (f t).re) atTop (𝓝 _))
  · rw [if_neg hv]
    have ht : Tendsto (fun n : ℝ => v*n) atTop (cocompact ℝ) := by
      rw [cocompact_eq_atBot_atTop]
      rcases lt_or_gt_of_ne hv with h|h
      · exact (tendsto_id.const_mul_atTop_of_neg h).mono_right le_sup_left
      · exact (tendsto_id.const_mul_atTop h).mono_right le_sup_right
    exact (dephase_real_cocompact hc hk).comp ht

/-- Every continuous compactly supported test sees cancellation of the
entire interference term in the high-frequency limit. -/
theorem phase_sweep_weak_limit (g h : CompactPulse) {w : ℝ → ℝ}
    (hw : Continuous w) (hk : HasCompactSupport w) :
    Tendsto (fun n : ℝ => ∫ t : ℝ, w t*phaseSweepError g h n t) atTop (𝓝 0) := by
  let f (t : ℝ) := (w t:ℂ)*tailCrossEnergy g h t
  have hc : Continuous f := (Complex.continuous_ofReal.comp hw).mul (continuous_tailCrossEnergy g h)
  have hs : HasCompactSupport f := (hk.comp_left (g:=fun x : ℝ => (x:ℂ)) (by simp)).mul_right
  have hl := (dephase_real hc hs).const_mul 2
  rw [mul_zero] at hl
  apply hl.congr
  intro n
  rw [←integral_const_mul]
  apply integral_congr_ae (Eventually.of_forall fun t => ?_)
  rw [phaseSweepError_eq_carrier]
  dsimp only [f]
  rw [mul_left_comm,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  ring

/-- The limiting local squared deviation equals twice the cross power.
The weight can have either sign. -/
theorem phase_sweep_squared_defect (g h : CompactPulse) {w : ℝ → ℝ}
    (hw : Continuous w) (hk : HasCompactSupport w) :
    Tendsto (fun n : ℝ => ∫ t : ℝ, w t*(phaseSweepError g h n t)^2) atTop
      (𝓝 (2*∫ t : ℝ, w t*‖tailCrossEnergy g h t‖^2)) := by
  let c := tailCrossEnergy g h
  let f (t : ℝ) := (w t:ℂ)*(c t)^2
  have hf : Continuous f := (Complex.continuous_ofReal.comp hw).mul ((continuous_tailCrossEnergy g h).pow 2)
  have hs : HasCompactSupport f := (hk.comp_left (g:=fun x : ℝ => (x:ℂ)) (by simp)).mul_right
  have hc : Integrable (fun t : ℝ => w t*‖c t‖^2) :=
    (hw.mul ((continuous_tailCrossEnergy g h).norm.pow 2)).integrable_of_hasCompactSupport hk.mul_right
  have hl := ((dephase_real hf hs).comp (tendsto_id.const_mul_atTop (by norm_num : (0:ℝ)<2))).const_add
    (∫ t : ℝ,w t*‖c t‖^2)
  rw [add_zero] at hl
  apply (hl.const_mul 2).congr
  intro n
  have hn : Integrable (fun t : ℝ => (phaseSweepCarrier (2*n) t*f t).re) :=
    (Complex.continuous_re.comp ((continuous_phaseSweepCarrier (2*n)).mul hf)).integrable_of_hasCompactSupport
    ((hs.mul_left).comp_left (g:=Complex.re) rfl)
  change 2*((∫ t : ℝ,w t*‖c t‖^2)+∫ t : ℝ,(phaseSweepCarrier (2*n) t*f t).re) = _
  rw [←integral_add hc hn,←integral_const_mul]
  apply integral_congr_ae (Eventually.of_forall fun t => ?_)
  let z := phaseSweepCarrier n t*c t
  have hpow : phaseSweepCarrier (2*n) t*f t=(w t:ℂ)*z^2 := by rw [←carrier_sq]; dsimp only [f,z]; ring
  have hnorm : ‖z‖=‖c t‖ := by simp only [z,norm_mul,carrier_unit,one_mul]
  have hre : (z^2).re=2*z.re^2-‖c t‖^2 := by
    rw [←hnorm,←Complex.normSq_eq_norm_sq,Complex.normSq_apply,pow_two,Complex.mul_re]
    ring
  rw [hpow,Complex.mul_re,Complex.ofReal_im,Complex.ofReal_re,zero_mul,sub_zero,hre,phaseSweepError_eq_carrier]
  change _=w t*(2*z.re)^2
  ring

/-- For two copies of a nonzero input, the microscopic defect is
strictly positive against every nonzero nonnegative compact continuous
weight. -/
theorem one_pulse_phase_sweep_has_positive_defect (h : CompactPulse) (hh : ∃ t : ℝ, h t≠0)
    {w : ℝ → ℝ} (hw : Continuous w) (hk : HasCompactSupport w)
    (hw₀ : ∀ t, 0≤w t) (hw₁ : ∃ t, 0<w t) :
    ∃ d : ℝ, 0<d ∧ Tendsto (fun n : ℝ => ∫ t : ℝ, w t*(phaseSweepError h h n t)^2) atTop (𝓝 d) := by
  have heq (t : ℝ) : tailCrossEnergy h h t=(tailEnergy h t:ℂ) := by
    unfold tailCrossEnergy tailEnergy
    simp_rw [Complex.mul_conj,Complex.normSq_eq_norm_sq]
    exact integral_complex_ofReal
  let f := fun t : ℝ => w t*‖tailCrossEnergy h h t‖^2
  have hc : Continuous f := hw.mul ((continuous_tailCrossEnergy h h).norm.pow 2)
  obtain ⟨t,ht⟩ := hw₁
  have hn : tailCrossEnergy h h t≠0 := by
    rw [heq]; exact Complex.ofReal_ne_zero.mpr (tailEnergy_pos h hh t).ne'
  have hp : 0<f t := mul_pos ht (sq_pos_of_pos (norm_pos_iff.mpr hn))
  have hpos : 0<∫ t : ℝ,f t := hc.integral_pos_of_hasCompactSupport_nonneg_nonzero
    hk.mul_right (fun t => mul_nonneg (hw₀ t) (sq_nonneg _)) hp.ne'
  exact ⟨_,mul_pos (by norm_num) hpos,phase_sweep_squared_defect h h hw hk⟩

#print axioms phase_sweep_weak_limit
#print axioms signed_phase_sweep_integral
#print axioms phase_sweep_squared_defect
#print axioms one_pulse_phase_sweep_has_positive_defect
end GaloisForLFunctions.BlackHoleRingdown
