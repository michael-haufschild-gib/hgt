import GaloisForLFunctions.MultiscaleMollifiedZetaField.TheDetectorEnergyComesFromThreeMoments
import Mathlib.Analysis.Calculus.Deriv.Star

/-!
# The actual mollified detector and its three coefficient moments

The product jets of zeta and the finite mollifier identify the first two
moment derivatives. The coefficient correction is the finite polynomial
with coefficients `-λ log(n) w(n)`.
-/

open Complex Filter MeasureTheory Metric Set Topology
open RHTower RHTower.ZetaGateProductAFE GaloisForLFunctions.HTGeometry

noncomputable section

namespace GaloisForLFunctions.MultiscaleMollifiedZetaField

/-- Zeta times the literal finite mollifier, as a function of the complex argument. -/
def mollifiedZetaField (N : ℕ) (w : ℕ → ℝ) (s : ℂ) : ℂ :=
  riemannZeta s * edPoly (fun n => (w n : ℂ)) (Finset.Icc 1 N) s

/-- Complex derivatives of the mollified zeta field. -/
def mollifiedZetaFieldJet (N : ℕ) (w : ℕ → ℝ) (n : ℕ) : ℂ → ℂ :=
  iteratedDeriv n (mollifiedZetaField N w)

theorem analyticAt_mollifiedZetaFieldJet (N : ℕ) (w : ℕ → ℝ) (n : ℕ)
    {s : ℂ} (hs : s ≠ 1) : AnalyticAt ℂ (mollifiedZetaFieldJet N w n) s := by
  have hf : DifferentiableOn ℂ (mollifiedZetaField N w) ({1}ᶜ : Set ℂ) := by
    intro v hv
    exact ((differentiableAt_riemannZeta hv).mul
      (differentiable_edPoly (fun n => (w n : ℂ))
        (fun n hn => (Finset.mem_Icc.mp hn).1) v)).differentiableWithinAt
  induction n with
  | zero => exact hf.analyticOnNhd isOpen_compl_singleton s hs
  | succ n ih => simpa only [mollifiedZetaFieldJet, iteratedDeriv_succ] using ih.deriv

theorem hasDerivAt_mollifiedZetaFieldJet (N : ℕ) (w : ℕ → ℝ) (n : ℕ)
    {s : ℂ} (hs : s ≠ 1) :
    HasDerivAt (mollifiedZetaFieldJet N w n) (mollifiedZetaFieldJet N w (n + 1) s) s := by
  simpa only [mollifiedZetaFieldJet, iteratedDeriv_succ] using
    (analyticAt_mollifiedZetaFieldJet N w n hs).differentiableAt.hasDerivAt

private theorem iteratedDeriv_commutes_conj {f : ℂ → ℂ}
    (hf : ∀ s, f (conj s) = conj (f s)) (n : ℕ) (s : ℂ) :
    iteratedDeriv n f (conj s) = conj (iteratedDeriv n f s) := by
  have he : (conj ∘ f ∘ conj) = f := by
    funext z
    simp [Function.comp_def, hf]
  have hh := congrFun (iteratedDeriv_conj_conj f n) (conj s)
  rw [he] at hh
  simpa [Function.comp_def] using hh

/-- Real coefficients preserve reflection for every field derivative. -/
theorem mollifiedZetaFieldJet_conj (N : ℕ) (w : ℕ → ℝ) (n : ℕ) (s : ℂ) :
    mollifiedZetaFieldJet N w n (conj s) = conj (mollifiedZetaFieldJet N w n s) := by
  apply iteratedDeriv_commutes_conj
  intro v
  unfold mollifiedZetaField
  rw [riemannZeta_conj, edPoly_conj (fun k => (w k : ℂ))
    (fun k hk => (Finset.mem_Icc.mp hk).1) (fun k _ => Complex.conj_ofReal (w k)), map_mul]

private theorem field_argument_ne_one {z : ℂ} (hz : ‖z‖ < 1 / 4) (t : ℝ) :
    (1 / 2 : ℂ) - z + (t : ℂ) * I ≠ 1 := by
  have hr := (Complex.abs_re_le_norm z).trans_lt hz
  intro he
  have hre := congrArg Complex.re he
  norm_num at hre
  linarith only [hre, (abs_lt.mp hr).1]

private theorem hasDerivAt_displacement_field_jet (N : ℕ) (w : ℕ → ℝ) (n : ℕ)
    {z : ℂ} (hz : ‖z‖ < 1 / 4) (t : ℝ) :
    HasDerivAt (fun v : ℂ => mollifiedZetaFieldJet N w n ((1 / 2 : ℂ) - v + (t : ℂ) * I))
      (-mollifiedZetaFieldJet N w (n + 1) ((1 / 2 : ℂ) - z + (t : ℂ) * I)) z := by
  have hp : HasDerivAt (fun v : ℂ => (1 / 2 : ℂ) - v + (t : ℂ) * I) (-1) z := by
    simpa using ((hasDerivAt_id z).const_sub (1 / 2 : ℂ)).add_const ((t : ℂ) * I)
  exact ((hasDerivAt_mollifiedZetaFieldJet N w n (field_argument_ne_one hz t)).comp z hp).congr_deriv (by ring)

/-- A complex field jet evaluated at the displaced vertical point. -/
def mollifiedLineJet (N : ℕ) (w : ℕ → ℝ) (n : ℕ) (z : ℂ) (t : ℝ) : ℂ :=
  mollifiedZetaFieldJet N w n ((1 / 2 : ℂ) - z + (t : ℂ) * I)

theorem mollifiedLineJet_zero (N : ℕ) (w : ℕ → ℝ) (z : ℂ) (t : ℝ) :
    mollifiedLineJet N w 0 z t = twistedMomentField N w z t := rfl

theorem mollifiedLineJet_neg (N : ℕ) (w : ℕ → ℝ) (n : ℕ) (d t : ℝ) :
    mollifiedLineJet N w n (d : ℂ) (-t) = conj (mollifiedLineJet N w n (d : ℂ) t) := by
  unfold mollifiedLineJet
  have he : (1 / 2 : ℂ) - (d : ℂ) + ((-t : ℝ) : ℂ) * I =
      conj ((1 / 2 : ℂ) - (d : ℂ) + (t : ℂ) * I) := by
    apply Complex.ext <;> simp
  rw [he, mollifiedZetaFieldJet_conj]

theorem continuous_mollifiedLineJet (N : ℕ) (w : ℕ → ℝ) (n : ℕ)
    {z : ℂ} (hz : ‖z‖ < 1 / 4) : Continuous (mollifiedLineJet N w n z) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  exact (analyticAt_mollifiedZetaFieldJet N w n (field_argument_ne_one hz t)).continuousAt.comp
    (f := fun u : ℝ => (1 / 2 : ℂ) - z + (u : ℂ) * I) (by fun_prop)

private theorem kernel_first (p q η : ℝ) (N : ℕ) (w : ℕ → ℝ)
    {z : ℂ} (hz : ‖z‖ < 1 / 4) (t : ℝ) :
    iteratedDeriv 1 (fun v : ℂ => blockWindowC p q η t *
      (twistedMomentField N w v t * twistedMomentField N w v (-t))) z =
      blockWindowC p q η t *
        (-mollifiedLineJet N w 1 z t * mollifiedLineJet N w 0 z (-t) -
          mollifiedLineJet N w 0 z t * mollifiedLineJet N w 1 z (-t)) := by
  have hh := ((hasDerivAt_displacement_field_jet N w 0 hz t).mul
    (hasDerivAt_displacement_field_jet N w 0 hz (-t))).const_mul (blockWindowC p q η t)
  have he := hh.congr_deriv (show _ = blockWindowC p q η t *
      (-mollifiedLineJet N w 1 z t * mollifiedLineJet N w 0 z (-t) -
        mollifiedLineJet N w 0 z t * mollifiedLineJet N w 1 z (-t)) by
    unfold mollifiedLineJet
    ring)
  simpa only [iteratedDeriv_one, mollifiedZetaFieldJet, iteratedDeriv_zero,
    mollifiedZetaField, twistedMomentField] using he.deriv

private theorem kernel_second (p q η : ℝ) (N : ℕ) (w : ℕ → ℝ)
    {z : ℂ} (hz : ‖z‖ < 1 / 4) (t : ℝ) :
    iteratedDeriv 2 (fun v : ℂ => blockWindowC p q η t *
      (twistedMomentField N w v t * twistedMomentField N w v (-t))) z =
      blockWindowC p q η t *
        (mollifiedLineJet N w 2 z t * mollifiedLineJet N w 0 z (-t) +
          2 * mollifiedLineJet N w 1 z t * mollifiedLineJet N w 1 z (-t) +
          mollifiedLineJet N w 0 z t * mollifiedLineJet N w 2 z (-t)) := by
  have he : iteratedDeriv 1 (fun v : ℂ => blockWindowC p q η t *
      (twistedMomentField N w v t * twistedMomentField N w v (-t))) =ᶠ[𝓝 z]
      (fun v : ℂ => blockWindowC p q η t *
        (-mollifiedLineJet N w 1 v t * mollifiedLineJet N w 0 v (-t) -
          mollifiedLineJet N w 0 v t * mollifiedLineJet N w 1 v (-t))) := by
    filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds hz] with v hv
    exact kernel_first p q η N w hv t
  have h₀ := hasDerivAt_displacement_field_jet N w 0 hz t
  have h₁ := hasDerivAt_displacement_field_jet N w 1 hz t
  have h₀m := hasDerivAt_displacement_field_jet N w 0 hz (-t)
  have h₁m := hasDerivAt_displacement_field_jet N w 1 hz (-t)
  have hh := (((h₁.neg.mul h₀m).sub (h₀.mul h₁m)).const_mul (blockWindowC p q η t))
  rw [show 2 = 1 + 1 from rfl, iteratedDeriv_succ, he.deriv_eq]
  exact (hh.congr_deriv (by unfold mollifiedLineJet; ring)).deriv

/-- The first real moment jet is the integrated first squared-field jet. -/
theorem realTwistedMomentJet_one_eq_integral {p q η : ℝ} (hη : 0 < η)
    (N : ℕ) (w : ℕ → ℝ) {d : ℝ} (hd : |d| < 1 / 4) :
    realTwistedMomentJet p q η N w 1 d =
      ∫ t, blockWindow p q η t * displacementEnergyFirst
        (mollifiedLineJet N w 0 (d : ℂ) t) (mollifiedLineJet N w 1 (d : ℂ) t) := by
  have hz : ‖(d : ℂ)‖ < 1 / 4 := by simpa only [Complex.norm_real, Real.norm_eq_abs] using hd
  have hc₀ := continuous_mollifiedLineJet N w 0 hz
  have hc₁ := continuous_mollifiedLineJet N w 1 hz
  have hcont : Continuous (fun t => blockWindowC p q η t *
      (-mollifiedLineJet N w 1 (d : ℂ) t * mollifiedLineJet N w 0 (d : ℂ) (-t) -
        mollifiedLineJet N w 0 (d : ℂ) t * mollifiedLineJet N w 1 (d : ℂ) (-t))) := by
    exact (contDiff_blockWindowC p q η).continuous.mul
      ((hc₁.neg.mul (hc₀.comp continuous_neg)).sub (hc₀.mul (hc₁.comp continuous_neg)))
  have hcompact : HasCompactSupport (blockWindowC p q η) :=
    hasCompactSupport_iteratedDeriv_blockWindowC 0 hη
  have hi := hcont.integrable_of_hasCompactSupport hcompact.mul_right
  unfold realTwistedMomentJet
  rw [iteratedDeriv_holomorphicTwistedMoment_eq_integral hη N w 1 hz]
  simp_rw [kernel_first p q η N w hz]
  change Complex.reCLM (∫ t, _) = _
  rw [← Complex.reCLM.integral_comp_comm hi]
  apply integral_congr_ae
  filter_upwards with t
  rw [mollifiedLineJet_neg, mollifiedLineJet_neg]
  simp only [Complex.reCLM_apply, blockWindowC, displacementEnergyFirst, Complex.mul_re,
    Complex.sub_re, Complex.neg_re, Complex.neg_im, Complex.conj_re, Complex.conj_im,
    Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- The second real moment jet is the integrated second squared-field jet. -/
theorem realTwistedMomentJet_two_eq_integral {p q η : ℝ} (hη : 0 < η)
    (N : ℕ) (w : ℕ → ℝ) {d : ℝ} (hd : |d| < 1 / 4) :
    realTwistedMomentJet p q η N w 2 d =
      ∫ t, blockWindow p q η t * displacementEnergySecond
        (mollifiedLineJet N w 0 (d : ℂ) t) (mollifiedLineJet N w 1 (d : ℂ) t)
        (mollifiedLineJet N w 2 (d : ℂ) t) := by
  have hz : ‖(d : ℂ)‖ < 1 / 4 := by simpa only [Complex.norm_real, Real.norm_eq_abs] using hd
  have hc (j : ℕ) := continuous_mollifiedLineJet N w j hz
  have hcont : Continuous (fun t => blockWindowC p q η t *
      (mollifiedLineJet N w 2 (d : ℂ) t * mollifiedLineJet N w 0 (d : ℂ) (-t) +
        2 * mollifiedLineJet N w 1 (d : ℂ) t * mollifiedLineJet N w 1 (d : ℂ) (-t) +
        mollifiedLineJet N w 0 (d : ℂ) t * mollifiedLineJet N w 2 (d : ℂ) (-t))) := by
    exact (contDiff_blockWindowC p q η).continuous.mul
      ((((hc 2).mul ((hc 0).comp continuous_neg)).add
        (((hc 1).const_mul 2).mul ((hc 1).comp continuous_neg))).add
          ((hc 0).mul ((hc 2).comp continuous_neg)))
  have hcompact : HasCompactSupport (blockWindowC p q η) :=
    hasCompactSupport_iteratedDeriv_blockWindowC 0 hη
  have hi := hcont.integrable_of_hasCompactSupport hcompact.mul_right
  unfold realTwistedMomentJet
  rw [iteratedDeriv_holomorphicTwistedMoment_eq_integral hη N w 2 hz]
  simp_rw [kernel_second p q η N w hz]
  change Complex.reCLM (∫ t, _) = _
  rw [← Complex.reCLM.integral_comp_comm hi]
  apply integral_congr_ae
  filter_upwards with t
  rw [mollifiedLineJet_neg, mollifiedLineJet_neg, mollifiedLineJet_neg]
  simp only [Complex.reCLM_apply, blockWindowC, displacementEnergySecond,
    ← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.mul_re, Complex.mul_im,
    Complex.add_re, Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.ofNat_re, Complex.ofNat_im]
  ring

end GaloisForLFunctions.MultiscaleMollifiedZetaField
