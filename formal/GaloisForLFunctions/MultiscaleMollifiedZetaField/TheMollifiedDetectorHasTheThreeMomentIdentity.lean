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

open scoped ComplexConjugate

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
    mollifiedZetaField, twistedMomentField, Pi.mul_apply] using he.deriv

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
  exact (hh.congr_deriv (by
    simp only [Pi.neg_apply, mollifiedLineJet]
    ring)).deriv

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
  have hi := hcont.integrable_of_hasCompactSupport (μ := volume) hcompact.mul_right
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
  have hi := hcont.integrable_of_hasCompactSupport (μ := volume) hcompact.mul_right
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
    Complex.add_re, Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im]
  norm_num only [show (2 : ℂ).re = 2 from rfl, show (2 : ℂ).im = 0 from rfl]
  ring

theorem hasDerivAt_mollifiedLineJet_height (N : ℕ) (w : ℕ → ℝ) (n : ℕ)
    {z : ℂ} (hz : ‖z‖ < 1 / 4) (t : ℝ) :
    HasDerivAt (mollifiedLineJet N w n z) (I * mollifiedLineJet N w (n + 1) z t) t := by
  have hp : HasDerivAt (fun u : ℝ => (1 / 2 : ℂ) - z + (u : ℂ) * I) I t := by
    simpa only [id_eq, Complex.ofReal_one, one_mul] using
      (((hasDerivAt_id t).ofReal_comp).mul_const I).const_add ((1 / 2 : ℂ) - z)
  exact ((hasDerivAt_mollifiedZetaFieldJet N w n (field_argument_ne_one hz t)).comp t hp).congr_deriv (by unfold mollifiedLineJet; exact mul_comm _ _)

private theorem mollifiedZetaField_sub (N : ℕ) (w v : ℕ → ℝ) :
    mollifiedZetaField N (fun n => w n - v n) =
      fun s => mollifiedZetaField N w s - mollifiedZetaField N v s := by
  funext s
  simp only [mollifiedZetaField, edPoly, Complex.ofReal_sub, sub_mul, Finset.sum_sub_distrib,
    mul_sub]

private theorem mollifiedLineJet_sub_zero (N : ℕ) (w v : ℕ → ℝ) (z : ℂ) (t : ℝ) :
    mollifiedLineJet N (fun n => w n - v n) 0 z t =
      mollifiedLineJet N w 0 z t - mollifiedLineJet N v 0 z t := by
  simp only [mollifiedLineJet, mollifiedZetaFieldJet, iteratedDeriv_zero, mollifiedZetaField_sub]

private theorem mollifiedLineJet_sub_one (N : ℕ) (w v : ℕ → ℝ)
    {z : ℂ} (hz : ‖z‖ < 1 / 4) (t : ℝ) :
    mollifiedLineJet N (fun n => w n - v n) 1 z t =
      mollifiedLineJet N w 1 z t - mollifiedLineJet N v 1 z t := by
  have hh := (hasDerivAt_mollifiedZetaFieldJet N w 0 (field_argument_ne_one hz t)).sub
    (hasDerivAt_mollifiedZetaFieldJet N v 0 (field_argument_ne_one hz t))
  have he := hh.deriv
  simp only [mollifiedZetaFieldJet, iteratedDeriv_zero, iteratedDeriv_one,
    Nat.zero_add] at he
  change deriv (fun s => mollifiedZetaField N w s - mollifiedZetaField N v s) _ = _ at he
  simpa only [mollifiedLineJet, mollifiedZetaFieldJet, iteratedDeriv_one,
    mollifiedZetaField_sub] using he

/-- Actual moment jets give the energy of the field and an arbitrary finite
coefficient correction, with both taper terms retained exactly. -/
theorem integral_mollifiedField_three_moments {p q η : ℝ} (hη : 0 < η)
    (N : ℕ) (w v : ℕ → ℝ) {d : ℝ} (hd : |d| < 1 / 4) (lam : ℝ) :
    (∫ t, blockWindow p q η t *
      ‖mollifiedLineJet N w 0 (d : ℂ) t + (lam : ℂ) * mollifiedLineJet N w 1 (d : ℂ) t -
        mollifiedLineJet N v 0 (d : ℂ) t‖ ^ 2) =
      twistedMoment d p q η N (fun n => w n - v n) - lam / 2 *
        (realTwistedMomentJet p q η N w 1 d - realTwistedMomentJet p q η N v 1 d +
          realTwistedMomentJet p q η N (fun n => w n - v n) 1 d) +
      lam ^ 2 / 4 * realTwistedMomentJet p q η N w 2 d +
      lam * (∫ t, iteratedDeriv 1 (blockWindow p q η) t *
        (mollifiedLineJet N w 0 (d : ℂ) t * conj (mollifiedLineJet N v 0 (d : ℂ) t)).im) +
      lam ^ 2 / 4 * (∫ t, iteratedDeriv 2 (blockWindow p q η) t *
        ‖mollifiedLineJet N w 0 (d : ℂ) t‖ ^ 2) := by
  have hz : ‖(d : ℂ)‖ < 1 / 4 := by simpa only [Complex.norm_real, Real.norm_eq_abs] using hd
  have hW (n : ℕ) (t : ℝ) : HasDerivAt (iteratedDeriv n (blockWindow p q η))
      (iteratedDeriv (n + 1) (blockWindow p q η) t) t := by
    simpa only [iteratedDeriv_succ] using
      (((contDiff_blockWindow p q η).of_le (by
        exact_mod_cast (show (n : ℕ∞) + 1 ≤ ⊤ from le_top))).differentiable_iteratedDeriv' n t).hasDerivAt
  have he := integral_detectorEnergy_three_moments
    (by simpa only [iteratedDeriv_zero] using hW 0) (hW 1)
    (continuous_iff_continuousAt.mpr (fun t => (hW 2 t).continuousAt))
    (hasCompactSupport_blockWindow hη)
    (hasDerivAt_mollifiedLineJet_height N w 0 hz)
    (hasDerivAt_mollifiedLineJet_height N w 1 hz) (continuous_mollifiedLineJet N w 2 hz)
    (hasDerivAt_mollifiedLineJet_height N v 0 hz) (continuous_mollifiedLineJet N v 1 hz) lam
  have hzero : (∫ t, blockWindow p q η t *
      ‖mollifiedLineJet N w 0 (d : ℂ) t - mollifiedLineJet N v 0 (d : ℂ) t‖ ^ 2) =
      twistedMoment d p q η N (fun n => w n - v n) := by
    simp_rw [← mollifiedLineJet_sub_zero]
    unfold twistedMoment mollifiedLineJet mollifiedZetaFieldJet mollifiedZetaField
    simp only [iteratedDeriv_zero, displacedLinePt, Complex.ofReal_sub,
      Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat, norm_mul, mul_pow]
  have hint (a : ℕ → ℝ) : Integrable (fun t => blockWindow p q η t *
      displacementEnergyFirst (mollifiedLineJet N a 0 (d : ℂ) t)
        (mollifiedLineJet N a 1 (d : ℂ) t)) volume := by
    apply Continuous.integrable_of_hasCompactSupport _ (hasCompactSupport_blockWindow hη).mul_right
    apply (contDiff_blockWindow p q η).continuous.mul
    unfold displacementEnergyFirst
    have hc₀ := continuous_mollifiedLineJet N a 0 hz
    have hc₁ := continuous_mollifiedLineJet N a 1 hz
    fun_prop
  have hfirst : (∫ t, blockWindow p q η t *
      (displacementEnergyFirst (mollifiedLineJet N w 0 (d : ℂ) t)
          (mollifiedLineJet N w 1 (d : ℂ) t) -
        displacementEnergyFirst (mollifiedLineJet N v 0 (d : ℂ) t)
          (mollifiedLineJet N v 1 (d : ℂ) t) +
        displacementEnergyFirst
          (mollifiedLineJet N w 0 (d : ℂ) t - mollifiedLineJet N v 0 (d : ℂ) t)
          (mollifiedLineJet N w 1 (d : ℂ) t - mollifiedLineJet N v 1 (d : ℂ) t))) =
      realTwistedMomentJet p q η N w 1 d - realTwistedMomentJet p q η N v 1 d +
        realTwistedMomentJet p q η N (fun n => w n - v n) 1 d := by
    simp_rw [← mollifiedLineJet_sub_zero, ← mollifiedLineJet_sub_one N w v hz, mul_add, mul_sub]
    have hsub := (hint w).sub (hint v)
    change Integrable (fun t => blockWindow p q η t * displacementEnergyFirst
      (mollifiedLineJet N w 0 (d : ℂ) t) (mollifiedLineJet N w 1 (d : ℂ) t) -
      blockWindow p q η t * displacementEnergyFirst
      (mollifiedLineJet N v 0 (d : ℂ) t) (mollifiedLineJet N v 1 (d : ℂ) t)) volume at hsub
    rw [integral_add hsub (hint (fun n => w n - v n)),
      integral_sub (hint w) (hint v)]
    rw [realTwistedMomentJet_one_eq_integral hη N w hd,
      realTwistedMomentJet_one_eq_integral hη N v hd,
      realTwistedMomentJet_one_eq_integral hη N (fun n => w n - v n) hd]
  rw [hzero, hfirst, ← realTwistedMomentJet_two_eq_integral hη N w hd] at he
  exact he

private theorem edPoly_real_eq_exp_sum (N : ℕ) (w : ℕ → ℝ) (s : ℂ) :
    edPoly (fun n => (w n : ℂ)) (Finset.Icc 1 N) s =
      ∑ n ∈ Finset.Icc 1 N, (w n : ℂ) * Complex.exp (-s * (Real.log n : ℂ)) := by
  unfold edPoly
  apply Finset.sum_congr rfl
  intro n hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hn0.ne'),
    ← Complex.ofReal_log hn0.le]
  congr 2
  ring

/-- Differentiation of the finite mollifier multiplies its real coefficients by `-log n`. -/
theorem hasDerivAt_edPoly_real_log_weight (N : ℕ) (w : ℕ → ℝ) (s : ℂ) :
    HasDerivAt (edPoly (fun n => (w n : ℂ)) (Finset.Icc 1 N))
      (edPoly (fun n => ((-Real.log n * w n : ℝ) : ℂ)) (Finset.Icc 1 N) s) s := by
  have hterm (n : ℕ) : HasDerivAt
      (fun z : ℂ => (w n : ℂ) * Complex.exp (-z * (Real.log n : ℂ)))
      (((-Real.log n * w n : ℝ) : ℂ) * Complex.exp (-s * (Real.log n : ℂ))) s := by
    have hh := ((Complex.hasDerivAt_exp _).comp s
      (((hasDerivAt_id s).neg).mul_const (Real.log n : ℂ))).const_mul (w n : ℂ)
    apply hh.congr_deriv
    simp only [Pi.neg_apply, id_eq]
    push_cast
    ring
  have hh := HasDerivAt.fun_sum (u := Finset.Icc 1 N) (fun n _ => hterm n)
  have he := funext (edPoly_real_eq_exp_sum N w)
  rw [← he, ← edPoly_real_eq_exp_sum N (fun n => -Real.log n * w n) s] at hh
  exact hh

/-- Coefficients of the correction `λζΨ′`. -/
def detectorCorrectionWeights (lam : ℝ) (w : ℕ → ℝ) (n : ℕ) : ℝ :=
  -lam * Real.log n * w n

/-- Coefficients of the residual field `ζ(Ψ−λΨ′)`. -/
def detectorResidualWeights (lam : ℝ) (w : ℕ → ℝ) (n : ℕ) : ℝ :=
  (1 + lam * Real.log n) * w n

private theorem correction_edPoly (N : ℕ) (w : ℕ → ℝ) (lam : ℝ) (s : ℂ) :
    edPoly (fun n => (detectorCorrectionWeights lam w n : ℂ)) (Finset.Icc 1 N) s =
      (lam : ℂ) * edPoly (fun n => ((-Real.log n * w n : ℝ) : ℂ)) (Finset.Icc 1 N) s := by
  unfold edPoly
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  unfold detectorCorrectionWeights
  push_cast
  ring

/-- The correction removes the differentiated mollifier and leaves the literal zeta detector. -/
theorem mollifiedField_detector_identity (N : ℕ) (w : ℕ → ℝ) (lam : ℝ)
    {z : ℂ} (hz : ‖z‖ < 1 / 4) (t : ℝ) :
    mollifiedLineJet N w 0 z t + (lam : ℂ) * mollifiedLineJet N w 1 z t -
      mollifiedLineJet N (detectorCorrectionWeights lam w) 0 z t =
      (riemannZeta ((1 / 2 : ℂ) - z + (t : ℂ) * I) +
        (lam : ℂ) * deriv riemannZeta ((1 / 2 : ℂ) - z + (t : ℂ) * I)) *
      edPoly (fun n => (w n : ℂ)) (Finset.Icc 1 N) ((1 / 2 : ℂ) - z + (t : ℂ) * I) := by
  let s : ℂ := (1 / 2 : ℂ) - z + (t : ℂ) * I
  have hh := (differentiableAt_riemannZeta (field_argument_ne_one hz t)).hasDerivAt.mul
    (hasDerivAt_edPoly_real_log_weight N w s)
  have hfield : mollifiedZetaFieldJet N w 1 s =
      deriv riemannZeta s * edPoly (fun n => (w n : ℂ)) (Finset.Icc 1 N) s +
        riemannZeta s * edPoly (fun n => ((-Real.log n * w n : ℝ) : ℂ)) (Finset.Icc 1 N) s := by
    change HasDerivAt (mollifiedZetaField N w) _ s at hh
    simpa only [mollifiedZetaFieldJet, iteratedDeriv_one] using hh.deriv
  change mollifiedZetaField N w s + (lam : ℂ) * mollifiedZetaFieldJet N w 1 s -
    mollifiedZetaField N (detectorCorrectionWeights lam w) s = _
  rw [hfield]
  unfold mollifiedZetaField
  rw [correction_edPoly]
  ring

/-- The literal mollified Levinson detector is exactly three real coefficient
moments and their first two displacement jets, plus explicit taper terms. -/
theorem integral_mollifiedDetector_three_moments {p q η : ℝ} (hη : 0 < η)
    (N : ℕ) (w : ℕ → ℝ) {d : ℝ} (hd : |d| < 1 / 4) (lam : ℝ) :
    (∫ t, blockWindow p q η t *
      ‖(riemannZeta (displacedLinePt d t) + (lam : ℂ) * deriv riemannZeta (displacedLinePt d t)) *
        edPoly (fun n => (w n : ℂ)) (Finset.Icc 1 N) (displacedLinePt d t)‖ ^ 2) =
      twistedMoment d p q η N (detectorResidualWeights lam w) - lam / 2 *
        (realTwistedMomentJet p q η N w 1 d -
          realTwistedMomentJet p q η N (detectorCorrectionWeights lam w) 1 d +
          realTwistedMomentJet p q η N (detectorResidualWeights lam w) 1 d) +
      lam ^ 2 / 4 * realTwistedMomentJet p q η N w 2 d +
      lam * (∫ t, iteratedDeriv 1 (blockWindow p q η) t *
        (mollifiedLineJet N w 0 (d : ℂ) t *
          conj (mollifiedLineJet N (detectorCorrectionWeights lam w) 0 (d : ℂ) t)).im) +
      lam ^ 2 / 4 * (∫ t, iteratedDeriv 2 (blockWindow p q η) t *
        ‖mollifiedLineJet N w 0 (d : ℂ) t‖ ^ 2) := by
  have hz : ‖(d : ℂ)‖ < 1 / 4 := by simpa only [Complex.norm_real, Real.norm_eq_abs] using hd
  have he := integral_mollifiedField_three_moments (p := p) (q := q) hη N w (detectorCorrectionWeights lam w) hd lam
  have hw : (fun n => w n - detectorCorrectionWeights lam w n) = detectorResidualWeights lam w := by
    funext n
    unfold detectorCorrectionWeights detectorResidualWeights
    ring
  rw [hw] at he
  simp_rw [mollifiedField_detector_identity N w lam hz] at he
  have hp (t : ℝ) : (1 / 2 : ℂ) - (d : ℂ) + (t : ℂ) * I = displacedLinePt d t := by
    simp only [displacedLinePt, Complex.ofReal_sub, Complex.ofReal_div, Complex.ofReal_one,
      Complex.ofReal_ofNat]
  simpa only [hp] using he

end GaloisForLFunctions.MultiscaleMollifiedZetaField
