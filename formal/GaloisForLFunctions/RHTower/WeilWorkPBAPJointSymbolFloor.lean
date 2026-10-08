import GaloisForLFunctions.RHTower.WeilWorkPBAPJointGridFrequency
import GaloisForLFunctions.RHTower.WeilWorkPBAPJointSourceBudget

/-!
# A source-uniform reserve for the actual corrected cutoff symbol

The actual low, middle and high frequency estimates join the existing
Gamma logarithmic-deficit floor. Every cutoff error and product with the
source Fourier density is proved integrable. Exact Plancherel mass and the
fixed integrable deficit then give L/3 times mass for all smooth sources
in the actual narrow window, with a threshold independent of their shapes.

The two-source theorem retains arbitrary phases and relative masses. Its
literal-coefficient version pays the numerical admissibility condition
using the audited plateau integral. This is the corrected-symbol component
of MC6; the full two-source pole/atom/Gamma identities remain separate.
-/

open Real Set Filter Topology MeasureTheory Zeta23
noncomputable section
namespace RHTower.WeilWorkPBAP
open WeilOneSided

private theorem tendsto_width_mul_exp_three_eighths {b : ℝ} (hb : 0 < b) :
    Tendsto (fun L : ℝ => jointUniformWidth b L*exp (3*L/8)) atTop (𝓝 0) := by
  have hmajor : Tendsto (fun L : ℝ => b*L^2*exp (-L/8)) atTop (𝓝 0) := by
    have ht := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 2 (1/8) (by norm_num)).const_mul b
    have he (L : ℝ) : -(1/8:ℝ)*L = -L/8 := by ring
    simpa only [Real.rpow_two, he, mul_zero, mul_assoc] using ht
  apply squeeze_zero' _ _ hmajor
  · filter_upwards [eventually_jointUniformWidth_grid_bounds hb] with L hw
    have hW := hw.2.1
    positivity
  · filter_upwards [eventually_ge_atTop (1:ℝ)] with L hL
    have hll : log (log L) ≤ L :=
      (log_le_self (log_nonneg hL)).trans (log_le_self (by linarith))
    have he : exp (-L/2)*exp (3*L/8) = exp (-L/8) := by
      rw [← exp_add]
      congr 1
      ring
    unfold jointUniformWidth
    calc
      _ = b*L*log (log L)*(exp (-L/2)*exp (3*L/8)) := by ring
      _ = b*L*log (log L)*exp (-L/8) := by rw [he]
      _ ≤ b*L*L*exp (-L/8) := by gcongr
      _ = _ := by ring

/-- The literal growing width leaves a uniform linear logarithmic reserve. -/
theorem eventually_jointUniformWidth_log_bounds {b : ℝ} (hb : 0 < b) :
    ∀ᶠ L : ℝ in atTop, 3*L/8 ≤ -log (jointUniformWidth b L) ∧
      -log (jointUniformWidth b L) ≤ L/2 := by
  have hs := (tendsto_width_mul_exp_three_eighths hb).eventually
    (gt_mem_nhds (by norm_num : (0:ℝ) < 1))
  have hc := ((tendsto_log_atTop.comp tendsto_log_atTop).const_mul_atTop hb).eventually_ge_atTop (1:ℝ)
  filter_upwards [hs, hc, eventually_jointUniformWidth_grid_bounds hb,
    eventually_ge_atTop (1:ℝ)] with L hs hc hw hL
  change 1 ≤ b*log (log L) at hc
  have hL0 : 0 < L := by linarith
  have hW := hw.2.1
  have hupper : jointUniformWidth b L ≤ exp (-(3*L/8)) := by
    calc
      _ ≤ 1/exp (3*L/8) := (le_div_iff₀ (exp_pos _)).mpr hs.le
      _ = _ := by rw [exp_neg, one_div]
  have hcoeff : 1 ≤ b*L*log (log L) := by
    calc
      (1:ℝ) ≤ L := hL
      _ ≤ (b*log (log L))*L := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hc hL0.le
      _ = _ := by ring
  have hlower : exp (-L/2) ≤ jointUniformWidth b L := by
    unfold jointUniformWidth
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hcoeff (exp_pos (-L/2)).le
  have hu := log_le_log hW hupper
  have hl := log_le_log (exp_pos (-L/2)) hlower
  rw [log_exp] at hu hl
  constructor <;> linarith

/-- All frequencies share the actual Gamma-minus-grid-error floor, with one paid o(L) loss. -/
theorem exists_jointCutoff_symbol_floor {b : ℝ} (hb : 0 < b)
    (heta : (∫ y : ℝ, jointPlateau y)*b*log 2 < 1) :
    ∃ r : ℝ → ℝ, Tendsto (fun L => r L/L) atTop (𝓝 0) ∧
      ∀ᶠ L : ℝ in atTop, 0 ≤ r L ∧ ∀ t : ℝ, t ≠ 0 →
        -log (jointUniformWidth b L)-(10+log 4)-r L-
          jointLogDeficit (jointUniformWidth b L*t) ≤
            EF.gammaBracket t-2*cosh (L/2)*‖jointCutoffFourierError L (jointUniformWidth b L) t‖ := by
  let A : ℝ := ∫ y : ℝ, jointPlateau y
  have hA : 0 < A := lt_of_lt_of_le (by norm_num : (0:ℝ) < 2) jointPlateau_integral_bounds.1
  obtain ⟨rl, hrl, hl⟩ := exists_jointCutoff_low_loss hb
  obtain ⟨rm, hrm, hm⟩ := exists_jointCutoff_middle_loss hb (mul_pos hA hb) heta
  let r : ℝ → ℝ := fun L => rl L+rm L
  refine ⟨r, ?_, ?_⟩
  · simpa only [r, add_div, add_zero] using hrl.add hrm
  · filter_upwards [hl, hm, eventually_jointCutoffFourierError_high hb,
      eventually_jointUniformWidth_grid_bounds hb, eventually_jointUniformWidth_log_bounds hb,
      eventually_ge_atTop (0:ℝ)] with L hl hm hh hw hlogW hL
    refine ⟨add_nonneg hl.1 hm.1, ?_⟩
    intro t ht
    have hgamma := joint_gamma_width_lower hw.2.1 ht
    have hdef := jointLogDeficit_nonneg (jointUniformWidth b L*t)
    dsimp only [r]
    by_cases hlow : |t| ≤ exp L/sqrt L
    · have he := hl.2 t hlow
      linarith [hm.1]
    · by_cases hmiddle : |t| ≤ exp ((A*b*log (log L)+1)*L)
      · have he := hm.2 t (lt_of_not_ge hlow).le hmiddle
        linarith [hl.1]
      · have he := hh t (lt_of_not_ge hmiddle).le
        have hg := joint_gamma_lower_log t
        have hlog := log_le_log (abs_pos.mpr ht) (show |t| ≤ 2+|t| by linarith)
        linarith [hl.1, hm.1, hlogW.2]

theorem continuous_jointCutoffFourierError (L : ℝ) {W : ℝ} (hW : 0 < W) :
    Continuous (fun t : ℝ => jointCutoffFourierError L W t) := by
  have hg : Continuous (jointCutoffGridFourier L W) := by
    unfold jointCutoffGridFourier
    fun_prop
  have hf := WeilHerglotz.continuous_paperFT_real (jointFixedCutoff_integrable L hW).ofReal
  have hform (t : ℝ) : paperFT (fun y => (jointFixedCutoff L W y:ℂ)) (t:ℂ) =
      ∫ y : ℝ, (jointFixedCutoff L W y:ℂ)*Complex.exp (((t*y:ℝ):ℂ)*Complex.I) := by
    unfold paperFT
    congr 1
    funext y
    congr 1
    congr 1
    push_cast
    ring
  have hf' : Continuous (fun t : ℝ =>
      ∫ y : ℝ, (jointFixedCutoff L W y:ℂ)*Complex.exp (((t*y:ℝ):ℂ)*Complex.I)) := by
    convert hf using 1
    funext t
    exact (hform t).symm
  exact hg.sub hf'

theorem joint_source_cutoff_error_integrable (f : JointSmoothTest) (L : ℝ) {W : ℝ}
    (hW : 0 < W) :
    Integrable (fun t : ℝ => ‖paperFT f.1.1 (t:ℂ)‖^2*‖jointCutoffFourierError L W t‖) := by
  apply (joint_source_fourier_integrable f).mul_bdd
    (continuous_jointCutoffFourierError L hW).norm.aestronglyMeasurable
  filter_upwards with t
  simpa only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using
    norm_jointCutoffFourierError_le_mass L W t

theorem joint_source_cutoff_symbol_integrable (f : JointSmoothTest) (L : ℝ) {W : ℝ}
    (hW : 0 < W) :
    Integrable (fun t : ℝ => ‖paperFT f.1.1 (t:ℂ)‖^2*
      (EF.gammaBracket t-2*cosh (L/2)*‖jointCutoffFourierError L W t‖)) := by
  have h := (joint_source_gamma_integrable f).sub
    ((joint_source_cutoff_error_integrable f L hW).const_mul (2*cosh (L/2)))
  exact h.congr (Eventually.of_forall (fun t => by dsimp only [Pi.sub_apply]; ring))

/-- Integrating the actual symbol floor costs only source mass and the fixed logarithmic deficit. -/
theorem exists_joint_source_cutoff_integral_floor {b : ℝ} (hb : 0 < b)
    (heta : (∫ y : ℝ, jointPlateau y)*b*log 2 < 1) :
    ∃ r : ℝ → ℝ, Tendsto (fun L => r L/L) atTop (𝓝 0) ∧
      ∀ᶠ L : ℝ in atTop, ∀ f : JointSmoothTest,
        tsupport f.1.1 ⊆ Icc 0 (jointUniformWidth b L) →
          testMass f.1.1*(-log (jointUniformWidth b L)-(10+log 4)-r L-
            (1/(2*Real.pi))*(∫ v : ℝ, jointLogDeficit v)) ≤
              (1/(2*Real.pi))*(∫ t : ℝ, ‖paperFT f.1.1 (t:ℂ)‖^2*
                (EF.gammaBracket t-2*cosh (L/2)*‖jointCutoffFourierError L (jointUniformWidth b L) t‖)) := by
  obtain ⟨r, hr, hfloor⟩ := exists_jointCutoff_symbol_floor hb heta
  refine ⟨r, hr, ?_⟩
  filter_upwards [hfloor, eventually_jointUniformWidth_grid_bounds hb] with L hfloor hw
  intro f hf
  let W := jointUniformWidth b L
  let q := fun t : ℝ => ‖paperFT f.1.1 (t:ℂ)‖^2
  let d := -log W-(10+log 4)-r L
  have hW : 0 < W := hw.2.1
  have hq := joint_source_fourier_integrable f
  have hh := joint_source_log_deficit_integrable f hW hf
  have hi := integral_mono_ae ((hq.mul_const d).sub hh)
    (joint_source_cutoff_symbol_integrable f L hW)
    (show ∀ᵐ t : ℝ, q t*d-q t*jointLogDeficit (W*t) ≤
      q t*(EF.gammaBracket t-2*cosh (L/2)*‖jointCutoffFourierError L W t‖) from by
      filter_upwards [volume.ae_ne (0:ℝ)] with t ht
      have h := mul_le_mul_of_nonneg_left (hfloor.2 t ht) (sq_nonneg ‖paperFT f.1.1 (t:ℂ)‖)
      dsimp only [q, d, W]
      nlinarith only [h])
  change (∫ t : ℝ, q t*d-q t*jointLogDeficit (W*t)) ≤ _ at hi
  rw [integral_sub (hq.mul_const d) hh, integral_mul_const] at hi
  have hi' := mul_le_mul_of_nonneg_left hi (by positivity : 0 ≤ 1/(2*Real.pi))
  have hm := LebesgueAtomWeil.integral_norm_sq_paperFT_eq f.1.2.1 f.1.2.2
  have hd := mul_le_mul_of_nonneg_left (joint_source_log_deficit_le f hW hf)
    (by positivity : 0 ≤ 1/(2*Real.pi))
  change (1/(2*Real.pi))*(∫ t, q t) = testMass f.1.1 at hm
  change testMass f.1.1*(d-(1/(2*Real.pi))*(∫ v, jointLogDeficit v)) ≤ _
  calc
    _ = testMass f.1.1*d-(1/(2*Real.pi))*(testMass f.1.1*∫ v, jointLogDeficit v) := by ring
    _ ≤ testMass f.1.1*d-(1/(2*Real.pi))*(∫ t, q t*jointLogDeficit (W*t)) :=
      sub_le_sub_left hd _
    _ = (1/(2*Real.pi))*((∫ t, q t)*d-∫ t, q t*jointLogDeficit (W*t)) := by
      linear_combination -d*hm
    _ ≤ _ := hi'

/-- Every actual narrow source receives a uniform linear reserve from the corrected symbol. -/
theorem eventually_joint_source_cutoff_symbol_coercive {b : ℝ} (hb : 0 < b)
    (heta : (∫ y : ℝ, jointPlateau y)*b*log 2 < 1) :
    ∀ᶠ L : ℝ in atTop, ∀ f : JointSmoothTest,
      tsupport f.1.1 ⊆ Icc 0 (jointUniformWidth b L) →
        (L/3)*testMass f.1.1 ≤
          (1/(2*Real.pi))*(∫ t : ℝ, ‖paperFT f.1.1 (t:ℂ)‖^2*
            (EF.gammaBracket t-2*cosh (L/2)*‖jointCutoffFourierError L (jointUniformWidth b L) t‖)) := by
  obtain ⟨r, hr, hfloor⟩ := exists_joint_source_cutoff_integral_floor hb heta
  let C : ℝ := (10+log 4)+(1/(2*Real.pi))*(∫ v : ℝ, jointLogDeficit v)
  have hs := hr.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1/48))
  filter_upwards [hfloor, hs, eventually_jointUniformWidth_log_bounds hb,
    eventually_ge_atTop (48*C), eventually_gt_atTop (0:ℝ)] with L hf hs hw hC hL
  intro f hfs
  have hrL := (div_lt_iff₀ hL).mp hs
  have hcost : L/3 ≤ -log (jointUniformWidth b L)-(10+log 4)-r L-
      (1/(2*Real.pi))*(∫ v : ℝ, jointLogDeficit v) := by
    dsimp only [C] at hC
    linarith [hw.1]
  have hmass : 0 ≤ testMass f.1.1 := by
    unfold testMass
    exact integral_nonneg (fun t => sq_nonneg _)
  have h := mul_le_mul_of_nonneg_right hcost hmass
  exact h.trans (by simpa only [mul_comm] using hf f hfs)

/-- Two unrelated narrow sources share the same corrected-symbol reserve. -/
theorem eventually_joint_two_source_cutoff_symbol_coercive {b : ℝ} (hb : 0 < b)
    (heta : (∫ y : ℝ, jointPlateau y)*b*log 2 < 1) :
    ∀ᶠ L : ℝ in atTop, ∀ f g : JointSmoothTest,
      tsupport f.1.1 ⊆ Icc 0 (jointUniformWidth b L) →
      tsupport g.1.1 ⊆ Icc 0 (jointUniformWidth b L) →
        (L/3)*(testMass f.1.1+testMass g.1.1) ≤
          (1/(2*Real.pi))*(∫ t : ℝ,
            (‖paperFT f.1.1 (t:ℂ)‖^2+‖paperFT g.1.1 (t:ℂ)‖^2)*
              (EF.gammaBracket t-2*cosh (L/2)*‖jointCutoffFourierError L (jointUniformWidth b L) t‖)) := by
  filter_upwards [eventually_joint_source_cutoff_symbol_coercive hb heta,
    eventually_jointUniformWidth_grid_bounds hb] with L hc hw
  intro f g hf hg
  have hi1 := joint_source_cutoff_symbol_integrable f L hw.2.1
  have hi2 := joint_source_cutoff_symbol_integrable g L hw.2.1
  simp_rw [add_mul]
  rw [integral_add hi1 hi2]
  nlinarith [hc f hf, hc g hg]

/-- A literal width coefficient discharges every numerical parameter condition. -/
theorem eventually_joint_literal_two_source_cutoff_symbol_coercive :
    let b : ℝ := 1/(8*log 2)
    ∀ᶠ L : ℝ in atTop, ∀ f g : JointSmoothTest,
      tsupport f.1.1 ⊆ Icc 0 (jointUniformWidth b L) →
      tsupport g.1.1 ⊆ Icc 0 (jointUniformWidth b L) →
        (L/3)*(testMass f.1.1+testMass g.1.1) ≤
          (1/(2*Real.pi))*(∫ t : ℝ,
            (‖paperFT f.1.1 (t:ℂ)‖^2+‖paperFT g.1.1 (t:ℂ)‖^2)*
              (EF.gammaBracket t-2*cosh (L/2)*‖jointCutoffFourierError L (jointUniformWidth b L) t‖)) := by
  dsimp only
  have hl : 0 < log (2:ℝ) := log_pos (by norm_num)
  apply eventually_joint_two_source_cutoff_symbol_coercive (by positivity)
  have he : (∫ y : ℝ, jointPlateau y)*(1/(8*log 2))*log 2 =
      (∫ y : ℝ, jointPlateau y)/8 := by field_simp
  rw [he]
  linarith [jointPlateau_integral_bounds.2]

end RHTower.WeilWorkPBAP
