import GaloisForLFunctions.RHTower.XiSliceHusimiPositivity
import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaKernelEnergy
import GaloisForLFunctions.RHTower.PrimeArchThetaModularDifferentialClosure
import GaloisForLFunctions.HTGeometry.EntireLogarithm

/-!
# The Husimi density of the theta source has zeros

The Husimi positivity of the height-averaged slice (`XiSliceHusimiPositivity`) writes
`e^{σ²x²}·(height average of g_t)(x)` as the exponential transform of the Husimi density
`|V_σ(s,t)|²`.  This file shows that the Husimi density vanishes somewhere, at every resolution
`σ`, and draws the consequence for WD.

**Bargmann form.**  `V_σ(s,t) = e^{−s²/(2σ²)} B_σ(s + iσ²t)` (`gaborAmp_eq_bargmann`), where
`B_σ(w) = ∫ Φ(u) e^{−u²/(2σ²)} e^{−uw/σ²} du` is entire.

**Zeros** (`exists_bargmann_eq_zero`).  The double-exponential decay of `Φ` gives
`|B_σ(w)| ≤ exp(C(1+|w|)^{3/2})`, which is order `< 2`.  A zero-free entire function of order
`< 2` is `B(0)e^{bw}` (`exists_linear_of_ne_zero_of_growth`).  Evenness forces `b = 0`, but
`B_σ(σ²) > B_σ(0)`.  So `B_σ`, and hence the Husimi density, has a zero.

**No-go** (`not_nonneg_smoothing_eq_husimi`).  At a height `t₀` through such a zero, the Husimi
density `q(·, t₀)` is not the Gaussian smoothing (of any positive variance) of a nonnegative
function, unless that function vanishes almost everywhere.  Every density for the heated height
average with heat constant `κ < 1` would give such a smoothing.  So below the Husimi constant,
WD positivity can never come from a nonnegative phase-space density.  It must come from
cancellation in the moments.  This is the theta-source case of the Lütkenhaus–Barnett
nonclassical depth law.
-/

open Complex MeasureTheory Real

namespace RHTower

noncomputable section

open HedenmalmThetaSource

/-- The Gaussian-damped theta source `Φ(u) e^{−u²/(2σ²)}`. -/
def dampedThetaSource (σ u : ℝ) : ℝ := thetaCuspFullSource u * Real.exp (-(u ^ 2 / (2 * σ ^ 2)))

/-- The Bargmann transform `B_σ(w) = ∫ Φ(u) e^{−u²/(2σ²)} e^{−uw/σ²} du`. -/
def thetaBargmann (σ : ℝ) (w : ℂ) : ℂ :=
  ∫ u : ℝ, cexp (-(u * w / σ ^ 2)) * (dampedThetaSource σ u : ℂ)

theorem dampedThetaSource_nonneg (σ u : ℝ) : 0 ≤ dampedThetaSource σ u :=
  mul_nonneg (thetaCuspFullSource_pos u).le (Real.exp_pos _).le

theorem dampedThetaSource_le (σ u : ℝ) : dampedThetaSource σ u ≤ thetaCuspFullSource u := by
  unfold dampedThetaSource
  refine mul_le_of_le_one_right (thetaCuspFullSource_pos u).le ?_
  rw [Real.exp_le_one_iff, neg_nonpos]
  positivity

theorem dampedThetaSource_neg (σ u : ℝ) : dampedThetaSource σ (-u) = dampedThetaSource σ u := by
  simp [dampedThetaSource, thetaCuspFullSource_neg]

theorem expMomentSource_dampedThetaSource (σ : ℝ) :
    ExpMomentSource (fun u => (dampedThetaSource σ u : ℂ)) := by
  refine ⟨?_, fun c => ?_⟩
  · unfold dampedThetaSource
    exact Complex.continuous_ofReal.comp
      (contDiff_thetaCuspFullSource.continuous.mul (by fun_prop))
  · refine (integrable_exp_abs_mul_thetaCuspFullSource c).mono' ?_
      (Filter.Eventually.of_forall fun u => ?_)
    · unfold dampedThetaSource
      exact (Continuous.mul (by fun_prop) (continuous_norm.comp
        (Complex.continuous_ofReal.comp (contDiff_thetaCuspFullSource.continuous.mul
          (by fun_prop))))).aestronglyMeasurable
    · rw [Real.norm_eq_abs, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (dampedThetaSource_nonneg σ u),
        abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (dampedThetaSource_nonneg σ u))]
      exact mul_le_mul_of_nonneg_left (dampedThetaSource_le σ u) (Real.exp_pos _).le

theorem thetaBargmann_eq_sourceTransform {σ : ℝ} (hσ : 0 < σ) (w : ℂ) :
    thetaBargmann σ w =
      sourceTransform (fun u => (dampedThetaSource σ u : ℂ)) (-I * w / σ ^ 2) := by
  unfold thetaBargmann sourceTransform
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  have hσ0 : (σ : ℂ) ≠ 0 := ofReal_ne_zero.mpr hσ.ne'
  simp only
  congr 2
  field_simp
  ring_nf
  rw [I_sq]
  ring

theorem differentiable_thetaBargmann {σ : ℝ} (hσ : 0 < σ) :
    Differentiable ℂ (thetaBargmann σ) := by
  have h := (expMomentSource_dampedThetaSource σ).differentiable_sourceTransform
  have e : thetaBargmann σ = fun w => sourceTransform (fun u => (dampedThetaSource σ u : ℂ))
      (-I * w / σ ^ 2) := funext (thetaBargmann_eq_sourceTransform hσ)
  rw [e]
  exact h.comp (by fun_prop)

/-- `xA ≤ A√A + 2x³` for `x, A ≥ 0`. -/
theorem mul_le_mul_sqrt_add_two_mul_cube {x A : ℝ} (hx : 0 ≤ x) (hA : 0 ≤ A) :
    x * A ≤ A * Real.sqrt A + 2 * x ^ 3 := by
  rcases le_total (x ^ 2) A with h | h
  · have hxs : x ≤ Real.sqrt A := Real.le_sqrt_of_sq_le h
    have : x * A ≤ Real.sqrt A * A := mul_le_mul_of_nonneg_right hxs hA
    nlinarith [pow_nonneg hx 3]
  · have : x * A ≤ x * x ^ 2 := mul_le_mul_of_nonneg_left h hx
    have e : x * x ^ 2 = x ^ 3 := by ring
    nlinarith [pow_nonneg hx 3, mul_nonneg hA (Real.sqrt_nonneg A)]

/-- **Envelope moment bound.**  For `x, R ≥ 0`,
`e^{9x/2} e^{−πe^{2x}} e^{xR} ≤ e^{A√A} e^{2−2x}` with `A = R + 9/2`. -/
theorem thetaEnvelope_mul_exp_le {x R : ℝ} (hx : 0 ≤ x) (hR : 0 ≤ R) :
    thetaEnvelope x * Real.exp (x * R) ≤
      Real.exp ((R + 9 / 2) * Real.sqrt (R + 9 / 2)) * Real.exp (2 - 2 * x) := by
  unfold thetaEnvelope
  rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hA : 0 ≤ R + 9 / 2 := by linarith
  have h1 := mul_le_mul_sqrt_add_two_mul_cube hx hA
  have hexp : 1 + 2 * x + 2 * x ^ 2 + 4 / 3 * x ^ 3 ≤ Real.exp (2 * x) := by
    have h := Real.sum_le_exp_of_nonneg (by linarith : (0 : ℝ) ≤ 2 * x) 4
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h
    norm_num at h
    nlinarith
  have hpi : 3 < Real.pi := Real.pi_gt_three
  have hcube : x - 1 ≤ x ^ 3 := by nlinarith [sq_nonneg (x - 1), sq_nonneg x]
  have hx3 : 0 ≤ x ^ 3 := pow_nonneg hx 3
  nlinarith

/-- The theta source is dominated by its envelope at `|u|`. -/
theorem thetaCuspFullSource_le_envelope_abs (u : ℝ) :
    thetaCuspFullSource u ≤ thetaEnvelopeUpper * thetaEnvelope |u| := by
  rcases le_total 0 u with hu | hu
  · rw [abs_of_nonneg hu]; exact thetaCuspFullSource_le_envelope hu
  · rw [abs_of_nonpos hu, ← thetaCuspFullSource_neg u]
    exact thetaCuspFullSource_le_envelope (by linarith)

theorem thetaEnvelopeUpper_nonneg : 0 ≤ thetaEnvelopeUpper := by
  unfold thetaEnvelopeUpper
  have := thetaCuspHigherAtomDominationWeight_nonneg
  positivity

/-- **Order `3/2` growth of the Bargmann transform.** -/
theorem exists_norm_thetaBargmann_le {σ : ℝ} (hσ : 0 < σ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : ℂ, ‖thetaBargmann σ w‖ ≤
      Real.exp (C * (1 + ‖w‖) ^ (3 / 2 : ℝ)) := by
  set U := thetaEnvelopeUpper with hU
  have hU0 : 0 ≤ U := thetaEnvelopeUpper_nonneg
  have hint2 : Integrable (fun u : ℝ => Real.exp (2 - 2 * |u|)) := by
    have h := (integrable_exp_neg_abs_line.comp_mul_left' (by norm_num : (2 : ℝ) ≠ 0)).const_mul
      (Real.exp 2)
    refine h.congr (Filter.Eventually.of_forall fun u => ?_)
    simp only [abs_mul, abs_two]
    rw [← Real.exp_add]
    ring_nf
  set M : ℝ := ∫ u : ℝ, U * Real.exp (2 - 2 * |u|) with hM
  have hM0 : 0 ≤ M := integral_nonneg fun u => mul_nonneg hU0 (Real.exp_pos _).le
  set k : ℝ := 1 / σ ^ 2 + 9 / 2 with hk
  have hk0 : 0 ≤ k := by positivity
  refine ⟨k * Real.sqrt k + Real.log (1 + M),
    add_nonneg (mul_nonneg hk0 (Real.sqrt_nonneg _)) (Real.log_nonneg (by linarith)), fun w => ?_⟩
  set R : ℝ := ‖w‖ / σ ^ 2 with hR
  have hR0 : 0 ≤ R := by positivity
  set A : ℝ := R + 9 / 2 with hA
  have hA0 : 0 ≤ A := by positivity
  -- pointwise bound
  have hpt : ∀ u : ℝ, ‖cexp (-(u * w / σ ^ 2)) * (dampedThetaSource σ u : ℂ)‖ ≤
      Real.exp (A * Real.sqrt A) * (U * Real.exp (2 - 2 * |u|)) := by
    intro u
    rw [norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (dampedThetaSource_nonneg σ u)]
    have hre : (-((u : ℂ) * w / (σ : ℂ) ^ 2)).re ≤ |u| * R := by
      have e : (-((u : ℂ) * w / (σ : ℂ) ^ 2)) = (-((u : ℂ) * w)) / ((σ ^ 2 : ℝ) : ℂ) := by
        push_cast; ring
      have : (-((u : ℂ) * w / (σ : ℂ) ^ 2)).re = -(u * w.re) / σ ^ 2 := by
        rw [e, Complex.div_ofReal_re]
        simp
      rw [this, hR, mul_div_assoc']
      apply div_le_div_of_nonneg_right _ (by positivity)
      have := Complex.abs_re_le_norm w
      have h2 : -(u * w.re) ≤ |u * w.re| := neg_le_abs _
      rw [abs_mul] at h2
      nlinarith [abs_nonneg u]
    calc Real.exp (-((u : ℂ) * w / (σ : ℂ) ^ 2)).re * dampedThetaSource σ u
        ≤ Real.exp (|u| * R) * (U * thetaEnvelope |u|) :=
          mul_le_mul (Real.exp_le_exp.mpr hre)
            ((dampedThetaSource_le σ u).trans (thetaCuspFullSource_le_envelope_abs u))
            (dampedThetaSource_nonneg σ u) (Real.exp_pos _).le
      _ = U * (thetaEnvelope |u| * Real.exp (|u| * R)) := by ring
      _ ≤ U * (Real.exp (A * Real.sqrt A) * Real.exp (2 - 2 * |u|)) :=
          mul_le_mul_of_nonneg_left (thetaEnvelope_mul_exp_le (abs_nonneg u) hR0) hU0
      _ = _ := by ring
  have hbound : ‖thetaBargmann σ w‖ ≤ Real.exp (A * Real.sqrt A) * M := by
    unfold thetaBargmann
    refine (norm_integral_le_integral_norm _).trans ?_
    rw [hM, ← integral_const_mul]
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun u => norm_nonneg _)
      ((hint2.const_mul U).const_mul _) (Filter.Eventually.of_forall hpt)
  -- compare with the growth envelope
  have hAk : A ≤ k * (1 + ‖w‖) := by
    rw [hA, hR, hk]
    have : ‖w‖ / σ ^ 2 = 1 / σ ^ 2 * ‖w‖ := by ring
    rw [this]
    nlinarith [norm_nonneg w, (by positivity : (0 : ℝ) ≤ 1 / σ ^ 2)]
  have hsq : Real.sqrt A ≤ Real.sqrt k * Real.sqrt (1 + ‖w‖) := by
    rw [← Real.sqrt_mul hk0]; exact Real.sqrt_le_sqrt hAk
  have hpow : (1 + ‖w‖) ^ (3 / 2 : ℝ) = (1 + ‖w‖) * Real.sqrt (1 + ‖w‖) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_one_add' (by positivity) (by norm_num)]
    norm_num
  have hge1 : 1 ≤ (1 + ‖w‖) ^ (3 / 2 : ℝ) := Real.one_le_rpow (by linarith [norm_nonneg w])
    (by norm_num)
  have hAA : A * Real.sqrt A ≤ k * Real.sqrt k * (1 + ‖w‖) ^ (3 / 2 : ℝ) := by
    rw [hpow]
    have := mul_le_mul hAk hsq (Real.sqrt_nonneg _) (by positivity)
    nlinarith [Real.sqrt_nonneg k, Real.sqrt_nonneg (1 + ‖w‖)]
  have hlog : M ≤ Real.exp (Real.log (1 + M) * (1 + ‖w‖) ^ (3 / 2 : ℝ)) := by
    have h1 : M ≤ Real.exp (Real.log (1 + M)) := by
      rw [Real.exp_log (by linarith)]; linarith
    refine h1.trans (Real.exp_le_exp.mpr ?_)
    have hl : 0 ≤ Real.log (1 + M) := Real.log_nonneg (by linarith)
    nlinarith
  calc ‖thetaBargmann σ w‖ ≤ Real.exp (A * Real.sqrt A) * M := hbound
    _ ≤ Real.exp (k * Real.sqrt k * (1 + ‖w‖) ^ (3 / 2 : ℝ)) *
        Real.exp (Real.log (1 + M) * (1 + ‖w‖) ^ (3 / 2 : ℝ)) :=
        mul_le_mul (Real.exp_le_exp.mpr hAA) hlog hM0 (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; ring_nf

theorem integrable_exp_mul_dampedThetaSource (σ b : ℝ) :
    Integrable (fun u => Real.exp (b * u) * dampedThetaSource σ u) := by
  refine (RHTower.HedenmalmThetaSource.integrable_exp_mul_thetaCuspFullSource b).mono' ?_
    (Filter.Eventually.of_forall fun u => ?_)
  · unfold dampedThetaSource
    exact ((by fun_prop : Continuous fun u : ℝ => Real.exp (b * u)).mul
      (contDiff_thetaCuspFullSource.continuous.mul (by fun_prop))).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le
      (dampedThetaSource_nonneg σ u))]
    exact mul_le_mul_of_nonneg_left (dampedThetaSource_le σ u) (Real.exp_pos _).le

/-- The Bargmann transform is even. -/
theorem thetaBargmann_neg (σ : ℝ) (w : ℂ) : thetaBargmann σ (-w) = thetaBargmann σ w := by
  unfold thetaBargmann
  rw [← integral_neg_eq_self]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  simp only [dampedThetaSource_neg, ofReal_neg]
  congr 2
  ring

/-- On the real axis the Bargmann transform is a real Laplace integral. -/
theorem thetaBargmann_ofReal (σ x : ℝ) :
    thetaBargmann σ (x : ℂ) =
      ((∫ u : ℝ, Real.exp (-x / σ ^ 2 * u) * dampedThetaSource σ u : ℝ) : ℂ) := by
  unfold thetaBargmann
  rw [← integral_complex_ofReal]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  push_cast
  congr 2
  ring

/-- The real Laplace integral `I(x) = ∫ e^{−xu/σ²} Φ(u) e^{−u²/(2σ²)} du`. -/
def thetaBargmannReal (σ x : ℝ) : ℝ := ∫ u : ℝ, Real.exp (-x / σ ^ 2 * u) * dampedThetaSource σ u

theorem thetaBargmannReal_zero_pos (σ : ℝ) : 0 < thetaBargmannReal σ 0 := by
  unfold thetaBargmannReal
  have hpos : ∀ u, 0 < Real.exp (-0 / σ ^ 2 * u) * dampedThetaSource σ u := fun u =>
    mul_pos (Real.exp_pos _) (mul_pos (thetaCuspFullSource_pos u) (Real.exp_pos _))
  refine (integral_pos_iff_support_of_nonneg (fun u => (hpos u).le)
    (integrable_exp_mul_dampedThetaSource σ _)).mpr ?_
  have : Function.support (fun u => Real.exp (-0 / σ ^ 2 * u) * dampedThetaSource σ u) =
      Set.univ := Set.eq_univ_of_forall fun u => (hpos u).ne'
  rw [this, Real.volume_univ]
  exact ENNReal.zero_lt_top

/-- **Strict growth on the real axis:** `I(σ²) > I(0)`. -/
theorem thetaBargmannReal_zero_lt {σ : ℝ} (hσ : 0 < σ) :
    thetaBargmannReal σ 0 < thetaBargmannReal σ (σ ^ 2) := by
  unfold thetaBargmannReal
  have hσ2 : σ ^ 2 ≠ 0 := by positivity
  have h1 : -(σ ^ 2) / σ ^ 2 = -1 := by field_simp
  have h0 : -(0 : ℝ) / σ ^ 2 = 0 := by simp
  simp only [h1, h0, zero_mul, Real.exp_zero, one_mul]
  -- evenness of the damped source
  have heven : ∫ u : ℝ, Real.exp (-1 * u) * dampedThetaSource σ u =
      ∫ u : ℝ, Real.exp (1 * u) * dampedThetaSource σ u := by
    rw [← integral_neg_eq_self]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    simp [dampedThetaSource_neg]
  have hA := integrable_exp_mul_dampedThetaSource σ (-1)
  have hB := integrable_exp_mul_dampedThetaSource σ 1
  have hC : Integrable (fun u => dampedThetaSource σ u) := by
    simpa using integrable_exp_mul_dampedThetaSource σ 0
  set f : ℝ → ℝ := fun u => (Real.exp (-1 * u) + Real.exp (1 * u) - 2) * dampedThetaSource σ u
    with hf
  have hf0 : ∀ u, 0 ≤ f u := by
    intro u
    refine mul_nonneg ?_ (dampedThetaSource_nonneg σ u)
    have := Real.add_one_le_exp (-1 * u)
    have := Real.add_one_le_exp (1 * u)
    linarith
  have hfint : Integrable f := by
    refine ((hA.add hB).sub (hC.const_mul 2)).congr (Filter.Eventually.of_forall fun u => ?_)
    simp only [hf, Pi.add_apply, Pi.sub_apply]
    ring
  have hfpos : 0 < ∫ u, f u := by
    refine (integral_pos_iff_support_of_nonneg hf0 hfint).mpr ?_
    have hsub : Set.Ioi (0 : ℝ) ⊆ Function.support f := by
      intro u hu
      have hu' : (0 : ℝ) < u := hu
      have h2 : 2 < Real.exp (-1 * u) + Real.exp (1 * u) := by
        have h3 : Real.exp (-1 * u) * Real.exp (1 * u) = 1 := by
          rw [← Real.exp_add]; ring_nf; exact Real.exp_zero
        have h4 : Real.exp (-1 * u) < Real.exp (1 * u) :=
          Real.exp_lt_exp.mpr (by linarith)
        nlinarith [Real.exp_pos (-1 * u), Real.exp_pos (1 * u), sq_nonneg (Real.exp (-1 * u) -
          Real.exp (1 * u))]
      exact (mul_pos (by linarith) (mul_pos (thetaCuspFullSource_pos u)
        (Real.exp_pos _))).ne'
    calc (0 : ENNReal) < volume (Set.Ioi (0 : ℝ)) := by rw [Real.volume_Ioi]; exact ENNReal.zero_lt_top
      _ ≤ _ := measure_mono hsub
  have hsplit : ∫ u, f u = (∫ u : ℝ, Real.exp (-1 * u) * dampedThetaSource σ u) +
      (∫ u : ℝ, Real.exp (1 * u) * dampedThetaSource σ u) - 2 * ∫ u, dampedThetaSource σ u := by
    have h1 := integral_sub (hA.add hB) (hC.const_mul 2)
    have h2 := integral_add hA hB
    have h3 := integral_const_mul (μ := volume) (2 : ℝ) (fun u => dampedThetaSource σ u)
    simp only [Pi.add_apply] at h1 h2
    rw [← h2, ← h3, ← h1]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    simp only [hf]
    ring
  linarith

/-- **The Bargmann transform has a zero.** -/
theorem exists_thetaBargmann_eq_zero {σ : ℝ} (hσ : 0 < σ) : ∃ w : ℂ, thetaBargmann σ w = 0 := by
  by_contra hne
  push Not at hne
  obtain ⟨C, hC, hgrow⟩ := exists_norm_thetaBargmann_le hσ
  obtain ⟨b, hb⟩ := GaloisForLFunctions.HTGeometry.exists_linear_of_ne_zero_of_growth
    (differentiable_thetaBargmann hσ) hne (by norm_num : (0 : ℝ) ≤ 3 / 2)
    (by norm_num : (3 / 2 : ℝ) < 2) hC hgrow
  have hplus := hb ((σ ^ 2 : ℝ) : ℂ)
  have hminus := hb (-((σ ^ 2 : ℝ) : ℂ))
  rw [thetaBargmann_neg] at hminus
  have hsq : thetaBargmann σ ((σ ^ 2 : ℝ) : ℂ) ^ 2 = thetaBargmann σ 0 ^ 2 := by
    calc thetaBargmann σ ((σ ^ 2 : ℝ) : ℂ) ^ 2 =
          thetaBargmann σ ((σ ^ 2 : ℝ) : ℂ) * thetaBargmann σ ((σ ^ 2 : ℝ) : ℂ) := sq _
      _ = (thetaBargmann σ 0 * cexp (b * ((σ ^ 2 : ℝ) : ℂ))) *
          (thetaBargmann σ 0 * cexp (b * -((σ ^ 2 : ℝ) : ℂ))) := by
          nth_rewrite 1 [hplus]; rw [← hminus]
      _ = thetaBargmann σ 0 ^ 2 * cexp (b * ((σ ^ 2 : ℝ) : ℂ) + b * -((σ ^ 2 : ℝ) : ℂ)) := by
          rw [Complex.exp_add]; ring
      _ = thetaBargmann σ 0 ^ 2 := by
          rw [show b * ((σ ^ 2 : ℝ) : ℂ) + b * -((σ ^ 2 : ℝ) : ℂ) = 0 by ring, Complex.exp_zero,
            mul_one]
  rw [thetaBargmann_ofReal, show (0 : ℂ) = ((0 : ℝ) : ℂ) by simp, thetaBargmann_ofReal,
    ← ofReal_pow, ← ofReal_pow] at hsq
  have hreal := ofReal_injective hsq
  have h0 := thetaBargmannReal_zero_pos σ
  have hlt := thetaBargmannReal_zero_lt hσ
  unfold thetaBargmannReal at h0 hlt
  nlinarith

/-- **Bargmann form of the Gabor amplitude:** `V_σ(s,t) = e^{−s²/(2σ²)} B_σ(s + iσ²t)`. -/
theorem gaborAmp_eq_bargmann {σ : ℝ} (hσ : 0 < σ) (t s : ℝ) :
    gaborAmp thetaCuspFullSource σ t s =
      ((Real.exp (-(s ^ 2 / (2 * σ ^ 2))) : ℝ) : ℂ) *
        thetaBargmann σ ((s : ℂ) + I * ((σ ^ 2 * t : ℝ) : ℂ)) := by
  unfold gaborAmp thetaBargmann
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  have hσ0 : (σ : ℂ) ≠ 0 := ofReal_ne_zero.mpr hσ.ne'
  simp only [dampedThetaSource, ofReal_mul, ofReal_exp]
  set E₁ : ℂ := (((-((u + s) ^ 2 / (2 * σ ^ 2))) : ℝ) : ℂ) with hE₁
  set E₂ : ℂ := (((-(s ^ 2 / (2 * σ ^ 2))) : ℝ) : ℂ) with hE₂
  set E₃ : ℂ := -((u : ℂ) * ((s : ℂ) + I * (((σ ^ 2 : ℝ) : ℂ) * (t : ℂ))) / (σ : ℂ) ^ 2) with hE₃
  set E₄ : ℂ := (((-(u ^ 2 / (2 * σ ^ 2))) : ℝ) : ℂ) with hE₄
  have key : E₁ + -I * t * u = E₂ + E₃ + E₄ := by
    simp only [hE₁, hE₂, hE₃, hE₄]
    push_cast
    field_simp
    ring
  calc (thetaCuspFullSource u : ℂ) * cexp E₁ * cexp (-I * t * u)
      = (thetaCuspFullSource u : ℂ) * cexp (E₁ + -I * t * u) := by rw [Complex.exp_add]; ring
    _ = (thetaCuspFullSource u : ℂ) * cexp (E₂ + E₃ + E₄) := by rw [key]
    _ = cexp E₂ * (cexp E₃ * ((thetaCuspFullSource u : ℂ) * cexp E₄)) := by
        rw [Complex.exp_add, Complex.exp_add]; ring

/-- **The Husimi density vanishes somewhere**, at every resolution `σ`. -/
theorem exists_gaborAmp_eq_zero {σ : ℝ} (hσ : 0 < σ) :
    ∃ s t : ℝ, gaborAmp thetaCuspFullSource σ t s = 0 := by
  obtain ⟨w, hw⟩ := exists_thetaBargmann_eq_zero hσ
  refine ⟨w.re, w.im / σ ^ 2, ?_⟩
  rw [gaborAmp_eq_bargmann hσ]
  have hσ2 : σ ^ 2 ≠ 0 := by positivity
  have : (w.re : ℂ) + I * ((σ ^ 2 * (w.im / σ ^ 2) : ℝ) : ℂ) = w := by
    rw [mul_div_cancel₀ _ hσ2, mul_comm I]
    exact Complex.re_add_im w
  rw [this, hw, mul_zero]

/-- The Husimi density does not vanish identically along any height line. -/
theorem exists_gaborAmp_ne_zero {σ : ℝ} (hσ : 0 < σ) (t : ℝ) :
    ∃ s : ℝ, gaborAmp thetaCuspFullSource σ t s ≠ 0 := by
  by_contra hall
  push Not at hall
  set z₀ : ℂ := I * ((σ ^ 2 * t : ℝ) : ℂ) with hz₀
  have hB : ∀ s : ℝ, thetaBargmann σ ((s : ℂ) + z₀) = 0 := by
    intro s
    have h := hall s
    rw [gaborAmp_eq_bargmann hσ] at h
    exact (mul_eq_zero.mp h).resolve_left (ofReal_ne_zero.mpr (Real.exp_pos _).ne')
  have han : AnalyticOnNhd ℂ (thetaBargmann σ) Set.univ :=
    fun z _ => (differentiable_thetaBargmann hσ).analyticAt z
  have htend : Filter.Tendsto (fun n : ℕ => ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) + z₀)
      Filter.atTop (nhdsWithin z₀ {z₀}ᶜ) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, Filter.Eventually.of_forall fun n => ?_⟩
    · have h := ((Complex.continuous_ofReal.tendsto 0).comp
        tendsto_one_div_add_atTop_nhds_zero_nat).add_const z₀
      simpa using h
    · simp only [Set.mem_compl_iff, Set.mem_singleton_iff, add_eq_right, ofReal_eq_zero]
      positivity
  have hfreq : ∃ᶠ z in nhdsWithin z₀ {z₀}ᶜ, thetaBargmann σ z = 0 :=
    htend.frequently (Filter.Frequently.of_forall fun n => hB _)
  have heq := han.eqOn_zero_of_preconnected_of_frequently_eq_zero isPreconnected_univ
    (Set.mem_univ z₀) hfreq
  have h0 := heq (Set.mem_univ (((0 : ℝ) : ℂ)))
  rw [Pi.zero_apply, thetaBargmann_ofReal] at h0
  have hpos := thetaBargmannReal_zero_pos σ
  unfold thetaBargmannReal at hpos
  exact absurd (ofReal_eq_zero.mp h0) hpos.ne'

/-- **No nonnegative density below the Husimi constant.**  There is a height `t₀` at which the
Husimi density `q(·,t₀) = |V_σ(·,t₀)|²` of the theta source is not the smoothing, by any strictly
positive kernel, of a nonnegative function. -/
theorem not_nonneg_smoothing_eq_husimi {σ : ℝ} (hσ : 0 < σ) :
    ∃ t₀ : ℝ, ∀ K : ℝ → ℝ, (∀ y, 0 < K y) → ¬ ∃ ρ : ℝ → ℝ, (∀ s, 0 ≤ ρ s) ∧
      (∀ s, Integrable (fun s' => ρ s' * K (s - s'))) ∧
      ∀ s, Complex.normSq (gaborAmp thetaCuspFullSource σ t₀ s) = ∫ s', ρ s' * K (s - s') := by
  obtain ⟨s₀, t₀, hzero⟩ := exists_gaborAmp_eq_zero hσ
  refine ⟨t₀, fun K hK ⟨ρ, hρ, hint, hrep⟩ => ?_⟩
  have hρae : ρ =ᵐ[volume] 0 := by
    have h0 : ∫ s', ρ s' * K (s₀ - s') = 0 := by
      rw [← hrep s₀, hzero, map_zero]
    have hae := (integral_eq_zero_iff_of_nonneg (fun s' => mul_nonneg (hρ s') (hK _).le)
      (hint s₀)).mp h0
    filter_upwards [hae] with s' hs'
    exact (mul_eq_zero.mp hs').resolve_right (hK _).ne'
  obtain ⟨s₁, hs₁⟩ := exists_gaborAmp_ne_zero hσ t₀
  apply hs₁
  have h1 : Complex.normSq (gaborAmp thetaCuspFullSource σ t₀ s₁) = 0 := by
    rw [hrep s₁]
    have : (fun s' => ρ s' * K (s₁ - s')) =ᵐ[volume] 0 := by
      filter_upwards [hρae] with s' hs'
      simp [hs']
    rw [integral_congr_ae this]
    simp
  exact Complex.normSq_eq_zero.mp h1

end

end RHTower
