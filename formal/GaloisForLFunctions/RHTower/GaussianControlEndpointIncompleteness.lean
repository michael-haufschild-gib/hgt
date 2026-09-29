import GaloisForLFunctions.RHTower.ThetaEndpointHarmonicCompleteness
import GaloisForLFunctions.HTGeometry.GaussianPairControlQuotient

/-!
# The Gaussian control fails the weighted `L¹` real-zero completeness test

For the positive even control `k_G(x) = [e^{-(x-a)²} + e^{-(x+a)²}]/2` with `aω = 2π`, `ω ≠ 0`, the
transform `F_G(z) = √π e^{-z²/4} cos(az)` has only real zeros.  Nevertheless the bounded even
function `g = cos(ω·) − e^{−ω²/4}` has zero `μ_G`-mean and annihilates every real-zero jet of `F_G`:
the source `k_G g` has transform `F_G (q_G − e^{−ω²/4})` with `q_G = e^{−ω²/4} cosh(ω z/2)`.  Since
`∫ g² dμ_G > 0`, `g` lies outside the `L¹(μ_G)` closure of `span({1} ∪ V_G)`.  The endpoint
completeness of the theta real-zero jets is therefore specific to the theta source.
-/
open MeasureTheory Set Filter Topology Complex
open scoped ENNReal NNReal

namespace RHTower

noncomputable section

/-! ## Exponential moments of the Gaussian control -/

theorem integrable_exp_neg_sq_add_real (b d : ℝ) :
    Integrable fun x : ℝ => Real.exp (-x ^ 2 + b * x + d) := by
  refine (HTGeometry.integrable_cexp_neg_sq_add b d).norm.congr (ae_of_all _ fun x => ?_)
  simp only [Complex.norm_exp]
  congr 1
  simp [sq]

theorem integrable_exp_mul_abs_mul_gaussPairSource (a c : ℝ) :
    Integrable fun x => Real.exp (c * |x|) * HTGeometry.gaussPairSource a x := by
  have hG : Integrable fun x : ℝ => (1 / 2 : ℝ) * (Real.exp (-x ^ 2 + (2 * a + c) * x + -a ^ 2) +
      Real.exp (-x ^ 2 + (2 * a - c) * x + -a ^ 2) + Real.exp (-x ^ 2 + (c - 2 * a) * x + -a ^ 2) +
      Real.exp (-x ^ 2 + (-2 * a - c) * x + -a ^ 2)) :=
    ((((integrable_exp_neg_sq_add_real _ _).add (integrable_exp_neg_sq_add_real _ _)).add
      (integrable_exp_neg_sq_add_real _ _)).add (integrable_exp_neg_sq_add_real _ _)).const_mul _
  refine hG.mono' (by unfold HTGeometry.gaussPairSource; fun_prop)
    (ae_of_all _ fun x => ?_)
  have hk := HTGeometry.gaussPairSource_pos a x
  rw [Real.norm_of_nonneg (mul_nonneg (Real.exp_pos _).le hk.le)]
  have he : Real.exp (c * |x|) ≤ Real.exp (c * x) + Real.exp (-(c * x)) := by
    rcases le_or_gt 0 x with h | h
    · rw [abs_of_nonneg h]; linarith [Real.exp_pos (-(c * x))]
    · rw [abs_of_neg h, show c * -x = -(c * x) by ring]; linarith [Real.exp_pos (c * x)]
  calc Real.exp (c * |x|) * HTGeometry.gaussPairSource a x ≤
        (Real.exp (c * x) + Real.exp (-(c * x))) * HTGeometry.gaussPairSource a x :=
        mul_le_mul_of_nonneg_right he hk.le
    _ = _ := by
        simp only [HTGeometry.gaussPairSource]
        rw [show -x ^ 2 + (2 * a + c) * x + -a ^ 2 = c * x + -(x - a) ^ 2 by ring,
          show -x ^ 2 + (2 * a - c) * x + -a ^ 2 = -(c * x) + -(x - a) ^ 2 by ring,
          show -x ^ 2 + (c - 2 * a) * x + -a ^ 2 = c * x + -(x + a) ^ 2 by ring,
          show -x ^ 2 + (-2 * a - c) * x + -a ^ 2 = -(c * x) + -(x + a) ^ 2 by ring]
        simp only [Real.exp_add]
        ring

theorem measurableMomentSource_of_le_gaussPairSource {a : ℝ} {v : ℝ → ℝ}
    (hv : AEStronglyMeasurable v) {C : ℝ} (hC : ∀ x, |v x| ≤ C * HTGeometry.gaussPairSource a x) :
    MeasurableMomentSource fun x => (v x : ℂ) := by
  refine ⟨Complex.continuous_ofReal.comp_aestronglyMeasurable hv, fun c => ?_⟩
  refine ((integrable_exp_mul_abs_mul_gaussPairSource a c).const_mul C).mono'
    ((by fun_prop : Continuous fun x : ℝ => Real.exp (c * |x|)).aestronglyMeasurable.mul
      (Complex.continuous_ofReal.comp_aestronglyMeasurable hv).norm) (ae_of_all _ fun x => ?_)
  rw [Real.norm_of_nonneg (mul_nonneg (Real.exp_pos _).le (norm_nonneg _)), Complex.norm_real,
    Real.norm_eq_abs]
  calc Real.exp (c * |x|) * |v x| ≤ Real.exp (c * |x|) * (C * HTGeometry.gaussPairSource a x) :=
        mul_le_mul_of_nonneg_left (hC x) (Real.exp_pos _).le
    _ = C * (Real.exp (c * |x|) * HTGeometry.gaussPairSource a x) := by ring

/-! ## The Gaussian control measure -/

/-- The density `k_G` of the Gaussian control measure. -/
def gaussPairDensity (a x : ℝ) : ℝ≥0 := (HTGeometry.gaussPairSource a x).toNNReal

theorem measurable_gaussPairDensity (a : ℝ) : Measurable (gaussPairDensity a) :=
  (by unfold HTGeometry.gaussPairSource; fun_prop : Continuous (HTGeometry.gaussPairSource a))
    |>.measurable.real_toNNReal

theorem gaussPairDensity_coe (a x : ℝ) :
    (gaussPairDensity a x : ℝ) = HTGeometry.gaussPairSource a x :=
  Real.coe_toNNReal _ (HTGeometry.gaussPairSource_pos a x).le

/-- The Gaussian control measure `dμ_G = k_G(x) dx`. -/
def gaussPairMeasure (a : ℝ) : Measure ℝ :=
  volume.withDensity fun x => (gaussPairDensity a x : ℝ≥0∞)

instance (a : ℝ) : IsFiniteMeasure (gaussPairMeasure a) := by
  have h : HasFiniteIntegral (HTGeometry.gaussPairSource a) :=
    ((integrable_exp_mul_abs_mul_gaussPairSource a 0).congr
      (ae_of_all _ fun x => by simp)).hasFiniteIntegral
  exact isFiniteMeasure_withDensity_ofReal h

theorem integral_gaussPairMeasure (a : ℝ) (g : ℝ → ℝ) :
    ∫ x, g x ∂gaussPairMeasure a = ∫ x, HTGeometry.gaussPairSource a x * g x := by
  rw [gaussPairMeasure, integral_withDensity_eq_integral_smul (measurable_gaussPairDensity a)]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp only [NNReal.smul_def, smul_eq_mul, gaussPairDensity_coe]

theorem integrable_gaussPairMeasure_iff (a : ℝ) {g : ℝ → ℝ} :
    Integrable g (gaussPairMeasure a) ↔
      Integrable fun x => HTGeometry.gaussPairSource a x * g x := by
  rw [gaussPairMeasure, integrable_withDensity_iff_integrable_smul (measurable_gaussPairDensity a)]
  simp only [NNReal.smul_def, smul_eq_mul, gaussPairDensity_coe]

theorem memLp_one_thetaCosJet_gaussPairMeasure (a γ : ℝ) (j : ℕ) :
    MemLp (thetaCosJet γ j) 1 (gaussPairMeasure a) := by
  rw [memLp_one_iff_integrable, integrable_gaussPairMeasure_iff]
  refine ((integrable_exp_mul_abs_mul_gaussPairSource a 1).const_mul (j.factorial : ℝ)).mono'
    ((by unfold HTGeometry.gaussPairSource; fun_prop : Continuous (HTGeometry.gaussPairSource a)).mul
      (continuous_thetaCosJet γ j)).aestronglyMeasurable (ae_of_all _ fun x => ?_)
  have hk := HTGeometry.gaussPairSource_pos a x
  rw [norm_mul, Real.norm_of_nonneg hk.le, Real.norm_eq_abs]
  calc HTGeometry.gaussPairSource a x * |thetaCosJet γ j x| ≤
        HTGeometry.gaussPairSource a x * (j.factorial * Real.exp |x|) :=
        mul_le_mul_of_nonneg_left ((abs_thetaCosJet_le γ j x).trans
          (abs_pow_le_factorial_mul_exp x j)) hk.le
    _ = j.factorial * (Real.exp (1 * |x|) * HTGeometry.gaussPairSource a x) := by
        rw [one_mul]; ring

/-- The jet `φ_{γ,j}` in `L¹(μ_G)`. -/
def gaussJetL1 (a γ : ℝ) (j : ℕ) : Lp ℝ 1 (gaussPairMeasure a) :=
  (memLp_one_thetaCosJet_gaussPairMeasure a γ j).toLp _

/-- The constant `1` in `L¹(μ_G)`. -/
def gaussOneL1 (a : ℝ) : Lp ℝ 1 (gaussPairMeasure a) := (memLp_const (1 : ℝ)).toLp fun _ => 1

/-- The real-zero jets of the control transform `F_G`. -/
def gaussJetSet (a : ℝ) : Set (Lp ℝ 1 (gaussPairMeasure a)) :=
  {f | ∃ γ : ℝ, 0 < γ ∧ HTGeometry.gaussPairTransform a γ = 0 ∧ ∃ j : ℕ,
    (j : ℕ∞) < analyticOrderAt (HTGeometry.gaussPairTransform a) γ ∧ f = gaussJetL1 a γ j}

/-! ## The bounded annihilator -/

theorem gaussPairTransform_zero_im {a ω : ℝ} (hω : a * ω = 2 * Real.pi) {z : ℂ}
    (hz : HTGeometry.gaussPairTransform a z = 0) : z.im = 0 := by
  obtain ⟨k, hk⟩ := (HTGeometry.gaussPairTransform_eq_zero_iff a z).1 hz
  have ha : a ≠ 0 := fun h => by rw [h, zero_mul] at hω; linarith [Real.pi_pos]
  have := congrArg Complex.im hk
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero] at this
  have h2 : ((2 * (k : ℂ) + 1) * (Real.pi : ℂ) / 2).im = 0 := by
    rw [show (2 * (k : ℂ) + 1) * (Real.pi : ℂ) / 2 = (((2 * k + 1) * Real.pi / 2 : ℝ) : ℂ) by
      push_cast; ring, Complex.ofReal_im]
  rw [h2] at this
  exact (mul_eq_zero.1 this).resolve_left ha

theorem differentiable_gaussPairTransform (a : ℝ) :
    Differentiable ℂ (HTGeometry.gaussPairTransform a) := by
  unfold HTGeometry.gaussPairTransform
  fun_prop

/-- The control source `k_G (cos(ω·) − e^{−ω²/4})` has transform `F_G (q_G − e^{−ω²/4})`. -/
theorem sourceTransform_gaussPair_annihilator {a ω : ℝ} (hω : a * ω = 2 * Real.pi) (z : ℂ) :
    sourceTransform (fun x => ((HTGeometry.gaussPairSource a x *
      (Real.cos (ω * x) - Real.exp (-ω ^ 2 / 4)) : ℝ) : ℂ)) z =
      HTGeometry.gaussPairTransform a z *
        (HTGeometry.gaussPairQuotient ω z - cexp (-(ω : ℂ) ^ 2 / 4)) := by
  have hk := measurableMomentSource_of_le_gaussPairSource (a := a)
    (v := HTGeometry.gaussPairSource a)
    ((by unfold HTGeometry.gaussPairSource; fun_prop :
      Continuous (HTGeometry.gaussPairSource a)).aestronglyMeasurable) (C := 1)
    (fun x => by rw [abs_of_pos (HTGeometry.gaussPairSource_pos a x), one_mul])
  have hu := measurableMomentSource_of_le_gaussPairSource (a := a)
    (v := HTGeometry.gaussPairCosSource a ω)
    ((by unfold HTGeometry.gaussPairCosSource HTGeometry.gaussPairSource; fun_prop :
      Continuous (HTGeometry.gaussPairCosSource a ω)).aestronglyMeasurable) (C := 1)
    (fun x => by rw [one_mul]; exact HTGeometry.abs_gaussPairCosSource_le a ω x)
  have hpt : (fun x : ℝ => cexp (-I * z * x) * ((HTGeometry.gaussPairSource a x *
      (Real.cos (ω * x) - Real.exp (-ω ^ 2 / 4)) : ℝ) : ℂ)) = fun x : ℝ =>
      cexp (-I * z * x) * (HTGeometry.gaussPairCosSource a ω x : ℂ) -
        ((Real.exp (-ω ^ 2 / 4) : ℝ) : ℂ) * (cexp (-I * z * x) *
          (HTGeometry.gaussPairSource a x : ℂ)) := by
    funext x
    simp only [HTGeometry.gaussPairCosSource]
    push_cast
    ring
  unfold sourceTransform
  rw [hpt, integral_sub (hu.integrable_cexp z) ((hk.integrable_cexp z).const_mul _),
    integral_const_mul, HTGeometry.integral_cexp_mul_gaussPairCosSource hω,
    HTGeometry.integral_cexp_mul_gaussPairSource, HTGeometry.gaussPairQuotient,
    show ((Real.exp (-ω ^ 2 / 4) : ℝ) : ℂ) = cexp (-(ω : ℂ) ^ 2 / 4) by
      rw [Complex.ofReal_exp]; push_cast; ring_nf]
  ring

/-- **The Gaussian control fails the weighted `L¹` completeness test.**  For
`k_G = [e^{-(x-a)²} + e^{-(x+a)²}]/2` with `aω = 2π`, `ω ≠ 0`, every zero of `F_G` is real, yet
the bounded even function `g = cos(ω·) − e^{−ω²/4}`, of zero `μ_G`-mean, is not in the `L¹(μ_G)`
closure of `span({1} ∪ V_G)`: it is itself a bounded annihilator of `1` and of every real-zero jet
of `F_G`, and `∫ g² dμ_G > 0`. -/
theorem gaussPair_not_mem_closure_span {a ω : ℝ} (hω : a * ω = 2 * Real.pi) (hω0 : ω ≠ 0) :
    (∀ z, HTGeometry.gaussPairTransform a z = 0 → z.im = 0) ∧
      ∃ g : ℝ → ℝ, Continuous g ∧ (∀ x, g (-x) = g x) ∧ (∀ x, |g x| ≤ 2) ∧
        ∫ x, g x ∂gaussPairMeasure a = 0 ∧
        ∃ hg : MemLp g 1 (gaussPairMeasure a), hg.toLp g ∉
          (Submodule.span ℝ (insert (gaussOneL1 a) (gaussJetSet a))).topologicalClosure := by
  set c := Real.exp (-ω ^ 2 / 4)
  set g : ℝ → ℝ := fun x => Real.cos (ω * x) - c
  have hc0 : 0 < c := Real.exp_pos _
  have hc1 : c < 1 := by
    have := pow_pos (abs_pos.2 hω0) 2
    rw [sq_abs] at this
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.2 (by linarith)
  have hgc : Continuous g := by fun_prop
  have hge : ∀ x, g (-x) = g x := fun x => by simp only [g, mul_neg, Real.cos_neg]
  have hgb : ∀ x, |g x| ≤ 2 := fun x => by
    have := Real.abs_cos_le_one (ω * x)
    rw [abs_le] at this ⊢
    constructor <;> linarith
  have hkc : Continuous (HTGeometry.gaussPairSource a) := by
    unfold HTGeometry.gaussPairSource; fun_prop
  set v : ℝ → ℝ := fun x => HTGeometry.gaussPairSource a x * g x
  have hv : MeasurableMomentSource fun x => (v x : ℂ) :=
    measurableMomentSource_of_le_gaussPairSource (hkc.mul hgc).aestronglyMeasurable (C := 2)
      fun x => by
        rw [abs_mul, abs_of_pos (HTGeometry.gaussPairSource_pos a x), mul_comm]
        exact mul_le_mul_of_nonneg_right (hgb x) (HTGeometry.gaussPairSource_pos a x).le
  have hve : ∀ x, v (-x) = v x := fun x => by
    simp only [v, hge, HTGeometry.gaussPairSource_neg]
  have hT : sourceTransform (fun x => (v x : ℂ)) = fun z => HTGeometry.gaussPairTransform a z *
      (HTGeometry.gaussPairQuotient ω z - cexp (-(ω : ℂ) ^ 2 / 4)) :=
    funext (sourceTransform_gaussPair_annihilator hω)
  have hQd : Differentiable ℂ fun z => HTGeometry.gaussPairQuotient ω z - cexp (-(ω : ℂ) ^ 2 / 4) :=
    (HTGeometry.differentiable_gaussPairQuotient ω).sub_const _
  -- the pairing with every jet is a jet of `F_G (q_G - c)`
  have hjet : ∀ γ : ℝ, ∀ j : ℕ, ((∫ x, g x * thetaCosJet γ j x ∂gaussPairMeasure a : ℝ) : ℂ) =
      iteratedDeriv j (fun z => HTGeometry.gaussPairTransform a z *
        (HTGeometry.gaussPairQuotient ω z - cexp (-(ω : ℂ) ^ 2 / 4))) γ := by
    intro γ j
    rw [← hT, iteratedDeriv_sourceTransform_ofReal_of_moment hv hve γ j,
      integral_gaussPairMeasure]
    congr 1
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp only [v]
    ring
  have hmass : ∫ x, g x ∂gaussPairMeasure a = 0 := by
    have h := hjet 0 0
    simp only [iteratedDeriv_zero, HTGeometry.gaussPairQuotient, Complex.ofReal_zero, mul_zero,
      zero_div, Complex.cosh_zero, mul_one, sub_self] at h
    have h' : ∫ x, g x * thetaCosJet 0 0 x ∂gaussPairMeasure a = 0 := by exact_mod_cast h
    simpa [thetaCosJet] using h'
  have hgm : MemLp g 1 (gaussPairMeasure a) :=
    memLp_one_iff_integrable.2 ((integrable_gaussPairMeasure_iff a).2
      ((integrable_exp_mul_abs_mul_gaussPairSource a 0).const_mul 2 |>.mono'
        (hkc.mul hgc).aestronglyMeasurable (ae_of_all _ fun x => by
          rw [norm_mul, Real.norm_of_nonneg (HTGeometry.gaussPairSource_pos a x).le,
            Real.norm_eq_abs, zero_mul, Real.exp_zero, one_mul, mul_comm]
          exact mul_le_mul_of_nonneg_right (hgb x) (HTGeometry.gaussPairSource_pos a x).le)))
  refine ⟨fun z hz => gaussPairTransform_zero_im hω hz, g, hgc, hge, hgb, hmass, hgm, ?_⟩
  rw [GaloisForLFunctions.HTGeometry.mem_topologicalClosure_iff_linfty]
  intro h
  have hann := h g hgc.stronglyMeasurable ⟨2, ae_of_all _ hgb⟩ fun s hs => by
    have hker : Submodule.span ℝ (insert (gaussOneL1 a) (gaussJetSet a)) ≤
        LinearMap.ker (GaloisForLFunctions.HTGeometry.linftyPairing (μ := gaussPairMeasure a) g
          hgc.stronglyMeasurable 2 (ae_of_all _ hgb) : Lp ℝ 1 (gaussPairMeasure a) →ₗ[ℝ] ℝ) := by
      rw [Submodule.span_le]
      rintro f (rfl | ⟨γ, -, -, j, hj, rfl⟩)
      · show GaloisForLFunctions.HTGeometry.linftyPairing g _ 2 _ (gaussOneL1 a) = 0
        have e1 : (fun x => g x * (gaussOneL1 a : ℝ → ℝ) x) =ᵐ[gaussPairMeasure a]
            fun x => g x * 1 :=
          ((memLp_const (1 : ℝ)).coeFn_toLp (μ := gaussPairMeasure a)).mono fun x hx => by
            simp only [gaussOneL1]
            rw [hx]
        rw [GaloisForLFunctions.HTGeometry.linftyPairing_apply, integral_congr_ae e1]
        simpa using hmass
      · show GaloisForLFunctions.HTGeometry.linftyPairing g _ 2 _ (gaussJetL1 a γ j) = 0
        have e1 : (fun x => g x * (gaussJetL1 a γ j : ℝ → ℝ) x) =ᵐ[gaussPairMeasure a]
            fun x => g x * thetaCosJet γ j x :=
          (memLp_one_thetaCosJet_gaussPairMeasure a γ j).coeFn_toLp.mono fun x hx => by
            simp only [gaussJetL1]
            rw [hx]
        rw [GaloisForLFunctions.HTGeometry.linftyPairing_apply, integral_congr_ae e1]
        have hA : AnalyticAt ℂ (fun z => HTGeometry.gaussPairTransform a z *
            (HTGeometry.gaussPairQuotient ω z - cexp (-(ω : ℂ) ^ 2 / 4))) γ :=
          ((differentiable_gaussPairTransform a).mul hQd).analyticAt _
        have hle : ((j + 1 : ℕ) : ℕ∞) ≤ analyticOrderAt (fun z => HTGeometry.gaussPairTransform a z *
            (HTGeometry.gaussPairQuotient ω z - cexp (-(ω : ℂ) ^ 2 / 4))) γ := by
          refine (Order.add_one_le_of_lt hj).trans ?_
          rw [show (fun z => HTGeometry.gaussPairTransform a z *
            (HTGeometry.gaussPairQuotient ω z - cexp (-(ω : ℂ) ^ 2 / 4))) =
              HTGeometry.gaussPairTransform a * fun z =>
                (HTGeometry.gaussPairQuotient ω z - cexp (-(ω : ℂ) ^ 2 / 4)) from rfl,
            analyticOrderAt_mul ((differentiable_gaussPairTransform a).analyticAt _)
              (hQd.analyticAt _)]
          exact le_self_add
        have h0 := (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hA).1 hle j (by omega)
        have h1 := hjet γ j
        rw [h0] at h1
        exact_mod_cast h1
    have := hker hs
    rwa [LinearMap.mem_ker, ContinuousLinearMap.coe_coe,
      GaloisForLFunctions.HTGeometry.linftyPairing_apply] at this
  have hsq : ∫ x, g x * (hgm.toLp g) x ∂gaussPairMeasure a =
      ∫ x, HTGeometry.gaussPairSource a x * (g x * g x) := by
    have e1 : (fun x => g x * (hgm.toLp g : ℝ → ℝ) x) =ᵐ[gaussPairMeasure a]
        fun x => g x * g x := hgm.coeFn_toLp.mono fun x hx => by simp only [hx]
    rw [integral_congr_ae e1, integral_gaussPairMeasure]
  rw [hsq] at hann
  have hpos : 0 < ∫ x, HTGeometry.gaussPairSource a x * (g x * g x) := by
    have hint : Integrable fun x => HTGeometry.gaussPairSource a x * (g x * g x) :=
      ((integrable_exp_mul_abs_mul_gaussPairSource a 0).const_mul 4).mono'
        (hkc.mul (hgc.mul hgc)).aestronglyMeasurable (ae_of_all _ fun x => by
          have hk := HTGeometry.gaussPairSource_pos a x
          have hb := hgb x
          rw [norm_mul, Real.norm_of_nonneg hk.le, norm_mul, Real.norm_eq_abs, zero_mul,
            Real.exp_zero, one_mul]
          have : |g x| * |g x| ≤ 4 := by nlinarith [abs_nonneg (g x)]
          nlinarith)
    have hnn : 0 ≤ fun x => HTGeometry.gaussPairSource a x * (g x * g x) := fun x =>
      mul_nonneg (HTGeometry.gaussPairSource_pos a x).le (mul_self_nonneg _)
    rw [integral_pos_iff_support_of_nonneg hnn hint]
    have hcont : Continuous fun x => HTGeometry.gaussPairSource a x * (g x * g x) :=
      hkc.mul (hgc.mul hgc)
    refine hcont.isOpen_support.measure_pos volume ⟨0, ?_⟩
    simp only [Function.mem_support, g, mul_zero, Real.cos_zero]
    exact mul_ne_zero (HTGeometry.gaussPairSource_pos a 0).ne'
      (mul_self_ne_zero.2 (by linarith))
  exact hpos.ne' hann

end

end RHTower
