import GaloisForLFunctions.RHTower.FiniteTransverseReflectionRigidity
import Mathlib.Analysis.Complex.Liouville

/-!
# Spacing-preserving holomorphic damping filters

A bounded holomorphic function on a right half-strip admits exponential-root
finite differences with one spacing factor per root. Polynomial evaluation
identifies these differences with their literal coefficient-weighted samples.
-/

open Complex Metric Set
noncomputable section
namespace GaloisForLFunctions.ExceptionalLayerTheory

/-- A half-strip is stable under nonnegative real translations. -/
def dampingHalfStrip (r : ℝ) : Set ℂ := {z | -r < z.re ∧ |z.im| < r}

private theorem isOpen_dampingHalfStrip (r : ℝ) : IsOpen (dampingHalfStrip r) :=
  (isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const)

private theorem convex_dampingHalfStrip (r : ℝ) : Convex ℝ (dampingHalfStrip r) := by
  have hi : Convex ℝ {z : ℂ | |z.im| < r} := by
    have he : {z : ℂ | |z.im| < r} = Complex.imLm ⁻¹' Ioo (-r) r := by
      ext z
      change |z.im| < r ↔ -r < z.im ∧ z.im < r
      exact abs_lt
    rw [he]
    exact (convex_Ioo (-r) r).linear_preimage Complex.imLm
  exact (convex_halfSpace_re_gt (-r)).inter hi

private theorem dampingHalfStrip_mono {r R : ℝ} (h : r ≤ R) :
    dampingHalfStrip r ⊆ dampingHalfStrip R := by
  intro z hz
  exact ⟨by linarith only [hz.1, h], hz.2.trans_le h⟩

private theorem add_mem_dampingHalfStrip {r h : ℝ} (hh : 0 ≤ h)
    {z : ℂ} (hz : z ∈ dampingHalfStrip r) : z + h ∈ dampingHalfStrip r := by
  constructor
  · simp only [Complex.add_re, Complex.ofReal_re]
    linarith only [hz.1, hh]
  · simpa only [Complex.add_im, Complex.ofReal_im, add_zero] using hz.2

private theorem closedBall_subset_dampingHalfStrip {r : ℝ} (_hr : 0 < r)
    {z : ℂ} (hz : z ∈ dampingHalfStrip (r / 2)) :
    closedBall z (r / 2) ⊆ dampingHalfStrip r := by
  intro w hw
  have hn : ‖w - z‖ ≤ r / 2 := by simpa only [Metric.mem_closedBall, dist_eq_norm] using hw
  have hre := (Complex.abs_re_le_norm (w - z)).trans hn
  have him := (Complex.abs_im_le_norm (w - z)).trans hn
  rw [Complex.sub_re] at hre
  rw [Complex.sub_im] at him
  constructor
  · have hh := (abs_le.mp hre).1
    linarith only [hz.1, hh]
  · have hh := abs_sub_abs_le_abs_sub w.im z.im
    linarith only [hz.2, hh, him]

private theorem norm_deriv_dampingHalfStrip_le {r M : ℝ} (hr : 0 < r)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (dampingHalfStrip r))
    (hb : ∀ z ∈ dampingHalfStrip r, ‖f z‖ ≤ M)
    {z : ℂ} (hz : z ∈ dampingHalfStrip (r / 2)) : ‖deriv f z‖ ≤ 2 * M / r := by
  have hsub := closedBall_subset_dampingHalfStrip hr hz
  have hd : DiffContOnCl ℂ f (ball z (r / 2)) := by
    refine ⟨hf.mono (ball_subset_closedBall.trans hsub), ?_⟩
    rw [closure_ball z (by positivity : r / 2 ≠ 0)]
    exact hf.continuousOn.mono hsub
  have hh := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le
    (by positivity : 0 < r / 2) hd (fun w hw => hb w (hsub (sphere_subset_closedBall hw)))
  convert hh using 1
  field_simp [hr.ne']

private theorem norm_shift_sub_dampingHalfStrip_le {r M h : ℝ} (hr : 0 < r) (hh : 0 ≤ h)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (dampingHalfStrip r))
    (hb : ∀ z ∈ dampingHalfStrip r, ‖f z‖ ≤ M)
    {z : ℂ} (hz : z ∈ dampingHalfStrip (r / 2)) :
    ‖f (z + h) - f z‖ ≤ (2 * M / r) * h := by
  have hsub := dampingHalfStrip_mono (show r / 2 ≤ r by linarith only [hr])
  have hd (w : ℂ) (hw : w ∈ dampingHalfStrip (r / 2)) :
      HasDerivWithinAt f (deriv f w) (dampingHalfStrip (r / 2)) w :=
    (hf.differentiableAt ((isOpen_dampingHalfStrip r).mem_nhds (hsub hw))).hasDerivAt.hasDerivWithinAt
  have hb' (w : ℂ) (hw : w ∈ dampingHalfStrip (r / 2)) :
      ‖deriv f w‖ ≤ 2 * M / r := norm_deriv_dampingHalfStrip_le hr hf hb hw
  have he := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hd hb'
    (convex_dampingHalfStrip (r / 2)) hz (add_mem_dampingHalfStrip hh hz)
  simpa only [add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hh] using he

/-- The scalar cost of one exponential root, uniform over unit spacing. -/
def dampingRootCost (ω : ℂ) : ℝ := 2 * ‖ω‖ * (1 + Real.exp ‖ω‖)

private theorem dampingRootCost_nonneg (ω : ℂ) : 0 ≤ dampingRootCost ω := by
  unfold dampingRootCost
  positivity

private theorem norm_exp_step_sub_one_le {h : ℝ} (hh : 0 ≤ h) (hh1 : h ≤ 1) (ω : ℂ) :
    ‖Complex.exp ((h : ℂ) * ω) - 1‖ ≤ h * dampingRootCost ω := by
  have hn : ‖(h : ℂ) * ω‖ = h * ‖ω‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hh]
  by_cases hs : h * ‖ω‖ ≤ 1
  · have hb := Complex.norm_exp_sub_one_le (by rwa [hn])
    rw [hn] at hb
    apply hb.trans
    unfold dampingRootCost
    have he := Real.exp_pos ‖ω‖
    nlinarith only [mul_nonneg (mul_nonneg hh (norm_nonneg ω)) he.le]
  · have hs1 : 1 ≤ h * ‖ω‖ := (lt_of_not_ge hs).le
    have hr : ((h : ℂ) * ω).re ≤ ‖ω‖ := by
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
      calc
        h * ω.re ≤ h * ‖ω‖ := mul_le_mul_of_nonneg_left (Complex.re_le_norm ω) hh
        _ ≤ 1 * ‖ω‖ := mul_le_mul_of_nonneg_right hh1 (norm_nonneg ω)
        _ = _ := one_mul _
    calc
      _ ≤ ‖Complex.exp ((h : ℂ) * ω)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ ≤ Real.exp ‖ω‖ + 1 := by rw [Complex.norm_exp, norm_one]; gcongr
      _ ≤ h * ‖ω‖ * (Real.exp ‖ω‖ + 1) := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hs1 (by positivity : 0 ≤ Real.exp ‖ω‖ + 1)
      _ ≤ h * dampingRootCost ω := by
        unfold dampingRootCost
        have hn0 : 0 ≤ h * ‖ω‖ * (Real.exp ‖ω‖ + 1) := by positivity
        nlinarith only [hn0]

/-- One factor in a geometric damping filter. -/
def twistedDampingDifference (h : ℝ) (ω : ℂ) (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  f (z + h) - Complex.exp ((h : ℂ) * ω) * f z

private theorem differentiableOn_twistedDampingDifference {r h : ℝ} (hh : 0 ≤ h)
    (ω : ℂ) {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (dampingHalfStrip r)) :
    DifferentiableOn ℂ (twistedDampingDifference h ω f) (dampingHalfStrip r) := by
  intro z hz
  have hz' := add_mem_dampingHalfStrip hh hz
  have hd := hf.differentiableAt ((isOpen_dampingHalfStrip r).mem_nhds hz)
  have hd' := hf.differentiableAt ((isOpen_dampingHalfStrip r).mem_nhds hz')
  exact ((hd'.comp z (differentiableAt_id.add_const (h : ℂ))).sub
    (hd.const_mul (Complex.exp ((h : ℂ) * ω)))).differentiableWithinAt

/-- Cauchy cancellation retains one full spacing factor. -/
theorem norm_twistedDampingDifference_le {r M h : ℝ} (hr : 0 < r) (_hM : 0 ≤ M)
    (hh : 0 ≤ h) (hh1 : h ≤ 1) (ω : ℂ) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (dampingHalfStrip r))
    (hb : ∀ z ∈ dampingHalfStrip r, ‖f z‖ ≤ M)
    {z : ℂ} (hz : z ∈ dampingHalfStrip (r / 2)) :
    ‖twistedDampingDifference h ω f z‖ ≤ h * M * (2 / r + dampingRootCost ω) := by
  have hz' := dampingHalfStrip_mono (show r / 2 ≤ r by linarith only [hr]) hz
  have he : twistedDampingDifference h ω f z =
      (f (z + h) - f z) + (1 - Complex.exp ((h : ℂ) * ω)) * f z := by
    unfold twistedDampingDifference
    ring
  rw [he]
  calc
    _ ≤ ‖f (z + h) - f z‖ + ‖(1 - Complex.exp ((h : ℂ) * ω)) * f z‖ := norm_add_le _ _
    _ ≤ (2 * M / r) * h + (h * dampingRootCost ω) * M := by
      apply _root_.add_le_add (norm_shift_sub_dampingHalfStrip_le hr hh hf hb hz)
      rw [norm_mul, norm_sub_rev]
      exact mul_le_mul (norm_exp_step_sub_one_le hh hh1 ω) (hb z hz')
        (norm_nonneg _) (mul_nonneg hh (dampingRootCost_nonneg ω))
    _ = _ := by ring

/-- A factored filter on the logarithmic damping variable. -/
def iteratedDampingDifference (h : ℝ) : List ℂ → (ℂ → ℂ) → (ℂ → ℂ)
  | [], f => f
  | ω :: ws, f => twistedDampingDifference h ω (iteratedDampingDifference h ws f)

/-- Constants depend on the roots and degree, never on the spacing. -/
def dampingFilterCost : List ℂ → ℝ
  | [] => 1
  | ω :: ws => dampingFilterCost ws * (2 * (2 : ℝ) ^ ws.length + dampingRootCost ω)

theorem dampingFilterCost_nonneg (ws : List ℂ) : 0 ≤ dampingFilterCost ws := by
  induction ws with
  | nil => norm_num [dampingFilterCost]
  | cons ω ws ih =>
    exact mul_nonneg ih (add_nonneg (by positivity) (dampingRootCost_nonneg ω))

private theorem differentiableOn_iteratedDampingDifference {r h : ℝ} (hh : 0 ≤ h)
    (ws : List ℂ) {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (dampingHalfStrip r)) :
    DifferentiableOn ℂ (iteratedDampingDifference h ws f) (dampingHalfStrip r) := by
  induction ws with
  | nil => exact hf
  | cons ω ws ih => exact differentiableOn_twistedDampingDifference hh ω ih

/-- Each exponential root retains its spacing factor, uniformly for all positive
real translates of a smaller half-strip. -/
theorem norm_iteratedDampingDifference_le {r M h : ℝ}
    (hr : 0 < r) (hr1 : r ≤ 1) (hM : 0 ≤ M) (hh : 0 ≤ h) (hh1 : h ≤ 1)
    (ws : List ℂ) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (dampingHalfStrip r))
    (hb : ∀ z ∈ dampingHalfStrip r, ‖f z‖ ≤ M)
    {z : ℂ} (hz : z ∈ dampingHalfStrip (r / (2 : ℝ) ^ ws.length)) :
    ‖iteratedDampingDifference h ws f z‖ ≤
      M * (h / r) ^ ws.length * dampingFilterCost ws := by
  induction ws generalizing z with
  | nil =>
    simp only [List.length_nil, pow_zero, div_one] at hz
    simpa only [List.length_nil, pow_zero, mul_one,
      iteratedDampingDifference, dampingFilterCost] using hb z hz
  | cons ω ws ih =>
    let R := r / (2 : ℝ) ^ ws.length
    let B := M * (h / r) ^ ws.length * dampingFilterCost ws
    have hR : 0 < R := by dsimp only [R]; positivity
    have hB : 0 ≤ B := mul_nonneg (by positivity) (dampingFilterCost_nonneg ws)
    have hRr : R ≤ r := div_le_self hr.le (one_le_pow₀ (by norm_num))
    have hz' : z ∈ dampingHalfStrip (R / 2) := by
      simpa only [R, List.length_cons, pow_succ, div_mul_eq_div_div] using hz
    have hi := norm_twistedDampingDifference_le hR hB hh hh1 ω
      ((differentiableOn_iteratedDampingDifference hh ws hf).mono (dampingHalfStrip_mono hRr))
      (fun w hw => ih hw) hz'
    have hfactor : 2 / R + dampingRootCost ω ≤
        (2 * (2 : ℝ) ^ ws.length + dampingRootCost ω) / r := by
      apply (le_div_iff₀ hr).mpr
      have hc := mul_le_mul_of_nonneg_left hr1 (dampingRootCost_nonneg ω)
      dsimp only [R]
      have he : (2 / (r / (2 : ℝ) ^ ws.length) + dampingRootCost ω) * r =
          2 * (2 : ℝ) ^ ws.length + dampingRootCost ω * r := by
        field_simp [hr.ne']
      rw [he]
      linarith only [hc]
    calc
      _ ≤ h * B * (2 / R + dampingRootCost ω) := hi
      _ ≤ h * B * ((2 * (2 : ℝ) ^ ws.length + dampingRootCost ω) / r) :=
        mul_le_mul_of_nonneg_left hfactor (mul_nonneg hh hB)
      _ = _ := by
        simp only [B, List.length_cons, dampingFilterCost, pow_succ]
        ring

private def dampingTranslation (h : ℝ) : Module.End ℂ (ℂ → ℂ) where
  toFun f z := f (z + h)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem dampingTranslation_pow_apply (h : ℝ) (n : ℕ) (f : ℂ → ℂ) (z : ℂ) :
    (dampingTranslation h ^ n) f z = f (z + (n : ℂ) * h) := by
  induction n generalizing f z with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Module.End.mul_apply, ih]
    change f ((z + (n : ℂ) * h) + h) = f (z + ((n + 1 : ℕ) : ℂ) * h)
    congr 1
    push_cast
    ring

private theorem polyShiftOp_dampingTranslation_apply (h : ℝ) (p : Polynomial ℂ)
    (f : ℂ → ℂ) (z : ℂ) :
    RHTower.polyShiftOp (dampingTranslation h) p f z =
      ∑ j ∈ Finset.range (p.natDegree + 1), p.coeff j * f (z + (j : ℂ) * h) := by
  rw [RHTower.polyShiftOp, Polynomial.eval₂_eq_sum_range]
  simp only [LinearMap.sum_apply, Finset.sum_apply, Module.End.mul_apply,
    Module.algebraMap_end_apply, Pi.smul_apply, smul_eq_mul, dampingTranslation_pow_apply]

/-- The actual characteristic polynomial for prescribed exponential roots. -/
def dampingFilterPolynomial (h : ℝ) : List ℂ → Polynomial ℂ
  | [] => 1
  | ω :: ws => (Polynomial.X - Polynomial.C (Complex.exp ((h : ℂ) * ω))) *
      dampingFilterPolynomial h ws

private theorem polyShiftOp_linear_damping (h : ℝ) (ω : ℂ) (f : ℂ → ℂ) :
    RHTower.polyShiftOp (dampingTranslation h)
      (Polynomial.X - Polynomial.C (Complex.exp ((h : ℂ) * ω))) f =
        twistedDampingDifference h ω f := by
  ext z
  rw [RHTower.polyShiftOp, Polynomial.eval₂_sub]
  simp only [Polynomial.eval₂_X, Polynomial.eval₂_C, LinearMap.sub_apply,
    Pi.sub_apply, Module.algebraMap_end_apply, Pi.smul_apply, smul_eq_mul]
  rfl

private theorem iteratedDampingDifference_eq_polyShiftOp (h : ℝ) (ws : List ℂ)
    (f : ℂ → ℂ) : iteratedDampingDifference h ws f =
      RHTower.polyShiftOp (dampingTranslation h) (dampingFilterPolynomial h ws) f := by
  induction ws with
  | nil => simp [iteratedDampingDifference, dampingFilterPolynomial]
  | cons ω ws ih =>
    rw [dampingFilterPolynomial, RHTower.polyShiftOp_mul, Module.End.mul_apply,
      polyShiftOp_linear_damping, ← ih]
    rfl

/-- The Cauchy estimate bounds the literal coefficient-weighted sample sum. -/
theorem norm_dampingFilterPolynomial_sum_le {r M h : ℝ}
    (hr : 0 < r) (hr1 : r ≤ 1) (hM : 0 ≤ M) (hh : 0 ≤ h) (hh1 : h ≤ 1)
    (ws : List ℂ) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (dampingHalfStrip r))
    (hb : ∀ z ∈ dampingHalfStrip r, ‖f z‖ ≤ M) :
    ‖∑ j ∈ Finset.range ((dampingFilterPolynomial h ws).natDegree + 1),
      (dampingFilterPolynomial h ws).coeff j * f ((j : ℂ) * h)‖ ≤
      M * (h / r) ^ ws.length * dampingFilterCost ws := by
  have hz : (0 : ℂ) ∈ dampingHalfStrip (r / (2 : ℝ) ^ ws.length) := by
    have hq : 0 < r / (2 : ℝ) ^ ws.length := by positivity
    exact ⟨by simpa only [Complex.zero_re] using neg_lt_zero.mpr hq,
      by simpa only [Complex.zero_im, abs_zero] using hq⟩
  have hb' := norm_iteratedDampingDifference_le hr hr1 hM hh hh1 ws hf hb hz
  rw [iteratedDampingDifference_eq_polyShiftOp, polyShiftOp_dampingTranslation_apply] at hb'
  simpa only [zero_add] using hb'

#print axioms norm_dampingFilterPolynomial_sum_le

end GaloisForLFunctions.ExceptionalLayerTheory
