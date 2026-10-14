import GaloisForLFunctions.RHTower.TwistedArcN1Reduction

/-!
# The single-twisted arc vectors and their mass

The twisted arc vectors of `TwistedArcGenerator` have log profile `√(y/2)(¼ − ∂²)² 𝒦_u`, which is
positive definite, tail-free and of mean zero.  The single twist `(¼ − ∂²) 𝒦_u` is also positive
definite (`integral_cos_mul_coshFirst`: Fourier multiplier `¼ + τ²`) and tail-free, but its mean is
not zero: the Wronskian of `T_0 = (cosh v − c)^{−1/2}` with `e^{v/2}` at `+∞` survives.

* `integral_exp_half_mul_coshFirst`: `∫ e^{v/2} (¼ − ∂²) T_0 dv = √2` for every `|c| < 1`, since
  `e^{v/2}(¼T_0 − T_0'') = (e^{v/2}(½T_0 − T_0'))'`, which tends to `√2` at `+∞` and to `0` at `−∞`.
* The single-twisted point vector `σ_c(x) = −2c x Q^{−3/2} + 3(1 − c²) x² Q^{−5/2}`
  (`swPointVec`, `Q = x² − 2cx + 1`) has log profile `(¼ − ∂²) T_0 / √2`, is invariant under
  `x ↦ 1/x` (weight `|x|`) and decays like `1/(1 + x²)`.
* The single-twisted arc vector `s_u = √y (σ_u + σ_{−u})` (`swArcVector`) has log profile
  `√(y/2)((¼ − ∂²)T_0(u) + (¼ − ∂²)T_0(−u))` and mass `∫ s_u = 4√y_u` (`integral_swArcVector`).
-/

open MeasureTheory Set Filter Topology
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-! ### The mass of the single twist -/

/-- `e^{−v}(cosh v − c) = (1 + e^{−2v})/2 − c e^{−v}`. -/
theorem exp_neg_mul_coshShift (c v : ℝ) :
    Real.exp (-v) * coshShift c v = (1 + Real.exp (-v) ^ 2) / 2 - c * Real.exp (-v) := by
  unfold coshShift
  rw [Real.cosh_eq]
  have h1 : Real.exp (-v) * Real.exp v = 1 := by rw [← Real.exp_add]; simp
  have e : Real.exp (-v) * ((Real.exp v + Real.exp (-v)) / 2 - c) =
      (Real.exp (-v) * Real.exp v + Real.exp (-v) ^ 2) / 2 - c * Real.exp (-v) := by ring
  rw [e, h1]

/-- `e^{v/2} T_0(v) = (e^{−v}(cosh v − c))^{−1/2}`. -/
theorem exp_half_mul_coshTerm_zero {c : ℝ} (hc : |c| < 1) (v : ℝ) :
    Real.exp (v / 2) * coshTerm c 0 v = (Real.exp (-v) * coshShift c v) ^ (-1 / 2 : ℝ) := by
  have hW := coshShift_pos hc v
  unfold coshTerm
  rw [pow_zero, div_one, Real.mul_rpow (Real.exp_pos _).le hW.le, ← Real.exp_mul]
  ring_nf

/-- `e^{v/2} sinh v T_1(v) = (e^{−v} sinh v) · w^{−1/2}/w`, `w = e^{−v}(cosh v − c)`. -/
theorem exp_half_mul_sinh_mul_coshTerm_one {c : ℝ} (hc : |c| < 1) (v : ℝ) :
    Real.exp (v / 2) * Real.sinh v * coshTerm c 1 v =
      Real.exp (-v) * Real.sinh v * ((Real.exp (-v) * coshShift c v) ^ (-1 / 2 : ℝ) /
        (Real.exp (-v) * coshShift c v)) := by
  have hW := coshShift_pos hc v
  have he := Real.exp_pos (-v)
  have hT := exp_half_mul_coshTerm_zero hc v
  rw [coshTerm_succ, ← hT]
  field_simp

theorem tendsto_exp_neg_mul_coshShift_atTop (c : ℝ) :
    Tendsto (fun v => Real.exp (-v) * coshShift c v) atTop (𝓝 (1 / 2)) := by
  have h := Real.tendsto_exp_neg_atTop_nhds_zero
  have h2 : Tendsto (fun v => (1 + Real.exp (-v) ^ 2) / 2 - c * Real.exp (-v)) atTop
      (𝓝 ((1 + 0 ^ 2) / 2 - c * 0)) :=
    (((tendsto_const_nhds.add (h.pow 2)).div_const 2).sub (tendsto_const_nhds.mul h))
  simp only [zero_pow two_ne_zero, add_zero, mul_zero, sub_zero] at h2
  refine h2.congr fun v => ?_
  rw [exp_neg_mul_coshShift]

theorem tendsto_exp_neg_mul_sinh_atTop :
    Tendsto (fun v => Real.exp (-v) * Real.sinh v) atTop (𝓝 (1 / 2)) := by
  have h := Real.tendsto_exp_neg_atTop_nhds_zero
  have h2 : Tendsto (fun v => (1 - Real.exp (-v) ^ 2) / 2) atTop (𝓝 ((1 - 0 ^ 2) / 2)) :=
    ((tendsto_const_nhds.sub (h.pow 2)).div_const 2)
  simp only [zero_pow two_ne_zero, sub_zero] at h2
  refine h2.congr fun v => ?_
  rw [Real.sinh_eq]
  have h1 : Real.exp (-v) * Real.exp v = 1 := by rw [← Real.exp_add]; simp
  have h3 : Real.exp (-v) ^ 2 = Real.exp (-v) * Real.exp (-v) := sq _
  nlinarith [h1, h3]

/-- The primitive `e^{v/2}(½T_0 − T_0')` of `e^{v/2}(¼ − ∂²)T_0`. -/
def coshFirstPrimitive (c v : ℝ) : ℝ :=
  Real.exp (v / 2) * (1 / 2 * coshTerm c 0 v - coshTermDeriv c 0 v)

theorem hasDerivAt_coshFirstPrimitive {c : ℝ} (hc : |c| < 1) (v : ℝ) :
    HasDerivAt (coshFirstPrimitive c) (Real.exp (v / 2) * coshFirst c v) v := by
  have he : HasDerivAt (fun x => Real.exp (x / 2)) (1 / 2 * Real.exp (v / 2)) v := by
    have h := ((hasDerivAt_id v).div_const 2).exp
    simp only [id] at h
    exact h.congr_deriv (by ring)
  have h : HasDerivAt (fun x => Real.exp (x / 2) * (1 / 2 * coshTerm c 0 x - coshTermDeriv c 0 x))
      _ v := he.mul (((hasDerivAt_coshTerm hc 0 v).const_mul (1 / 2)).sub
        (hasDerivAt_coshTermDeriv hc 0 v))
  unfold coshFirstPrimitive
  refine h.congr_deriv ?_
  rw [← quarter_sub_coshTermDeriv2_zero]
  unfold coshTermDeriv
  push_cast
  ring

theorem coshFirstPrimitive_eq (c v : ℝ) :
    coshFirstPrimitive c v = 1 / 2 * (Real.exp (v / 2) * coshTerm c 0 v) +
      1 / 2 * (Real.exp (v / 2) * Real.sinh v * coshTerm c 1 v) := by
  unfold coshFirstPrimitive coshTermDeriv
  push_cast
  ring

theorem tendsto_coshFirstPrimitive_atTop {c : ℝ} (hc : |c| < 1) :
    Tendsto (coshFirstPrimitive c) atTop (𝓝 (Real.sqrt 2)) := by
  have hw := tendsto_exp_neg_mul_coshShift_atTop c
  have hs := tendsto_exp_neg_mul_sinh_atTop
  have hp : ContinuousAt (fun w : ℝ => w ^ (-1 / 2 : ℝ)) (1 / 2) :=
    Real.continuousAt_rpow_const _ _ (Or.inl (by norm_num))
  have h1 : Tendsto (fun v => (Real.exp (-v) * coshShift c v) ^ (-1 / 2 : ℝ)) atTop
      (𝓝 ((1 / 2 : ℝ) ^ (-1 / 2 : ℝ))) := hp.tendsto.comp hw
  have h2 : Tendsto (fun v => Real.exp (-v) * Real.sinh v *
      ((Real.exp (-v) * coshShift c v) ^ (-1 / 2 : ℝ) / (Real.exp (-v) * coshShift c v))) atTop
      (𝓝 (1 / 2 * ((1 / 2 : ℝ) ^ (-1 / 2 : ℝ) / (1 / 2)))) :=
    hs.mul (h1.div hw (by norm_num))
  have h := (h1.const_mul (1 / 2)).add (h2.const_mul (1 / 2))
  have hval : 1 / 2 * (1 / 2 : ℝ) ^ (-1 / 2 : ℝ) +
      1 / 2 * (1 / 2 * ((1 / 2 : ℝ) ^ (-1 / 2 : ℝ) / (1 / 2))) = Real.sqrt 2 := by
    have : (1 / 2 : ℝ) ^ (-1 / 2 : ℝ) = Real.sqrt 2 := by
      rw [show (-1 / 2 : ℝ) = -(1 / 2) by norm_num, Real.rpow_neg (by norm_num),
        ← Real.sqrt_eq_rpow, Real.sqrt_div' 1 (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_one,
        inv_div, div_one]
    rw [this]; ring
  rw [hval] at h
  refine h.congr fun v => ?_
  rw [coshFirstPrimitive_eq, exp_half_mul_coshTerm_zero hc,
    exp_half_mul_sinh_mul_coshTerm_one hc]

theorem coshTerm_zero_le_const {c : ℝ} (hc : |c| < 1) (v : ℝ) :
    coshTerm c 0 v ≤ (1 - |c|) ^ (-1 / 2 : ℝ) := by
  have h1 : 0 < 1 - |c| := by linarith
  have hW : 1 - |c| ≤ coshShift c v :=
    le_trans (by nlinarith [Real.one_le_cosh v]) (coshShift_ge c v)
  unfold coshTerm
  rw [pow_zero, div_one]
  exact Real.rpow_le_rpow_of_nonpos h1 hW (by norm_num)

theorem abs_sinh_mul_coshTerm_one_le {c : ℝ} (hc : |c| < 1) (v : ℝ) :
    |Real.sinh v * coshTerm c 1 v| ≤ (1 - |c|) ^ (-1 / 2 : ℝ) / (1 - |c|) := by
  have h1 : 0 < 1 - |c| := by linarith
  have hW := coshShift_pos hc v
  have hg := coshShift_ge c v
  have hT0 := coshTerm_zero_le_const hc v
  have hT0p := (coshTerm_pos hc 0 v).le
  rw [coshTerm_succ, abs_mul, abs_of_nonneg (div_nonneg hT0p hW.le)]
  have hsc : |Real.sinh v| ≤ Real.cosh v := by
    rw [abs_le]; constructor <;> nlinarith [Real.cosh_sq v, Real.cosh_pos v, Real.sinh_sq v,
      Real.cosh_eq v, Real.sinh_eq v, Real.exp_pos v, Real.exp_pos (-v)]
  have hcw : Real.cosh v ≤ coshShift c v / (1 - |c|) := by
    rw [le_div_iff₀ h1]; linarith
  calc |Real.sinh v| * (coshTerm c 0 v / coshShift c v)
      ≤ coshShift c v / (1 - |c|) * (coshTerm c 0 v / coshShift c v) :=
        mul_le_mul_of_nonneg_right (hsc.trans hcw) (div_nonneg hT0p hW.le)
    _ = coshTerm c 0 v / (1 - |c|) := by field_simp
    _ ≤ (1 - |c|) ^ (-1 / 2 : ℝ) / (1 - |c|) := div_le_div_of_nonneg_right hT0 h1.le

theorem tendsto_coshFirstPrimitive_atBot {c : ℝ} (hc : |c| < 1) :
    Tendsto (coshFirstPrimitive c) atBot (𝓝 0) := by
  set K : ℝ := (1 - |c|) ^ (-1 / 2 : ℝ) + (1 - |c|) ^ (-1 / 2 : ℝ) / (1 - |c|)
  have he : Tendsto (fun v : ℝ => Real.exp (v / 2)) atBot (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_id.atBot_div_const (by norm_num))
  have hu : Tendsto (fun v : ℝ => 1 / 2 * K * Real.exp (v / 2)) atBot (𝓝 0) := by
    simpa using he.const_mul (1 / 2 * K)
  have hl : Tendsto (fun v : ℝ => -(1 / 2 * K * Real.exp (v / 2))) atBot (𝓝 0) := by
    simpa using hu.neg
  have hb : ∀ v, |coshFirstPrimitive c v| ≤ 1 / 2 * K * Real.exp (v / 2) := fun v => by
    rw [coshFirstPrimitive_eq]
    have h0 := coshTerm_zero_le_const hc v
    have h0p := (coshTerm_pos hc 0 v).le
    have h1 := abs_sinh_mul_coshTerm_one_le hc v
    have hep := (Real.exp_pos (v / 2)).le
    calc |1 / 2 * (Real.exp (v / 2) * coshTerm c 0 v) +
          1 / 2 * (Real.exp (v / 2) * Real.sinh v * coshTerm c 1 v)|
        ≤ 1 / 2 * (Real.exp (v / 2) * coshTerm c 0 v) +
          1 / 2 * (Real.exp (v / 2) * |Real.sinh v * coshTerm c 1 v|) := by
          refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
          · rw [abs_of_nonneg (by positivity)]
          · rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2), mul_assoc, abs_mul,
              abs_of_nonneg hep]
      _ ≤ 1 / 2 * (Real.exp (v / 2) * (1 - |c|) ^ (-1 / 2 : ℝ)) +
          1 / 2 * (Real.exp (v / 2) * ((1 - |c|) ^ (-1 / 2 : ℝ) / (1 - |c|))) := by
          gcongr
      _ = 1 / 2 * K * Real.exp (v / 2) := by ring
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hl hu
    (fun v => neg_le_of_abs_le (hb v)) (fun v => le_of_abs_le (hb v))

/-- **The mass of the single twist.**  `∫ e^{v/2} (¼ − ∂²) T_0 dv = √2` for every `|c| < 1`. -/
theorem integral_exp_half_mul_coshFirst {c : ℝ} (hc : |c| < 1) :
    ∫ v, Real.exp (v / 2) * coshFirst c v = Real.sqrt 2 := by
  obtain ⟨C0, d0⟩ := coshFirst_dom hc
  have hint := integrable_exp_half_mul_of_dom hc (continuous_coshFirst hc) d0
  rw [integral_of_hasDerivAt_of_tendsto (hasDerivAt_coshFirstPrimitive hc) hint
    (tendsto_coshFirstPrimitive_atBot hc) (tendsto_coshFirstPrimitive_atTop hc), sub_zero]

/-! ### The single-twisted point vector -/

/-- `σ_c(x) = −2c x Q^{−3/2} + 3(1 − c²) x² Q^{−5/2}`. -/
def swPointVec (c x : ℝ) : ℝ :=
  -2 * c * x * arcQuadTerm c 1 x + 3 * (1 - c ^ 2) * x ^ 2 * arcQuadTerm c 2 x

theorem exp_half_mul_swPointVec {c : ℝ} (hc : |c| < 1) (v : ℝ) :
    Real.exp (v / 2) * swPointVec c (Real.exp v) = coshFirst c v / Real.sqrt 2 := by
  have k1 := exp_mul_arcQuadTerm_exp hc 1 v
  have k2 := exp_mul_arcQuadTerm_exp hc 2 v
  have h2 : (0 : ℝ) < Real.sqrt 2 := by positivity
  unfold swPointVec coshFirst
  have e : Real.exp (v / 2) * (-2 * c * Real.exp v * arcQuadTerm c 1 (Real.exp v) +
      3 * (1 - c ^ 2) * Real.exp v ^ 2 * arcQuadTerm c 2 (Real.exp v)) =
      -2 * c * (Real.exp (v / 2) * Real.exp v ^ 1 * arcQuadTerm c 1 (Real.exp v)) +
      3 * (1 - c ^ 2) * (Real.exp (v / 2) * Real.exp v ^ 2 * arcQuadTerm c 2 (Real.exp v)) := by
    ring
  rw [e, k1, k2]
  field_simp
  ring

theorem swPointVec_neg_neg (c x : ℝ) : swPointVec (-c) (-x) = swPointVec c x := by
  unfold swPointVec
  simp only [arcQuadTerm_neg_neg]
  ring

/-- `σ_c(1/x) = |x| σ_c(x)`. -/
theorem swPointVec_inv {c : ℝ} (hc : |c| < 1) {x : ℝ} (hx : x ≠ 0) :
    swPointVec c (1 / x) = |x| * swPointVec c x := by
  unfold swPointVec
  simp only [arcQuadTerm_inv hc _ hx]
  field_simp
  ring

/-- The derivative of `σ_c`, expanded into monomials `x^i Q^{−1/2−j}`. -/
def swPointDeriv (c x : ℝ) : ℝ :=
  -2 * c * arcQuadTerm c 1 x + 6 * c * x ^ 2 * arcQuadTerm c 2 x -
    6 * c ^ 2 * x * arcQuadTerm c 2 x + 6 * (1 - c ^ 2) * x * arcQuadTerm c 2 x -
    15 * (1 - c ^ 2) * x ^ 3 * arcQuadTerm c 3 x + 15 * c * (1 - c ^ 2) * x ^ 2 * arcQuadTerm c 3 x

theorem hasDerivAt_swPointVec {c : ℝ} (hc : |c| < 1) (x : ℝ) :
    HasDerivAt (swPointVec c) (swPointDeriv c x) x := by
  have t1 := hasDerivAt_arcQuadTerm hc 1 x
  have t2 := hasDerivAt_arcQuadTerm hc 2 x
  have hx := hasDerivAt_id x
  have h := (((hx.const_mul (-2 * c)).mul t1).add
    (((hx.pow 2).const_mul (3 * (1 - c ^ 2))).mul t2))
  simp only [id, Pi.pow_apply] at h
  unfold swPointVec
  refine h.congr_deriv ?_
  unfold swPointDeriv
  push_cast
  ring

theorem continuous_swPointVec {c : ℝ} (hc : |c| < 1) : Continuous (swPointVec c) := by
  unfold swPointVec; have := continuous_arcQuadTerm hc; fun_prop

theorem continuous_swPointDeriv {c : ℝ} (hc : |c| < 1) : Continuous (swPointDeriv c) := by
  unfold swPointDeriv; have := continuous_arcQuadTerm hc; fun_prop

theorem abs_sw_coef_le {c : ℝ} (hc : |c| ≤ 1 / 2) :
    |-2 * c| ≤ 1 ∧ |3 * (1 - c ^ 2)| ≤ 3 ∧ |6 * c| ≤ 3 ∧ |6 * c ^ 2| ≤ 3 / 2 ∧
      |6 * (1 - c ^ 2)| ≤ 6 ∧ |15 * (1 - c ^ 2)| ≤ 15 ∧ |15 * c * (1 - c ^ 2)| ≤ 15 / 2 := by
  have h0 := abs_nonneg c
  have hsq : c ^ 2 ≤ 1 / 4 := by nlinarith [sq_abs c]
  have hsq0 : 0 ≤ c ^ 2 := sq_nonneg c
  have h1 : 0 ≤ 1 - c ^ 2 := by linarith
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [abs_mul]; norm_num; linarith
  · rw [abs_of_nonneg (by positivity)]; linarith
  · rw [abs_mul]; norm_num; linarith
  · rw [abs_of_nonneg (by positivity)]; linarith
  · rw [abs_of_nonneg (by positivity)]; linarith
  · rw [abs_of_nonneg (by positivity)]; linarith
  · rw [abs_mul, abs_mul, abs_of_nonneg h1]
    norm_num
    nlinarith

/-- `|σ_c(x)| ≤ 30 / (1 + x²)` for `|c| ≤ ½`. -/
theorem abs_swPointVec_le {c : ℝ} (hc : |c| ≤ 1 / 2) (x : ℝ) :
    |swPointVec c x| ≤ 30 * (1 + x ^ 2)⁻¹ := by
  obtain ⟨b1, b2, -⟩ := abs_sw_coef_le hc
  have m1 := abs_mono_le hc (-2 * c) (i := 1) (j := 1) (by norm_num) x
  have m2 := abs_mono_le hc (3 * (1 - c ^ 2)) (i := 2) (j := 2) (by norm_num) x
  have hp : 0 < (1 + x ^ 2)⁻¹ := by positivity
  unfold swPointVec
  have e : -2 * c * x * arcQuadTerm c 1 x = -2 * c * x ^ 1 * arcQuadTerm c 1 x := by ring
  rw [e]
  calc _ ≤ |-2 * c * x ^ 1 * arcQuadTerm c 1 x| + |3 * (1 - c ^ 2) * x ^ 2 * arcQuadTerm c 2 x| :=
        abs_add_le _ _
    _ ≤ 1 * 2 ^ (1 + 1) * (1 + x ^ 2)⁻¹ + 3 * 2 ^ (2 + 1) * (1 + x ^ 2)⁻¹ := by
        gcongr
        · exact m1.trans (by gcongr)
        · exact m2.trans (by gcongr)
    _ ≤ 30 * (1 + x ^ 2)⁻¹ := by nlinarith

/-- `|σ_c′(x)| ≤ 450 / (1 + x²)` for `|c| ≤ ½`. -/
theorem abs_swPointDeriv_le {c : ℝ} (hc : |c| ≤ 1 / 2) (x : ℝ) :
    |swPointDeriv c x| ≤ 450 * (1 + x ^ 2)⁻¹ := by
  obtain ⟨b1, -, b3, b4, b5, b6, b7⟩ := abs_sw_coef_le hc
  have m1 := abs_mono_le hc (-2 * c) (i := 0) (j := 1) (by norm_num) x
  have m2 := abs_mono_le hc (6 * c) (i := 2) (j := 2) (by norm_num) x
  have m3 := abs_mono_le hc (6 * c ^ 2) (i := 1) (j := 2) (by norm_num) x
  have m4 := abs_mono_le hc (6 * (1 - c ^ 2)) (i := 1) (j := 2) (by norm_num) x
  have m5 := abs_mono_le hc (15 * (1 - c ^ 2)) (i := 3) (j := 3) (by norm_num) x
  have m6 := abs_mono_le hc (15 * c * (1 - c ^ 2)) (i := 2) (j := 3) (by norm_num) x
  have hp : 0 < (1 + x ^ 2)⁻¹ := by positivity
  unfold swPointDeriv
  have e1 : -2 * c * arcQuadTerm c 1 x = -2 * c * x ^ 0 * arcQuadTerm c 1 x := by ring
  have e3 : 6 * c ^ 2 * x * arcQuadTerm c 2 x = 6 * c ^ 2 * x ^ 1 * arcQuadTerm c 2 x := by ring
  have e4 : 6 * (1 - c ^ 2) * x * arcQuadTerm c 2 x =
      6 * (1 - c ^ 2) * x ^ 1 * arcQuadTerm c 2 x := by ring
  rw [e1, e3, e4]
  set A1 := -2 * c * x ^ 0 * arcQuadTerm c 1 x
  set A2 := 6 * c * x ^ 2 * arcQuadTerm c 2 x
  set A3 := 6 * c ^ 2 * x ^ 1 * arcQuadTerm c 2 x
  set A4 := 6 * (1 - c ^ 2) * x ^ 1 * arcQuadTerm c 2 x
  set A5 := 15 * (1 - c ^ 2) * x ^ 3 * arcQuadTerm c 3 x
  set A6 := 15 * c * (1 - c ^ 2) * x ^ 2 * arcQuadTerm c 3 x
  have hsum : |A1 + A2 - A3 + A4 - A5 + A6| ≤ |A1| + |A2| + |A3| + |A4| + |A5| + |A6| := by
    have := abs_add_le (A1 + A2 - A3 + A4 - A5) A6
    have := abs_sub (A1 + A2 - A3 + A4) A5
    have := abs_add_le (A1 + A2 - A3) A4
    have := abs_sub (A1 + A2) A3
    have := abs_add_le A1 A2
    linarith
  refine hsum.trans ?_
  have t1 : |A1| ≤ 1 * 2 ^ (1 + 1) * (1 + x ^ 2)⁻¹ := m1.trans (by gcongr)
  have t2 : |A2| ≤ 3 * 2 ^ (2 + 1) * (1 + x ^ 2)⁻¹ := m2.trans (by gcongr)
  have t3 : |A3| ≤ 3 / 2 * 2 ^ (2 + 1) * (1 + x ^ 2)⁻¹ := m3.trans (by gcongr)
  have t4 : |A4| ≤ 6 * 2 ^ (2 + 1) * (1 + x ^ 2)⁻¹ := m4.trans (by gcongr)
  have t5 : |A5| ≤ 15 * 2 ^ (3 + 1) * (1 + x ^ 2)⁻¹ := m5.trans (by gcongr)
  have t6 : |A6| ≤ 15 / 2 * 2 ^ (3 + 1) * (1 + x ^ 2)⁻¹ := m6.trans (by gcongr)
  norm_num at t1 t2 t3 t4 t5 t6
  linarith

/-! ### The single-twisted arc vector -/

/-- The single-twisted arc vector `s_u = √y (σ_u + σ_{−u})`. -/
def swArcVector (u : ArcParam) (x : ℝ) : ℝ :=
  Real.sqrt (modularArcHeight u) * (swPointVec u x + swPointVec (-u) x)

/-- Its derivative. -/
def swArcDeriv (u : ArcParam) (x : ℝ) : ℝ :=
  Real.sqrt (modularArcHeight u) * (swPointDeriv u x + swPointDeriv (-u) x)

theorem hasDerivAt_swArcVector (u : ArcParam) (x : ℝ) :
    HasDerivAt (swArcVector u) (swArcDeriv u x) x := by
  have hu := abs_arcParam_lt u
  have hu' : |-(u : ℝ)| < 1 := by rwa [abs_neg]
  exact ((hasDerivAt_swPointVec hu x).add (hasDerivAt_swPointVec hu' x)).const_mul _

theorem swArcVector_neg (u : ArcParam) (x : ℝ) : swArcVector u (-x) = swArcVector u x := by
  unfold swArcVector
  have h1 := swPointVec_neg_neg (u : ℝ) x
  have h2 := swPointVec_neg_neg (-(u : ℝ)) x
  rw [neg_neg] at h2
  rw [h1, h2]; ring

theorem swArcVector_inv (u : ArcParam) {x : ℝ} (hx : x ≠ 0) :
    swArcVector u (1 / x) = |x| * swArcVector u x := by
  have hu := abs_arcParam_lt u
  have hu' : |-(u : ℝ)| < 1 := by rwa [abs_neg]
  unfold swArcVector
  rw [swPointVec_inv hu hx, swPointVec_inv hu' hx]; ring

theorem abs_swArcVector_le (u : ArcParam) (x : ℝ) :
    |swArcVector u x| ≤ 60 * (1 + x ^ 2)⁻¹ := by
  have h1 := abs_swPointVec_le (abs_arcParam_le u) x
  have h2 := abs_swPointVec_le (abs_neg_arcParam_le u) x
  have hs := sqrt_modularArcHeight_le_one u
  have hs0 := Real.sqrt_nonneg (modularArcHeight u)
  unfold swArcVector
  rw [abs_mul, abs_of_nonneg hs0]
  calc Real.sqrt (modularArcHeight u) * |swPointVec u x + swPointVec (-u) x|
      ≤ 1 * (30 * (1 + x ^ 2)⁻¹ + 30 * (1 + x ^ 2)⁻¹) :=
        mul_le_mul hs ((abs_add_le _ _).trans (add_le_add h1 h2)) (abs_nonneg _) zero_le_one
    _ = _ := by ring

theorem abs_swArcDeriv_le (u : ArcParam) (x : ℝ) :
    |swArcDeriv u x| ≤ 900 * (1 + x ^ 2)⁻¹ := by
  have h1 := abs_swPointDeriv_le (abs_arcParam_le u) x
  have h2 := abs_swPointDeriv_le (abs_neg_arcParam_le u) x
  have hs := sqrt_modularArcHeight_le_one u
  have hs0 := Real.sqrt_nonneg (modularArcHeight u)
  unfold swArcDeriv
  rw [abs_mul, abs_of_nonneg hs0]
  calc Real.sqrt (modularArcHeight u) * |swPointDeriv u x + swPointDeriv (-u) x|
      ≤ 1 * (450 * (1 + x ^ 2)⁻¹ + 450 * (1 + x ^ 2)⁻¹) :=
        mul_le_mul hs ((abs_add_le _ _).trans (add_le_add h1 h2)) (abs_nonneg _) zero_le_one
    _ = _ := by ring

theorem continuous_swArcVector (u : ArcParam) : Continuous (swArcVector u) := by
  have hu := abs_arcParam_lt u
  have hu' : |-(u : ℝ)| < 1 := by rwa [abs_neg]
  unfold swArcVector
  exact continuous_const.mul ((continuous_swPointVec hu).add (continuous_swPointVec hu'))

theorem continuous_swArcDeriv (u : ArcParam) : Continuous (swArcDeriv u) := by
  have hu := abs_arcParam_lt u
  have hu' : |-(u : ℝ)| < 1 := by rwa [abs_neg]
  unfold swArcDeriv
  exact continuous_const.mul ((continuous_swPointDeriv hu).add (continuous_swPointDeriv hu'))

theorem continuous_swArcVector_param :
    Continuous fun p : ℝ × ArcParam => swArcVector p.2 p.1 := by
  have h1 := continuous_arcQuadTerm_param 1
  have h2 := continuous_arcQuadTerm_param 2
  have g1 := continuous_arcQuadTerm_param_neg 1
  have g2 := continuous_arcQuadTerm_param_neg 2
  have hy : Continuous fun p : ℝ × ArcParam => Real.sqrt (modularArcHeight p.2) := by
    unfold modularArcHeight; fun_prop
  unfold swArcVector swPointVec
  fun_prop

theorem continuous_swArcDeriv_param :
    Continuous fun p : ℝ × ArcParam => swArcDeriv p.2 p.1 := by
  have h1 := continuous_arcQuadTerm_param 1
  have h2 := continuous_arcQuadTerm_param 2
  have h3 := continuous_arcQuadTerm_param 3
  have g1 := continuous_arcQuadTerm_param_neg 1
  have g2 := continuous_arcQuadTerm_param_neg 2
  have g3 := continuous_arcQuadTerm_param_neg 3
  have hy : Continuous fun p : ℝ × ArcParam => Real.sqrt (modularArcHeight p.2) := by
    unfold modularArcHeight; fun_prop
  unfold swArcDeriv swPointDeriv
  fun_prop

theorem continuous_swArcVector_at (x : ℝ) : Continuous fun u : ArcParam => swArcVector u x :=
  continuous_swArcVector_param.comp (continuous_const.prodMk continuous_id)

theorem continuous_swArcDeriv_at (x : ℝ) : Continuous fun u : ArcParam => swArcDeriv u x :=
  continuous_swArcDeriv_param.comp (continuous_const.prodMk continuous_id)

theorem integrable_swArcVector (u : ArcParam) : Integrable (swArcVector u) :=
  integrable_of_le_inv_one_add_sq (continuous_swArcVector u) (abs_swArcVector_le u)

theorem integrable_swArcDeriv (u : ArcParam) : Integrable (swArcDeriv u) :=
  integrable_of_le_inv_one_add_sq (continuous_swArcDeriv u) (abs_swArcDeriv_le u)

theorem abs_exp_half_mul_swArcVector_le (u : ArcParam) (v : ℝ) :
    |Real.exp (v / 2) * swArcVector u (Real.exp v)| ≤ 60 * Real.exp (-(3 * |v| / 2)) :=
  abs_exp_half_mul_le_of_inv (abs_swArcVector_le u) (fun _ hx => swArcVector_inv u hx) v

/-- **Logarithmic profile**: `e^{v/2} s_u(e^v) = √(y/2) ((¼ − ∂²)T_0(u) + (¼ − ∂²)T_0(−u))`. -/
theorem exp_half_mul_swArcVector (u : ArcParam) (v : ℝ) :
    Real.exp (v / 2) * swArcVector u (Real.exp v) =
      Real.sqrt (modularArcHeight u / 2) * (coshFirst u v + coshFirst (-u) v) := by
  have hu := abs_arcParam_lt u
  have hu' : |-(u : ℝ)| < 1 := by rwa [abs_neg]
  have h1 := exp_half_mul_swPointVec hu v
  have h2 := exp_half_mul_swPointVec hu' v
  unfold swArcVector
  rw [Real.sqrt_div' _ (by norm_num : (0 : ℝ) ≤ 2)]
  have h22 : (0 : ℝ) < Real.sqrt 2 := by positivity
  rw [show Real.exp (v / 2) * (Real.sqrt (modularArcHeight u) * (swPointVec u (Real.exp v) +
      swPointVec (-u) (Real.exp v))) = Real.sqrt (modularArcHeight u) *
      (Real.exp (v / 2) * swPointVec u (Real.exp v) +
        Real.exp (v / 2) * swPointVec (-u) (Real.exp v)) by ring, h1, h2]
  field_simp

/-- **The mass of the single-twisted arc vector**: `∫ s_u = 4 √y_u`. -/
theorem integral_swArcVector (u : ArcParam) :
    ∫ x, swArcVector u x = 4 * Real.sqrt (modularArcHeight u) := by
  have hu := abs_arcParam_lt u
  have hu' : |-(u : ℝ)| < 1 := by rwa [abs_neg]
  have heven : ∀ x, swArcVector u |x| = swArcVector u x := fun x => by
    rcases le_total 0 x with hx | hx
    · rw [abs_of_nonneg hx]
    · rw [abs_of_nonpos hx, swArcVector_neg]
  have h1 : ∫ x, swArcVector u x = 2 * ∫ x in Ioi 0, swArcVector u x := by
    rw [← integral_comp_abs (f := swArcVector u)]
    exact integral_congr_ae (Eventually.of_forall fun x => (heven x).symm)
  rw [h1, setIntegral_Ioi_eq_integral_exp_mul]
  have h2 : ∀ v, Real.exp v * swArcVector u (Real.exp v) = Real.sqrt (modularArcHeight u / 2) *
      (Real.exp (v / 2) * coshFirst u v + Real.exp (v / 2) * coshFirst (-u) v) := fun v => by
    have hh := exp_half_mul_swArcVector u v
    have he : Real.exp v = Real.exp (v / 2) * Real.exp (v / 2) := by
      rw [← Real.exp_add]; ring_nf
    calc Real.exp v * swArcVector u (Real.exp v) =
        Real.exp (v / 2) * (Real.exp (v / 2) * swArcVector u (Real.exp v)) := by
          rw [← mul_assoc, ← he]
      _ = _ := by rw [hh]; ring
  simp_rw [h2]
  obtain ⟨C0, d0⟩ := coshFirst_dom hu
  obtain ⟨C1, d1⟩ := coshFirst_dom hu'
  have i0 := integrable_exp_half_mul_of_dom hu (continuous_coshFirst hu) d0
  have i1 := integrable_exp_half_mul_of_dom hu' (continuous_coshFirst hu') d1
  rw [integral_const_mul, integral_add i0 i1, integral_exp_half_mul_coshFirst hu,
    integral_exp_half_mul_coshFirst hu']
  have hy : 0 ≤ modularArcHeight u := by unfold modularArcHeight; exact Real.sqrt_nonneg _
  have e : Real.sqrt (modularArcHeight u / 2) * Real.sqrt 2 = Real.sqrt (modularArcHeight u) := by
    rw [← Real.sqrt_mul (by positivity)]; ring_nf
  linear_combination 4 * e

/-- **Moments**: `∫ s_u′ sin(ωx) = −ω ∫ s_u cos(ωx)`. -/
theorem integral_swArcDeriv_mul_sin (u : ArcParam) (ω : ℝ) :
    ∫ x, swArcDeriv u x * Real.sin (ω * x) = -(ω * ∫ x, swArcVector u x * Real.cos (ω * x)) := by
  have hs : ∀ x, HasDerivAt (fun y => Real.sin (ω * y)) (ω * Real.cos (ω * x)) x := fun x => by
    have h := ((hasDerivAt_id x).const_mul ω).sin
    simp only [id, mul_one] at h
    exact h.congr_deriv (by ring)
  have bsin : ∀ x, |Real.sin (ω * x)| ≤ 1 := fun x => Real.abs_sin_le_one _
  have i1 : Integrable fun x => Real.sin (ω * x) * swArcDeriv u x :=
    integrable_of_le_inv_one_add_sq (by have := continuous_swArcDeriv u; fun_prop)
      (C := 900) fun x => by
        rw [abs_mul]
        exact (mul_le_mul (bsin x) (abs_swArcDeriv_le u x) (abs_nonneg _) zero_le_one).trans
          (by rw [one_mul])
  have i2 : Integrable fun x => ω * Real.cos (ω * x) * swArcVector u x :=
    integrable_of_le_inv_one_add_sq (by have := continuous_swArcVector u; fun_prop)
      (C := |ω| * 60) fun x => by
        rw [abs_mul, abs_mul, mul_assoc]
        exact mul_le_mul_of_nonneg_left ((mul_le_mul (Real.abs_cos_le_one _)
          (abs_swArcVector_le u x) (abs_nonneg _) zero_le_one).trans (by rw [one_mul]))
          (abs_nonneg ω) |>.trans (by ring_nf; exact le_rfl)
  have i3 : Integrable fun x => Real.sin (ω * x) * swArcVector u x :=
    integrable_of_le_inv_one_add_sq (by have := continuous_swArcVector u; fun_prop)
      (C := 60) fun x => by
        rw [abs_mul]
        exact (mul_le_mul (bsin x) (abs_swArcVector_le u x) (abs_nonneg _) zero_le_one).trans
          (by rw [one_mul])
  have h := integral_mul_deriv_eq_deriv_mul_of_integrable (fun x _ => hs x)
    (fun x _ => hasDerivAt_swArcVector u x) i1 i2 i3
  have e1 : (fun x => swArcDeriv u x * Real.sin (ω * x)) =
      fun x => Real.sin (ω * x) * swArcDeriv u x := by funext x; ring
  have e2 : (fun x => ω * Real.cos (ω * x) * swArcVector u x) =
      fun x => ω * (swArcVector u x * Real.cos (ω * x)) := by funext x; ring
  rw [e1, h, e2, integral_const_mul]

/-- **Spectrum**: the cosine transform of the log profile of `s_u` is `√(y/2)(¼ + τ²) Ŝ_u(τ)`. -/
theorem integral_cos_mul_swArcProfile (u : ArcParam) (τ : ℝ) :
    ∫ v, Real.cos (τ * v) * (Real.exp (v / 2) * swArcVector u (Real.exp v)) =
      Real.sqrt (modularArcHeight u / 2) * ((1 / 4 + τ ^ 2) *
        ∫ v, Real.cos (τ * v) * symCoshKernel u v) := by
  have hu := abs_arcParam_lt u
  have hu' : |-(u : ℝ)| < 1 := by rwa [abs_neg]
  have bc : ∀ v, |Real.cos (τ * v)| ≤ 1 := fun v => Real.abs_cos_le_one _
  have cc : Continuous fun v : ℝ => Real.cos (τ * v) := by fun_prop
  obtain ⟨C0, d0⟩ := coshFirst_dom hu
  obtain ⟨C1, d1⟩ := coshFirst_dom hu'
  have i0 := integrable_mul_of_dom hu cc bc (continuous_coshFirst hu) d0
  have i1 := integrable_mul_of_dom hu' cc bc (continuous_coshFirst hu') d1
  have j0 : ∀ {d : ℝ}, |d| < 1 → Integrable fun v => Real.cos (τ * v) * coshTerm d 0 v :=
    fun hd => integrable_mul_of_dom hd cc bc (continuous_coshTerm hd 0) (C := 1)
      fun v => by rw [one_mul, abs_of_pos (coshTerm_pos hd 0 v)]
  simp_rw [exp_half_mul_swArcVector]
  have e : (fun v => Real.cos (τ * v) * (Real.sqrt (modularArcHeight u / 2) *
      (coshFirst u v + coshFirst (-u) v))) = fun v => Real.sqrt (modularArcHeight u / 2) *
        (Real.cos (τ * v) * coshFirst u v + Real.cos (τ * v) * coshFirst (-u) v) := by
    funext v; ring
  have e2 : (fun v => Real.cos (τ * v) * symCoshKernel u v) =
      fun v => Real.cos (τ * v) * coshTerm (-u) 0 v + Real.cos (τ * v) * coshTerm u 0 v := by
    funext v; rw [symCoshKernel_eq_coshTerm]; ring
  rw [e, integral_const_mul, integral_add i0 i1, integral_cos_mul_coshFirst hu,
    integral_cos_mul_coshFirst hu', e2, integral_add (j0 hu') (j0 hu)]
  ring

end

end RHTower
