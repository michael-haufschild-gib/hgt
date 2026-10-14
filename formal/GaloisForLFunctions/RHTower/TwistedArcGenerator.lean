import GaloisForLFunctions.HTGeometry.TwistedCoshKernel
import GaloisForLFunctions.RHTower.FilteredArcGeneratorDecay

/-!
# Twisted arc generators: strictly positive definite decay-class `s = ½` vectors

For an arc point `u + iy`, `u² + y² = 1`, put `Q_c(x) = x² − 2cx + 1` and

`τ_c(x) = 4c x Q^{−3/2} + (42c² − 18) x² Q^{−5/2} + 120c(c² − 1) x³ Q^{−7/2} + 105(1 − c²)² x⁴ Q^{−9/2}`,

and the twisted arc vector `g_u = √y (τ_u + τ_{−u})`.  In logarithmic coordinates
(`Q_c(e^v) = 2e^v(cosh v − c)`) this is the twisted kernel of `HTGeometry.TwistedCoshKernel`:

`e^{v/2} g_u(e^v) = √(y/2) · (¼ − ∂_v²)² 𝒦_u(v)`, with `𝒦_u(v) = (cosh v − u)^{−1/2} + (cosh v + u)^{−1/2}`
(`exp_half_mul_twArcVector`).

So `g_u = 𝒟² ψ_u` for the dilation operator `𝒟 = −∂_x x² ∂_x` and the arc pair vector `ψ_u`, and:

* `g_u` is even and satisfies `g_u(1/x) = |x| g_u(x)` (`twArcVector_neg`, `twArcVector_inv`);
* `∫ g_u = 0` (`integral_twArcVector_eq_zero`) and its log profile is `O(e^{−3|v|/2})`;
* its log profile has cosine transform `(¼ + τ²)² √(y/2) ∫ cos(τv) 𝒦_u > 0`
  (`integral_cos_mul_twArcProfile_pos`).

These are the generators of decay-class (N1)-type vectors on the modular bottom arc.
-/

open MeasureTheory Set Filter Topology
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-- `Q_c(x) = x² − 2cx + 1`. -/
def arcQuad (c x : ℝ) : ℝ := x ^ 2 - 2 * c * x + 1

theorem arcQuad_ge (c x : ℝ) : (1 - |c|) * (1 + x ^ 2) ≤ arcQuad c x := by
  unfold arcQuad
  have h1 : 2 * |x| ≤ 1 + x ^ 2 := by nlinarith [sq_nonneg (|x| - 1), sq_abs x]
  have h2 : c * x ≤ |c| * |x| := by rw [← abs_mul]; exact le_abs_self _
  nlinarith [abs_nonneg c]

theorem arcQuad_pos {c : ℝ} (hc : |c| < 1) (x : ℝ) : 0 < arcQuad c x :=
  lt_of_lt_of_le (mul_pos (by linarith) (by positivity)) (arcQuad_ge c x)

theorem arcQuad_exp (c v : ℝ) : arcQuad c (Real.exp v) = 2 * Real.exp v * coshShift c v := by
  unfold arcQuad coshShift
  rw [Real.cosh_eq, Real.exp_neg]
  field_simp
  ring

theorem hasDerivAt_arcQuad (c x : ℝ) : HasDerivAt (arcQuad c) (2 * x - 2 * c) x := by
  have h := (((hasDerivAt_id x).pow 2).sub ((hasDerivAt_id x).const_mul (2 * c))).add_const 1
  simp only [id] at h
  unfold arcQuad
  exact h.congr_deriv (by ring)

/-- `Q_c(x)^{−1/2} / Q_c(x)^j`. -/
def arcQuadTerm (c : ℝ) (j : ℕ) (x : ℝ) : ℝ := arcQuad c x ^ (-1 / 2 : ℝ) / arcQuad c x ^ j

theorem arcQuadTerm_pos {c : ℝ} (hc : |c| < 1) (j : ℕ) (x : ℝ) : 0 < arcQuadTerm c j x :=
  div_pos (Real.rpow_pos_of_pos (arcQuad_pos hc x) _) (pow_pos (arcQuad_pos hc x) _)

theorem continuous_arcQuadTerm {c : ℝ} (hc : |c| < 1) (j : ℕ) : Continuous (arcQuadTerm c j) := by
  have hQ : Continuous (arcQuad c) := by unfold arcQuad; fun_prop
  exact Continuous.div (hQ.rpow_const fun x => Or.inl (arcQuad_pos hc x).ne') (hQ.pow j)
    fun x => (pow_pos (arcQuad_pos hc x) j).ne'

theorem hasDerivAt_arcQuadTerm {c : ℝ} (hc : |c| < 1) (j : ℕ) (x : ℝ) :
    HasDerivAt (arcQuadTerm c j)
      (-((j : ℝ) + 1 / 2) * (2 * x - 2 * c) * arcQuadTerm c (j + 1) x) x := by
  have hQ := arcQuad_pos hc x
  have h1 := (hasDerivAt_arcQuad c x).rpow_const (p := (-1 / 2 : ℝ)) (Or.inl hQ.ne')
  have h2 := (hasDerivAt_arcQuad c x).pow j
  have h3 : HasDerivAt (fun y => arcQuad c y ^ (-1 / 2 : ℝ) / arcQuad c y ^ j) _ x :=
    h1.div h2 (pow_pos hQ j).ne'
  refine h3.congr_deriv ?_
  have e : arcQuad c x ^ ((-1 / 2 : ℝ) - 1) = arcQuad c x ^ (-1 / 2 : ℝ) / arcQuad c x := by
    rw [Real.rpow_sub hQ, Real.rpow_one]
  unfold arcQuadTerm
  rw [e]
  rcases j with _ | j
  · simp
    field_simp
  · push_cast
    rw [pow_succ]
    field_simp
    ring

/-- In logarithmic coordinates `e^{v/2} e^{jv} Q^{−1/2−j}(e^v) = T_j(v) / (√2 · 2^j)`. -/
theorem exp_mul_arcQuadTerm_exp {c : ℝ} (hc : |c| < 1) (j : ℕ) (v : ℝ) :
    Real.exp (v / 2) * Real.exp v ^ j * arcQuadTerm c j (Real.exp v) =
      coshTerm c j v / (Real.sqrt 2 * 2 ^ j) := by
  have hW := coshShift_pos hc v
  have he := Real.exp_pos v
  unfold arcQuadTerm coshTerm
  rw [arcQuad_exp, Real.mul_rpow (by positivity) hW.le,
    Real.mul_rpow (by norm_num) he.le, mul_pow, mul_pow]
  have e1 : (2 : ℝ) ^ (-1 / 2 : ℝ) = (Real.sqrt 2)⁻¹ := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg (by norm_num)]; norm_num
  have e2 : Real.exp v ^ (-1 / 2 : ℝ) = (Real.exp (v / 2))⁻¹ := by
    rw [← Real.exp_mul, ← Real.exp_neg]; ring_nf
  rw [e1, e2]
  have h2 : (0 : ℝ) < Real.sqrt 2 := by positivity
  field_simp

/-- The twisted point vector `τ_c`. -/
def twPointVec (c x : ℝ) : ℝ :=
  4 * c * x * arcQuadTerm c 1 x + (42 * c ^ 2 - 18) * x ^ 2 * arcQuadTerm c 2 x +
    120 * c * (c ^ 2 - 1) * x ^ 3 * arcQuadTerm c 3 x +
      105 * (1 - c ^ 2) ^ 2 * x ^ 4 * arcQuadTerm c 4 x

theorem exp_half_mul_twPointVec {c : ℝ} (hc : |c| < 1) (v : ℝ) :
    Real.exp (v / 2) * twPointVec c (Real.exp v) = twCoshKernel c v / Real.sqrt 2 := by
  have k1 := exp_mul_arcQuadTerm_exp hc 1 v
  have k2 := exp_mul_arcQuadTerm_exp hc 2 v
  have k3 := exp_mul_arcQuadTerm_exp hc 3 v
  have k4 := exp_mul_arcQuadTerm_exp hc 4 v
  have h2 : (0 : ℝ) < Real.sqrt 2 := by positivity
  unfold twPointVec twCoshKernel
  have e : Real.exp (v / 2) * (4 * c * Real.exp v * arcQuadTerm c 1 (Real.exp v) +
      (42 * c ^ 2 - 18) * Real.exp v ^ 2 * arcQuadTerm c 2 (Real.exp v) +
      120 * c * (c ^ 2 - 1) * Real.exp v ^ 3 * arcQuadTerm c 3 (Real.exp v) +
      105 * (1 - c ^ 2) ^ 2 * Real.exp v ^ 4 * arcQuadTerm c 4 (Real.exp v)) =
      4 * c * (Real.exp (v / 2) * Real.exp v ^ 1 * arcQuadTerm c 1 (Real.exp v)) +
      (42 * c ^ 2 - 18) * (Real.exp (v / 2) * Real.exp v ^ 2 * arcQuadTerm c 2 (Real.exp v)) +
      120 * c * (c ^ 2 - 1) * (Real.exp (v / 2) * Real.exp v ^ 3 * arcQuadTerm c 3 (Real.exp v)) +
      105 * (1 - c ^ 2) ^ 2 * (Real.exp (v / 2) * Real.exp v ^ 4 *
        arcQuadTerm c 4 (Real.exp v)) := by ring
  rw [e, k1, k2, k3, k4]
  field_simp
  ring

/-! ### Symmetries -/

theorem arcQuad_neg_neg (c x : ℝ) : arcQuad (-c) (-x) = arcQuad c x := by unfold arcQuad; ring

theorem arcQuadTerm_neg_neg (c : ℝ) (j : ℕ) (x : ℝ) :
    arcQuadTerm (-c) j (-x) = arcQuadTerm c j x := by
  unfold arcQuadTerm; rw [arcQuad_neg_neg]

theorem twPointVec_neg_neg (c x : ℝ) : twPointVec (-c) (-x) = twPointVec c x := by
  unfold twPointVec
  simp only [arcQuadTerm_neg_neg]
  ring

theorem arcQuadTerm_inv {c : ℝ} (hc : |c| < 1) (j : ℕ) {x : ℝ} (hx : x ≠ 0) :
    arcQuadTerm c j (1 / x) = |x| * x ^ (2 * j) * arcQuadTerm c j x := by
  have hQ := arcQuad_pos hc x
  have hx2 : 0 < x ^ 2 := by positivity
  have e : arcQuad c (1 / x) = arcQuad c x / x ^ 2 := by
    unfold arcQuad; field_simp; ring
  unfold arcQuadTerm
  rw [e, Real.div_rpow hQ.le hx2.le, div_pow]
  have e2 : (x ^ 2) ^ (-1 / 2 : ℝ) = |x|⁻¹ := by
    rw [show (-1 / 2 : ℝ) = -(1 / 2) by norm_num, Real.rpow_neg hx2.le, ← Real.sqrt_eq_rpow,
      Real.sqrt_sq_eq_abs]
  rw [e2, pow_mul]
  have hax : 0 < |x| := abs_pos.mpr hx
  field_simp

/-- `τ_c(1/x) = |x| τ_c(x)`. -/
theorem twPointVec_inv {c : ℝ} (hc : |c| < 1) {x : ℝ} (hx : x ≠ 0) :
    twPointVec c (1 / x) = |x| * twPointVec c x := by
  unfold twPointVec
  simp only [arcQuadTerm_inv hc _ hx]
  field_simp
  ring

/-! ### The derivative -/

/-- The derivative of `τ_c`, expanded into monomials `x^i Q^{−1/2−j}`. -/
def twPointDeriv (c x : ℝ) : ℝ :=
  4 * c * arcQuadTerm c 1 x - 12 * c * x ^ 2 * arcQuadTerm c 2 x +
    12 * c ^ 2 * x * arcQuadTerm c 2 x + (84 * c ^ 2 - 36) * x * arcQuadTerm c 2 x -
    (210 * c ^ 2 - 90) * x ^ 3 * arcQuadTerm c 3 x + (210 * c ^ 3 - 90 * c) * x ^ 2 * arcQuadTerm c 3 x +
    360 * c * (c ^ 2 - 1) * x ^ 2 * arcQuadTerm c 3 x -
    840 * c * (c ^ 2 - 1) * x ^ 4 * arcQuadTerm c 4 x +
    840 * c ^ 2 * (c ^ 2 - 1) * x ^ 3 * arcQuadTerm c 4 x +
    420 * (1 - c ^ 2) ^ 2 * x ^ 3 * arcQuadTerm c 4 x -
    945 * (1 - c ^ 2) ^ 2 * x ^ 5 * arcQuadTerm c 5 x +
    945 * c * (1 - c ^ 2) ^ 2 * x ^ 4 * arcQuadTerm c 5 x

theorem hasDerivAt_twPointVec {c : ℝ} (hc : |c| < 1) (x : ℝ) :
    HasDerivAt (twPointVec c) (twPointDeriv c x) x := by
  have t1 := hasDerivAt_arcQuadTerm hc 1 x
  have t2 := hasDerivAt_arcQuadTerm hc 2 x
  have t3 := hasDerivAt_arcQuadTerm hc 3 x
  have t4 := hasDerivAt_arcQuadTerm hc 4 x
  have hx := hasDerivAt_id x
  have h := ((((hx.const_mul (4 * c)).mul t1).add
    ((((hx.pow 2).const_mul (42 * c ^ 2 - 18)).mul t2))).add
    ((((hx.pow 3).const_mul (120 * c * (c ^ 2 - 1))).mul t3))).add
    ((((hx.pow 4).const_mul (105 * (1 - c ^ 2) ^ 2)).mul t4))
  simp only [id, Pi.pow_apply] at h
  unfold twPointVec
  refine h.congr_deriv ?_
  unfold twPointDeriv
  push_cast
  ring

theorem continuous_twPointVec {c : ℝ} (hc : |c| < 1) : Continuous (twPointVec c) := by
  unfold twPointVec; have := continuous_arcQuadTerm hc; fun_prop

theorem continuous_twPointDeriv {c : ℝ} (hc : |c| < 1) : Continuous (twPointDeriv c) := by
  unfold twPointDeriv; have := continuous_arcQuadTerm hc; fun_prop

/-! ### Decay in `x` -/

/-- `|x|^i Q_c(x)^{−1/2−j} ≤ 2^{j+1} / (1 + x²)` for `|c| ≤ ½` and `i + 1 ≤ 2j`. -/
theorem pow_abs_mul_arcQuadTerm_le {c : ℝ} (hc : |c| ≤ 1 / 2) {i j : ℕ} (hij : i + 1 ≤ 2 * j)
    (x : ℝ) : |x| ^ i * arcQuadTerm c j x ≤ 2 ^ (j + 1) * (1 + x ^ 2)⁻¹ := by
  have hc1 : |c| < 1 := by linarith
  set a := 1 - |c| with ha_def
  set s := 1 + x ^ 2 with hs_def
  have ha : 1 / 2 ≤ a := by rw [ha_def]; linarith
  have ha0 : 0 < a := by linarith
  have hs : 1 ≤ s := by rw [hs_def]; nlinarith [sq_nonneg x]
  have hs0 : 0 < s := by linarith
  have hQ : a * s ≤ arcQuad c x := arcQuad_ge c x
  have hQ0 := arcQuad_pos hc1 x
  set r := Real.sqrt s with hr_def
  have hr1 : 1 ≤ r := by rw [hr_def]; exact Real.one_le_sqrt.mpr hs
  have hr0 : 0 < r := by linarith
  have hrs : r ^ 2 = s := Real.sq_sqrt hs0.le
  have hxr : |x| ≤ r := by
    rw [hr_def, ← Real.sqrt_sq_eq_abs]; exact Real.sqrt_le_sqrt (by rw [hs_def]; linarith)
  -- `Q^{−1/2} ≤ a^{−1/2} r⁻¹`
  have h1 : arcQuad c x ^ (-1 / 2 : ℝ) ≤ a ^ (-1 / 2 : ℝ) * r⁻¹ := by
    have e : r⁻¹ = s ^ (-1 / 2 : ℝ) := by
      rw [hr_def, Real.sqrt_eq_rpow, ← Real.rpow_neg hs0.le]; norm_num
    rw [e, ← Real.mul_rpow ha0.le hs0.le]
    exact Real.rpow_le_rpow_of_nonpos (by positivity) hQ (by norm_num)
  have h2 : a ^ (-1 / 2 : ℝ) ≤ 2 := by
    have : a ^ (-1 / 2 : ℝ) ≤ (1 / 2 : ℝ) ^ (-1 / 2 : ℝ) :=
      Real.rpow_le_rpow_of_nonpos (by norm_num) ha (by norm_num)
    refine this.trans ?_
    rw [show (-1 / 2 : ℝ) = -(1 / 2) by norm_num, Real.rpow_neg (by norm_num),
      ← Real.sqrt_eq_rpow, Real.sqrt_div' 1 (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_one, inv_div]
    rw [div_one]
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
  have h3 : (a * s) ^ j ≤ arcQuad c x ^ j := pow_le_pow_left₀ (by positivity) hQ j
  have h4 : (1 / 2 : ℝ) ^ j * r ^ (2 * j) ≤ (a * s) ^ j := by
    rw [pow_mul, hrs, ← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_right ha hs0.le) j
  have h5 : |x| ^ i ≤ r ^ i := pow_le_pow_left₀ (abs_nonneg x) hxr i
  have h6 : r ^ i * r ^ 2 ≤ r ^ (2 * j) * r := by
    rw [← pow_add, ← pow_succ]
    exact pow_le_pow_right₀ hr1 (by omega)
  unfold arcQuadTerm
  rw [← hrs]
  have hT0 : 0 ≤ arcQuad c x ^ (-1 / 2 : ℝ) := Real.rpow_nonneg hQ0.le _
  calc |x| ^ i * (arcQuad c x ^ (-1 / 2 : ℝ) / arcQuad c x ^ j)
      ≤ r ^ i * (a ^ (-1 / 2 : ℝ) * r⁻¹ / ((1 / 2 : ℝ) ^ j * r ^ (2 * j))) := by
        gcongr
        · exact h4.trans h3
    _ ≤ r ^ i * (2 * r⁻¹ / ((1 / 2 : ℝ) ^ j * r ^ (2 * j))) := by gcongr
    _ = 2 ^ (j + 1) * (r ^ i / (r ^ (2 * j) * r)) := by
        rw [one_div, inv_pow, pow_succ]; field_simp
    _ ≤ 2 ^ (j + 1) * (r ^ 2)⁻¹ := by
        gcongr
        rw [div_le_iff₀ (by positivity), inv_mul_eq_div, le_div_iff₀ (by positivity)]
        linarith [h6]

theorem abs_mono_le {c : ℝ} (hc : |c| ≤ 1 / 2) (α : ℝ) {i j : ℕ} (hij : i + 1 ≤ 2 * j) (x : ℝ) :
    |α * x ^ i * arcQuadTerm c j x| ≤ |α| * 2 ^ (j + 1) * (1 + x ^ 2)⁻¹ := by
  have hc1 : |c| < 1 := by linarith
  rw [abs_mul, abs_mul, abs_pow, abs_of_pos (arcQuadTerm_pos hc1 j x), mul_assoc, mul_assoc]
  exact mul_le_mul_of_nonneg_left (pow_abs_mul_arcQuadTerm_le hc hij x) (abs_nonneg α)

theorem abs_coef_le {c : ℝ} (hc : |c| ≤ 1 / 2) :
    |4 * c| ≤ 2 ∧ |42 * c ^ 2 - 18| ≤ 18 ∧ |120 * c * (c ^ 2 - 1)| ≤ 60 ∧
      |105 * (1 - c ^ 2) ^ 2| ≤ 105 := by
  have h0 := abs_nonneg c
  have hsq : c ^ 2 ≤ 1 / 4 := by nlinarith [sq_abs c]
  have hsq0 : 0 ≤ c ^ 2 := sq_nonneg c
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [abs_mul]; norm_num; linarith
  · rw [abs_le]; constructor <;> nlinarith
  · rw [abs_mul, abs_mul, abs_of_nonpos (by linarith : c ^ 2 - 1 ≤ 0)]
    norm_num
    nlinarith
  · rw [abs_of_nonneg (by positivity)]
    nlinarith [sq_nonneg (1 - c ^ 2)]

/-- `|τ_c(x)| ≤ 4500 / (1 + x²)` for `|c| ≤ ½`. -/
theorem abs_twPointVec_le {c : ℝ} (hc : |c| ≤ 1 / 2) (x : ℝ) :
    |twPointVec c x| ≤ 4500 * (1 + x ^ 2)⁻¹ := by
  obtain ⟨b1, b2, b3, b4⟩ := abs_coef_le hc
  have m1 := abs_mono_le hc (4 * c) (i := 1) (j := 1) (by norm_num) x
  have m2 := abs_mono_le hc (42 * c ^ 2 - 18) (i := 2) (j := 2) (by norm_num) x
  have m3 := abs_mono_le hc (120 * c * (c ^ 2 - 1)) (i := 3) (j := 3) (by norm_num) x
  have m4 := abs_mono_le hc (105 * (1 - c ^ 2) ^ 2) (i := 4) (j := 4) (by norm_num) x
  have hp : 0 < (1 + x ^ 2)⁻¹ := by positivity
  unfold twPointVec
  have e : 4 * c * x * arcQuadTerm c 1 x = 4 * c * x ^ 1 * arcQuadTerm c 1 x := by ring
  rw [e]
  calc _ ≤ |4 * c * x ^ 1 * arcQuadTerm c 1 x| + |(42 * c ^ 2 - 18) * x ^ 2 * arcQuadTerm c 2 x| +
        |120 * c * (c ^ 2 - 1) * x ^ 3 * arcQuadTerm c 3 x| +
        |105 * (1 - c ^ 2) ^ 2 * x ^ 4 * arcQuadTerm c 4 x| := by
        refine (abs_add_le _ _).trans ?_
        exact add_le_add ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)) le_rfl
    _ ≤ 2 * 2 ^ 2 * (1 + x ^ 2)⁻¹ + 18 * 2 ^ 3 * (1 + x ^ 2)⁻¹ + 60 * 2 ^ 4 * (1 + x ^ 2)⁻¹ +
        105 * 2 ^ 5 * (1 + x ^ 2)⁻¹ := by
        gcongr
        · exact m1.trans (by gcongr)
        · exact m2.trans (by gcongr)
        · exact m3.trans (by gcongr)
        · exact m4.trans (by gcongr)
    _ ≤ 4500 * (1 + x ^ 2)⁻¹ := by nlinarith

/-- `|τ_c′(x)| ≤ 130000 / (1 + x²)` for `|c| ≤ ½`. -/
theorem abs_twPointDeriv_le {c : ℝ} (hc : |c| ≤ 1 / 2) (x : ℝ) :
    |twPointDeriv c x| ≤ 130000 * (1 + x ^ 2)⁻¹ := by
  have h0 := abs_nonneg c
  have hsq : c ^ 2 ≤ 1 / 4 := by nlinarith [sq_abs c]
  have hsq0 : 0 ≤ c ^ 2 := sq_nonneg c
  have hcc : |c| ^ 2 = c ^ 2 := sq_abs c
  have k1 : |4 * c| ≤ 2 := by rw [abs_mul]; norm_num; linarith
  have k2 : |12 * c| ≤ 6 := by rw [abs_mul]; norm_num; linarith
  have k3 : |12 * c ^ 2| ≤ 3 := by rw [abs_of_nonneg (by positivity)]; linarith
  have k4 : |84 * c ^ 2 - 36| ≤ 36 := by rw [abs_le]; constructor <;> nlinarith
  have k5 : |210 * c ^ 2 - 90| ≤ 90 := by rw [abs_le]; constructor <;> nlinarith
  have k6 : |210 * c ^ 3 - 90 * c| ≤ 45 := by
    have : 210 * c ^ 3 - 90 * c = c * (210 * c ^ 2 - 90) := by ring
    rw [this, abs_mul]; nlinarith
  have k7 : |360 * c * (c ^ 2 - 1)| ≤ 180 := by
    rw [abs_mul, abs_mul, abs_of_nonpos (by linarith : c ^ 2 - 1 ≤ 0)]; norm_num; nlinarith
  have k8 : |840 * c * (c ^ 2 - 1)| ≤ 420 := by
    rw [abs_mul, abs_mul, abs_of_nonpos (by linarith : c ^ 2 - 1 ≤ 0)]; norm_num; nlinarith
  have k9 : |840 * c ^ 2 * (c ^ 2 - 1)| ≤ 210 := by
    rw [abs_mul, abs_of_nonpos (by linarith : c ^ 2 - 1 ≤ 0), abs_of_nonneg (by positivity)]
    nlinarith
  have k10 : |420 * (1 - c ^ 2) ^ 2| ≤ 420 := by
    rw [abs_of_nonneg (by positivity)]; nlinarith [sq_nonneg (1 - c ^ 2)]
  have k11 : |945 * (1 - c ^ 2) ^ 2| ≤ 945 := by
    rw [abs_of_nonneg (by positivity)]; nlinarith [sq_nonneg (1 - c ^ 2)]
  have k12 : |945 * c * (1 - c ^ 2) ^ 2| ≤ 473 := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (1 - c ^ 2) ^ 2)]
    norm_num
    have : (1 - c ^ 2) ^ 2 ≤ 1 := by nlinarith
    nlinarith
  have hp : 0 < (1 + x ^ 2)⁻¹ := by positivity
  have m1 := abs_mono_le hc (4 * c) (i := 0) (j := 1) (by norm_num) x
  have m2 := abs_mono_le hc (12 * c) (i := 2) (j := 2) (by norm_num) x
  have m3 := abs_mono_le hc (12 * c ^ 2) (i := 1) (j := 2) (by norm_num) x
  have m4 := abs_mono_le hc (84 * c ^ 2 - 36) (i := 1) (j := 2) (by norm_num) x
  have m5 := abs_mono_le hc (210 * c ^ 2 - 90) (i := 3) (j := 3) (by norm_num) x
  have m6 := abs_mono_le hc (210 * c ^ 3 - 90 * c) (i := 2) (j := 3) (by norm_num) x
  have m7 := abs_mono_le hc (360 * c * (c ^ 2 - 1)) (i := 2) (j := 3) (by norm_num) x
  have m8 := abs_mono_le hc (840 * c * (c ^ 2 - 1)) (i := 4) (j := 4) (by norm_num) x
  have m9 := abs_mono_le hc (840 * c ^ 2 * (c ^ 2 - 1)) (i := 3) (j := 4) (by norm_num) x
  have m10 := abs_mono_le hc (420 * (1 - c ^ 2) ^ 2) (i := 3) (j := 4) (by norm_num) x
  have m11 := abs_mono_le hc (945 * (1 - c ^ 2) ^ 2) (i := 5) (j := 5) (by norm_num) x
  have m12 := abs_mono_le hc (945 * c * (1 - c ^ 2) ^ 2) (i := 4) (j := 5) (by norm_num) x
  have e : twPointDeriv c x = 4 * c * x ^ 0 * arcQuadTerm c 1 x - 12 * c * x ^ 2 * arcQuadTerm c 2 x +
      12 * c ^ 2 * x ^ 1 * arcQuadTerm c 2 x + (84 * c ^ 2 - 36) * x ^ 1 * arcQuadTerm c 2 x -
      (210 * c ^ 2 - 90) * x ^ 3 * arcQuadTerm c 3 x +
      (210 * c ^ 3 - 90 * c) * x ^ 2 * arcQuadTerm c 3 x +
      360 * c * (c ^ 2 - 1) * x ^ 2 * arcQuadTerm c 3 x -
      840 * c * (c ^ 2 - 1) * x ^ 4 * arcQuadTerm c 4 x +
      840 * c ^ 2 * (c ^ 2 - 1) * x ^ 3 * arcQuadTerm c 4 x +
      420 * (1 - c ^ 2) ^ 2 * x ^ 3 * arcQuadTerm c 4 x -
      945 * (1 - c ^ 2) ^ 2 * x ^ 5 * arcQuadTerm c 5 x +
      945 * c * (1 - c ^ 2) ^ 2 * x ^ 4 * arcQuadTerm c 5 x := by
    unfold twPointDeriv; ring
  rw [e]
  have t1 := m1.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right k1 (by positivity)) hp.le)
  have t2 := m2.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right k2 (by positivity)) hp.le)
  have t3 := m3.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right k3 (by positivity)) hp.le)
  have t4 := m4.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right k4 (by positivity)) hp.le)
  have t5 := m5.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right k5 (by positivity)) hp.le)
  have t6 := m6.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right k6 (by positivity)) hp.le)
  have t7 := m7.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right k7 (by positivity)) hp.le)
  have t8 := m8.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right k8 (by positivity)) hp.le)
  have t9 := m9.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right k9 (by positivity)) hp.le)
  have t10 := m10.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right k10 (by positivity)) hp.le)
  have t11 := m11.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right k11 (by positivity)) hp.le)
  have t12 := m12.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right k12 (by positivity)) hp.le)
  set A1 := 4 * c * x ^ 0 * arcQuadTerm c 1 x
  set A2 := 12 * c * x ^ 2 * arcQuadTerm c 2 x
  set A3 := 12 * c ^ 2 * x ^ 1 * arcQuadTerm c 2 x
  set A4 := (84 * c ^ 2 - 36) * x ^ 1 * arcQuadTerm c 2 x
  set A5 := (210 * c ^ 2 - 90) * x ^ 3 * arcQuadTerm c 3 x
  set A6 := (210 * c ^ 3 - 90 * c) * x ^ 2 * arcQuadTerm c 3 x
  set A7 := 360 * c * (c ^ 2 - 1) * x ^ 2 * arcQuadTerm c 3 x
  set A8 := 840 * c * (c ^ 2 - 1) * x ^ 4 * arcQuadTerm c 4 x
  set A9 := 840 * c ^ 2 * (c ^ 2 - 1) * x ^ 3 * arcQuadTerm c 4 x
  set A10 := 420 * (1 - c ^ 2) ^ 2 * x ^ 3 * arcQuadTerm c 4 x
  set A11 := 945 * (1 - c ^ 2) ^ 2 * x ^ 5 * arcQuadTerm c 5 x
  set A12 := 945 * c * (1 - c ^ 2) ^ 2 * x ^ 4 * arcQuadTerm c 5 x
  have hsum : |A1 - A2 + A3 + A4 - A5 + A6 + A7 - A8 + A9 + A10 - A11 + A12| ≤
      |A1| + |A2| + |A3| + |A4| + |A5| + |A6| + |A7| + |A8| + |A9| + |A10| + |A11| + |A12| := by
    rw [abs_le]
    constructor <;> linarith [neg_abs_le A1, neg_abs_le A2, neg_abs_le A3, neg_abs_le A4,
      neg_abs_le A5, neg_abs_le A6, neg_abs_le A7, neg_abs_le A8, neg_abs_le A9, neg_abs_le A10,
      neg_abs_le A11, neg_abs_le A12, le_abs_self A1, le_abs_self A2, le_abs_self A3,
      le_abs_self A4, le_abs_self A5, le_abs_self A6, le_abs_self A7, le_abs_self A8,
      le_abs_self A9, le_abs_self A10, le_abs_self A11, le_abs_self A12]
  refine hsum.trans ?_
  norm_num at t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12
  linarith

/-! ### The twisted arc vector of an arc point -/

theorem abs_arcParam_le (u : ArcParam) : |(u : ℝ)| ≤ 1 / 2 :=
  abs_le.mpr ⟨by linarith [u.2.1], u.2.2⟩

theorem abs_arcParam_lt (u : ArcParam) : |(u : ℝ)| < 1 := by linarith [abs_arcParam_le u]

theorem abs_neg_arcParam_le (u : ArcParam) : |-(u : ℝ)| ≤ 1 / 2 := by
  rw [abs_neg]; exact abs_arcParam_le u

/-- The twisted arc vector `g_u = √y (τ_u + τ_{−u})`. -/
def twArcVector (u : ArcParam) (x : ℝ) : ℝ :=
  Real.sqrt (modularArcHeight u) * (twPointVec u x + twPointVec (-u) x)

/-- Its derivative. -/
def twArcDeriv (u : ArcParam) (x : ℝ) : ℝ :=
  Real.sqrt (modularArcHeight u) * (twPointDeriv u x + twPointDeriv (-u) x)

theorem hasDerivAt_twArcVector (u : ArcParam) (x : ℝ) :
    HasDerivAt (twArcVector u) (twArcDeriv u x) x := by
  have hu := abs_arcParam_lt u
  have hu' : |-(u : ℝ)| < 1 := by rwa [abs_neg]
  exact ((hasDerivAt_twPointVec hu x).add (hasDerivAt_twPointVec hu' x)).const_mul _

theorem twArcVector_neg (u : ArcParam) (x : ℝ) : twArcVector u (-x) = twArcVector u x := by
  unfold twArcVector
  have h1 := twPointVec_neg_neg (u : ℝ) x
  have h2 := twPointVec_neg_neg (-(u : ℝ)) x
  rw [neg_neg] at h2
  rw [h1, h2]; ring

theorem twArcVector_inv (u : ArcParam) {x : ℝ} (hx : x ≠ 0) :
    twArcVector u (1 / x) = |x| * twArcVector u x := by
  have hu := abs_arcParam_lt u
  have hu' : |-(u : ℝ)| < 1 := by rwa [abs_neg]
  unfold twArcVector
  rw [twPointVec_inv hu hx, twPointVec_inv hu' hx]; ring

theorem sqrt_modularArcHeight_le_one (u : ArcParam) : Real.sqrt (modularArcHeight u) ≤ 1 :=
  Real.sqrt_le_one.mpr (modularArcHeight_le_one u)

theorem abs_twArcVector_le (u : ArcParam) (x : ℝ) :
    |twArcVector u x| ≤ 9000 * (1 + x ^ 2)⁻¹ := by
  have h1 := abs_twPointVec_le (abs_arcParam_le u) x
  have h2 := abs_twPointVec_le (abs_neg_arcParam_le u) x
  have hs := sqrt_modularArcHeight_le_one u
  have hs0 := Real.sqrt_nonneg (modularArcHeight u)
  unfold twArcVector
  rw [abs_mul, abs_of_nonneg hs0]
  calc Real.sqrt (modularArcHeight u) * |twPointVec u x + twPointVec (-u) x|
      ≤ 1 * (4500 * (1 + x ^ 2)⁻¹ + 4500 * (1 + x ^ 2)⁻¹) :=
        mul_le_mul hs ((abs_add_le _ _).trans (add_le_add h1 h2)) (abs_nonneg _) zero_le_one
    _ = _ := by ring

theorem abs_twArcDeriv_le (u : ArcParam) (x : ℝ) :
    |twArcDeriv u x| ≤ 260000 * (1 + x ^ 2)⁻¹ := by
  have h1 := abs_twPointDeriv_le (abs_arcParam_le u) x
  have h2 := abs_twPointDeriv_le (abs_neg_arcParam_le u) x
  have hs := sqrt_modularArcHeight_le_one u
  have hs0 := Real.sqrt_nonneg (modularArcHeight u)
  unfold twArcDeriv
  rw [abs_mul, abs_of_nonneg hs0]
  calc Real.sqrt (modularArcHeight u) * |twPointDeriv u x + twPointDeriv (-u) x|
      ≤ 1 * (130000 * (1 + x ^ 2)⁻¹ + 130000 * (1 + x ^ 2)⁻¹) :=
        mul_le_mul hs ((abs_add_le _ _).trans (add_le_add h1 h2)) (abs_nonneg _) zero_le_one
    _ = _ := by ring

theorem continuous_twArcVector (u : ArcParam) : Continuous (twArcVector u) := by
  have hu := abs_arcParam_lt u
  have hu' : |-(u : ℝ)| < 1 := by rwa [abs_neg]
  unfold twArcVector
  exact continuous_const.mul ((continuous_twPointVec hu).add (continuous_twPointVec hu'))

theorem continuous_twArcDeriv (u : ArcParam) : Continuous (twArcDeriv u) := by
  have hu := abs_arcParam_lt u
  have hu' : |-(u : ℝ)| < 1 := by rwa [abs_neg]
  unfold twArcDeriv
  exact continuous_const.mul ((continuous_twPointDeriv hu).add (continuous_twPointDeriv hu'))

theorem integrable_of_le_inv_one_add_sq {f : ℝ → ℝ} (hf : Continuous f) {C : ℝ}
    (hC : ∀ x, |f x| ≤ C * (1 + x ^ 2)⁻¹) : Integrable f :=
  (integrable_inv_one_add_sq.const_mul C).mono' hf.aestronglyMeasurable
    (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hC x)

theorem integrable_twArcVector (u : ArcParam) : Integrable (twArcVector u) :=
  integrable_of_le_inv_one_add_sq (continuous_twArcVector u) (abs_twArcVector_le u)

theorem integrable_twArcDeriv (u : ArcParam) : Integrable (twArcDeriv u) :=
  integrable_of_le_inv_one_add_sq (continuous_twArcDeriv u) (abs_twArcDeriv_le u)

/-- **Logarithmic profile**: `e^{v/2} g_u(e^v) = √(y/2) (¼ − ∂²)² 𝒦_u(v)`. -/
theorem exp_half_mul_twArcVector (u : ArcParam) (v : ℝ) :
    Real.exp (v / 2) * twArcVector u (Real.exp v) =
      Real.sqrt (modularArcHeight u / 2) * twSymCoshKernel u v := by
  have hu := abs_arcParam_lt u
  have hu' : |-(u : ℝ)| < 1 := by rwa [abs_neg]
  have h1 := exp_half_mul_twPointVec hu v
  have h2 := exp_half_mul_twPointVec hu' v
  unfold twArcVector twSymCoshKernel
  rw [Real.sqrt_div' _ (by norm_num : (0 : ℝ) ≤ 2)]
  have h22 : (0 : ℝ) < Real.sqrt 2 := by positivity
  rw [show Real.exp (v / 2) * (Real.sqrt (modularArcHeight u) * (twPointVec u (Real.exp v) +
      twPointVec (-u) (Real.exp v))) = Real.sqrt (modularArcHeight u) *
      (Real.exp (v / 2) * twPointVec u (Real.exp v) + Real.exp (v / 2) * twPointVec (-u) (Real.exp v))
      by ring, h1, h2]
  field_simp

/-- **Zero mean**: `∫ g_u = 0`. -/
theorem integral_twArcVector_eq_zero (u : ArcParam) : ∫ x, twArcVector u x = 0 := by
  have hu := abs_arcParam_lt u
  have heven : ∀ x, twArcVector u |x| = twArcVector u x := fun x => by
    rcases le_total 0 x with hx | hx
    · rw [abs_of_nonneg hx]
    · rw [abs_of_nonpos hx, twArcVector_neg]
  have h1 : ∫ x, twArcVector u x = 2 * ∫ x in Ioi 0, twArcVector u x := by
    rw [← integral_comp_abs (f := twArcVector u)]
    exact integral_congr_ae (Eventually.of_forall fun x => (heven x).symm)
  rw [h1, setIntegral_Ioi_eq_integral_exp_mul]
  have h2 : ∀ v, Real.exp v * twArcVector u (Real.exp v) = Real.exp (v / 2) *
      (Real.sqrt (modularArcHeight u / 2) * twSymCoshKernel u v) := fun v => by
    rw [← exp_half_mul_twArcVector, ← mul_assoc, ← Real.exp_add]; ring_nf
  simp_rw [h2]
  have e : (fun v => Real.exp (v / 2) * (Real.sqrt (modularArcHeight u / 2) *
      twSymCoshKernel u v)) = fun v => Real.sqrt (modularArcHeight u / 2) *
        (Real.exp (v / 2) * twSymCoshKernel u v) := by funext v; ring
  rw [e, integral_const_mul, integral_exp_half_mul_twSymCoshKernel hu, mul_zero, mul_zero]

/-- **Strict positive definiteness** of the log profile of `g_u`. -/
theorem integral_cos_mul_twArcProfile_pos (u : ArcParam) (τ : ℝ) :
    0 < ∫ v, Real.cos (τ * v) * (Real.exp (v / 2) * twArcVector u (Real.exp v)) := by
  have hu := abs_arcParam_lt u
  simp_rw [exp_half_mul_twArcVector]
  have e : (fun v => Real.cos (τ * v) * (Real.sqrt (modularArcHeight u / 2) *
      twSymCoshKernel u v)) = fun v => Real.sqrt (modularArcHeight u / 2) *
        (Real.cos (τ * v) * twSymCoshKernel u v) := by funext v; ring
  rw [e, integral_const_mul]
  exact mul_pos (Real.sqrt_pos.mpr (by have := modularArcHeight_pos u.2; positivity))
    (integral_cos_mul_twSymCoshKernel_pos hu τ)

/-- **Moments**: `∫ g_u′ sin(ωx) = −ω ∫ g_u cos(ωx)`. -/
theorem integral_twArcDeriv_mul_sin (u : ArcParam) (ω : ℝ) :
    ∫ x, twArcDeriv u x * Real.sin (ω * x) = -(ω * ∫ x, twArcVector u x * Real.cos (ω * x)) := by
  have hs : ∀ x, HasDerivAt (fun y => Real.sin (ω * y)) (ω * Real.cos (ω * x)) x := fun x => by
    have h := ((hasDerivAt_id x).const_mul ω).sin
    simp only [id, mul_one] at h
    exact h.congr_deriv (by ring)
  have bsin : ∀ x, |Real.sin (ω * x)| ≤ 1 := fun x => Real.abs_sin_le_one _
  have i1 : Integrable fun x => Real.sin (ω * x) * twArcDeriv u x :=
    integrable_of_le_inv_one_add_sq (by have := continuous_twArcDeriv u; fun_prop)
      (C := 260000) fun x => by
        rw [abs_mul]
        exact (mul_le_mul (bsin x) (abs_twArcDeriv_le u x) (abs_nonneg _) zero_le_one).trans
          (by rw [one_mul])
  have i2 : Integrable fun x => ω * Real.cos (ω * x) * twArcVector u x :=
    integrable_of_le_inv_one_add_sq (by have := continuous_twArcVector u; fun_prop)
      (C := |ω| * 9000) fun x => by
        rw [abs_mul, abs_mul, mul_assoc]
        exact mul_le_mul_of_nonneg_left ((mul_le_mul (Real.abs_cos_le_one _)
          (abs_twArcVector_le u x) (abs_nonneg _) zero_le_one).trans (by rw [one_mul]))
          (abs_nonneg ω) |>.trans (by ring_nf; exact le_rfl)
  have i3 : Integrable fun x => Real.sin (ω * x) * twArcVector u x :=
    integrable_of_le_inv_one_add_sq (by have := continuous_twArcVector u; fun_prop)
      (C := 9000) fun x => by
        rw [abs_mul]
        exact (mul_le_mul (bsin x) (abs_twArcVector_le u x) (abs_nonneg _) zero_le_one).trans
          (by rw [one_mul])
  have h := integral_mul_deriv_eq_deriv_mul_of_integrable (fun x _ => hs x)
    (fun x _ => hasDerivAt_twArcVector u x) i1 i2 i3
  have e1 : (fun x => twArcDeriv u x * Real.sin (ω * x)) =
      fun x => Real.sin (ω * x) * twArcDeriv u x := by funext x; ring
  have e2 : (fun x => ω * Real.cos (ω * x) * twArcVector u x) =
      fun x => ω * (twArcVector u x * Real.cos (ω * x)) := by funext x; ring
  rw [e1, h, e2, integral_const_mul]

end

end RHTower
