import GaloisForLFunctions.RHTower.WeilRegularVariationLockRigidity

/-!
# Lock densities decaying like `1/log x` are impossible

Let `G` be a Herglotz producer.  Suppose that on the lower critical line

`G(1 − s) = κ₀ e^{iθ(x)} G(s)`,  `s = ½ − 2ix`, `x > 0`,  `θ(x) = x / log(x + e)`.

The density `θ'(x)/2π ≈ 1/(2π log x)` tends to `0`, so the non-integer spectral mass `θ(x)/2π` is
`x/log x`.  It grows faster than every power `x^α`, `α < 1`, the reach of the power-growth
theorem (`abelian_twist_power_rigidity`), and has no positive density margin
(`margin_twist_lock_impossible`).

**Theorem** (`log_density_lock_impossible`).  No Herglotz producer has this lock.

This places the regular-variation theorem (`regular_twist_lock_impossible`) on the range between
the power theorem and the margin theorem.

**Proof.**  With `w = i(s − ½)/2` (so `w = x` on the lower line) and `ℓ = Log(w + e)`, the phase
extends to `L(s) = i w/ℓ`, holomorphic on the lower region, where `Re w > 0`, `Im w ≥ 0`, `Re ℓ ≥ 1`
and `0 ≤ Im ℓ = arg(w + e) ≤ (π/2) Im w/|w + e|`.
* `Re L = (Re w · Im ℓ − Im w · Re ℓ)/|ℓ|² ≤ π/4` on the lower strip, and `Re L = 0` on the line.
* `L' = −θ₁(w)/2` with `θ₁ = 1/ℓ − w/((w + e)ℓ²)`, and `Re θ₁ ≥ (Re ℓ − 1)/|ℓ|² ≥ 1/(4 Re ℓ)`, so
  `y Re L'(3/2 + iy) ≥ |y|/(8 log(|y| + 4)) → ∞`.
* `L'' = −iθ₂(w)/4` with `|θ₂| ≤ 4/(|w + e||ℓ|²)`, so `‖L''‖/(Re L')² ≤ 64/|w + e| → 0`.
-/

open Complex Filter Topology Set MeasureTheory

namespace RHTower

namespace AbelianTwist

open GaloisForLFunctions GaloisForLFunctions.HTGeometry IntegerMassRigidity FractionalMassRigidity
  PhaseLockRigidity HamburgerStability TruncatedRadial RightEdgeKernel FractionalMassTailRigidity

noncomputable section

/-- `e` as a complex number. -/
def eC : ℂ := ((Real.exp 1 : ℝ) : ℂ)

/-- The phase `θ(w) = w / Log(w + e)`. -/
def ldTheta (w : ℂ) : ℂ := w / Complex.log (w + eC)

/-- `θ'(w) = 1/ℓ − w/((w + e)ℓ²)`, `ℓ = Log(w + e)`. -/
def ldTheta1 (w : ℂ) : ℂ :=
  1 / Complex.log (w + eC) - w / ((w + eC) * Complex.log (w + eC) ^ 2)

/-- `θ''(w) = −1/((w + e)ℓ²) − e/((w + e)²ℓ²) + 2w/((w + e)²ℓ³)`. -/
def ldTheta2 (w : ℂ) : ℂ :=
  -(1 / ((w + eC) * Complex.log (w + eC) ^ 2)) - eC / ((w + eC) ^ 2 * Complex.log (w + eC) ^ 2) +
    2 * w / ((w + eC) ^ 2 * Complex.log (w + eC) ^ 3)

/-- `w(s) = i(s − ½)/2`. -/
def ldW (s : ℂ) : ℂ := I * (s - 1 / 2) / 2

/-- The lock exponent `L(s) = i θ(w(s))`. -/
def ldExponent (s : ℂ) : ℂ := I * ldTheta (ldW s)

theorem eC_re : eC.re = Real.exp 1 := by rw [eC, Complex.ofReal_re]

theorem eC_im : eC.im = 0 := by rw [eC, Complex.ofReal_im]

/-! ### The region `Re w ≥ 0`, `Im w ≥ 0` -/

theorem re_add_eC_pos {w : ℂ} (hw : 0 ≤ w.re) : Real.exp 1 ≤ (w + eC).re := by
  simp [eC_re]; linarith

theorem slitPlane_add_eC {w : ℂ} (hw : 0 ≤ w.re) : w + eC ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]; left
  have := re_add_eC_pos hw; have := Real.exp_pos 1; linarith

theorem add_eC_ne_zero {w : ℂ} (hw : 0 ≤ w.re) : w + eC ≠ 0 :=
  Complex.slitPlane_ne_zero (slitPlane_add_eC hw)

theorem exp_one_le_norm_add_eC {w : ℂ} (hw : 0 ≤ w.re) : Real.exp 1 ≤ ‖w + eC‖ :=
  (re_add_eC_pos hw).trans (Complex.re_le_norm _)

theorem one_le_re_log {w : ℂ} (hw : 0 ≤ w.re) : 1 ≤ (Complex.log (w + eC)).re := by
  rw [Complex.log_re]
  have h := exp_one_le_norm_add_eC hw
  have := Real.log_le_log (Real.exp_pos 1) h
  rwa [Real.log_exp] at this

theorem log_add_eC_ne_zero {w : ℂ} (hw : 0 ≤ w.re) : Complex.log (w + eC) ≠ 0 := by
  intro h
  have := one_le_re_log hw
  rw [h] at this; simp at this; linarith

theorem one_le_norm_log {w : ℂ} (hw : 0 ≤ w.re) : 1 ≤ ‖Complex.log (w + eC)‖ :=
  (one_le_re_log hw).trans (Complex.re_le_norm _)

theorem norm_le_norm_add_eC {w : ℂ} (hw : 0 ≤ w.re) : ‖w‖ ≤ ‖w + eC‖ := by
  have h1 : ‖w‖ ^ 2 ≤ ‖w + eC‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.add_im, eC_re, eC_im, add_zero]
    have := Real.exp_pos 1
    nlinarith
  by_contra h
  push Not at h
  nlinarith [norm_nonneg w, norm_nonneg (w + eC)]

theorem im_log_nonneg {w : ℂ} (hw : 0 ≤ w.im) : 0 ≤ (Complex.log (w + eC)).im := by
  rw [Complex.log_im, Complex.arg_nonneg_iff]; simp [eC_im]; exact hw

theorem im_log_le {w : ℂ} (hwre : 0 ≤ w.re) (hw : 0 ≤ w.im) :
    (Complex.log (w + eC)).im ≤ Real.pi / 2 * (w.im / ‖w + eC‖) := by
  rw [Complex.log_im]
  have h0 : 0 ≤ (w + eC).arg := Complex.arg_nonneg_iff.mpr (by simp [eC_im]; exact hw)
  have h1 : (w + eC).arg ≤ Real.pi / 2 :=
    Complex.arg_le_pi_div_two_iff.mpr (Or.inl (by have := re_add_eC_pos hwre; have := Real.exp_pos 1; linarith))
  have hs := Real.mul_le_sin h0 h1
  rw [Complex.sin_arg] at hs
  have him : (w + eC).im = w.im := by simp [eC_im]
  rw [him] at hs
  have hpi := Real.pi_pos
  calc (w + eC).arg = Real.pi / 2 * (2 / Real.pi * (w + eC).arg) := by field_simp
    _ ≤ Real.pi / 2 * (w.im / ‖w + eC‖) := by gcongr


/-! ### Derivatives -/

theorem hasDerivAt_logAddEC {w : ℂ} (hw : 0 ≤ w.re) :
    HasDerivAt (fun t : ℂ => Complex.log (t + eC)) (1 / (w + eC)) w := by
  have h := ((hasDerivAt_id w).add_const eC).clog (slitPlane_add_eC hw)
  simpa using h

theorem hasDerivAt_ldTheta {w : ℂ} (hw : 0 ≤ w.re) : HasDerivAt ldTheta (ldTheta1 w) w := by
  have hℓ := hasDerivAt_logAddEC hw
  have hℓ0 := log_add_eC_ne_zero hw
  have he0 := add_eC_ne_zero hw
  have h := (hasDerivAt_id w).div hℓ hℓ0
  unfold ldTheta
  refine h.congr_deriv ?_
  unfold ldTheta1
  simp only [id]
  field_simp

theorem hasDerivAt_ldTheta1 {w : ℂ} (hw : 0 ≤ w.re) : HasDerivAt ldTheta1 (ldTheta2 w) w := by
  have hℓ := hasDerivAt_logAddEC hw
  have hℓ0 := log_add_eC_ne_zero hw
  have he0 := add_eC_ne_zero hw
  have h1 := (hasDerivAt_const w (1 : ℂ)).div hℓ hℓ0
  have hA : HasDerivAt (fun t : ℂ => t + eC) 1 w := by
    simpa using (hasDerivAt_id w).add_const eC
  have hD := hA.mul (hℓ.pow 2)
  have hD0 : (w + eC) * Complex.log (w + eC) ^ 2 ≠ 0 := mul_ne_zero he0 (pow_ne_zero 2 hℓ0)
  have h2 := (hasDerivAt_id w).div hD hD0
  have h := h1.sub h2
  unfold ldTheta1
  refine h.congr_deriv ?_
  unfold ldTheta2
  simp only [Pi.pow_apply, Pi.mul_apply, id, Nat.cast_ofNat]
  norm_num
  field_simp
  ring

theorem hasDerivAt_ldW (s : ℂ) : HasDerivAt ldW (I / 2) s := by
  have h := (((hasDerivAt_id s).sub_const (1 / 2 : ℂ)).const_mul I).div_const 2
  unfold ldW
  refine h.congr_deriv ?_
  ring

theorem ldW_re (s : ℂ) : (ldW s).re = -s.im / 2 := by simp [ldW]

theorem ldW_im (s : ℂ) : (ldW s).im = (s.re - 1 / 2) / 2 := by simp [ldW]

/-- `L' = i θ₁(w) i/2`. -/
def ldDeriv (s : ℂ) : ℂ := I * (ldTheta1 (ldW s) * (I / 2))

/-- `L'' = i θ₂(w) (i/2)²`. -/
def ldDeriv2 (s : ℂ) : ℂ := I * (ldTheta2 (ldW s) * (I / 2) * (I / 2))

theorem hasDerivAt_ldExponent {s : ℂ} (hs : s.im ≤ 0) :
    HasDerivAt ldExponent (ldDeriv s) s := by
  have hw : 0 ≤ (ldW s).re := by rw [ldW_re]; linarith
  have h := ((hasDerivAt_ldTheta hw).comp s (hasDerivAt_ldW s)).const_mul I
  exact h

theorem hasDerivAt_ldDeriv {s : ℂ} (hs : s.im ≤ 0) :
    HasDerivAt ldDeriv (ldDeriv2 s) s := by
  have hw : 0 ≤ (ldW s).re := by rw [ldW_re]; linarith
  have h := (((hasDerivAt_ldTheta1 hw).comp s (hasDerivAt_ldW s)).mul_const (I / 2)).const_mul I
  unfold ldDeriv ldDeriv2
  exact h

/-! ### The phase on the lower line and the strip -/

theorem ldW_lineS {t : ℝ} : ldW (lineS t) = ((-t : ℝ) : ℂ) := by
  rw [ldW, lineS_eq]; push_cast; ring_nf; rw [Complex.I_sq]; ring

theorem re_ldExponent_lineS {t : ℝ} (ht : t < 0) : (ldExponent (lineS t)).re = 0 := by
  unfold ldExponent ldTheta
  rw [ldW_lineS]
  have hpos : (0 : ℝ) < -t + Real.exp 1 := by have := Real.exp_pos 1; linarith
  have hlog : Complex.log (((-t : ℝ) : ℂ) + eC) = ((Real.log (-t + Real.exp 1) : ℝ) : ℂ) := by
    rw [eC, ← Complex.ofReal_add, Complex.ofReal_log hpos.le]
  rw [hlog, ← Complex.ofReal_div]
  simp

theorem re_ldExponent_le {s : ℂ} (hs1 : 1 / 2 ≤ s.re) (hs2 : s.re ≤ 3 / 2) (hs : s.im ≤ 0) :
    (ldExponent s).re ≤ Real.pi / 4 := by
  set w := ldW s with hw
  have hwre : 0 ≤ w.re := by rw [hw, ldW_re]; linarith
  have hwim : 0 ≤ w.im := by rw [hw, ldW_im]; linarith
  have hwim2 : w.im ≤ 1 / 2 := by rw [hw, ldW_im]; linarith
  set ℓ := Complex.log (w + eC) with hℓ
  have hℓre := one_le_re_log hwre
  have hℓim0 := im_log_nonneg (w := w) hwim
  have hℓim := im_log_le hwre hwim
  have hnsq : 1 ≤ Complex.normSq ℓ := by
    rw [Complex.normSq_apply]; nlinarith
  have hre : (ldExponent s).re = (w.re * ℓ.im - w.im * ℓ.re) / Complex.normSq ℓ := by
    unfold ldExponent ldTheta
    rw [← hw, ← hℓ]
    simp only [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.div_re, Complex.div_im]
    ring
  rw [hre]
  have hwle : w.re ≤ ‖w + eC‖ := by
    have := re_add_eC_pos hwre
    have := Complex.re_le_norm (w + eC)
    have h2 : w.re ≤ (w + eC).re := by simp [eC_re]; have := Real.exp_pos 1; linarith
    linarith
  have hnorm0 : 0 < ‖w + eC‖ := by have := exp_one_le_norm_add_eC hwre; have := Real.exp_pos 1; linarith
  have h1 : w.re * ℓ.im ≤ Real.pi / 2 * w.im := by
    calc w.re * ℓ.im ≤ w.re * (Real.pi / 2 * (w.im / ‖w + eC‖)) :=
          mul_le_mul_of_nonneg_left hℓim hwre
      _ = Real.pi / 2 * w.im * (w.re / ‖w + eC‖) := by ring
      _ ≤ Real.pi / 2 * w.im * 1 := by
          gcongr
          rw [div_le_one hnorm0]; exact hwle
      _ = Real.pi / 2 * w.im := by ring
  have h2 : 0 ≤ w.im * ℓ.re := by positivity
  have hnum : w.re * ℓ.im - w.im * ℓ.re ≤ Real.pi / 4 := by
    have := Real.pi_pos; nlinarith
  have hnum0 : 0 ≤ Real.pi / 4 := by have := Real.pi_pos; linarith
  calc (w.re * ℓ.im - w.im * ℓ.re) / Complex.normSq ℓ ≤ (Real.pi / 4) / Complex.normSq ℓ :=
        div_le_div_of_nonneg_right hnum (by linarith)
    _ ≤ Real.pi / 4 / 1 := div_le_div_of_nonneg_left hnum0 one_pos hnsq
    _ = Real.pi / 4 := by ring


/-! ### Asymptotics on the edge `Re s = 3/2` -/

theorem im_log_le_pi_div_two {w : ℂ} (hwre : 0 ≤ w.re) (hw : 0 ≤ w.im) :
    (Complex.log (w + eC)).im ≤ Real.pi / 2 := by
  refine (im_log_le hwre hw).trans ?_
  have hn : 0 < ‖w + eC‖ := by have := exp_one_le_norm_add_eC hwre; have := Real.exp_pos 1; linarith
  have h1 : w.im / ‖w + eC‖ ≤ 1 := by
    rw [div_le_one hn]
    exact (le_abs_self _).trans ((Complex.abs_im_le_norm w).trans (norm_le_norm_add_eC hwre))
  have := Real.pi_pos
  nlinarith

theorem re_ldTheta1_ge {w : ℂ} (hwre : 0 ≤ w.re) (hw : 0 ≤ w.im)
    (h2 : 2 ≤ (Complex.log (w + eC)).re) :
    1 / (4 * (Complex.log (w + eC)).re) ≤ (ldTheta1 w).re := by
  set ℓ := Complex.log (w + eC) with hℓ
  have hℓ0 : ℓ ≠ 0 := log_add_eC_ne_zero hwre
  have he0 := add_eC_ne_zero hwre
  have him0 := im_log_nonneg (w := w) hw
  have him := im_log_le_pi_div_two hwre hw
  have hpi := Real.pi_lt_d2
  have hn : Complex.normSq ℓ = ℓ.re ^ 2 + ℓ.im ^ 2 := by rw [Complex.normSq_apply]; ring
  have hnpos : 0 < Complex.normSq ℓ := Complex.normSq_pos.mpr hℓ0
  have hnle : Complex.normSq ℓ ≤ 2 * ℓ.re ^ 2 := by
    rw [hn]; nlinarith
  have hinv : (1 / ℓ).re = ℓ.re / Complex.normSq ℓ := by rw [one_div, Complex.inv_re]
  have hsecond : ‖w / ((w + eC) * ℓ ^ 2)‖ ≤ 1 / Complex.normSq ℓ := by
    rw [norm_div, norm_mul, norm_pow]
    have hwn := norm_le_norm_add_eC hwre
    have hp : 0 < ‖w + eC‖ := norm_pos_iff.mpr he0
    have hsq : ‖ℓ‖ ^ 2 = Complex.normSq ℓ := Complex.sq_norm ℓ
    rw [hsq, div_le_div_iff₀ (by positivity) hnpos]
    nlinarith
  have hre : (ldTheta1 w).re ≥ ℓ.re / Complex.normSq ℓ - 1 / Complex.normSq ℓ := by
    unfold ldTheta1
    rw [← hℓ, Complex.sub_re, hinv]
    have := Complex.re_le_norm (w / ((w + eC) * ℓ ^ 2))
    linarith
  have hgoal : 1 / (4 * ℓ.re) ≤ ℓ.re / Complex.normSq ℓ - 1 / Complex.normSq ℓ := by
    rw [← sub_div, div_le_div_iff₀ (by linarith) hnpos]
    nlinarith
  linarith

theorem norm_ldTheta2_le {w : ℂ} (hwre : 0 ≤ w.re) :
    ‖ldTheta2 w‖ ≤ 4 / (‖w + eC‖ * Complex.normSq (Complex.log (w + eC))) := by
  set ℓ := Complex.log (w + eC) with hℓ
  have hℓ1 := one_le_norm_log hwre
  have he0 := add_eC_ne_zero hwre
  have hp : 0 < ‖w + eC‖ := norm_pos_iff.mpr he0
  have heC : ‖eC‖ ≤ ‖w + eC‖ := by
    have : ‖eC‖ = Real.exp 1 := by rw [eC, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos 1)]
    rw [this]; exact exp_one_le_norm_add_eC hwre
  have hwn := norm_le_norm_add_eC hwre
  have hsq : Complex.normSq ℓ = ‖ℓ‖ ^ 2 := (Complex.sq_norm ℓ).symm
  rw [hsq]
  set N := ‖w + eC‖ with hN
  set M := ‖ℓ‖ with hM
  have hM0 : 0 < M := by linarith
  unfold ldTheta2
  rw [← hℓ]
  have t1 : ‖-(1 / ((w + eC) * ℓ ^ 2))‖ = 1 / (N * M ^ 2) := by
    rw [norm_neg, norm_div, norm_one, norm_mul, norm_pow]
  have t2 : ‖eC / ((w + eC) ^ 2 * ℓ ^ 2)‖ ≤ 1 / (N * M ^ 2) := by
    rw [norm_div, norm_mul, norm_pow, norm_pow, div_le_div_iff₀ (by positivity) (by positivity)]
    have : ‖eC‖ * (N * M ^ 2) ≤ N * (N * M ^ 2) := by gcongr
    nlinarith
  have t3 : ‖2 * w / ((w + eC) ^ 2 * ℓ ^ 3)‖ ≤ 2 / (N * M ^ 2) := by
    rw [norm_div, norm_mul, norm_mul, norm_pow, norm_pow, Complex.norm_two,
      div_le_div_iff₀ (by positivity) (by positivity)]
    have hM3 : M ^ 2 ≤ M ^ 3 := by nlinarith
    have : 2 * ‖w‖ * (N * M ^ 2) ≤ 2 * N * (N * M ^ 3) := by
      have h1 : ‖w‖ * M ^ 2 ≤ N * M ^ 3 := mul_le_mul hwn hM3 (by positivity) (by positivity)
      nlinarith
    linarith
  calc ‖-(1 / ((w + eC) * ℓ ^ 2)) - eC / ((w + eC) ^ 2 * ℓ ^ 2) +
        2 * w / ((w + eC) ^ 2 * ℓ ^ 3)‖
      ≤ ‖-(1 / ((w + eC) * ℓ ^ 2))‖ + ‖eC / ((w + eC) ^ 2 * ℓ ^ 2)‖ +
          ‖2 * w / ((w + eC) ^ 2 * ℓ ^ 3)‖ := by
        refine (norm_add_le _ _).trans ?_
        gcongr
        exact norm_sub_le _ _
    _ ≤ 1 / (N * M ^ 2) + 1 / (N * M ^ 2) + 2 / (N * M ^ 2) := by rw [t1]; gcongr
    _ = 4 / (N * M ^ 2) := by ring


theorem log_le_two_mul_sqrt_of_pos {v : ℝ} (hv : 0 < v) : Real.log v ≤ 2 * Real.sqrt v := by
  have hs : 0 < Real.sqrt v := Real.sqrt_pos.mpr hv
  have h := Real.log_le_sub_one_of_pos hs
  rw [Real.log_sqrt hv.le] at h
  linarith

theorem ldW_edgePt (y : ℝ) : ldW (edgePt y) = (((-y / 2) : ℝ) : ℂ) + ((1 / 2 : ℝ) : ℂ) * I := by
  apply Complex.ext
  · simp [ldW, edgePt]
  · simp [ldW, edgePt]; norm_num

/-- On the edge, for `y ≤ −10`: `x = −y/2 ≥ 5`, `2 ≤ Re ℓ ≤ log(x + 4)` and `x + e ≤ ‖w + e‖`. -/
theorem edge_log_bounds {y : ℝ} (hy : y ≤ -10) :
    2 ≤ (Complex.log (ldW (edgePt y) + eC)).re ∧
      (Complex.log (ldW (edgePt y) + eC)).re ≤ Real.log (-y / 2 + 4) ∧
      -y / 2 ≤ ‖ldW (edgePt y) + eC‖ := by
  have he := Real.exp_one_lt_d9
  have he1 := Real.exp_pos 1
  set w := ldW (edgePt y) with hw
  have hwre : w.re = -y / 2 := by rw [hw, ldW_edgePt]; simp
  have hwim : w.im = 1 / 2 := by rw [hw, ldW_edgePt]; simp
  have hre : (w + eC).re = -y / 2 + Real.exp 1 := by simp [eC_re, hwre]
  have him : (w + eC).im = 1 / 2 := by simp [eC_im, hwim]
  have hlow : -y / 2 + Real.exp 1 ≤ ‖w + eC‖ := hre ▸ Complex.re_le_norm _
  have hup : ‖w + eC‖ ≤ -y / 2 + 4 := by
    have h := norm_le_abs_re_add_abs_im (w + eC)
    rw [hre, him, abs_of_pos (by linarith), abs_of_pos (by norm_num)] at h
    linarith
  have hpos : 0 < ‖w + eC‖ := by linarith
  refine ⟨?_, ?_, by linarith⟩
  · rw [Complex.log_re]
    have hee : Real.exp 2 ≤ ‖w + eC‖ := by
      have : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
      rw [this]; nlinarith
    have := Real.log_le_log (Real.exp_pos 2) hee
    rwa [Real.log_exp] at this
  · rw [Complex.log_re]
    exact Real.log_le_log hpos hup

theorem ldDeriv_re (s : ℂ) : (ldDeriv s).re = -(ldTheta1 (ldW s)).re / 2 := by
  simp only [ldDeriv, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.div_ofNat_re, Complex.div_ofNat_im]
  ring

theorem norm_ldDeriv2 (s : ℂ) : ‖ldDeriv2 s‖ = ‖ldTheta2 (ldW s)‖ / 4 := by
  simp only [ldDeriv2, norm_mul, norm_div, Complex.norm_I, Complex.norm_ofNat]
  ring

/-- `y Re L'(3/2 + iy) ≥ √(−y/2)/12` for `y ≤ −10`. -/
theorem edge_density_ge {y : ℝ} (hy : y ≤ -10) :
    Real.sqrt (-y / 2) / 12 ≤ y * (ldDeriv (edgePt y)).re := by
  obtain ⟨h2, hup, _⟩ := edge_log_bounds hy
  set w := ldW (edgePt y) with hw
  have hwre : 0 ≤ w.re := by rw [hw, ldW_edgePt]; simp; linarith
  have hwim : 0 ≤ w.im := by rw [hw, ldW_edgePt]; simp
  have hθ := re_ldTheta1_ge hwre hwim h2
  set ℓre := (Complex.log (w + eC)).re with hℓre
  set x : ℝ := -y / 2 with hx
  have hx5 : 5 ≤ x := by rw [hx]; linarith
  rw [ldDeriv_re, ← hw]
  have e1 : y * (-(ldTheta1 w).re / 2) = x * (ldTheta1 w).re := by rw [hx]; ring
  rw [e1]
  have hlog : Real.log (x + 4) ≤ 3 * Real.sqrt x := by
    have h1 := log_le_two_mul_sqrt_of_pos (v := x + 4) (by linarith)
    have h2 : Real.sqrt (x + 4) ≤ Real.sqrt (2 * x) := Real.sqrt_le_sqrt (by linarith)
    have h3 : Real.sqrt (2 * x) = Real.sqrt 2 * Real.sqrt x :=
      Real.sqrt_mul (by norm_num) x
    have h4 : Real.sqrt 2 ≤ 3 / 2 := by
      rw [Real.sqrt_le_left (by norm_num)]; norm_num
    have hsx := Real.sqrt_nonneg x
    nlinarith
  have hsx : 0 < Real.sqrt x := Real.sqrt_pos.mpr (by linarith)
  have hℓpos : 0 < ℓre := by linarith
  have h1 : x * (1 / (4 * ℓre)) ≤ x * (ldTheta1 w).re := mul_le_mul_of_nonneg_left hθ (by linarith)
  have h2' : Real.sqrt x / 12 ≤ x * (1 / (4 * ℓre)) := by
    rw [mul_one_div, div_le_div_iff₀ (by norm_num) (by positivity)]
    have hxx : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt (by linarith)
    nlinarith
  linarith

/-- `‖L''‖/(Re L')² ≤ 128/(−y)` for `y ≤ −10`. -/
theorem edge_ratio_le {y : ℝ} (hy : y ≤ -10) :
    ‖ldDeriv2 (edgePt y)‖ / (ldDeriv (edgePt y)).re ^ 2 ≤ 128 / (-y) := by
  obtain ⟨h2, _, hlow⟩ := edge_log_bounds hy
  set w := ldW (edgePt y) with hw
  have hwre : 0 ≤ w.re := by rw [hw, ldW_edgePt]; simp; linarith
  have hwim : 0 ≤ w.im := by rw [hw, ldW_edgePt]; simp
  have hθ := re_ldTheta1_ge hwre hwim h2
  have hθ2 := norm_ldTheta2_le hwre
  set ℓ := Complex.log (w + eC) with hℓ
  have hℓre_le : ℓ.re ^ 2 ≤ Complex.normSq ℓ := by
    rw [Complex.normSq_apply]; nlinarith
  rw [norm_ldDeriv2, ldDeriv_re, ← hw]
  have hℓpos : 0 < ℓ.re := by linarith
  have hθpos : 0 < (ldTheta1 w).re := lt_of_lt_of_le (div_pos one_pos (by linarith)) hθ
  have hN : 0 < ‖w + eC‖ := by linarith
  have hnsq : 0 < Complex.normSq ℓ := by nlinarith
  have hden : 0 < (-(ldTheta1 w).re / 2) ^ 2 :=
    lt_of_le_of_ne (sq_nonneg _)
      (Ne.symm (pow_ne_zero 2 (ne_of_lt (by linarith : -(ldTheta1 w).re / 2 < 0))))
  rw [div_le_div_iff₀ hden (by linarith)]
  have hsq : 1 / (16 * ℓ.re ^ 2) ≤ (ldTheta1 w).re ^ 2 := by
    have := pow_le_pow_left₀ (by positivity) hθ 2
    calc 1 / (16 * ℓ.re ^ 2) = (1 / (4 * ℓ.re)) ^ 2 := by
          rw [div_pow, one_pow, mul_pow]; norm_num
      _ ≤ _ := this
  have hθ2' : ‖ldTheta2 w‖ ≤ 4 / (‖w + eC‖ * ℓ.re ^ 2) := by
    refine hθ2.trans ?_
    exact div_le_div_of_nonneg_left (by norm_num) (mul_pos hN (pow_pos hℓpos 2))
      (mul_le_mul_of_nonneg_left hℓre_le hN.le)
  have hy' : -y ≤ 2 * ‖w + eC‖ := by linarith
  have key : ‖ldTheta2 w‖ * (-y) ≤ 128 * (ldTheta1 w).re ^ 2 := by
    have hA : ‖ldTheta2 w‖ * (-y) ≤ 4 / (‖w + eC‖ * ℓ.re ^ 2) * (2 * ‖w + eC‖) :=
      mul_le_mul hθ2' hy' (by linarith) (by positivity)
    have hB : 4 / (‖w + eC‖ * ℓ.re ^ 2) * (2 * ‖w + eC‖) = 8 / ℓ.re ^ 2 := by
      field_simp; ring
    have hC : 8 / ℓ.re ^ 2 = 128 * (1 / (16 * ℓ.re ^ 2)) := by field_simp; ring
    nlinarith
  calc ‖ldTheta2 w‖ / 4 * (-y) = ‖ldTheta2 w‖ * (-y) / 4 := by ring
    _ ≤ 128 * (ldTheta1 w).re ^ 2 / 4 := by linarith
    _ = 128 * (-(ldTheta1 w).re / 2) ^ 2 := by ring


/-! ### The theorem -/

theorem ldExponent_lineS {t : ℝ} (ht : t < 0) :
    ldExponent (lineS t) = (((-t) / Real.log (-t + Real.exp 1) : ℝ) : ℂ) * I := by
  unfold ldExponent ldTheta
  rw [ldW_lineS]
  have hpos : (0 : ℝ) < -t + Real.exp 1 := by have := Real.exp_pos 1; linarith
  have hlog : Complex.log (((-t : ℝ) : ℂ) + eC) = ((Real.log (-t + Real.exp 1) : ℝ) : ℂ) := by
    rw [eC, ← Complex.ofReal_add, Complex.ofReal_log hpos.le]
  rw [hlog, ← Complex.ofReal_div]
  ring

/-- **Lock densities decaying like `1/log x` are impossible.**  No Herglotz producer satisfies
`G(1 − s) = κ₀ e^{iθ(−τ)} G(s)` at `s = ½ + 2iτ`, `τ < 0`, with `θ(x) = x/log(x + e)`. -/
theorem log_density_lock_impossible {lam : ℕ → ℝ} {Φ G : ℂ → ℂ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hΦd : DifferentiableOn ℂ Φ {s : ℂ | 1 / 2 < s.re})
    (hΦre : ∀ s : ℂ, 1 / 2 < s.re → 0 ≤ (Φ s).re)
    (hid : ∀ s : ℂ, 1 < s.re → Φ s = zetaArchimedeanDatum s + 1 / (s - 1) -
      LSeries (fun n => if 2 ≤ n then (lam n : ℂ) else 0) s)
    (hGc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt G s)
    (hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (Φ s * G s) s) (hG2 : G 2 = bigG lam 2)
    {κ₀ : ℂ}
    (hlock : ∀ τ : ℝ, τ < 0 → G (1 - lineS τ) =
      κ₀ * cexp ((((-τ) / Real.log (-τ + Real.exp 1) : ℝ) : ℂ) * I) * G (lineS τ)) :
    False := by
  have hpi := Real.pi_pos
  set V : Set ℂ := {s : ℂ | s.im < 0} with hV
  have hVo : IsOpen V := isOpen_lt Complex.continuous_im continuous_const
  have hderiv : ∀ y : ℝ, y < 0 → deriv ldExponent (edgePt y) = ldDeriv (edgePt y) := fun y hy =>
    (hasDerivAt_ldExponent (by simp [edgePt]; linarith)).deriv
  have hderiv2 : ∀ y : ℝ, y < 0 →
      deriv (deriv ldExponent) (edgePt y) = ldDeriv2 (edgePt y) := by
    intro y hy
    have hmem : edgePt y ∈ V := by show (edgePt y).im < 0; simp [edgePt]; exact hy
    have hev : deriv ldExponent =ᶠ[𝓝 (edgePt y)] ldDeriv :=
      Filter.eventually_of_mem (hVo.mem_nhds hmem)
        fun z hz => (hasDerivAt_ldExponent (le_of_lt hz)).deriv
    rw [hev.deriv_eq]
    exact (hasDerivAt_ldDeriv (by simp [edgePt]; linarith)).deriv
  refine regular_twist_lock_impossible hsl hΦd hΦre hid hGc hGd hG2 (L := ldExponent)
    (fun s _ him => (hasDerivAt_ldExponent him.le).continuousAt)
    (fun s _ him => (hasDerivAt_ldExponent him.le).differentiableAt) (A := Real.pi / 4)
    (fun s hs1 hs2 him => re_ldExponent_le hs1 hs2 (by linarith))
    (fun t ht => by rw [re_ldExponent_lineS ht]; linarith) ?_ ?_ (κ₀ := κ₀) (fun τ hτ => ?_)
  · -- `y Re L' → ∞`
    have hsq : Tendsto (fun y : ℝ => Real.sqrt (-y / 2) / 12) atBot atTop := by
      have h1 : Tendsto (fun y : ℝ => -y / 2) atBot atTop :=
        (tendsto_neg_atBot_atTop).atTop_div_const (by norm_num)
      exact (Real.tendsto_sqrt_atTop.comp h1).atTop_div_const (by norm_num)
    refine tendsto_atTop_mono' _ ?_ hsq
    filter_upwards [eventually_le_atBot (-10 : ℝ)] with y hy
    rw [hderiv y (by linarith)]
    exact edge_density_ge hy
  · -- `‖L''‖/(Re L')² → 0`
    have hlim : Tendsto (fun y : ℝ => 128 / (-y)) atBot (𝓝 0) := by
      have := (tendsto_inv_atTop_zero.comp tendsto_neg_atBot_atTop).const_mul (128 : ℝ)
      rw [mul_zero] at this
      exact this.congr fun y => by simp [div_eq_mul_inv]
    refine squeeze_zero' (Eventually.of_forall fun y => by positivity) ?_ hlim
    filter_upwards [eventually_le_atBot (-10 : ℝ)] with y hy
    rw [hderiv y (by linarith), hderiv2 y (by linarith)]
    exact edge_ratio_le hy
  · rw [hlock τ hτ, ldExponent_lineS hτ]

end

end AbelianTwist

end RHTower
