import GaloisForLFunctions.EulerFETransportTheory.UnequalCoefficientsFloorTheAbelMass
import GaloisForLFunctions.EulerFETransportTheory.TheBoundaryPreservesDefectEnergy

/-!
# Missing resonances cost logarithmic defect energy

Let `Z(s) = Σ a_n n^{-s}` continue to the critical line in the Hamburger strip class with defect
`g` (`HamburgerStripDefect`), let its coefficients have density `A > 0`
(`a_1 + ⋯ + a_n = A n + o(n)`), and let every multiple of `p` be missing: `a_{pk} = 0`.

**Theorem** (`integral_norm_sq_mul_exp_ge_of_missing_multiples`).  For all large `T`,

`∫ ‖g(t)‖² e^{-|t|/T} dt ≥ A²/(256πp) · T log T`.

**Corollary** (`not_le_sqrt_log_of_missing_multiples`).  `limsup ‖g(t)‖/√(log|t|) ≥ A/(32√(πp))`;
in particular `g` is unbounded.

**Proof.**  Write `J = J_g` for the defect Laplace transform and `τ(r) = r e^{i(π/2-θ)}` for the ray
tilted by `θ` from the imaginary axis.
* *Energy on the ray* (`ray_energy_le`).  By Mellin–Plancherel,
  `∫₀^∞ ‖J(τ(r))‖² dr = (1/4π) ∫ ‖g(t)‖² ‖k(2t, e^{i(π/2-θ)})‖² dt ≤ (1/π) ∫ ‖g‖² e^{-4θ|t|}`.
* *A spike at each missing resonance* (`le_norm_defectLaplace_of_window`).  Near `τ = i m`,
  `m = pk`, the Hamburger identity reads `J = L_a - F_a + β/(πτ) - β`.  By periodicity and Abel
  summation `F_a(τ) = A w/(1 - w) + (1 - w) Σ R(n) wⁿ` with `w = e^{-2π(τ - im)}`, so
  `‖F_a(τ)‖ ≈ A/(2π‖τ - im‖)`; the series `L_a` has no pole at `i m` because `a_m = 0`, and is
  `O(m²)` there (`norm_hamburgerSeries_le_of_coeff_eq_zero`).  On an `r`-window of length `mθ/2`
  this gives `‖J‖ ≥ A/(8πmθ)`.
* *Summation.*  The windows for `m = pk ≤ θ^{-1/4}` are disjoint; their energies add to
  `A²/(128π²pθ) · Σ_{k ≤ K} 1/k ≥ A²/(1024π²pθ) · log(1/θ)`.  Take `θ = 1/(4T)`.
-/

open Complex MeasureTheory Filter Topology Set
open RHTower.HamburgerStability GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.ExactEventTheory

noncomputable section

namespace GaloisForLFunctions.EulerFETransportTheory

/-! ## Mellin–Plancherel along a ray -/

/-- The critical-line Mellin data `s ↦ f(-Im s/2)/2` of a source `f`. -/
def rayMellinData (f : ℝ → ℂ) (s : ℂ) : ℂ := (1 / 2 : ℂ) * f (-s.im / 2)

theorem rayMellinData_line (f : ℝ → ℂ) (σ v : ℝ) :
    rayMellinData f ((σ : ℂ) + v * I) = (1 / 2 : ℂ) * f ((-1 / 2 : ℝ) * v) := by
  have hi : ((σ : ℂ) + (v : ℂ) * I).im = v := by simp
  rw [rayMellinData, hi]
  congr 2
  ring

theorem integrable_rayMellinData {f : ℝ → ℂ} (hf : Integrable f) {σ : ℝ} :
    Integrable fun v : ℝ => rayMellinData f ((σ : ℂ) + v * I) := by
  simp only [rayMellinData_line]
  exact (hf.comp_mul_left' (by norm_num : (-1 / 2 : ℝ) ≠ 0)).const_mul _

theorem memLp_rayMellinData {f : ℝ → ℂ} (hf : Integrable f) (hf2 : MemLp f 2) {σ : ℝ} :
    MemLp (fun v : ℝ => rayMellinData f ((σ : ℂ) + v * I)) 2 := by
  rw [memLp_two_iff_integrable_sq_norm (integrable_rayMellinData hf).aestronglyMeasurable]
  have hsq := (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp hf2
  have hi := (hsq.comp_mul_left' (by norm_num : (-1 / 2 : ℝ) ≠ 0)).const_mul (1 / 4 : ℝ)
  convert hi using 1
  funext v
  rw [rayMellinData_line, norm_mul, mul_pow]
  norm_num

theorem integral_norm_sq_rayMellinData (f : ℝ → ℂ) (σ : ℝ) :
    ∫ v : ℝ, ‖rayMellinData f ((σ : ℂ) + v * I)‖ ^ 2 = (1 / 2 : ℝ) * ∫ t : ℝ, ‖f t‖ ^ 2 := by
  simp only [rayMellinData_line, norm_mul, mul_pow]
  rw [integral_const_mul, Measure.integral_comp_mul_left (fun t : ℝ => ‖f t‖ ^ 2) (-1 / 2)]
  norm_num
  ring

/-- Inverse Mellin transform on `Re s = 1/2` of data given along the critical line:
`(1/2π) ∫ f(t) y^{s_t - 1} dt` with `s_t = linePt (2t)`. -/
theorem mellinInv_rayMellinData (f : ℝ → ℂ) (y : ℝ) :
    mellinInv (1 / 2) (rayMellinData f) y =
      ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ t : ℝ, f t * (y : ℂ) ^ (linePt (2 * t) - 1) := by
  unfold mellinInv
  simp only [rayMellinData_line, smul_eq_mul, Complex.real_smul]
  have heq : (fun v : ℝ => (y : ℂ) ^ (-((1 / 2 : ℝ) + v * I)) *
      ((1 / 2 : ℂ) * f ((-1 / 2 : ℝ) * v))) =
      fun v : ℝ => (1 / 2 : ℂ) *
        (fun t : ℝ => f t * (y : ℂ) ^ (linePt (2 * t) - 1)) ((-1 / 2 : ℝ) * v) := by
    funext v
    have he : -((1 / 2 : ℝ) + (v : ℂ) * I) = linePt (2 * ((-1 / 2 : ℝ) * v)) - 1 := by
      simp only [linePt]; push_cast; ring
    rw [he]
    ring
  rw [heq, integral_const_mul,
    Measure.integral_comp_mul_left (fun t : ℝ => f t * (y : ℂ) ^ (linePt (2 * t) - 1)) (-1 / 2)]
  norm_num [Complex.real_smul]
  ring

/-- **Mellin–Plancherel for a critical-line source.**  For `f ∈ L¹ ∩ L²` the function
`y ↦ (1/2π) ∫ f(t) y^{-1/2 + 2it} dt` has energy `(1/4π) ∫ ‖f‖²` on `(0, ∞)`. -/
theorem rayMellin_energy {f : ℝ → ℂ} (hf : Integrable f) (hf2 : MemLp f 2) :
    IntegrableOn (fun y : ℝ => ‖mellinInv (1 / 2) (rayMellinData f) y‖ ^ 2) (Ioi 0) ∧
    ∫ y in Ioi (0 : ℝ), ‖mellinInv (1 / 2) (rayMellinData f) y‖ ^ 2 =
      1 / (4 * Real.pi) * ∫ t : ℝ, ‖f t‖ ^ 2 := by
  have hdi := integrable_rayMellinData (σ := 1 / 2) hf
  have hd2 := memLp_rayMellinData (σ := 1 / 2) hf hf2
  have hw : (fun y : ℝ => ‖mellinInv (1 / 2) (rayMellinData f) y‖ ^ 2 *
      y ^ (2 * (1 / 2 : ℝ) - 1)) = fun y => ‖mellinInv (1 / 2) (rayMellinData f) y‖ ^ 2 := by
    funext y
    norm_num
  have h1 := integrableOn_norm_sq_mellinInv hdi hd2
  have h2 := integral_norm_sq_mellinInv hdi hd2
  rw [hw] at h1 h2
  refine ⟨h1, ?_⟩
  rw [h2, integral_norm_sq_rayMellinData]
  ring

/-- On a ray `r z` (`Re z > 0`) the defect Laplace transform is the critical-line Mellin inverse
of the source `g(t) k(2t, z)`. -/
theorem defectLaplace_ofReal_mul (g : ℝ → ℂ) {z : ℂ} (hz : 0 < z.re) {r : ℝ} (hr : 0 < r) :
    defectLaplace g ((r : ℂ) * z) =
      mellinInv (1 / 2) (rayMellinData fun t => g t * boundaryPairKernel (2 * t) z) r := by
  have hz0 : z ≠ 0 := by intro h; simp [h] at hz
  have hre : 0 < ((r : ℂ) * z).re := by rw [Complex.re_ofReal_mul]; exact mul_pos hr hz
  rw [← closedDefectLaplace_eq hre, mellinInv_rayMellinData, closedDefectLaplace]
  congr 1
  apply integral_congr_ae
  filter_upwards with t
  rw [boundaryPairKernel_mul_pos (2 * t) hr hz0]
  ring

/-! ## The kernel on a tilted ray -/

/-- `|sin(π/4 + iy)|² = (e^{2y} + e^{-2y})/4`. -/
theorem norm_sin_quarter_sq (y : ℝ) :
    ‖Complex.sin (((Real.pi / 4 : ℝ) : ℂ) + (y : ℂ) * I)‖ ^ 2 =
      (Real.exp (2 * y) + Real.exp (-(2 * y))) / 4 := by
  rw [Complex.sq_norm]
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  rw [Complex.sin_add_mul_I]
  simp only [← Complex.ofReal_sin, ← Complex.ofReal_cos, ← Complex.ofReal_cosh,
    ← Complex.ofReal_sinh, Real.sin_pi_div_four, Real.cos_pi_div_four,
    Complex.normSq_apply, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.add_im, Complex.mul_im]
  simp only [mul_zero, sub_zero, zero_mul, zero_add, add_zero, mul_one]
  rw [Real.cosh_eq, Real.sinh_eq, show -(2 * y) = -y + -y by ring,
    show 2 * y = y + y by ring, Real.exp_add, Real.exp_add]
  ring_nf
  rw [hs]
  ring

theorem norm_boundaryPairKernel_of_norm_eq_one (v : ℝ) {z : ℂ} (hz : ‖z‖ = 1) :
    ‖boundaryPairKernel v z‖ = Real.exp (-(z.arg * v)) /
      ‖Complex.sin ((Real.pi : ℂ) * (linePt v / 2))‖ := by
  have hz0 : z ≠ 0 := by intro h; simp [h] at hz
  rw [boundaryPairKernel_eq_cpow_div_sin v hz0, norm_div,
    Complex.norm_cpow_of_ne_zero hz0, hz, Real.one_rpow]
  have hi : (linePt v - 1).im = v := by simp [linePt]
  rw [hi, one_div, ← Real.exp_neg]

/-- The unit direction `e^{i(π/2 - θ)} = sin θ + i cos θ`, tilted by `θ` from `i`. -/
def tiltDir (θ : ℝ) : ℂ := cexp (((Real.pi / 2 - θ : ℝ) : ℂ) * I)

theorem tiltDir_re (θ : ℝ) : (tiltDir θ).re = Real.sin θ := by
  rw [tiltDir, Complex.exp_ofReal_mul_I_re, Real.cos_pi_div_two_sub]

theorem tiltDir_im (θ : ℝ) : (tiltDir θ).im = Real.cos θ := by
  rw [tiltDir, Complex.exp_ofReal_mul_I_im, Real.sin_pi_div_two_sub]

theorem norm_tiltDir (θ : ℝ) : ‖tiltDir θ‖ = 1 := Complex.norm_exp_ofReal_mul_I _

theorem arg_tiltDir {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ Real.pi / 2) :
    (tiltDir θ).arg = Real.pi / 2 - θ := by
  rw [tiltDir, Complex.exp_mul_I]
  exact Complex.arg_cos_add_sin_mul_I ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩

/-- On the tilted ray the kernel decays at rate `4θ`: `‖k(2t, e^{i(π/2-θ)})‖² ≤ 4 e^{-4θ|t|}`. -/
theorem norm_sq_boundaryPairKernel_tiltDir_le {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ Real.pi / 2)
    (t : ℝ) :
    ‖boundaryPairKernel (2 * t) (tiltDir θ)‖ ^ 2 ≤ 4 * Real.exp (-(4 * θ * |t|)) := by
  have hs : (Real.pi : ℂ) * (linePt (2 * t) / 2) =
      ((Real.pi / 4 : ℝ) : ℂ) + ((Real.pi * t : ℝ) : ℂ) * I := by
    simp only [linePt]; push_cast; ring
  rw [norm_boundaryPairKernel_of_norm_eq_one (2 * t) (norm_tiltDir θ), arg_tiltDir h0 h1,
    div_pow, hs, norm_sin_quarter_sq]
  have hE : Real.exp (-((Real.pi / 2 - θ) * (2 * t))) ^ 2 =
      Real.exp (-((2 * Real.pi - 4 * θ) * t)) := by
    rw [pow_two, ← Real.exp_add]; congr 1; ring
  rw [hE]
  have hS : 0 < Real.exp (2 * (Real.pi * t)) + Real.exp (-(2 * (Real.pi * t))) := by positivity
  rw [div_div_eq_mul_div, div_le_iff₀ hS]
  -- `e^{-(2π - 4θ)t} ≤ e^{-4θ|t|} (e^{2πt} + e^{-2πt})`
  have hkey : Real.exp (-((2 * Real.pi - 4 * θ) * t)) ≤
      Real.exp (-(4 * θ * |t|)) *
        (Real.exp (2 * (Real.pi * t)) + Real.exp (-(2 * (Real.pi * t)))) := by
    rw [mul_add, ← Real.exp_add, ← Real.exp_add]
    rcases le_or_gt 0 t with ht | ht
    · rw [abs_of_nonneg ht]
      have : Real.exp (-((2 * Real.pi - 4 * θ) * t)) ≤
          Real.exp (-(4 * θ * t) + 2 * (Real.pi * t)) :=
        Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
      linarith [Real.exp_pos (-(4 * θ * t) + -(2 * (Real.pi * t)))]
    · rw [abs_of_neg ht]
      have : Real.exp (-((2 * Real.pi - 4 * θ) * t)) ≤
          Real.exp (-(4 * θ * -t) + -(2 * (Real.pi * t))) :=
        Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
      linarith [Real.exp_pos (-(4 * θ * -t) + 2 * (Real.pi * t))]
  nlinarith [hkey]

/-- **Energy on a tilted ray.**  For a measurable polynomially bounded `g` and
`0 < θ ≤ 1`, `∫₀^∞ ‖J_g(r e^{i(π/2-θ)})‖² dr ≤ (1/π) ∫ ‖g(t)‖² e^{-4θ|t|} dt`. -/
theorem ray_energy_le {g : ℝ → ℂ} {Cg : ℝ} {N : ℕ} (hgm : AEStronglyMeasurable g volume)
    (hgb : ∀ t, ‖g t‖ ≤ Cg * (1 + |t|) ^ N) {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) :
    IntegrableOn (fun r : ℝ => ‖defectLaplace g ((r : ℂ) * tiltDir θ)‖ ^ 2) (Ioi 0) ∧
    ∫ r in Ioi (0 : ℝ), ‖defectLaplace g ((r : ℂ) * tiltDir θ)‖ ^ 2 ≤
      1 / Real.pi * ∫ t : ℝ, ‖g t‖ ^ 2 * Real.exp (-(4 * θ * |t|)) := by
  have hpi := Real.pi_pos
  have hθπ : θ ≤ Real.pi / 2 := by linarith [Real.pi_gt_three]
  have hCg : 0 ≤ Cg := by have := (norm_nonneg _).trans (hgb 0); simpa using this
  set z := tiltDir θ with hzdef
  have hz : 0 < z.re := by
    rw [hzdef, tiltDir_re]
    exact Real.sin_pos_of_pos_of_lt_pi hθ0 (by linarith [Real.pi_gt_three])
  have hz0 : z ≠ 0 := by intro h; simp [h] at hz
  set f : ℝ → ℂ := fun t => g t * boundaryPairKernel (2 * t) z with hf
  have hk : ∀ t, ‖boundaryPairKernel (2 * t) z‖ ≤ 2 * Real.exp (-(2 * θ * |t|)) := by
    intro t
    have h := norm_sq_boundaryPairKernel_tiltDir_le hθ0.le hθπ t
    have he : 4 * Real.exp (-(4 * θ * |t|)) = (2 * Real.exp (-(2 * θ * |t|))) ^ 2 := by
      rw [mul_pow, ← Real.exp_nat_mul]; norm_num; ring_nf
    rw [he] at h
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h
  have hkm : AEStronglyMeasurable (fun t : ℝ => boundaryPairKernel (2 * t) z) volume :=
    ((continuous_boundaryPairKernel_parameter hz0).comp
      (continuous_const.mul continuous_id)).aestronglyMeasurable
  have hfi : Integrable f := by
    refine integrable_mul_of_poly_damped (M := 0) (A := 2) hgm hgb hkm
      (mul_pos two_pos hθ0) fun t => ?_
    rw [pow_zero, mul_one]
    exact hk t
  -- a majorant for `‖f‖²` and for `‖g‖² e^{-4θ|t|}`
  have hmaj : Integrable fun t : ℝ => (1 + |t|) ^ (2 * N) * Real.exp (-((4 * θ) * |t|)) :=
    integrable_one_add_abs_pow_mul_exp (by positivity) (2 * N)
  have hgsq : ∀ t, ‖g t‖ ^ 2 ≤ Cg ^ 2 * (1 + |t|) ^ (2 * N) := by
    intro t
    rw [pow_mul', ← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (hgb t) 2
  have hgi : Integrable fun t : ℝ => ‖g t‖ ^ 2 * Real.exp (-(4 * θ * |t|)) := by
    refine (hmaj.const_mul (Cg ^ 2)).mono' ((hgm.norm.pow 2).mul (by fun_prop :
      Continuous fun t : ℝ => Real.exp (-(4 * θ * |t|))).aestronglyMeasurable)
      (Eventually.of_forall fun t => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc ‖g t‖ ^ 2 * Real.exp (-(4 * θ * |t|))
        ≤ Cg ^ 2 * (1 + |t|) ^ (2 * N) * Real.exp (-(4 * θ * |t|)) := by
          gcongr; exact hgsq t
      _ = Cg ^ 2 * ((1 + |t|) ^ (2 * N) * Real.exp (-((4 * θ) * |t|))) := by ring
  have hfsq : ∀ t, ‖f t‖ ^ 2 ≤ 4 * (‖g t‖ ^ 2 * Real.exp (-(4 * θ * |t|))) := by
    intro t
    rw [hf, norm_mul, mul_pow]
    calc ‖g t‖ ^ 2 * ‖boundaryPairKernel (2 * t) z‖ ^ 2
        ≤ ‖g t‖ ^ 2 * (4 * Real.exp (-(4 * θ * |t|))) :=
          mul_le_mul_of_nonneg_left (norm_sq_boundaryPairKernel_tiltDir_le hθ0.le hθπ t)
            (by positivity)
      _ = 4 * (‖g t‖ ^ 2 * Real.exp (-(4 * θ * |t|))) := by ring
  have hfsqi : Integrable fun t => ‖f t‖ ^ 2 :=
    (hgi.const_mul 4).mono' (hfi.aestronglyMeasurable.norm.pow 2)
      (Eventually.of_forall fun t => by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]; exact hfsq t)
  have hf2 : MemLp f 2 := (memLp_two_iff_integrable_sq_norm hfi.aestronglyMeasurable).mpr hfsqi
  obtain ⟨hint, heq⟩ := rayMellin_energy hfi hf2
  have hon : EqOn (fun r : ℝ => ‖defectLaplace g ((r : ℂ) * z)‖ ^ 2)
      (fun r => ‖mellinInv (1 / 2) (rayMellinData f) r‖ ^ 2) (Ioi 0) := by
    intro r hr
    simp only [defectLaplace_ofReal_mul g hz hr, hf]
  refine ⟨hint.congr_fun (fun r hr => (hon hr).symm) measurableSet_Ioi, ?_⟩
  rw [setIntegral_congr_fun measurableSet_Ioi hon, heq]
  have hle : ∫ t : ℝ, ‖f t‖ ^ 2 ≤ ∫ t : ℝ, 4 * (‖g t‖ ^ 2 * Real.exp (-(4 * θ * |t|))) :=
    integral_mono hfsqi (hgi.const_mul 4) hfsq
  rw [integral_const_mul] at hle
  calc 1 / (4 * Real.pi) * ∫ t : ℝ, ‖f t‖ ^ 2
      ≤ 1 / (4 * Real.pi) * (4 * ∫ t : ℝ, ‖g t‖ ^ 2 * Real.exp (-(4 * θ * |t|))) := by gcongr
    _ = 1 / Real.pi * ∫ t : ℝ, ‖g t‖ ^ 2 * Real.exp (-(4 * θ * |t|)) := by
        field_simp

/-! ## Elementary exponential bounds -/

/-- `‖1 - e^{-u}‖ ≤ ‖u‖` on the closed right half-plane. -/
theorem norm_one_sub_cexp_neg_le {u : ℂ} (hu : 0 ≤ u.re) : ‖1 - cexp (-u)‖ ≤ ‖u‖ := by
  have hderiv : ∀ x ∈ Icc (0 : ℝ) 1, HasDerivWithinAt (fun s : ℝ => cexp (-((s : ℂ) * u)))
      (cexp (-((x : ℂ) * u)) * (-u)) (Icc 0 1) x := by
    intro x _
    have h1 : HasDerivAt (fun s : ℝ => (s : ℂ) * u) u x := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := x)).mul_const u
    have h : HasDerivAt (fun s : ℝ => -((s : ℂ) * u)) (-u) x := h1.neg
    exact h.cexp.hasDerivWithinAt
  have hbound : ∀ x ∈ Ico (0 : ℝ) 1, ‖cexp (-((x : ℂ) * u)) * (-u)‖ ≤ ‖u‖ := by
    intro x hx
    rw [norm_mul, norm_neg, Complex.norm_exp]
    have hre : (-((x : ℂ) * u)).re = -(x * u.re) := by simp
    rw [hre]
    have : Real.exp (-(x * u.re)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith [hx.1])
    nlinarith [norm_nonneg u]
  have h := norm_image_sub_le_of_norm_deriv_le_segment' hderiv hbound 1 ⟨zero_le_one, le_rfl⟩
  simp only [Complex.ofReal_one, one_mul, Complex.ofReal_zero, zero_mul, neg_zero,
    Complex.exp_zero, sub_zero, mul_one] at h
  rwa [norm_sub_rev] at h

/-- `1 - e^{-u} ≥ u/2` for `0 ≤ u ≤ 1/2`. -/
theorem half_le_one_sub_exp_neg {u : ℝ} (h0 : 0 ≤ u) (h1 : u ≤ 1 / 2) :
    u / 2 ≤ 1 - Real.exp (-u) := by
  have he := Real.add_one_le_exp u
  have hm := Real.add_one_le_exp (-u)
  have hprod : Real.exp (-u) * Real.exp u = 1 := by rw [← Real.exp_add]; simp
  have hp := Real.exp_pos (-u)
  nlinarith

/-! ## Abel summation of the exponential series -/

/-- The partial sums `N_a(n) = a_1 + ⋯ + a_n`. -/
def coeffSum (a : ℕ → ℂ) (n : ℕ) : ℂ := ∑ k ∈ Finset.range n, a (k + 1)

theorem expSeries_eq_tsum_pow (a : ℕ → ℂ) (τ : ℂ) :
    expSeries a τ = ∑' n : ℕ, a (n + 1) * cexp (-(2 * Real.pi * τ)) ^ (n + 1) := by
  unfold expSeries
  refine tsum_congr fun n => ?_
  rw [← Complex.exp_nat_mul]
  congr 2
  push_cast
  ring

/-- **Abel summation.**  If the partial sums are `O(n)` and `‖w‖ < 1`, then
`Σ a_{n} wⁿ = A w/(1 - w) + (1 - w) Σ (N_a(n) - A n) wⁿ`. -/
theorem tsum_coeff_mul_pow_eq {a : ℕ → ℂ} (A : ℂ) {K : ℝ}
    (hK : ∀ n, ‖coeffSum a n‖ ≤ K * ((n : ℝ) + 1)) {w : ℂ} (hw : ‖w‖ < 1) :
    ∑' n : ℕ, a (n + 1) * w ^ (n + 1) =
      A * w / (1 - w) + (1 - w) * ∑' n : ℕ, (coeffSum a (n + 1) - A * ((n : ℂ) + 1)) *
        w ^ (n + 1) := by
  have hw1 : 1 - w ≠ 0 := by
    intro h
    have : w = 1 := by linear_combination -h
    rw [this, norm_one] at hw
    exact lt_irrefl _ hw
  -- summability
  have hgeo1 : Summable fun n : ℕ => ((n : ℝ) + 1) * ‖w‖ ^ n := by
    have h1 := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1
      (r := ‖w‖) (by rw [norm_norm]; exact hw)
    have h0 := summable_geometric_of_lt_one (norm_nonneg w) hw
    refine (h1.add h0).congr fun n => ?_
    simp only [pow_one]; ring
  have hNs : Summable fun n : ℕ => coeffSum a n * w ^ n := by
    refine Summable.of_norm_bounded (hgeo1.mul_left K) fun n => ?_
    rw [norm_mul, norm_pow]
    calc ‖coeffSum a n‖ * ‖w‖ ^ n ≤ K * ((n : ℝ) + 1) * ‖w‖ ^ n :=
          mul_le_mul_of_nonneg_right (hK n) (by positivity)
      _ = K * (((n : ℝ) + 1) * ‖w‖ ^ n) := by ring
  have hNs1 : Summable fun n : ℕ => coeffSum a (n + 1) * w ^ (n + 1) :=
    (summable_nat_add_iff 1).mpr hNs
  have hNsw : Summable fun n : ℕ => coeffSum a n * w ^ (n + 1) :=
    (hNs.mul_left w).congr fun n => by ring
  have hlin : Summable fun n : ℕ => ((n : ℂ) + 1) * w ^ (n + 1) := by
    have h := (summable_pow_mul_geometric_of_norm_lt_one (R := ℂ) 1 hw)
    have h' := (summable_nat_add_iff 1).mpr h
    refine h'.congr fun n => ?_
    push_cast; ring
  have hlinA : Summable fun n : ℕ => A * ((n : ℂ) + 1) * w ^ (n + 1) :=
    (hlin.mul_left A).congr fun n => by ring
  -- `Σ a_{n+1} w^{n+1} = (1 - w) Σ N(n+1) w^{n+1}`
  have hstep : ∀ n, a (n + 1) * w ^ (n + 1) =
      coeffSum a (n + 1) * w ^ (n + 1) - coeffSum a n * w ^ (n + 1) := by
    intro n
    rw [coeffSum, Finset.sum_range_succ, ← coeffSum]
    ring
  have hshift : ∑' n : ℕ, coeffSum a n * w ^ (n + 1) =
      w * ∑' n : ℕ, coeffSum a (n + 1) * w ^ (n + 1) := by
    rw [← tsum_mul_left, hNsw.tsum_eq_zero_add]
    simp only [coeffSum, Finset.range_zero, Finset.sum_empty, zero_mul, zero_add]
    exact tsum_congr fun n => by ring
  have hR : Summable fun n : ℕ => (coeffSum a (n + 1) - A * ((n : ℂ) + 1)) * w ^ (n + 1) :=
    (hNs1.sub hlinA).congr fun n => by ring
  have hsplit : ∑' n : ℕ, coeffSum a (n + 1) * w ^ (n + 1) =
      ∑' n : ℕ, A * ((n : ℂ) + 1) * w ^ (n + 1) +
        ∑' n : ℕ, (coeffSum a (n + 1) - A * ((n : ℂ) + 1)) * w ^ (n + 1) := by
    rw [← hlinA.tsum_add hR]
    exact tsum_congr fun n => by ring
  have hs : Summable fun m : ℕ => (m : ℂ) * w ^ m :=
    (summable_pow_mul_geometric_of_norm_lt_one (R := ℂ) 1 hw).congr fun n => by simp
  have hgeom : ∑' n : ℕ, A * ((n : ℂ) + 1) * w ^ (n + 1) = A * (w / (1 - w) ^ 2) := by
    rw [← tsum_coe_mul_geometric_of_norm_lt_one hw, hs.tsum_eq_zero_add]
    simp only [Nat.cast_zero, zero_mul, zero_add]
    rw [← tsum_mul_left]
    exact tsum_congr fun n => by push_cast; ring
  rw [show (∑' n : ℕ, a (n + 1) * w ^ (n + 1)) =
      ∑' n : ℕ, (coeffSum a (n + 1) * w ^ (n + 1) - coeffSum a n * w ^ (n + 1)) from
      tsum_congr hstep, hNs1.tsum_sub hNsw, hshift, hsplit, hgeom]
  field_simp

/-- The Abel remainder is bounded by the remainder of the density: if
`‖N_a(n) - A n‖ ≤ η n + C`, then `‖Σ (N_a(n) - A n) wⁿ‖ ≤ η/(1 - ‖w‖)² + C/(1 - ‖w‖)`. -/
theorem norm_tsum_remainder_le {a : ℕ → ℂ} {A η C : ℝ} (hη : 0 ≤ η) (hC : 0 ≤ C)
    (hN : ∀ n : ℕ, ‖coeffSum a n - A * n‖ ≤ η * n + C) {w : ℂ} (hw : ‖w‖ < 1) :
    ‖∑' n : ℕ, (coeffSum a (n + 1) - (A : ℂ) * ((n : ℂ) + 1)) * w ^ (n + 1)‖ ≤
      η / (1 - ‖w‖) ^ 2 + C / (1 - ‖w‖) := by
  set q := ‖w‖ with hq
  have hq0 : 0 ≤ q := norm_nonneg w
  have h1q : 0 < 1 - q := by linarith
  have hlin : Summable fun n : ℕ => (n : ℝ) * q ^ n :=
    (summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 (r := q)
      (by rw [Real.norm_of_nonneg hq0]; exact hw)).congr fun n => by simp
  have hgeo : Summable fun n : ℕ => q ^ n := summable_geometric_of_lt_one hq0 hw
  have hmaj : Summable fun n : ℕ => η * ((n + 1 : ℕ) * q ^ (n + 1)) + C * q ^ (n + 1) :=
    (((summable_nat_add_iff 1).mpr hlin).mul_left η).add
      (((summable_nat_add_iff 1).mpr hgeo).mul_left C)
  have hpt : ∀ n : ℕ, ‖(coeffSum a (n + 1) - (A : ℂ) * ((n : ℂ) + 1)) * w ^ (n + 1)‖ ≤
      η * ((n + 1 : ℕ) * q ^ (n + 1)) + C * q ^ (n + 1) := by
    intro n
    rw [norm_mul, norm_pow, ← hq]
    have h := hN (n + 1)
    push_cast at h ⊢
    calc ‖coeffSum a (n + 1) - (A : ℂ) * ((n : ℂ) + 1)‖ * q ^ (n + 1)
        ≤ (η * ((n : ℝ) + 1) + C) * q ^ (n + 1) := mul_le_mul_of_nonneg_right h (by positivity)
      _ = η * (((n : ℝ) + 1) * q ^ (n + 1)) + C * q ^ (n + 1) := by ring
  have hsl : Summable fun n : ℕ => (n : ℝ) * q ^ n := hlin
  have hsum1 : ∑' n : ℕ, ((n + 1 : ℕ) : ℝ) * q ^ (n + 1) = q / (1 - q) ^ 2 := by
    rw [← tsum_coe_mul_geometric_of_norm_lt_one (by rw [Real.norm_of_nonneg hq0]; exact hw),
      hsl.tsum_eq_zero_add]
    simp
  have hsum2 : ∑' n : ℕ, q ^ (n + 1) = q / (1 - q) := by
    simp_rw [pow_succ']
    rw [tsum_mul_left, tsum_geometric_of_lt_one hq0 hw]
    field_simp
  have hnorms : Summable fun n : ℕ =>
      ‖(coeffSum a (n + 1) - (A : ℂ) * ((n : ℂ) + 1)) * w ^ (n + 1)‖ :=
    hmaj.of_nonneg_of_le (fun n => norm_nonneg _) hpt
  calc ‖∑' n : ℕ, (coeffSum a (n + 1) - (A : ℂ) * ((n : ℂ) + 1)) * w ^ (n + 1)‖
      ≤ ∑' n : ℕ, ‖(coeffSum a (n + 1) - (A : ℂ) * ((n : ℂ) + 1)) * w ^ (n + 1)‖ :=
        norm_tsum_le_tsum_norm hnorms
    _ ≤ ∑' n : ℕ, (η * ((n + 1 : ℕ) * q ^ (n + 1)) + C * q ^ (n + 1)) :=
        Summable.tsum_le_tsum hpt hnorms hmaj
    _ = η * (q / (1 - q) ^ 2) + C * (q / (1 - q)) := by
        rw [(((summable_nat_add_iff 1).mpr hlin).mul_left η).tsum_add
          (((summable_nat_add_iff 1).mpr hgeo).mul_left C), tsum_mul_left, tsum_mul_left,
          hsum1, hsum2]
    _ ≤ η / (1 - q) ^ 2 + C / (1 - q) := by
        have hq1 : q ≤ 1 := hw.le
        have e1 : η * (q / (1 - q) ^ 2) = η * q / (1 - q) ^ 2 := by ring
        have e2 : C * (q / (1 - q)) = C * q / (1 - q) := by ring
        rw [e1, e2]
        gcongr
        · exact mul_le_of_le_one_right hη hq1
        · exact mul_le_of_le_one_right hC hq1

/-! ## The Hamburger series near a missing resonance -/

/-- `‖k² + τ²‖ ≥ k |k - Im τ|` for `k ≥ 0` and `Im τ ≥ 0`. -/
theorem mul_abs_sub_im_le_norm_sq_add_sq {k : ℝ} (hk : 0 ≤ k) {τ : ℂ} (hy : 0 ≤ τ.im) :
    k * |k - τ.im| ≤ ‖(k : ℂ) ^ 2 + τ ^ 2‖ := by
  have hf : (k : ℂ) ^ 2 + τ ^ 2 = ((k : ℂ) - I * τ) * ((k : ℂ) + I * τ) := by
    ring_nf; rw [I_sq]; ring
  have h1 : |k - τ.im| ≤ ‖(k : ℂ) + I * τ‖ := by
    have h := Complex.abs_re_le_norm ((k : ℂ) + I * τ)
    simpa [sub_eq_add_neg] using h
  have h2 : k ≤ ‖(k : ℂ) - I * τ‖ := by
    have h := Complex.abs_re_le_norm ((k : ℂ) - I * τ)
    have hre : ((k : ℂ) - I * τ).re = k + τ.im := by simp
    rw [hre, abs_of_nonneg (by linarith)] at h
    linarith
  rw [hf, norm_mul]
  exact mul_le_mul h2 h1 (abs_nonneg _) (norm_nonneg _)

/-- **No pole at a missing resonance.**  If `a_m = 0`, `Im τ ≥ 0`, `|Im τ - m| ≤ 1/4` and
`‖τ‖ ≤ 2m`, then `‖L_a(τ)‖ ≤ (16/3π) m² Σ ‖a_n‖/n²`. -/
theorem norm_hamburgerSeries_le_of_coeff_eq_zero {a : ℕ → ℂ}
    (ha : Summable fun n : ℕ => ‖a (n + 1)‖ / ((n + 1 : ℕ) : ℝ) ^ 2) {m : ℕ} (hm : 1 ≤ m)
    (ham : a m = 0) {τ : ℂ} (hy0 : 0 ≤ τ.im) (hym : |τ.im - m| ≤ 1 / 4)
    (hτ : ‖τ‖ ≤ 2 * m) :
    ‖hamburgerSeries a τ‖ ≤
      16 / (3 * Real.pi) * m ^ 2 * ∑' n : ℕ, ‖a (n + 1)‖ / ((n + 1 : ℕ) : ℝ) ^ 2 := by
  have hpi := Real.pi_pos
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hpt : ∀ n : ℕ, ‖a (n + 1) * τ / ((Real.pi : ℂ) * (((n + 1 : ℕ) : ℂ) ^ 2 + τ ^ 2))‖ ≤
      16 / (3 * Real.pi) * m ^ 2 * (‖a (n + 1)‖ / ((n + 1 : ℕ) : ℝ) ^ 2) := by
    intro n
    by_cases hnm : n + 1 = m
    · rw [hnm, ham]; simp only [zero_mul, zero_div, norm_zero]; positivity
    set k : ℝ := ((n + 1 : ℕ) : ℝ) with hk
    have hk1 : (1 : ℝ) ≤ k := by rw [hk]; exact_mod_cast Nat.succ_pos n
    set d : ℝ := |k - m| with hd
    have hd1 : 1 ≤ d := by
      rw [hd, hk]
      rcases Nat.lt_or_gt_of_ne hnm with h | h
      · have : ((n + 1 : ℕ) : ℝ) + 1 ≤ m := by exact_mod_cast h
        rw [abs_of_neg (by linarith)]; linarith
      · have : (m : ℝ) + 1 ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast h
        rw [abs_of_pos (by linarith)]; linarith
    -- `|k - Im τ| ≥ (3/4) |k - m|`
    have hky : 3 / 4 * d ≤ |k - τ.im| := by
      have := abs_sub_abs_le_abs_sub (k - m) (k - τ.im)
      rw [show k - m - (k - τ.im) = τ.im - m by ring] at this
      linarith
    have hD : 3 / 4 * (k * d) ≤ ‖(k : ℂ) ^ 2 + τ ^ 2‖ := by
      have := mul_abs_sub_im_le_norm_sq_add_sq (by linarith : (0 : ℝ) ≤ k) hy0
      nlinarith
    -- `k ≤ 2 m |k - m|`
    have hkd : k ≤ 2 * m * d := by
      rcases le_or_gt k (2 * m) with h | h
      · nlinarith
      · rw [hd, abs_of_pos (by linarith)]; nlinarith
    have hkey : 2 * m * k ^ 2 ≤ 16 / 3 * m ^ 2 * (3 / 4 * (k * d)) := by
      nlinarith [mul_le_mul_of_nonneg_left hkd (by positivity : (0 : ℝ) ≤ 2 * m * k)]
    have hnorm : ‖a (n + 1) * τ / ((Real.pi : ℂ) * (((n + 1 : ℕ) : ℂ) ^ 2 + τ ^ 2))‖ =
        ‖a (n + 1)‖ * ‖τ‖ / (Real.pi * ‖(k : ℂ) ^ 2 + τ ^ 2‖) := by
      rw [norm_div, norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hpi.le, hk]
      push_cast; rfl
    rw [hnorm]
    have hX := norm_nonneg (a (n + 1))
    calc ‖a (n + 1)‖ * ‖τ‖ / (Real.pi * ‖(k : ℂ) ^ 2 + τ ^ 2‖)
        ≤ ‖a (n + 1)‖ * (2 * m) / (Real.pi * (3 / 4 * (k * d))) := by
          gcongr
      _ = ‖a (n + 1)‖ / Real.pi * (2 * m / (3 / 4 * (k * d))) := by ring
      _ ≤ ‖a (n + 1)‖ / Real.pi * (16 / 3 * m ^ 2 / k ^ 2) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          exact hkey
      _ = 16 / (3 * Real.pi) * m ^ 2 * (‖a (n + 1)‖ / k ^ 2) := by ring
  have hmaj : Summable fun n : ℕ => 16 / (3 * Real.pi) * m ^ 2 *
      (‖a (n + 1)‖ / ((n + 1 : ℕ) : ℝ) ^ 2) := ha.mul_left _
  have hnorms := hmaj.of_nonneg_of_le (fun n => norm_nonneg _) hpt
  unfold hamburgerSeries
  calc ‖∑' n : ℕ, a (n + 1) * τ / ((Real.pi : ℂ) * (((n + 1 : ℕ) : ℂ) ^ 2 + τ ^ 2))‖
      ≤ ∑' n : ℕ, ‖a (n + 1) * τ / ((Real.pi : ℂ) * (((n + 1 : ℕ) : ℂ) ^ 2 + τ ^ 2))‖ :=
        norm_tsum_le_tsum_norm hnorms
    _ ≤ ∑' n : ℕ, 16 / (3 * Real.pi) * m ^ 2 * (‖a (n + 1)‖ / ((n + 1 : ℕ) : ℝ) ^ 2) :=
        Summable.tsum_le_tsum hpt hnorms hmaj
    _ = _ := tsum_mul_left

/-! ## A spike of the defect at a missing resonance -/

/-- The Abel variable `w = e^{-2πu}` at a point `u` with `3μ/(2π) ≤ Re u ≤ 3μ/2` and
`|Im u| ≤ μ/4`, `3πμ ≤ 1/8`: `‖w‖ ≥ 7/8`, `1 - ‖w‖ ≥ 3μ/2` and `‖1 - w‖ ≤ 7πμ/2`. -/
theorem abelVariable_bounds {μ : ℝ} (hμ : 0 < μ) (hμ1 : 3 * Real.pi * μ ≤ 1 / 8) {u : ℂ}
    (hx1 : 3 / (2 * Real.pi) * μ ≤ u.re) (hx2 : u.re ≤ 3 / 2 * μ) (hy : |u.im| ≤ μ / 4) :
    7 / 8 ≤ ‖cexp (-(2 * Real.pi * u))‖ ∧ 3 / 2 * μ ≤ 1 - ‖cexp (-(2 * Real.pi * u))‖ ∧
      ‖1 - cexp (-(2 * Real.pi * u))‖ ≤ 7 / 2 * Real.pi * μ := by
  have hpi := Real.pi_pos
  have hx0 : 0 < u.re := lt_of_lt_of_le (by positivity) hx1
  have hwn : ‖cexp (-(2 * Real.pi * u))‖ = Real.exp (-(2 * Real.pi * u.re)) := by
    rw [Complex.norm_exp]
    congr 1
    simp
  have h2x : 2 * Real.pi * u.re ≤ 3 * Real.pi * μ := by nlinarith
  refine ⟨?_, ?_, ?_⟩
  · rw [hwn]
    have := Real.add_one_le_exp (-(2 * Real.pi * u.re))
    linarith
  · rw [hwn]
    have h := half_le_one_sub_exp_neg (u := 2 * Real.pi * u.re) (by positivity) (by linarith)
    have : 3 / 2 * μ ≤ Real.pi * u.re := by
      calc 3 / 2 * μ = Real.pi * (3 / (2 * Real.pi) * μ) := by field_simp
        _ ≤ Real.pi * u.re := mul_le_mul_of_nonneg_left hx1 hpi.le
    linarith
  · have hun : ‖u‖ ≤ 7 / 4 * μ := by
      have := Complex.norm_le_abs_re_add_abs_im u
      rw [abs_of_pos hx0] at this
      linarith
    have h := norm_one_sub_cexp_neg_le (u := 2 * Real.pi * u) (by simp; positivity)
    calc ‖1 - cexp (-(2 * Real.pi * u))‖ ≤ ‖2 * (Real.pi : ℂ) * u‖ := h
      _ = 2 * Real.pi * ‖u‖ := by
          rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hpi.le]; norm_num
      _ ≤ 2 * Real.pi * (7 / 4 * μ) := by gcongr
      _ = 7 / 2 * Real.pi * μ := by ring

/-- **The exponential series near `i m`.**  Under the density bound
`‖N_a(n) - A n‖ ≤ (A/64π²) n + C` and `(7π/3) C ≤ A/(32πμ)`, at every `τ` with
`3μ/(2π) ≤ Re τ ≤ 3μ/2`, `|Im τ - m| ≤ μ/4` one has `‖F_a(τ)‖ ≥ 3A/(16πμ)`. -/
theorem le_norm_expSeries_of_window {a : ℕ → ℂ} {A C : ℝ} (hA : 0 < A) (hC : 0 ≤ C)
    (hN : ∀ n : ℕ, ‖coeffSum a n - A * n‖ ≤ A / (64 * Real.pi ^ 2) * n + C)
    {μ : ℝ} (hμ : 0 < μ) (hμ1 : 3 * Real.pi * μ ≤ 1 / 8)
    (hRC : 7 * Real.pi / 3 * C ≤ A / (32 * Real.pi * μ)) (m : ℕ) {τ : ℂ}
    (hx1 : 3 / (2 * Real.pi) * μ ≤ τ.re) (hx2 : τ.re ≤ 3 / 2 * μ)
    (hy : |τ.im - m| ≤ μ / 4) :
    3 * A / (16 * Real.pi * μ) ≤ ‖expSeries a τ‖ := by
  have hpi := Real.pi_pos
  have hper : expSeries a τ = expSeries a (τ - (m : ℂ) * I) := by
    rw [← expSeries_add_nat_mul_I a (τ - (m : ℂ) * I) m, sub_add_cancel]
  obtain ⟨hq78, h1q, h1w⟩ := abelVariable_bounds (u := τ - (m : ℂ) * I) hμ hμ1
    (by simpa using hx1) (by simpa using hx2) (by simpa using hy)
  set w : ℂ := cexp (-(2 * Real.pi * (τ - (m : ℂ) * I))) with hw
  clear_value w
  have hq1 : ‖w‖ < 1 := by linarith
  have h1w0 : 0 < ‖1 - w‖ := by
    refine norm_pos_iff.mpr fun h => ?_
    have : w = 1 := by linear_combination -h
    rw [this, norm_one] at hq1
    exact lt_irrefl _ hq1
  have hK : ∀ n, ‖coeffSum a n‖ ≤ (A / (64 * Real.pi ^ 2) + A + C) * ((n : ℝ) + 1) := by
    intro n
    have h1 := hN n
    have h2 : ‖coeffSum a n‖ ≤ ‖coeffSum a n - A * n‖ + ‖(A : ℂ) * n‖ := by
      have := norm_add_le (coeffSum a n - A * n) ((A : ℂ) * n)
      simpa using this
    have h3 : ‖(A : ℂ) * n‖ = A * n := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hA.le, Complex.norm_natCast]
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hη0 : 0 ≤ A / (64 * Real.pi ^ 2) := by positivity
    nlinarith
  have hRem := norm_tsum_remainder_le (a := a) (A := A) (by positivity) hC hN hq1
  set Rs := ∑' n : ℕ, (coeffSum a (n + 1) - (A : ℂ) * ((n : ℂ) + 1)) * w ^ (n + 1) with hRs
  have hF : expSeries a τ = (A : ℂ) * w / (1 - w) + (1 - w) * Rs := by
    rw [hper, expSeries_eq_tsum_pow, ← hw, tsum_coeff_mul_pow_eq (A : ℂ) hK hq1]
  have hmain : A / (4 * Real.pi * μ) ≤ ‖(A : ℂ) * w / (1 - w)‖ := by
    rw [norm_div, norm_mul, Complex.norm_real, Real.norm_of_nonneg hA.le]
    calc A / (4 * Real.pi * μ) = A * (7 / 8) / (7 / 2 * Real.pi * μ) := by field_simp; ring
      _ ≤ A * ‖w‖ / ‖1 - w‖ := by gcongr
  have hrem : ‖(1 - w) * Rs‖ ≤ A / (16 * Real.pi * μ) := by
    rw [norm_mul]
    have hq0 : 0 < 1 - ‖w‖ := by linarith
    have hb : ‖Rs‖ ≤ A / (64 * Real.pi ^ 2) / (3 / 2 * μ) ^ 2 + C / (3 / 2 * μ) :=
      hRem.trans (add_le_add (by gcongr) (by gcongr))
    have e1 : 14 / 576 * (A / (Real.pi * μ)) ≤ A / (32 * Real.pi * μ) := by
      rw [show A / (32 * Real.pi * μ) = 1 / 32 * (A / (Real.pi * μ)) by field_simp]
      exact mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
    calc ‖1 - w‖ * ‖Rs‖
        ≤ 7 / 2 * Real.pi * μ * (A / (64 * Real.pi ^ 2) / (3 / 2 * μ) ^ 2 + C / (3 / 2 * μ)) :=
          mul_le_mul h1w hb (norm_nonneg _) (by positivity)
      _ = 14 / 576 * (A / (Real.pi * μ)) + 7 * Real.pi / 3 * C := by field_simp; ring
      _ ≤ A / (32 * Real.pi * μ) + A / (32 * Real.pi * μ) := add_le_add e1 hRC
      _ = A / (16 * Real.pi * μ) := by field_simp; ring
  have htri := norm_sub_norm_le ((A : ℂ) * w / (1 - w)) (-((1 - w) * Rs))
  rw [sub_neg_eq_add, norm_neg] at htri
  have e2 : 3 * A / (16 * Real.pi * μ) = A / (4 * Real.pi * μ) - A / (16 * Real.pi * μ) := by
    field_simp; ring
  rw [hF, e2]
  linarith only [htri, hmain, hrem]

/-- **The spike.**  Let the coefficients have density `A > 0` with
`‖N_a(n) - A n‖ ≤ (A/64π²) n + C`, let `a_m = 0`, and let `τ` lie in the window
`3μ/(2π) ≤ Re τ ≤ 3μ/2`, `|Im τ - m| ≤ μ/4` with `μ` small in the stated sense.  Then
`‖J_g(τ)‖ ≥ A/(8πμ)`. -/
theorem le_norm_defectLaplace_of_window {a : ℕ → ℂ}
    (ha : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => ‖a (n + 1)‖ / ((n : ℝ) + 1) ^ σ)
    {β : ℂ} {g : ℝ → ℂ} (hH : HamburgerStripDefect (coeffDirichlet a) β g)
    {A C : ℝ} (hA : 0 < A) (hC : 0 ≤ C)
    (hN : ∀ n : ℕ, ‖coeffSum a n - A * n‖ ≤ A / (64 * Real.pi ^ 2) * n + C)
    {m : ℕ} (hm : 1 ≤ m) (ham : a m = 0) {μ : ℝ} (hμ : 0 < μ)
    (hμ1 : 3 * Real.pi * μ ≤ 1 / 8)
    (hRC : 7 * Real.pi / 3 * C ≤ A / (32 * Real.pi * μ))
    (hLS : 16 / (3 * Real.pi) * m ^ 2 * (∑' n : ℕ, ‖a (n + 1)‖ / ((n + 1 : ℕ) : ℝ) ^ 2) ≤
      A / (32 * Real.pi * μ))
    (hβ : ‖β‖ * (4 / (3 * Real.pi) + 1) ≤ A / (32 * Real.pi * μ))
    {τ : ℂ} (hx1 : 3 / (2 * Real.pi) * μ ≤ τ.re) (hx2 : τ.re ≤ 3 / 2 * μ)
    (hy : |τ.im - m| ≤ μ / 4) :
    A / (8 * Real.pi * μ) ≤ ‖defectLaplace g τ‖ := by
  have hpi := Real.pi_pos
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hμs : μ ≤ 1 / 64 := by nlinarith [Real.pi_gt_three]
  have hx0 : 0 < τ.re := lt_of_lt_of_le (by positivity) hx1
  have hym := abs_le.mp hy
  have hy0 : 0 ≤ τ.im := by linarith [hym.1]
  have hF := le_norm_expSeries_of_window hA hC hN hμ hμ1 hRC m hx1 hx2 hy
  have hτn : ‖τ‖ ≤ 2 * m := by
    have := Complex.norm_le_abs_re_add_abs_im τ
    rw [abs_of_pos hx0, abs_of_nonneg hy0] at this
    linarith [hym.2]
  have hL := norm_hamburgerSeries_le_of_coeff_eq_zero (by simpa using summable_sq_of_forall_rpow ha)
    hm ham hy0 (abs_le.mpr ⟨by linarith [hym.1], by linarith [hym.2]⟩) hτn
  have hτ34 : 3 / 4 ≤ ‖τ‖ := by
    have := Complex.abs_im_le_norm τ
    rw [abs_of_nonneg hy0] at this
    linarith [hym.1]
  have hpol : ‖β / (Real.pi * τ)‖ + ‖β‖ ≤ A / (32 * Real.pi * μ) := by
    rw [norm_div, norm_mul, Complex.norm_real, Real.norm_of_nonneg hpi.le]
    have h1 : ‖β‖ / (Real.pi * ‖τ‖) ≤ ‖β‖ * (4 / (3 * Real.pi)) := by
      rw [div_le_iff₀ (by positivity)]
      have : ‖β‖ * (4 / (3 * Real.pi)) * (Real.pi * ‖τ‖) = ‖β‖ * (4 / 3 * ‖τ‖) := by
        field_simp
      rw [this]
      exact le_mul_of_one_le_right (norm_nonneg β) (by linarith)
    have e : ‖β‖ * (4 / (3 * Real.pi) + 1) = ‖β‖ * (4 / (3 * Real.pi)) + ‖β‖ := by ring
    linarith only [h1, hβ, e]
  -- `F_a = L_a - J_g + β/(πτ) - β`
  have e : expSeries a τ = hamburgerSeries a τ - defectLaplace g τ +
      β / (Real.pi * τ) - β := by
    rw [hamburgerSeries_eq_defect ha hH hx0]
    ring
  have h1 := norm_sub_le (hamburgerSeries a τ - defectLaplace g τ + β / (Real.pi * τ)) β
  have h2 := norm_add_le (hamburgerSeries a τ - defectLaplace g τ) (β / (Real.pi * τ))
  have h3 := norm_sub_le (hamburgerSeries a τ) (defectLaplace g τ)
  rw [← e] at h1
  have e2 : A / (8 * Real.pi * μ) =
      3 * A / (16 * Real.pi * μ) - A / (32 * Real.pi * μ) - A / (32 * Real.pi * μ) := by
    field_simp; ring
  rw [e2]
  linarith only [h1, h2, h3, hF, hL, hLS, hpol]

/-! ## Windows on the tilted ray -/

theorem cos_bounds {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1 / 2) :
    7 / 8 ≤ Real.cos θ ∧ Real.cos θ ≤ 1 := by
  refine ⟨?_, Real.cos_le_one θ⟩
  have := Real.one_sub_sq_div_two_le_cos (x := θ)
  nlinarith

/-- **Windows on the tilted ray.**  For `0 < θ ≤ 1/2`, `m ≥ 1` and `|r - m/cos θ| ≤ mθ/4`, the
point `τ = r e^{i(π/2-θ)}` has `3mθ/(2π) ≤ Re τ ≤ 3mθ/2` and `|Im τ - m| ≤ mθ/4`. -/
theorem tiltDir_window {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1 / 2) {m : ℝ} (hm : 1 ≤ m) {r : ℝ}
    (hr : |r - m / Real.cos θ| ≤ m * θ / 4) :
    3 / (2 * Real.pi) * (m * θ) ≤ ((r : ℂ) * tiltDir θ).re ∧
      ((r : ℂ) * tiltDir θ).re ≤ 3 / 2 * (m * θ) ∧
      |((r : ℂ) * tiltDir θ).im - m| ≤ m * θ / 4 := by
  have hpi := Real.pi_pos
  have hpi3 := Real.pi_gt_three
  obtain ⟨hcos78, hcos1⟩ := cos_bounds hθ0 hθ1
  have hcpos : 0 < Real.cos θ := by linarith
  have hsin1 : Real.sin θ ≤ θ := Real.sin_le hθ0.le
  have hsin2 : 2 / Real.pi * θ ≤ Real.sin θ := Real.mul_le_sin hθ0.le (by linarith)
  have hsin0 : 0 ≤ Real.sin θ := Real.sin_nonneg_of_nonneg_of_le_pi hθ0.le (by linarith)
  have hmc1 : m ≤ m / Real.cos θ := by rw [le_div_iff₀ hcpos]; nlinarith
  have hmc2 : m / Real.cos θ ≤ 8 / 7 * m := by rw [div_le_iff₀ hcpos]; nlinarith
  have hmθ : m * θ ≤ m / 2 := by nlinarith
  obtain ⟨hr1, hr2⟩ := abs_le.mp hr
  have hrlo : 7 / 8 * m ≤ r := by linarith
  have hrhi : r ≤ 3 / 2 * m := by linarith
  rw [Complex.re_ofReal_mul, Complex.im_ofReal_mul, tiltDir_re, tiltDir_im]
  refine ⟨?_, ?_, ?_⟩
  · calc 3 / (2 * Real.pi) * (m * θ) ≤ 7 / 4 / Real.pi * (m * θ) := by
          rw [show 3 / (2 * Real.pi) = 3 / 2 / Real.pi by field_simp]
          exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (by norm_num) hpi.le)
            (by positivity)
      _ = 7 / 8 * m * (2 / Real.pi * θ) := by ring
      _ ≤ r * Real.sin θ := mul_le_mul hrlo hsin2 (by positivity) (by linarith)
  · calc r * Real.sin θ ≤ 3 / 2 * m * θ := mul_le_mul hrhi hsin1 hsin0 (by positivity)
      _ = 3 / 2 * (m * θ) := by ring
  · have e : r * Real.cos θ - m = (r - m / Real.cos θ) * Real.cos θ := by field_simp
    rw [e, abs_mul, abs_of_pos hcpos]
    calc |r - m / Real.cos θ| * Real.cos θ ≤ m * θ / 4 * 1 :=
          mul_le_mul hr hcos1 hcpos.le (by positivity)
      _ = m * θ / 4 := by ring

/-- The energy of one window: if `a_m = 0` and `μ = mθ` is small, the window
`|r - m/cos θ| ≤ mθ/4` carries energy at least `A²/(128π² mθ)`. -/
theorem setIntegral_window_ge {a : ℕ → ℂ}
    (ha : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => ‖a (n + 1)‖ / ((n : ℝ) + 1) ^ σ)
    {β : ℂ} {g : ℝ → ℂ} (hH : HamburgerStripDefect (coeffDirichlet a) β g)
    {A C : ℝ} (hA : 0 < A) (hC : 0 ≤ C)
    (hN : ∀ n : ℕ, ‖coeffSum a n - A * n‖ ≤ A / (64 * Real.pi ^ 2) * n + C)
    {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1 / 2) {m : ℕ} (hm : 1 ≤ m) (ham : a m = 0)
    (hμ1 : 3 * Real.pi * (m * θ) ≤ 1 / 8)
    (hRC : 7 * Real.pi / 3 * C ≤ A / (32 * Real.pi * (m * θ)))
    (hLS : 16 / (3 * Real.pi) * m ^ 2 * (∑' n : ℕ, ‖a (n + 1)‖ / ((n + 1 : ℕ) : ℝ) ^ 2) ≤
      A / (32 * Real.pi * (m * θ)))
    (hβ : ‖β‖ * (4 / (3 * Real.pi) + 1) ≤ A / (32 * Real.pi * (m * θ)))
    (hint : IntegrableOn (fun r : ℝ => ‖defectLaplace g ((r : ℂ) * tiltDir θ)‖ ^ 2) (Ioi 0)) :
    A ^ 2 / (128 * Real.pi ^ 2 * (m * θ)) ≤
      ∫ r in Icc ((m : ℝ) / Real.cos θ - m * θ / 4) (m / Real.cos θ + m * θ / 4),
        ‖defectLaplace g ((r : ℂ) * tiltDir θ)‖ ^ 2 := by
  have hpi := Real.pi_pos
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hμ : 0 < (m : ℝ) * θ := by positivity
  obtain ⟨hcos78, hcos1⟩ := cos_bounds hθ0 hθ1
  have hcpos : 0 < Real.cos θ := by linarith
  have hmc1 : (m : ℝ) ≤ m / Real.cos θ := by rw [le_div_iff₀ hcpos]; nlinarith
  have hsub : Icc ((m : ℝ) / Real.cos θ - m * θ / 4) (m / Real.cos θ + m * θ / 4) ⊆ Ioi 0 := by
    intro r hr
    have : (m : ℝ) * θ ≤ m / 2 := by nlinarith
    exact lt_of_lt_of_le (by linarith) hr.1
  have hpt : ∀ r ∈ Icc ((m : ℝ) / Real.cos θ - m * θ / 4) (m / Real.cos θ + m * θ / 4),
      (A / (8 * Real.pi * (m * θ))) ^ 2 ≤ ‖defectLaplace g ((r : ℂ) * tiltDir θ)‖ ^ 2 := by
    intro r hr
    have hr' : |r - m / Real.cos θ| ≤ m * θ / 4 :=
      abs_le.mpr ⟨by linarith [hr.1], by linarith [hr.2]⟩
    obtain ⟨hx1, hx2, hy⟩ := tiltDir_window hθ0 hθ1 hm1 hr'
    exact pow_le_pow_left₀ (by positivity)
      (le_norm_defectLaplace_of_window ha hH hA hC hN hm ham hμ hμ1 hRC hLS hβ hx1 hx2 hy) 2
  have hge := setIntegral_ge_of_const_le (μ := volume) measurableSet_Icc
    (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top) hpt (hint.mono_set hsub)
  have hvol : volume.real (Icc ((m : ℝ) / Real.cos θ - m * θ / 4) (m / Real.cos θ + m * θ / 4)) =
      m * θ / 2 := by
    rw [measureReal_def, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)]
    ring
  rw [hvol, smul_eq_mul] at hge
  calc A ^ 2 / (128 * Real.pi ^ 2 * (m * θ)) = m * θ / 2 * (A / (8 * Real.pi * (m * θ))) ^ 2 := by
        field_simp; ring
    _ ≤ _ := hge

/-- Disjoint windows inside `(0, ∞)` carry at most the whole energy. -/
theorem sum_setIntegral_Icc_le {f : ℝ → ℝ} (hf : IntegrableOn f (Ioi 0))
    (hf0 : ∀ r, 0 < r → 0 ≤ f r) (s : Finset ℕ) (l u : ℕ → ℝ) (hl : ∀ k ∈ s, 0 < l k)
    (hdisj : ∀ k ∈ s, ∀ k' ∈ s, k < k' → u k < l k') :
    ∑ k ∈ s, ∫ r in Icc (l k) (u k), f r ≤ ∫ r in Ioi 0, f r := by
  have hsub : ∀ k ∈ s, Icc (l k) (u k) ⊆ Ioi 0 := fun k hk r hr =>
    lt_of_lt_of_le (hl k hk) hr.1
  have hpair : (s : Set ℕ).Pairwise (Function.onFun Disjoint fun k => Icc (l k) (u k)) := by
    intro k hk k' hk' hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact Set.disjoint_left.mpr fun r hr hr' =>
        absurd (hdisj k hk k' hk' h) (not_lt.mpr (hr'.1.trans hr.2))
    · exact Set.disjoint_left.mpr fun r hr hr' =>
        absurd (hdisj k' hk' k hk h) (not_lt.mpr (hr.1.trans hr'.2))
  rw [← integral_biUnion_finset s (fun k _ => measurableSet_Icc) hpair
    (fun k hk => hf.mono_set (hsub k hk))]
  refine setIntegral_mono_set hf ?_ (LE.le.eventuallyLE
    (Set.iUnion₂_subset fun k hk => hsub k hk))
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr using hf0 r hr

/-- **Summing the windows.**  If the windows at `m = pk`, `1 ≤ k ≤ K`, are small in the sense
of `setIntegral_window_ge` and `2pKθ ≤ 1`, the energy on the tilted ray is at least
`A²/(128π² pθ) · H_K`. -/
theorem harmonic_le_ray_energy {a : ℕ → ℂ}
    (ha : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => ‖a (n + 1)‖ / ((n : ℝ) + 1) ^ σ)
    {β : ℂ} {g : ℝ → ℂ} (hH : HamburgerStripDefect (coeffDirichlet a) β g)
    {A C : ℝ} (hA : 0 < A) (hC : 0 ≤ C)
    (hN : ∀ n : ℕ, ‖coeffSum a n - A * n‖ ≤ A / (64 * Real.pi ^ 2) * n + C)
    {p : ℕ} (hp : 1 ≤ p) (hres : ∀ k : ℕ, 1 ≤ k → a (p * k) = 0)
    {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1 / 2) (K : ℕ) (hKθ : 2 * ((p * K : ℕ) : ℝ) * θ ≤ 1)
    (hsmall : ∀ k : ℕ, 1 ≤ k → k ≤ K →
      3 * Real.pi * (((p * k : ℕ) : ℝ) * θ) ≤ 1 / 8 ∧
      7 * Real.pi / 3 * C ≤ A / (32 * Real.pi * (((p * k : ℕ) : ℝ) * θ)) ∧
      16 / (3 * Real.pi) * ((p * k : ℕ) : ℝ) ^ 2 *
          (∑' n : ℕ, ‖a (n + 1)‖ / ((n + 1 : ℕ) : ℝ) ^ 2) ≤
        A / (32 * Real.pi * (((p * k : ℕ) : ℝ) * θ)) ∧
      ‖β‖ * (4 / (3 * Real.pi) + 1) ≤ A / (32 * Real.pi * (((p * k : ℕ) : ℝ) * θ)))
    (hint : IntegrableOn (fun r : ℝ => ‖defectLaplace g ((r : ℂ) * tiltDir θ)‖ ^ 2) (Ioi 0)) :
    A ^ 2 / (128 * Real.pi ^ 2 * (p * θ)) * harmonic K ≤
      ∫ r in Ioi (0 : ℝ), ‖defectLaplace g ((r : ℂ) * tiltDir θ)‖ ^ 2 := by
  have hpi := Real.pi_pos
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
  obtain ⟨hcos78, hcos1⟩ := cos_bounds hθ0 hθ1
  have hcpos : 0 < Real.cos θ := by linarith
  set l : ℕ → ℝ := fun k => ((p * k : ℕ) : ℝ) / Real.cos θ - ((p * k : ℕ) : ℝ) * θ / 4 with hl
  set u : ℕ → ℝ := fun k => ((p * k : ℕ) : ℝ) / Real.cos θ + ((p * k : ℕ) : ℝ) * θ / 4 with hu
  -- each window
  have hwin : ∀ k ∈ Finset.Icc 1 K, A ^ 2 / (128 * Real.pi ^ 2 * (p * θ)) * (k : ℝ)⁻¹ ≤
      ∫ r in Icc (l k) (u k), ‖defectLaplace g ((r : ℂ) * tiltDir θ)‖ ^ 2 := by
    intro k hk
    obtain ⟨hk1, hkK⟩ := Finset.mem_Icc.mp hk
    obtain ⟨h1, h2, h3, h4⟩ := hsmall k hk1 hkK
    have hm : 1 ≤ p * k := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
    have h := setIntegral_window_ge ha hH hA hC hN hθ0 hθ1 hm (hres k hk1) h1 h2 h3 h4 hint
    have hk1' : (1 : ℝ) ≤ k := by exact_mod_cast hk1
    calc A ^ 2 / (128 * Real.pi ^ 2 * (p * θ)) * (k : ℝ)⁻¹ =
          A ^ 2 / (128 * Real.pi ^ 2 * (((p * k : ℕ) : ℝ) * θ)) := by
          push_cast; field_simp
      _ ≤ _ := h
  -- the windows are disjoint and lie in `(0, ∞)`
  have hpos : ∀ k ∈ Finset.Icc 1 K, 0 < l k := by
    intro k hk
    obtain ⟨hk1, -⟩ := Finset.mem_Icc.mp hk
    have hm : (1 : ℝ) ≤ ((p * k : ℕ) : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
    have : ((p * k : ℕ) : ℝ) ≤ ((p * k : ℕ) : ℝ) / Real.cos θ := by
      rw [le_div_iff₀ hcpos]; nlinarith
    simp only [hl]
    nlinarith
  have hdisj : ∀ k ∈ Finset.Icc 1 K, ∀ k' ∈ Finset.Icc 1 K, k < k' → u k < l k' := by
    intro k hk k' hk' hkk'
    obtain ⟨-, hkK⟩ := Finset.mem_Icc.mp hk
    obtain ⟨-, hk'K⟩ := Finset.mem_Icc.mp hk'
    have hgap : (1 : ℝ) ≤ ((p * k' : ℕ) : ℝ) - ((p * k : ℕ) : ℝ) := by
      have : p * k + 1 ≤ p * k' := by nlinarith
      have : ((p * k : ℕ) : ℝ) + 1 ≤ ((p * k' : ℕ) : ℝ) := by exact_mod_cast this
      linarith
    have hdiv : ((p * k' : ℕ) : ℝ) - ((p * k : ℕ) : ℝ) ≤
        (((p * k' : ℕ) : ℝ) - ((p * k : ℕ) : ℝ)) / Real.cos θ := by
      rw [le_div_iff₀ hcpos]; nlinarith
    have hkθ : (((p * k : ℕ) : ℝ) + ((p * k' : ℕ) : ℝ)) * θ ≤ 1 := by
      have e1 : ((p * k : ℕ) : ℝ) ≤ ((p * K : ℕ) : ℝ) := by exact_mod_cast Nat.mul_le_mul_left p hkK
      have e2 : ((p * k' : ℕ) : ℝ) ≤ ((p * K : ℕ) : ℝ) := by
        exact_mod_cast Nat.mul_le_mul_left p hk'K
      nlinarith
    have e : l k' - u k = (((p * k' : ℕ) : ℝ) - ((p * k : ℕ) : ℝ)) / Real.cos θ -
        (((p * k : ℕ) : ℝ) + ((p * k' : ℕ) : ℝ)) * θ / 4 := by
      simp only [hl, hu]; ring
    linarith
  have hsum := sum_setIntegral_Icc_le hint (fun r _ => by positivity) (Finset.Icc 1 K) l u
    hpos hdisj
  have hH' : (harmonic K : ℝ) = ∑ k ∈ Finset.Icc 1 K, (k : ℝ)⁻¹ := by
    rw [harmonic_eq_sum_Icc]; push_cast; rfl
  rw [hH', Finset.mul_sum]
  exact (Finset.sum_le_sum hwin).trans hsum

/-- The four smallness conditions of a window from `μ ≤ ψ`, `M² μ ≤ ψ` and four thresholds
on `ψ`. -/
theorem window_conditions {A C S B μ ψ M : ℝ} (_hA : 0 < A) (hC : 0 ≤ C) (hS : 0 ≤ S)
    (hB : 0 ≤ B) (hμ : 0 < μ) (hμψ : μ ≤ ψ) (hm3 : M ^ 2 * μ ≤ ψ)
    (h1 : ψ ≤ 1 / (24 * Real.pi)) (h2 : ψ ≤ 3 * A / (224 * Real.pi ^ 2 * (C + 1)))
    (h3 : ψ ≤ 3 * A / (512 * (S + 1)))
    (h4 : ψ ≤ A / (32 * Real.pi * (B + 1) * (4 / (3 * Real.pi) + 1))) :
    3 * Real.pi * μ ≤ 1 / 8 ∧ 7 * Real.pi / 3 * C ≤ A / (32 * Real.pi * μ) ∧
      16 / (3 * Real.pi) * M ^ 2 * S ≤ A / (32 * Real.pi * μ) ∧
      B * (4 / (3 * Real.pi) + 1) ≤ A / (32 * Real.pi * μ) := by
  have hpi := Real.pi_pos
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h := hμψ.trans h1
    rw [le_div_iff₀ (by positivity)] at h
    linarith
  · rw [le_div_iff₀ (by positivity)]
    have h := hμψ.trans h2
    rw [le_div_iff₀ (by positivity)] at h
    have e : 7 * Real.pi / 3 * C * (32 * Real.pi * μ) =
        C / (C + 1) * (μ * (224 * Real.pi ^ 2 * (C + 1)) / 3) := by field_simp; ring
    rw [e]
    calc C / (C + 1) * (μ * (224 * Real.pi ^ 2 * (C + 1)) / 3) ≤ 1 * (3 * A / 3) :=
          mul_le_mul ((div_le_one (by positivity)).mpr (by linarith))
            (div_le_div_of_nonneg_right h (by norm_num)) (by positivity) zero_le_one
      _ = A := by ring
  · rw [le_div_iff₀ (by positivity)]
    have h := hm3.trans h3
    rw [le_div_iff₀ (by positivity)] at h
    have e : 16 / (3 * Real.pi) * M ^ 2 * S * (32 * Real.pi * μ) =
        S / (S + 1) * (M ^ 2 * μ * (512 * (S + 1)) / 3) := by field_simp; ring
    rw [e]
    calc S / (S + 1) * (M ^ 2 * μ * (512 * (S + 1)) / 3) ≤ 1 * (3 * A / 3) :=
          mul_le_mul ((div_le_one (by positivity)).mpr (by linarith))
            (div_le_div_of_nonneg_right h (by norm_num)) (by positivity) zero_le_one
      _ = A := by ring
  · rw [le_div_iff₀ (by positivity)]
    have h := hμψ.trans h4
    rw [le_div_iff₀ (by positivity)] at h
    have e : B * (4 / (3 * Real.pi) + 1) * (32 * Real.pi * μ) =
        B / (B + 1) * (μ * (32 * Real.pi * (B + 1) * (4 / (3 * Real.pi) + 1))) := by
      field_simp
    rw [e]
    calc B / (B + 1) * (μ * (32 * Real.pi * (B + 1) * (4 / (3 * Real.pi) + 1))) ≤ 1 * A :=
          mul_le_mul ((div_le_one (by positivity)).mpr (by linarith)) h (by positivity)
            zero_le_one
      _ = A := one_mul A

/-- **The energy bound at one scale.**  With `θ = ψ⁴` and `ψ` below the four thresholds and
below `1/p²`, the windows `m = pk ≤ 1/ψ` give
`∫₀^∞ ‖J_g(r e^{i(π/2-θ)})‖² dr ≥ A²/(128π² pθ) · (1/2) log(1/ψ)`. -/
theorem log_le_ray_energy {a : ℕ → ℂ}
    (ha : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => ‖a (n + 1)‖ / ((n : ℝ) + 1) ^ σ)
    {β : ℂ} {g : ℝ → ℂ} (hH : HamburgerStripDefect (coeffDirichlet a) β g)
    {A C : ℝ} (hA : 0 < A) (hC : 0 ≤ C)
    (hN : ∀ n : ℕ, ‖coeffSum a n - A * n‖ ≤ A / (64 * Real.pi ^ 2) * n + C)
    {p : ℕ} (hp : 1 ≤ p) (hres : ∀ k : ℕ, 1 ≤ k → a (p * k) = 0)
    {ψ : ℝ} (hψ0 : 0 < ψ) (hψ1 : ψ ≤ 1 / 2) (h1 : ψ ≤ 1 / (24 * Real.pi))
    (h2 : ψ ≤ 3 * A / (224 * Real.pi ^ 2 * (C + 1)))
    (h3 : ψ ≤ 3 * A / (512 * ((∑' n : ℕ, ‖a (n + 1)‖ / ((n + 1 : ℕ) : ℝ) ^ 2) + 1)))
    (h4 : ψ ≤ A / (32 * Real.pi * (‖β‖ + 1) * (4 / (3 * Real.pi) + 1)))
    (hψp : ψ ≤ 1 / (p : ℝ) ^ 2)
    (hint : IntegrableOn (fun r : ℝ => ‖defectLaplace g ((r : ℂ) * tiltDir (ψ ^ 4))‖ ^ 2)
      (Ioi 0)) :
    A ^ 2 / (128 * Real.pi ^ 2 * (p * ψ ^ 4)) * (1 / 2 * Real.log (1 / ψ)) ≤
      ∫ r in Ioi (0 : ℝ), ‖defectLaplace g ((r : ℂ) * tiltDir (ψ ^ 4))‖ ^ 2 := by
  have hpi := Real.pi_pos
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hS0 : 0 ≤ ∑' n : ℕ, ‖a (n + 1)‖ / ((n + 1 : ℕ) : ℝ) ^ 2 :=
    tsum_nonneg fun n => by positivity
  have hθ0 : 0 < ψ ^ 4 := by positivity
  have hψle1 : ψ ≤ 1 := by linarith
  have hθψ : ψ ^ 4 ≤ ψ := by
    calc ψ ^ 4 ≤ ψ ^ 1 := pow_le_pow_of_le_one hψ0.le hψle1 (by norm_num)
      _ = ψ := pow_one ψ
  have hθ1 : ψ ^ 4 ≤ 1 / 2 := hθψ.trans hψ1
  set K : ℕ := ⌊1 / (p * ψ)⌋₊ with hK
  have hpK : ((p * K : ℕ) : ℝ) * ψ ≤ 1 := by
    have h := Nat.floor_le (show (0 : ℝ) ≤ 1 / (p * ψ) by positivity)
    rw [← hK] at h
    push_cast
    calc (p : ℝ) * K * ψ = (p * ψ) * K := by ring
      _ ≤ (p * ψ) * (1 / (p * ψ)) := by gcongr
      _ = 1 := by field_simp
  have hmψ : ∀ k : ℕ, k ≤ K → ((p * k : ℕ) : ℝ) * ψ ≤ 1 := by
    intro k hk
    have : ((p * k : ℕ) : ℝ) ≤ ((p * K : ℕ) : ℝ) := by exact_mod_cast Nat.mul_le_mul_left p hk
    nlinarith
  have hμψ : ∀ k : ℕ, k ≤ K → ((p * k : ℕ) : ℝ) * ψ ^ 4 ≤ ψ := by
    intro k hk
    have h := hmψ k hk
    have hψ3 : ψ ^ 3 ≤ ψ := by
      calc ψ ^ 3 ≤ ψ ^ 1 := pow_le_pow_of_le_one hψ0.le hψle1 (by norm_num)
        _ = ψ := pow_one ψ
    calc ((p * k : ℕ) : ℝ) * ψ ^ 4 = (((p * k : ℕ) : ℝ) * ψ) * ψ ^ 3 := by ring
      _ ≤ 1 * ψ ^ 3 := by gcongr
      _ ≤ ψ := by linarith
  have hm3ψ : ∀ k : ℕ, k ≤ K → ((p * k : ℕ) : ℝ) ^ 2 * (((p * k : ℕ) : ℝ) * ψ ^ 4) ≤ ψ := by
    intro k hk
    have h := hmψ k hk
    have hm0 : (0 : ℝ) ≤ ((p * k : ℕ) : ℝ) * ψ := by positivity
    calc ((p * k : ℕ) : ℝ) ^ 2 * (((p * k : ℕ) : ℝ) * ψ ^ 4) =
          (((p * k : ℕ) : ℝ) * ψ) ^ 3 * ψ := by ring
      _ ≤ 1 * ψ := by gcongr; exact pow_le_one₀ hm0 h
      _ = ψ := one_mul ψ
  have hsmall : ∀ k : ℕ, 1 ≤ k → k ≤ K →
      3 * Real.pi * (((p * k : ℕ) : ℝ) * ψ ^ 4) ≤ 1 / 8 ∧
      7 * Real.pi / 3 * C ≤ A / (32 * Real.pi * (((p * k : ℕ) : ℝ) * ψ ^ 4)) ∧
      16 / (3 * Real.pi) * ((p * k : ℕ) : ℝ) ^ 2 *
          (∑' n : ℕ, ‖a (n + 1)‖ / ((n + 1 : ℕ) : ℝ) ^ 2) ≤
        A / (32 * Real.pi * (((p * k : ℕ) : ℝ) * ψ ^ 4)) ∧
      ‖β‖ * (4 / (3 * Real.pi) + 1) ≤ A / (32 * Real.pi * (((p * k : ℕ) : ℝ) * ψ ^ 4)) := by
    intro k hk1 hkK
    have hm0 : (0 : ℝ) < ((p * k : ℕ) : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (Nat.mul_ne_zero (by omega) (by omega))
    exact window_conditions hA hC hS0 (norm_nonneg β) (by positivity) (hμψ k hkK) (hm3ψ k hkK)
      h1 h2 h3 h4
  have hKθ : 2 * ((p * K : ℕ) : ℝ) * ψ ^ 4 ≤ 1 := by
    have h := hμψ K le_rfl
    nlinarith
  have hsum := harmonic_le_ray_energy ha hH hA hC hN hp hres hθ0 hθ1 K hKθ hsmall hint
  -- `H_K ≥ log(K + 1) ≥ (1/2) log(1/ψ)`
  have hlogK : 1 / 2 * Real.log (1 / ψ) ≤ Real.log ((K : ℝ) + 1) := by
    have hK1 : 1 / (p * ψ) ≤ (K : ℝ) + 1 := (Nat.lt_floor_add_one _).le
    have hpψ : (p : ℝ) ^ 2 ≤ 1 / ψ := by
      rw [le_div_iff₀ hψ0]
      rw [le_div_iff₀ (by positivity)] at hψp
      linarith
    have hlogp : 2 * Real.log p ≤ Real.log (1 / ψ) := by
      have e := Real.log_pow (p : ℝ) 2
      push_cast at e
      rw [← e]
      exact Real.log_le_log (by positivity) hpψ
    have hl1 : Real.log (1 / (p * ψ)) ≤ Real.log ((K : ℝ) + 1) :=
      Real.log_le_log (by positivity) hK1
    have hl2 : Real.log (1 / (p * ψ)) = Real.log (1 / ψ) - Real.log p := by
      rw [one_div, Real.log_inv, Real.log_mul (by positivity) hψ0.ne', one_div, Real.log_inv]
      ring
    linarith
  have hharm : 1 / 2 * Real.log (1 / ψ) ≤ (harmonic K : ℝ) := by
    have := log_add_one_le_harmonic K
    push_cast at this
    linarith
  have hcoef : 0 ≤ A ^ 2 / (128 * Real.pi ^ 2 * (p * ψ ^ 4)) := by positivity
  exact (mul_le_mul_of_nonneg_left hharm hcoef).trans hsum

/-- **Theorem (logarithmic defect energy).**  Let `Z = Σ a_n n^{-s}` continue to the critical line
in the Hamburger strip class with defect `g`, let `a_1 + ⋯ + a_n = A n + o(n)` with `A > 0`, and let
`a_{pk} = 0` for all `k ≥ 1`.  Then for all large `T`,
`∫ ‖g(t)‖² e^{-|t|/T} dt ≥ A²/(256πp) · T log T`. -/
theorem integral_norm_sq_mul_exp_ge_of_missing_multiples {a : ℕ → ℂ}
    (ha : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => ‖a (n + 1)‖ / ((n : ℝ) + 1) ^ σ)
    {β : ℂ} {g : ℝ → ℂ} (hH : HamburgerStripDefect (coeffDirichlet a) β g)
    {A : ℝ} (hA : 0 < A)
    (hN : ∀ η : ℝ, 0 < η → ∃ C : ℝ, ∀ n : ℕ, ‖coeffSum a n - A * n‖ ≤ η * n + C)
    {p : ℕ} (hp : 1 ≤ p) (hres : ∀ k : ℕ, 1 ≤ k → a (p * k) = 0) :
    ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
      A ^ 2 / (256 * Real.pi * p) * (T * Real.log T) ≤
        ∫ t : ℝ, ‖g t‖ ^ 2 * Real.exp (-(|t| / T)) := by
  have hpi := Real.pi_pos
  obtain ⟨-, -, -, -, -, -, -, hgm, Cg, Ng, hgb⟩ := id hH
  obtain ⟨C₀, hC₀⟩ := hN (A / (64 * Real.pi ^ 2)) (by positivity)
  have hC : 0 ≤ max C₀ 0 := le_max_right _ _
  have hNC : ∀ n : ℕ, ‖coeffSum a n - A * n‖ ≤ A / (64 * Real.pi ^ 2) * n + max C₀ 0 :=
    fun n => (hC₀ n).trans (by linarith [le_max_left C₀ 0])
  have hS0 : 0 ≤ ∑' n : ℕ, ‖a (n + 1)‖ / ((n + 1 : ℕ) : ℝ) ^ 2 :=
    tsum_nonneg fun n => by positivity
  -- the scale threshold
  obtain ⟨ψ₀, hψ₀0, hψ₀1, hψ₀b₁, hψ₀b₂, hψ₀b₃, hψ₀b₄, hψ₀p⟩ : ∃ ψ₀ : ℝ, 0 < ψ₀ ∧ ψ₀ ≤ 1 / 2 ∧
      ψ₀ ≤ 1 / (24 * Real.pi) ∧ ψ₀ ≤ 3 * A / (224 * Real.pi ^ 2 * (max C₀ 0 + 1)) ∧
      ψ₀ ≤ 3 * A / (512 * ((∑' n : ℕ, ‖a (n + 1)‖ / ((n + 1 : ℕ) : ℝ) ^ 2) + 1)) ∧
      ψ₀ ≤ A / (32 * Real.pi * (‖β‖ + 1) * (4 / (3 * Real.pi) + 1)) ∧
      ψ₀ ≤ 1 / (p : ℝ) ^ 2 := by
    refine ⟨min (min (1 / 2) (min (1 / (24 * Real.pi))
      (3 * A / (224 * Real.pi ^ 2 * (max C₀ 0 + 1))))) (min (min
      (3 * A / (512 * ((∑' n : ℕ, ‖a (n + 1)‖ / ((n + 1 : ℕ) : ℝ) ^ 2) + 1)))
      (A / (32 * Real.pi * (‖β‖ + 1) * (4 / (3 * Real.pi) + 1)))) (1 / (p : ℝ) ^ 2)),
      by positivity, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact (min_le_left _ _).trans (min_le_left _ _)
    · exact (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
    · exact (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
    · exact (min_le_right _ _).trans ((min_le_left _ _).trans (min_le_left _ _))
    · exact (min_le_right _ _).trans ((min_le_left _ _).trans (min_le_right _ _))
    · exact (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨1 / (4 * ψ₀ ^ 4), fun T hT => ?_⟩
  have hT0 : 0 < T := lt_of_lt_of_le (by positivity) hT
  have hT1 : 1 ≤ T := by
    refine le_trans ?_ hT
    rw [le_div_iff₀ (by positivity)]
    have h4 : ψ₀ ^ 4 ≤ (1 / 2) ^ 4 := pow_le_pow_left₀ hψ₀0.le hψ₀1 4
    nlinarith
  -- `θ = 1/(4T) = ψ⁴`
  set ψ : ℝ := (1 / (4 * T)) ^ (1 / 4 : ℝ) with hψ
  have hψ0 : 0 < ψ := Real.rpow_pos_of_pos (by positivity) _
  have hψ4 : ψ ^ 4 = 1 / (4 * T) := by
    rw [hψ, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; norm_num
  have hψle : ψ ≤ ψ₀ := by
    rw [← pow_le_pow_iff_left₀ hψ0.le hψ₀0.le (by norm_num : (4 : ℕ) ≠ 0), hψ4,
      div_le_iff₀ (by positivity)]
    rw [div_le_iff₀ (by positivity)] at hT
    nlinarith
  obtain ⟨hint, hray⟩ := ray_energy_le hgm.aestronglyMeasurable hgb
    (by positivity : (0 : ℝ) < ψ ^ 4) (by rw [hψ4]; rw [div_le_iff₀ (by positivity)]; linarith)
  have hlow := log_le_ray_energy ha hH hA hC hNC hp hres hψ0 (hψle.trans hψ₀1)
    (hψle.trans hψ₀b₁) (hψle.trans hψ₀b₂) (hψle.trans hψ₀b₃) (hψle.trans hψ₀b₄)
    (hψle.trans hψ₀p) hint
  have hθT : ∀ t : ℝ, Real.exp (-(4 * ψ ^ 4 * |t|)) = Real.exp (-(|t| / T)) := by
    intro t; rw [hψ4]; congr 1; field_simp
  simp only [hθT] at hray
  -- `log(1/ψ) = (1/4) log(4T)`
  have hlogψ : 4 * Real.log (1 / ψ) = Real.log (4 * T) := by
    have : Real.log (1 / ψ ^ 4) = 4 * Real.log (1 / ψ) := by
      rw [one_div, one_div, Real.log_inv, Real.log_inv, Real.log_pow]; push_cast; ring
    rw [← this, hψ4, one_div_one_div]
  have hlog4 : Real.log T ≤ Real.log (4 * T) := Real.log_le_log hT0 (by linarith)
  have hfinal := hlow.trans hray
  have e : A ^ 2 / (128 * Real.pi ^ 2 * (p * ψ ^ 4)) * (1 / 2 * Real.log (1 / ψ)) =
      1 / Real.pi * (A ^ 2 / (256 * Real.pi * p) * (T * Real.log (4 * T))) := by
    rw [hψ4, ← hlogψ]; field_simp; ring
  rw [e] at hfinal
  have hfinal' := (mul_le_mul_iff_of_pos_left (by positivity : (0 : ℝ) < 1 / Real.pi)).mp hfinal
  have hlogT0 : 0 ≤ Real.log T := Real.log_nonneg hT1
  calc A ^ 2 / (256 * Real.pi * p) * (T * Real.log T)
      ≤ A ^ 2 / (256 * Real.pi * p) * (T * Real.log (4 * T)) := by gcongr
    _ ≤ _ := hfinal'

/-! ## Pointwise consequence -/

/-- `∫ (log T + |t|/T) e^{-|t|/T} dt = 2T log T + 2T`. -/
theorem integral_log_add_mul_exp {T : ℝ} (hT : 0 < T) :
    ∫ t : ℝ, (Real.log T + |t| / T) * Real.exp (-(|t| / T)) = 2 * T * Real.log T + 2 * T := by
  rw [integral_comp_abs (f := fun x => (Real.log T + x / T) * Real.exp (-(x / T)))]
  have hb : (0 : ℝ) < 1 / T := by positivity
  have i0 : IntegrableOn (fun x : ℝ => x ^ (0 : ℝ) * Real.exp (-(1 / T) * x ^ (1 : ℝ))) (Ioi 0) :=
    integrableOn_rpow_mul_exp_neg_mul_rpow (by norm_num) le_rfl hb
  have i1 : IntegrableOn (fun x : ℝ => x ^ (1 : ℝ) * Real.exp (-(1 / T) * x ^ (1 : ℝ))) (Ioi 0) :=
    integrableOn_rpow_mul_exp_neg_mul_rpow (by norm_num) le_rfl hb
  have e0 : ∀ x : ℝ, x ^ (0 : ℝ) * Real.exp (-(1 / T) * x ^ (1 : ℝ)) = Real.exp (-(x / T)) := by
    intro x; rw [Real.rpow_zero, Real.rpow_one, one_mul]; congr 1; ring
  have e1 : ∀ x : ℝ, x ^ (1 : ℝ) * Real.exp (-(1 / T) * x ^ (1 : ℝ)) =
      x * Real.exp (-(x / T)) := by
    intro x; rw [Real.rpow_one]; congr 2; ring
  simp only [e0, e1] at i0 i1
  have g0 : ∫ x in Ioi (0 : ℝ), Real.exp (-(x / T)) = T := by
    have := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 1) (r := 1 / T) one_pos hb
    rw [Real.Gamma_one] at this
    simp only [sub_self, Real.rpow_zero, one_mul, Real.rpow_one, mul_one] at this
    rw [show (fun x : ℝ => Real.exp (-(x / T))) = fun x => Real.exp (-(1 / T * x)) by
      funext x; congr 1; ring, this]
    field_simp
  have g1 : ∫ x in Ioi (0 : ℝ), x * Real.exp (-(x / T)) = T ^ 2 := by
    have := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 2) (r := 1 / T) two_pos hb
    rw [Real.Gamma_two] at this
    norm_num at this
    rw [show (fun x : ℝ => x * Real.exp (-(x / T))) = fun x => x * Real.exp (-(T⁻¹ * x)) by
      funext x; congr 2; field_simp, this]
  have hsplit : (fun x : ℝ => (Real.log T + x / T) * Real.exp (-(x / T))) =
      fun x => Real.log T * Real.exp (-(x / T)) + T⁻¹ * (x * Real.exp (-(x / T))) := by
    funext x; field_simp
  rw [hsplit, integral_add (i0.const_mul _) (i1.const_mul _), integral_const_mul,
    integral_const_mul, g0, g1]
  field_simp

/-- **Corollary (the defect is not `O(√log|t|)` with a small constant).**  Under the hypotheses of
`integral_norm_sq_mul_exp_ge_of_missing_multiples`, no `c < A/(32√(πp))` has
`‖g(t)‖ ≤ c √(log|t|)` for all large `|t|`: `limsup ‖g(t)‖/√(log|t|) ≥ A/(32√(πp))`. -/
theorem not_le_sqrt_log_of_missing_multiples {a : ℕ → ℂ}
    (ha : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => ‖a (n + 1)‖ / ((n : ℝ) + 1) ^ σ)
    {β : ℂ} {g : ℝ → ℂ} (hH : HamburgerStripDefect (coeffDirichlet a) β g)
    {A : ℝ} (hA : 0 < A)
    (hN : ∀ η : ℝ, 0 < η → ∃ C : ℝ, ∀ n : ℕ, ‖coeffSum a n - A * n‖ ≤ η * n + C)
    {p : ℕ} (hp : 1 ≤ p) (hres : ∀ k : ℕ, 1 ≤ k → a (p * k) = 0)
    {c : ℝ} (hc : c < A / (32 * Real.sqrt (Real.pi * p))) (t₁ : ℝ) :
    ¬ ∀ t : ℝ, t₁ ≤ |t| → ‖g t‖ ≤ c * Real.sqrt (Real.log |t|) := by
  intro hg
  have hpi := Real.pi_pos
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
  obtain ⟨-, -, -, -, -, -, -, hgm, Cg, Ng, hgb⟩ := id hH
  have hCg : 0 ≤ Cg := by have := (norm_nonneg _).trans (hgb 0); simpa using this
  obtain ⟨T₀, hT₀⟩ := integral_norm_sq_mul_exp_ge_of_missing_multiples ha hH hA hN hp hres
  set t₂ : ℝ := max t₁ 2 with ht₂
  have ht₂2 : 2 ≤ t₂ := le_max_right _ _
  -- `c ≥ 0`
  have hc0 : 0 ≤ c := by
    have h := hg t₂ (by rw [abs_of_pos (by linarith)]; exact le_max_left _ _)
    have hl : 0 < Real.sqrt (Real.log |t₂|) :=
      Real.sqrt_pos.mpr (Real.log_pos (by rw [abs_of_pos (by linarith)]; linarith))
    by_contra hneg
    push Not at hneg
    have : c * Real.sqrt (Real.log |t₂|) < 0 := mul_neg_of_neg_of_pos hneg hl
    linarith [norm_nonneg (g t₂)]
  -- `2c² < A²/(512πp)`
  have hc2 : 2 * c ^ 2 < A ^ 2 / (512 * Real.pi * p) := by
    have hs : Real.sqrt (Real.pi * p) ^ 2 = Real.pi * p := Real.sq_sqrt (by positivity)
    have h1 : c * (32 * Real.sqrt (Real.pi * p)) < A := by
      rwa [lt_div_iff₀ (by positivity)] at hc
    have h2 : (c * (32 * Real.sqrt (Real.pi * p))) ^ 2 < A ^ 2 :=
      pow_lt_pow_left₀ h1 (by positivity) two_ne_zero
    rw [lt_div_iff₀ (by positivity)]
    have e : (c * (32 * Real.sqrt (Real.pi * p))) ^ 2 = 1024 * (Real.pi * p) * c ^ 2 := by
      rw [mul_pow, mul_pow, hs]; ring
    nlinarith
  set K₁ : ℝ := (Cg * (1 + t₂) ^ Ng) ^ 2 with hK₁
  have hK₁0 : 0 ≤ K₁ := sq_nonneg _
  -- the pointwise majorant
  have hmaj : ∀ T : ℝ, 1 ≤ T → ∀ t : ℝ, ‖g t‖ ^ 2 * Real.exp (-(|t| / T)) ≤
      (Icc (-t₂) t₂).indicator (fun _ => K₁) t +
        c ^ 2 * ((Real.log T + |t| / T) * Real.exp (-(|t| / T))) := by
    intro T hT t
    have hT0 : 0 < T := by linarith
    have hlogT : 0 ≤ Real.log T := Real.log_nonneg hT
    have he1 : Real.exp (-(|t| / T)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (neg_nonpos.mpr (by positivity))
    have hsec : 0 ≤ c ^ 2 * ((Real.log T + |t| / T) * Real.exp (-(|t| / T))) := by positivity
    by_cases ht : |t| ≤ t₂
    · rw [indicator_of_mem (show t ∈ Icc (-t₂) t₂ from abs_le.mp ht)]
      have hb : ‖g t‖ ≤ Cg * (1 + t₂) ^ Ng :=
        (hgb t).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity)
          (by linarith) Ng) hCg)
      have : ‖g t‖ ^ 2 * Real.exp (-(|t| / T)) ≤ K₁ :=
        (mul_le_of_le_one_right (by positivity) he1).trans
          (pow_le_pow_left₀ (norm_nonneg _) hb 2)
      linarith
    · push Not at ht
      rw [indicator_of_notMem (fun h => by have := abs_le.mpr h; linarith), zero_add]
      have htpos : 0 < |t| := by linarith
      have hlog0 : 0 ≤ Real.log |t| := Real.log_nonneg (by linarith)
      have hgt : ‖g t‖ ^ 2 ≤ c ^ 2 * Real.log |t| := by
        have h := hg t (le_trans (le_max_left _ _) ht.le)
        calc ‖g t‖ ^ 2 ≤ (c * Real.sqrt (Real.log |t|)) ^ 2 :=
              pow_le_pow_left₀ (norm_nonneg _) h 2
          _ = c ^ 2 * Real.log |t| := by rw [mul_pow, Real.sq_sqrt hlog0]
      have hlt : Real.log |t| ≤ Real.log T + |t| / T := by
        have h := Real.log_le_sub_one_of_pos (div_pos htpos hT0)
        rw [Real.log_div htpos.ne' hT0.ne'] at h
        linarith [div_nonneg htpos.le hT0.le]
      calc ‖g t‖ ^ 2 * Real.exp (-(|t| / T)) ≤ c ^ 2 * Real.log |t| * Real.exp (-(|t| / T)) :=
            mul_le_mul_of_nonneg_right hgt (by positivity)
        _ ≤ c ^ 2 * (Real.log T + |t| / T) * Real.exp (-(|t| / T)) := by gcongr
        _ = c ^ 2 * ((Real.log T + |t| / T) * Real.exp (-(|t| / T))) := by ring
  -- integrate the majorant
  have hupper : ∀ T : ℝ, 1 ≤ T → ∫ t : ℝ, ‖g t‖ ^ 2 * Real.exp (-(|t| / T)) ≤
      2 * t₂ * K₁ + c ^ 2 * (2 * T * Real.log T + 2 * T) := by
    intro T hT
    have hT0 : 0 < T := by linarith
    have hδ : 0 < 1 / T := by positivity
    have hexpT : ∀ t : ℝ, Real.exp (-(|t| / T)) = Real.exp (-((1 / T) * |t|)) := by
      intro t; congr 1; ring
    have iind : Integrable ((Icc (-t₂) t₂).indicator (fun _ => K₁)) :=
      (integrableOn_const (by simp)).integrable_indicator measurableSet_Icc
    have ilog : Integrable fun t : ℝ => (Real.log T + |t| / T) * Real.exp (-(|t| / T)) := by
      refine ((integrable_one_add_abs_pow_mul_exp hδ 1).const_mul (Real.log T + 1 / T)).mono'
        (by fun_prop) (Eventually.of_forall fun t => ?_)
      have hlogT : 0 ≤ Real.log T := Real.log_nonneg hT
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), hexpT, pow_one]
      have : Real.log T + |t| / T ≤ (Real.log T + 1 / T) * (1 + |t|) := by
        have h1 : |t| / T = 1 / T * |t| := by ring
        nlinarith [abs_nonneg t, hδ]
      calc (Real.log T + |t| / T) * Real.exp (-((1 / T) * |t|))
          ≤ (Real.log T + 1 / T) * (1 + |t|) * Real.exp (-((1 / T) * |t|)) := by gcongr
        _ = _ := by ring
    have ig : Integrable fun t : ℝ => ‖g t‖ ^ 2 * Real.exp (-(|t| / T)) := by
      refine ((integrable_one_add_abs_pow_mul_exp hδ (2 * Ng)).const_mul (Cg ^ 2)).mono'
        ((hgm.aestronglyMeasurable.norm.pow 2).mul (by fun_prop :
          Continuous fun t : ℝ => Real.exp (-(|t| / T))).aestronglyMeasurable)
        (Eventually.of_forall fun t => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), hexpT]
      have hgsq : ‖g t‖ ^ 2 ≤ Cg ^ 2 * (1 + |t|) ^ (2 * Ng) := by
        rw [pow_mul', ← mul_pow]
        exact pow_le_pow_left₀ (norm_nonneg _) (hgb t) 2
      calc ‖g t‖ ^ 2 * Real.exp (-((1 / T) * |t|))
          ≤ Cg ^ 2 * (1 + |t|) ^ (2 * Ng) * Real.exp (-((1 / T) * |t|)) := by gcongr
        _ = _ := by ring
    have hle : ∫ t : ℝ, ‖g t‖ ^ 2 * Real.exp (-(|t| / T)) ≤
        ∫ t : ℝ, ((Icc (-t₂) t₂).indicator (fun _ => K₁) t +
          c ^ 2 * ((Real.log T + |t| / T) * Real.exp (-(|t| / T)))) :=
      integral_mono ig (iind.add (ilog.const_mul (c ^ 2))) (hmaj T hT)
    rw [integral_add iind (ilog.const_mul _), integral_const_mul, integral_log_add_mul_exp hT0,
      integral_indicator measurableSet_Icc, setIntegral_const, smul_eq_mul,
      measureReal_def, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)] at hle
    linarith
  -- a large `T` contradicts the logarithmic lower bound
  set δ₀ : ℝ := A ^ 2 / (256 * Real.pi * p) - 2 * c ^ 2 with hδ₀
  have hδ₀0 : 0 < δ₀ := by
    have : A ^ 2 / (512 * Real.pi * p) ≤ A ^ 2 / (256 * Real.pi * p) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) (by nlinarith)
    linarith
  set T : ℝ := max (max T₀ 1) (Real.exp ((2 * t₂ * K₁ + 2 * c ^ 2 + 1) / δ₀)) with hTdef
  have hT1 : 1 ≤ T := (le_max_right _ _).trans (le_max_left _ _)
  have hT0 : 0 < T := by linarith
  have hlow := hT₀ T ((le_max_left _ _).trans (le_max_left _ _))
  have hup := hupper T hT1
  have hlogT : (2 * t₂ * K₁ + 2 * c ^ 2 + 1) / δ₀ ≤ Real.log T := by
    rw [Real.le_log_iff_exp_le hT0]; exact le_max_right _ _
  have hlogT' : 2 * t₂ * K₁ + 2 * c ^ 2 + 1 ≤ δ₀ * Real.log T := by
    rw [div_le_iff₀ hδ₀0] at hlogT
    linarith
  have hK : 0 ≤ 2 * t₂ * K₁ := by positivity
  have key : δ₀ * (T * Real.log T) ≤ 2 * t₂ * K₁ + 2 * c ^ 2 * T := by
    have e : δ₀ * (T * Real.log T) = A ^ 2 / (256 * Real.pi * p) * (T * Real.log T) -
        c ^ 2 * (2 * T * Real.log T) := by rw [hδ₀]; ring
    rw [e]
    nlinarith
  have : (2 * t₂ * K₁ + 2 * c ^ 2 + 1) * T ≤ δ₀ * (T * Real.log T) := by
    calc (2 * t₂ * K₁ + 2 * c ^ 2 + 1) * T ≤ δ₀ * Real.log T * T :=
          mul_le_mul_of_nonneg_right hlogT' hT0.le
      _ = δ₀ * (T * Real.log T) := by ring
  nlinarith

/-- **Corollary (the defect is unbounded).** -/
theorem not_bounded_of_missing_multiples {a : ℕ → ℂ}
    (ha : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => ‖a (n + 1)‖ / ((n : ℝ) + 1) ^ σ)
    {β : ℂ} {g : ℝ → ℂ} (hH : HamburgerStripDefect (coeffDirichlet a) β g)
    {A : ℝ} (hA : 0 < A)
    (hN : ∀ η : ℝ, 0 < η → ∃ C : ℝ, ∀ n : ℕ, ‖coeffSum a n - A * n‖ ≤ η * n + C)
    {p : ℕ} (hp : 1 ≤ p) (hres : ∀ k : ℕ, 1 ≤ k → a (p * k) = 0) (M : ℝ) :
    ¬ ∀ t : ℝ, ‖g t‖ ≤ M := by
  intro hM
  have hpi := Real.pi_pos
  set c : ℝ := A / (64 * Real.sqrt (Real.pi * p)) with hc
  have hsq : 0 < Real.sqrt (Real.pi * p) := Real.sqrt_pos.mpr (by
    have : (1 : ℝ) ≤ p := by exact_mod_cast hp
    positivity)
  have hc0 : 0 < c := by positivity
  have hclt : c < A / (32 * Real.sqrt (Real.pi * p)) := by
    rw [hc]; gcongr; norm_num
  refine not_le_sqrt_log_of_missing_multiples ha hH hA hN hp hres hclt
    (Real.exp ((|M| / c) ^ 2)) fun t ht => ?_
  have htpos : 0 < |t| := lt_of_lt_of_le (Real.exp_pos _) ht
  have hlog : (|M| / c) ^ 2 ≤ Real.log |t| := (Real.le_log_iff_exp_le htpos).mpr ht
  have hs : |M| / c ≤ Real.sqrt (Real.log |t|) :=
    Real.le_sqrt_of_sq_le hlog
  calc ‖g t‖ ≤ M := hM t
    _ ≤ |M| := le_abs_self M
    _ = c * (|M| / c) := by field_simp
    _ ≤ c * Real.sqrt (Real.log |t|) := by gcongr

/-! ## The pole parameter is half the density -/

/-- On the positive axis `‖L_a(ε)‖ ≤ (ε/π) Σ ‖a_n‖/n²`. -/
theorem norm_hamburgerSeries_ofReal_le {a : ℕ → ℂ}
    (ha : Summable fun n : ℕ => ‖a (n + 1)‖ / ((n + 1 : ℕ) : ℝ) ^ 2) {ε : ℝ} (hε : 0 < ε) :
    ‖hamburgerSeries a ε‖ ≤
      ε / Real.pi * ∑' n : ℕ, ‖a (n + 1)‖ / ((n + 1 : ℕ) : ℝ) ^ 2 := by
  have hpi := Real.pi_pos
  have hpt : ∀ n : ℕ, ‖a (n + 1) * (ε : ℂ) / ((Real.pi : ℂ) * (((n + 1 : ℕ) : ℂ) ^ 2 +
      (ε : ℂ) ^ 2))‖ ≤ ε / Real.pi * (‖a (n + 1)‖ / ((n + 1 : ℕ) : ℝ) ^ 2) := by
    intro n
    have e : (Real.pi : ℂ) * (((n + 1 : ℕ) : ℂ) ^ 2 + (ε : ℂ) ^ 2) =
        ((Real.pi * (((n + 1 : ℕ) : ℝ) ^ 2 + ε ^ 2) : ℝ) : ℂ) := by push_cast; ring
    have hk : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
    rw [e, norm_div, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg hε.le,
      Real.norm_of_nonneg (by positivity)]
    rw [div_le_iff₀ (by positivity)]
    have : ‖a (n + 1)‖ * ε ≤ ε / Real.pi * (‖a (n + 1)‖ / ((n + 1 : ℕ) : ℝ) ^ 2) *
        (Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2) := by
      field_simp; rfl
    have h2 : ε / Real.pi * (‖a (n + 1)‖ / ((n + 1 : ℕ) : ℝ) ^ 2) *
        (Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2) ≤ ε / Real.pi * (‖a (n + 1)‖ / ((n + 1 : ℕ) : ℝ) ^ 2) *
        (Real.pi * (((n + 1 : ℕ) : ℝ) ^ 2 + ε ^ 2)) := by gcongr; linarith [sq_nonneg ε]
    linarith
  have hmaj : Summable fun n : ℕ => ε / Real.pi * (‖a (n + 1)‖ / ((n + 1 : ℕ) : ℝ) ^ 2) :=
    ha.mul_left _
  have hnorms := hmaj.of_nonneg_of_le (fun n => norm_nonneg _) hpt
  unfold hamburgerSeries
  calc _ ≤ _ := norm_tsum_le_tsum_norm hnorms
    _ ≤ _ := Summable.tsum_le_tsum hpt hnorms hmaj
    _ = _ := tsum_mul_left

/-- `ε e^{-2πε}/(1 - e^{-2πε})` is within `ε` of `1/(2π)`. -/
theorem abs_mul_exp_div_sub_le {ε : ℝ} (hε : 0 < ε) :
    |ε * Real.exp (-(2 * Real.pi * ε)) / (1 - Real.exp (-(2 * Real.pi * ε))) -
      1 / (2 * Real.pi)| ≤ ε := by
  have hpi := Real.pi_pos
  set u : ℝ := 2 * Real.pi * ε with hu
  have hu0 : 0 < u := by positivity
  have he := Real.add_one_le_exp u
  have hm := Real.add_one_le_exp (-u)
  have hprod : Real.exp (-u) * Real.exp u = 1 := by rw [← Real.exp_add]; simp
  have hp := Real.exp_pos (-u)
  have h1 : u * Real.exp (-u) ≤ 1 - Real.exp (-u) := by nlinarith
  have h2 : 1 - Real.exp (-u) ≤ u := by linarith
  have hd : 0 < 1 - Real.exp (-u) := lt_of_lt_of_le (by positivity) h1
  have hε' : ε = u / (2 * Real.pi) := by rw [hu]; field_simp
  rw [hε']
  have e : u / (2 * Real.pi) * Real.exp (-u) / (1 - Real.exp (-u)) - 1 / (2 * Real.pi) =
      (u * Real.exp (-u) - (1 - Real.exp (-u))) / (2 * Real.pi * (1 - Real.exp (-u))) := by
    field_simp
  rw [e, abs_div, abs_of_pos (by positivity : 0 < 2 * Real.pi * (1 - Real.exp (-u))),
    abs_of_nonpos (by linarith), div_le_div_iff₀ (by positivity) (by positivity)]
  -- `(1 - e^{-u} - u e^{-u}) · 2π ≤ u · 2π (1 - e^{-u})`
  have h3 : 1 - Real.exp (-u) - u * Real.exp (-u) ≤ u * (1 - Real.exp (-u)) := by nlinarith
  nlinarith

/-- **The pole parameter is half the density.**  If `N_a(n) = A n + o(n)`, then `β = A/2`.
On the positive axis `ε L_a(ε) → 0` and `ε J_g(ε) → 0`, while Abel summation gives
`ε F_a(ε) → A/(2π)`; the Hamburger identity then reads `0 = A/(2π) - β/π`. -/
theorem pole_eq_half_density {a : ℕ → ℂ}
    (ha : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => ‖a (n + 1)‖ / ((n : ℝ) + 1) ^ σ)
    {β : ℂ} {g : ℝ → ℂ} (hH : HamburgerStripDefect (coeffDirichlet a) β g) {A : ℝ}
    (hN : ∀ η : ℝ, 0 < η → ∃ C : ℝ, ∀ n : ℕ, ‖coeffSum a n - A * n‖ ≤ η * n + C) :
    β = A / 2 := by
  have hpi := Real.pi_pos
  obtain ⟨-, -, -, -, -, -, -, hgm, Cg, Ng, hgb⟩ := id hH
  have hgm' := hgm.aestronglyMeasurable (μ := volume)
  have ha2 : Summable fun n : ℕ => ‖a (n + 1)‖ / ((n + 1 : ℕ) : ℝ) ^ 2 := by
    simpa using summable_sq_of_forall_rpow ha
  set S : ℝ := ∑' n : ℕ, ‖a (n + 1)‖ / ((n + 1 : ℕ) : ℝ) ^ 2 with hS
  set M₂ : ℝ := abelMass g 2 with hM₂
  set D : ℝ := ‖β / Real.pi - (A : ℂ) / (2 * Real.pi)‖ with hD
  -- for every `η > 0`, `D ≤ 2η/π`
  have hηb : ∀ η : ℝ, 0 < η → D ≤ 2 * η / Real.pi := by
    intro η hη
    obtain ⟨C₀, hC₀⟩ := hN η hη
    have hC : 0 ≤ max C₀ 0 := le_max_right _ _
    have hNC : ∀ n : ℕ, ‖coeffSum a n - A * n‖ ≤ η * n + max C₀ 0 :=
      fun n => (hC₀ n).trans (by linarith [le_max_left C₀ 0])
    have hK : ∀ n, ‖coeffSum a n‖ ≤ (η + |A| + max C₀ 0) * ((n : ℝ) + 1) := by
      intro n
      have h1 := hNC n
      have h2 : ‖coeffSum a n‖ ≤ ‖coeffSum a n - A * n‖ + ‖(A : ℂ) * n‖ := by
        have := norm_add_le (coeffSum a n - A * n) ((A : ℂ) * n)
        simpa using this
      have h3 : ‖(A : ℂ) * n‖ = |A| * n := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_natCast]
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      nlinarith [abs_nonneg A]
    -- the bound at a small positive `ε`
    have hbound : ∀ ε : ℝ, 0 < ε → ε ≤ 1 / (4 * Real.pi) →
        D ≤ 2 * η / Real.pi + ((|A| + ‖β‖ + 2 * max C₀ 0) * ε +
          3 / (2 * Real.pi) * M₂ * ε ^ (1 / 2 : ℝ) + S / Real.pi * ε ^ 2) := by
      intro ε hε hε4
      have hu : 2 * Real.pi * ε ≤ 1 / 2 := by
        rw [le_div_iff₀ (by positivity)] at hε4; linarith
      set w : ℂ := cexp (-(2 * Real.pi * (ε : ℂ))) with hw
      have hwr : w = ((Real.exp (-(2 * Real.pi * ε)) : ℝ) : ℂ) := by
        rw [hw, Complex.ofReal_exp]; push_cast; ring_nf
      have hwn : ‖w‖ = Real.exp (-(2 * Real.pi * ε)) := by
        rw [hwr, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
      have hq1 : ‖w‖ < 1 := by
        rw [hwn]
        have h : Real.exp (-(2 * Real.pi * ε)) < Real.exp 0 :=
          Real.exp_lt_exp.mpr (by nlinarith)
        rwa [Real.exp_zero] at h
      have h1q : Real.pi * ε ≤ 1 - ‖w‖ := by
        rw [hwn]
        have := half_le_one_sub_exp_neg (u := 2 * Real.pi * ε) (by positivity) hu
        linarith
      have h1w : ‖1 - w‖ ≤ 2 * Real.pi * ε := by
        have h := norm_one_sub_cexp_neg_le (u := 2 * Real.pi * (ε : ℂ)) (by simp; positivity)
        calc ‖1 - w‖ ≤ ‖2 * (Real.pi : ℂ) * (ε : ℂ)‖ := h
          _ = 2 * Real.pi * ε := by
              rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
                Real.norm_of_nonneg hpi.le, Real.norm_of_nonneg hε.le]; norm_num
      have hRem := norm_tsum_remainder_le (a := a) (A := A) hη.le hC hNC hq1
      set Rs := ∑' n : ℕ, (coeffSum a (n + 1) - (A : ℂ) * ((n : ℂ) + 1)) * w ^ (n + 1) with hRs
      have hF : expSeries a ε = (A : ℂ) * w / (1 - w) + (1 - w) * Rs := by
        rw [expSeries_eq_tsum_pow, ← hw, tsum_coeff_mul_pow_eq (A : ℂ) hK hq1]
      -- the Abel remainder
      have hRs : ‖(ε : ℂ) * ((1 - w) * Rs)‖ ≤ 2 * η / Real.pi + 2 * max C₀ 0 * ε := by
        have hb : ‖Rs‖ ≤ η / (Real.pi * ε) ^ 2 + max C₀ 0 / (Real.pi * ε) :=
          hRem.trans (add_le_add (by gcongr) (by gcongr))
        rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hε.le]
        calc ε * (‖1 - w‖ * ‖Rs‖)
            ≤ ε * (2 * Real.pi * ε * (η / (Real.pi * ε) ^ 2 + max C₀ 0 / (Real.pi * ε))) := by
              gcongr
          _ = 2 * η / Real.pi + 2 * max C₀ 0 * ε := by field_simp
      -- the main term
      have hmain : ‖(ε : ℂ) * ((A : ℂ) * w / (1 - w)) - (A : ℂ) / (2 * Real.pi)‖ ≤ |A| * ε := by
        have e : (ε : ℂ) * ((A : ℂ) * w / (1 - w)) - (A : ℂ) / (2 * Real.pi) =
            ((A * (ε * Real.exp (-(2 * Real.pi * ε)) / (1 - Real.exp (-(2 * Real.pi * ε))) -
              1 / (2 * Real.pi)) : ℝ) : ℂ) := by
          rw [hwr]; push_cast; ring
        rw [e, Complex.norm_real, Real.norm_eq_abs, abs_mul]
        exact mul_le_mul_of_nonneg_left (abs_mul_exp_div_sub_le hε) (abs_nonneg A)
      -- the defect term
      have hJ : ‖(ε : ℂ) * defectLaplace g ε‖ ≤ 3 / (2 * Real.pi) * M₂ * ε ^ (1 / 2 : ℝ) := by
        have hre : 0 < ((ε : ℂ)).re := by simpa using hε
        have hb := norm_defectLaplace_le hgm' hgb hre
        have hn : ‖(ε : ℂ)‖ = ε := by rw [Complex.norm_real, Real.norm_of_nonneg hε.le]
        rw [hn, Complex.ofReal_re, div_self hε.ne', mul_one] at hb
        rw [norm_mul, hn]
        have e : ε * ε ^ (-(1 / 2 : ℝ)) = ε ^ (1 / 2 : ℝ) := by
          rw [← Real.rpow_one_add' hε.le (by norm_num)]; norm_num
        calc ε * ‖defectLaplace g ε‖ ≤ ε * (3 / (2 * Real.pi) * ε ^ (-(1 / 2 : ℝ)) * M₂) := by
              gcongr
          _ = 3 / (2 * Real.pi) * M₂ * (ε * ε ^ (-(1 / 2 : ℝ))) := by ring
          _ = _ := by rw [e]
      -- the Hamburger series term
      have hL : ‖(ε : ℂ) * hamburgerSeries a ε‖ ≤ S / Real.pi * ε ^ 2 := by
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hε.le]
        calc ε * ‖hamburgerSeries a ε‖ ≤ ε * (ε / Real.pi * S) := by
              gcongr; exact norm_hamburgerSeries_ofReal_le ha2 hε
          _ = S / Real.pi * ε ^ 2 := by ring
      have hβε : ‖(ε : ℂ) * β‖ = ‖β‖ * ε := by
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hε.le, mul_comm]
      -- the Hamburger identity on the axis
      have hid := hamburgerSeries_eq_defect ha hH (τ := (ε : ℂ)) (by simpa using hε)
      have hεne : (ε : ℂ) ≠ 0 := by exact_mod_cast hε.ne'
      have hπne : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast hpi.ne'
      have hkey : β / Real.pi - (A : ℂ) / (2 * Real.pi) =
          ((ε : ℂ) * ((A : ℂ) * w / (1 - w)) - (A : ℂ) / (2 * Real.pi)) +
            (ε : ℂ) * ((1 - w) * Rs) + (ε : ℂ) * β + (ε : ℂ) * defectLaplace g ε -
              (ε : ℂ) * hamburgerSeries a ε := by
        have hcancel : (ε : ℂ) * (β / ((Real.pi : ℂ) * ε)) = β / Real.pi := by field_simp
        rw [hid, hF]
        linear_combination (-1 : ℂ) * hcancel
      rw [hD, hkey]
      have t1 := norm_sub_le (((ε : ℂ) * ((A : ℂ) * w / (1 - w)) - (A : ℂ) / (2 * Real.pi)) +
        (ε : ℂ) * ((1 - w) * Rs) + (ε : ℂ) * β + (ε : ℂ) * defectLaplace g ε)
        ((ε : ℂ) * hamburgerSeries a ε)
      have t2 := norm_add_le (((ε : ℂ) * ((A : ℂ) * w / (1 - w)) - (A : ℂ) / (2 * Real.pi)) +
        (ε : ℂ) * ((1 - w) * Rs) + (ε : ℂ) * β) ((ε : ℂ) * defectLaplace g ε)
      have t3 := norm_add_le (((ε : ℂ) * ((A : ℂ) * w / (1 - w)) - (A : ℂ) / (2 * Real.pi)) +
        (ε : ℂ) * ((1 - w) * Rs)) ((ε : ℂ) * β)
      have t4 := norm_add_le ((ε : ℂ) * ((A : ℂ) * w / (1 - w)) - (A : ℂ) / (2 * Real.pi))
        ((ε : ℂ) * ((1 - w) * Rs))
      rw [hβε] at t3
      linarith only [t1, t2, t3, t4, hmain, hRs, hJ, hL]
    -- let `ε → 0⁺`
    have hlim : Tendsto (fun ε : ℝ => 2 * η / Real.pi + ((|A| + ‖β‖ + 2 * max C₀ 0) * ε +
        3 / (2 * Real.pi) * M₂ * ε ^ (1 / 2 : ℝ) + S / Real.pi * ε ^ 2)) (𝓝[>] 0)
        (𝓝 (2 * η / Real.pi)) := by
      have hc : ContinuousAt (fun ε : ℝ => 2 * η / Real.pi + ((|A| + ‖β‖ + 2 * max C₀ 0) * ε +
          3 / (2 * Real.pi) * M₂ * ε ^ (1 / 2 : ℝ) + S / Real.pi * ε ^ 2)) 0 := by
        have := Real.continuousAt_rpow_const 0 (1 / 2 : ℝ) (Or.inr (by norm_num))
        fun_prop
      have := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi 0))
      simpa [Real.zero_rpow (by norm_num : (1 / 2 : ℝ) ≠ 0)] using this
    refine ge_of_tendsto hlim ?_
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Iio_mem_nhds (by positivity : (0 : ℝ) < 1 / (4 * Real.pi)))]
      with ε hε hε4
    exact hbound ε hε (le_of_lt hε4)
  -- hence `D = 0`
  have hD0 : D = 0 := by
    by_contra hne
    have hpos : 0 < D := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)
    have h := hηb (Real.pi * D / 4) (by positivity)
    have e : 2 * (Real.pi * D / 4) / Real.pi = D / 2 := by field_simp; ring
    rw [e] at h
    linarith
  have hz : β / Real.pi - (A : ℂ) / (2 * Real.pi) = 0 := norm_eq_zero.mp hD0
  have hπne : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast hpi.ne'
  field_simp at hz
  linear_combination hz / 2

end GaloisForLFunctions.EulerFETransportTheory
