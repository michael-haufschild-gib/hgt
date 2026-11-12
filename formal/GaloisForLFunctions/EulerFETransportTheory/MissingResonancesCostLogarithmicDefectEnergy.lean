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
    have hkey : 2 * m * k ^ 2 ≤ 16 / 3 * m ^ 2 * (3 / 4 * (k * d)) := by nlinarith
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
          gcongr
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
  have hpi3 := Real.pi_gt_three
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  set ι : ℝ := A / (32 * Real.pi * μ) with hι
  have hι0 : 0 < ι := by positivity
  have hμs : μ ≤ 1 / (24 * Real.pi) := by
    rw [le_div_iff₀ (by positivity)]; nlinarith
  have hμs' : μ ≤ 1 / 64 := hμs.trans (by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith)
  set x := τ.re with hxdef
  set y := τ.im with hydef
  have hx0 : 0 < x := lt_of_lt_of_le (by positivity) hx1
  have hym := abs_le.mp hy
  have hy0 : 0 ≤ y := by linarith
  -- the shifted point `τ - i m`
  set u : ℂ := τ - (m : ℂ) * I with hu
  have hure : u.re = x := by simp [hu, hxdef]
  have huim : u.im = y - m := by simp [hu, hydef]
  have hun : ‖u‖ ≤ 7 / 4 * μ := by
    have := Complex.norm_le_abs_re_add_abs_im u
    rw [hure, huim, abs_of_pos hx0] at this
    linarith
  have hper : expSeries a τ = expSeries a u := by
    rw [show τ = u + (m : ℂ) * I by rw [hu]; ring, expSeries_add_nat_mul_I]
  -- Abel summation at `w = e^{-2πu}`
  set w : ℂ := cexp (-(2 * Real.pi * u)) with hw
  have hwn : ‖w‖ = Real.exp (-(2 * Real.pi * x)) := by
    rw [hw, Complex.norm_exp]
    congr 1
    simp [hure]
  have hq1 : ‖w‖ < 1 := by
    rw [hwn, Real.exp_lt_one]; nlinarith
  have hq78 : 7 / 8 ≤ ‖w‖ := by
    rw [hwn]
    have := Real.add_one_le_exp (-(2 * Real.pi * x))
    nlinarith
  have h1q : 3 / 2 * μ ≤ 1 - ‖w‖ := by
    rw [hwn]
    have h := half_le_one_sub_exp_neg (u := 2 * Real.pi * x) (by positivity) (by nlinarith)
    have : 3 / 2 * μ ≤ Real.pi * x := by
      have := mul_le_mul_of_nonneg_left hx1 hpi.le
      calc 3 / 2 * μ = Real.pi * (3 / (2 * Real.pi) * μ) := by field_simp
        _ ≤ Real.pi * x := this
    linarith
  have h1w : ‖1 - w‖ ≤ 7 / 2 * Real.pi * μ := by
    have h := norm_one_sub_cexp_neg_le (u := 2 * Real.pi * u)
      (by simp [hure]; positivity)
    calc ‖1 - w‖ ≤ ‖2 * (Real.pi : ℂ) * u‖ := h
      _ = 2 * Real.pi * ‖u‖ := by
          rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hpi.le]; norm_num
      _ ≤ 2 * Real.pi * (7 / 4 * μ) := by gcongr
      _ = 7 / 2 * Real.pi * μ := by ring
  have h1w0 : 0 < ‖1 - w‖ := by
    refine norm_pos_iff.mpr fun h => ?_
    have : w = 1 := by linear_combination -h
    rw [this, norm_one] at hq1
    exact lt_irrefl _ hq1
  -- linear growth of the partial sums
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
  have hAbel := tsum_coeff_mul_pow_eq (a := a) (A : ℂ) hK hq1
  have hRem := norm_tsum_remainder_le (a := a) (A := A) (by positivity) hC hN hq1
  set Rs := ∑' n : ℕ, (coeffSum a (n + 1) - (A : ℂ) * ((n : ℂ) + 1)) * w ^ (n + 1) with hRs
  have hF : expSeries a u = (A : ℂ) * w / (1 - w) + (1 - w) * Rs := by
    rw [expSeries_eq_tsum_pow, ← hw, hAbel]
  -- the main term is at least `8ι`
  have hmain : 8 * ι ≤ ‖(A : ℂ) * w / (1 - w)‖ := by
    rw [norm_div, norm_mul, Complex.norm_real, Real.norm_of_nonneg hA.le]
    calc 8 * ι = A * (7 / 8) / (7 / 2 * Real.pi * μ) := by rw [hι]; field_simp; ring
      _ ≤ A * ‖w‖ / ‖1 - w‖ := by
          gcongr
  -- the Abel remainder is at most `2ι`
  have hrem : ‖(1 - w) * Rs‖ ≤ 2 * ι := by
    rw [norm_mul]
    have hq0 : 0 < 1 - ‖w‖ := by linarith
    have hb : ‖Rs‖ ≤ A / (64 * Real.pi ^ 2) / (3 / 2 * μ) ^ 2 + C / (3 / 2 * μ) := by
      refine hRem.trans (add_le_add ?_ ?_)
      · gcongr
      · gcongr
    calc ‖1 - w‖ * ‖Rs‖
        ≤ 7 / 2 * Real.pi * μ * (A / (64 * Real.pi ^ 2) / (3 / 2 * μ) ^ 2 + C / (3 / 2 * μ)) :=
          mul_le_mul h1w hb (norm_nonneg _) (by positivity)
      _ = 14 / 576 * (A / (Real.pi * μ)) + 7 * Real.pi / 3 * C := by
          field_simp; ring
      _ ≤ ι + ι := by
          gcongr
          rw [hι, show A / (32 * Real.pi * μ) = 1 / 32 * (A / (Real.pi * μ)) by field_simp]
          gcongr
          norm_num
      _ = 2 * ι := by ring
  -- the Hamburger series has no pole at `i m`
  have hτn : ‖τ‖ ≤ 2 * m := by
    have := Complex.norm_le_abs_re_add_abs_im τ
    rw [← hxdef, ← hydef, abs_of_pos hx0, abs_of_nonneg hy0] at this
    nlinarith
  have hL := norm_hamburgerSeries_le_of_coeff_eq_zero (by simpa using summable_sq_of_forall_rpow ha)
    hm ham hy0 (by linarith [hym.1, hym.2] |> fun _ => abs_le.mpr ⟨by linarith, by linarith⟩) hτn
  -- the polar terms
  have hτ34 : 3 / 4 ≤ ‖τ‖ := by
    have := Complex.abs_im_le_norm τ
    rw [← hydef, abs_of_nonneg hy0] at this
    linarith
  have hpol : ‖β / (Real.pi * τ)‖ + ‖β‖ ≤ ι := by
    rw [norm_div, norm_mul, Complex.norm_real, Real.norm_of_nonneg hpi.le]
    have h1 : ‖β‖ / (Real.pi * ‖τ‖) ≤ ‖β‖ * (4 / (3 * Real.pi)) := by
      rw [div_le_iff₀ (by positivity)]
      have : ‖β‖ * (4 / (3 * Real.pi)) * (Real.pi * ‖τ‖) = ‖β‖ * (4 / 3 * ‖τ‖) := by
        field_simp
      rw [this]
      nlinarith [norm_nonneg β]
    linarith
  -- assemble `J = L - F + β/(πτ) - β`
  have hJ : defectLaplace g τ =
      hamburgerSeries a τ - expSeries a τ + β / (Real.pi * τ) - β := by
    rw [hamburgerSeries_eq_defect ha hH (by rw [← hxdef]; exact hx0)]
    ring
  have hFn : 6 * ι ≤ ‖expSeries a τ‖ := by
    rw [hper, hF]
    have := norm_sub_norm_le ((A : ℂ) * w / (1 - w)) (-((1 - w) * Rs))
    rw [sub_neg_eq_add, norm_neg] at this
    linarith
  have hfin : 6 * ι ≤ ‖defectLaplace g τ‖ + ‖hamburgerSeries a τ‖ +
      (‖β / (Real.pi * τ)‖ + ‖β‖) := by
    have e : expSeries a τ = hamburgerSeries a τ - defectLaplace g τ +
        β / (Real.pi * τ) - β := by rw [hJ]; ring
    have h1 := norm_sub_le (hamburgerSeries a τ - defectLaplace g τ + β / (Real.pi * τ)) β
    have h2 := norm_add_le (hamburgerSeries a τ - defectLaplace g τ) (β / (Real.pi * τ))
    have h3 := norm_sub_le (hamburgerSeries a τ) (defectLaplace g τ)
    rw [← e] at h1
    linarith
  have hgoal : A / (8 * Real.pi * μ) = 4 * ι := by rw [hι]; field_simp; ring
  rw [hgoal]
  linarith

end GaloisForLFunctions.EulerFETransportTheory
