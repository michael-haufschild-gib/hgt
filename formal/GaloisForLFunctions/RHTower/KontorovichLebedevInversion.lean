import GaloisForLFunctions.RHTower.KontorovichLebedevTransform
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import GaloisForLFunctions.RHTower.CauchyBetaIntegral

/-!
# The Kontorovich–Lebedev inversion formula

For a smooth `f` with compact support in `(0, ∞)`, `g(y) = ∫ f(t) K_{iy}(t) dt` and `x > 0`,

`∫_ℝ y sinh(πy) K_{iy}(x) g(y) dy = π² x f(x)`                       (`kontorovichLebedev_inversion`).

Proof.  For `|α| < π/2` the Schläfli integral on the line `Im u = α` gives the Fourier transform
`∫ e^{−x cosh(v+iα)} e^{iyv} dv = 2 e^{αy} K_{iy}(x)` (`fourier_shiftKer`).  With
`F(w) = ∫ f(t) e^{−t cosh w} dt`, `A_α = ½(F(·+iα) + F(·−iα))` and
`h_α = ½(e^{−x cosh(·+iα)} − e^{−x cosh(·−iα)})`, the transforms of `A_α` and of `D_α = h_α'` are
`2cosh(αy)g(y)` and `−2iy sinh(αy)K_{iy}(x)` (at `y = −2πξ`), so the multiplication formula and
Fourier inversion give `∫ y sinh(2αy) K_{iy}(x) g(y) dy = iπ ∫ A_α D_α`.  As `α → π/2`, dominated
convergence applies on both sides: `|F(v ± iα)| ≤ C cosh⁻²v` uniformly (two integrations by parts)
and `|D_α(v)| ≤ x cosh v`; on the spectral side `|y sinh(πy) K_{iy}(x) g(y)|` is integrable by the
decay of `g`.  At `α = π/2`, `A(v) = ∫ f(t) cos(t sinh v) dt` and `D(v) = −ix cosh v cos(x sinh v)`;
the substitution `ξ = sinh v` and Fourier inversion for `f` give `∫ A D = −iπ x f(x)`.
-/

open Complex MeasureTheory Set Filter Topology
open scoped ContDiff FourierTransform

namespace GaloisForLFunctions.RHTower.KontorovichLebedev

open GaloisForLFunctions.HTGeometry

noncomputable section

/-! ## The shifted Schläfli kernel and its Fourier transform -/

/-- `K_{iy}(x)`. -/
def kIm (x y : ℝ) : ℂ := modifiedBesselKOrder x ((y : ℂ) * I)

theorem kIm_neg (x y : ℝ) : kIm x (-y) = kIm x y := by
  unfold kIm
  rw [show ((-y : ℝ) : ℂ) * I = -((y : ℂ) * I) by push_cast; ring, modifiedBesselKOrder_neg]

/-- The shifted Schläfli kernel `v ↦ e^{−x cosh(v + iα)}`. -/
def shiftKer (x α v : ℝ) : ℂ := cexp (-(x : ℂ) * Complex.cosh ((v : ℂ) + (α : ℂ) * I))

theorem shiftKer_neg (x α v : ℝ) : shiftKer x (-α) v = shiftKer x α (-v) := by
  unfold shiftKer
  rw [← Complex.cosh_neg ((((-v : ℝ) : ℂ)) + (α : ℂ) * I)]
  congr 3
  push_cast
  ring

theorem norm_shiftKer (x α v : ℝ) :
    ‖shiftKer x α v‖ = Real.exp (-x * (Real.cosh v * Real.cos α)) := by
  unfold shiftKer
  rw [Complex.norm_exp]
  congr 1
  rw [show -(x : ℂ) * Complex.cosh ((v : ℂ) + (α : ℂ) * I) =
      ((-x : ℝ) : ℂ) * Complex.cosh ((v : ℂ) + (α : ℂ) * I) by push_cast; ring,
    Complex.re_ofReal_mul, cosh_re_eq]

theorem continuous_shiftKer (x α : ℝ) : Continuous (shiftKer x α) := by
  unfold shiftKer
  fun_prop

theorem norm_shiftKer_le {x α : ℝ} (hx : 0 ≤ x) (hα : |α| ≤ Real.pi / 2) (v : ℝ) :
    ‖shiftKer x α v‖ ≤ 1 := by
  rw [norm_shiftKer, Real.exp_le_one_iff]
  have hc : 0 ≤ Real.cos α := Real.cos_nonneg_of_mem_Icc ⟨by linarith [neg_abs_le α],
    by linarith [le_abs_self α]⟩
  have := mul_nonneg (Real.cosh_pos v).le hc
  nlinarith

theorem integrable_shiftKer {x : ℝ} (hx : 0 < x) {α : ℝ} (hα : |α| < Real.pi / 2) :
    Integrable (shiftKer x α) := by
  have hc : 0 < Real.cos α := Real.cos_pos_of_mem_Ioo ⟨by linarith [neg_abs_le α],
    by linarith [le_abs_self α]⟩
  refine ((integrable_besselOrderExpKernel (mul_pos hx hc) 0).norm).mono'
    (continuous_shiftKer x α).aestronglyMeasurable (Eventually.of_forall fun v => ?_)
  rw [norm_shiftKer, besselOrderExpKernel, Complex.norm_exp]
  apply le_of_eq
  congr 1
  simp [Complex.cosh_ofReal_re, -Complex.ofReal_cos]
  ring

/-- **The Schläfli integral on a shifted line**: `∫ e^{−x cosh(v+iα)} e^{iyv} dv = 2e^{αy}K_{iy}(x)`
for `0 ≤ α < π/2`. -/
theorem integral_shiftKer_mul_exp {x : ℝ} (hx : 0 < x) {α : ℝ} (hα0 : 0 ≤ α)
    (hα : α < Real.pi / 2) (y : ℝ) :
    ∫ v : ℝ, shiftKer x α v * cexp ((y : ℂ) * v * I) = 2 * Real.exp (α * y) * kIm x y := by
  have h2 := integral_besselOrderExpKernel_eq_two_mul hx ((y : ℂ) * I)
  rw [integral_besselOrderExpKernel_eq_shifted hx _ hα0 hα] at h2
  have hpt : ∀ v : ℝ, besselOrderEntireKernel x ((y : ℂ) * I) ((v : ℂ) + (α : ℂ) * I) =
      (Real.exp (-(α * y)) : ℂ) * (shiftKer x α v * cexp ((y : ℂ) * v * I)) := fun v => by
    unfold besselOrderEntireKernel shiftKer
    rw [Complex.ofReal_exp, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    push_cast
    ring_nf
    rw [Complex.I_sq]
    ring
  simp_rw [hpt] at h2
  rw [integral_const_mul] at h2
  have he : (Real.exp (α * y) : ℂ) * (Real.exp (-(α * y)) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, ← Real.exp_add, add_neg_cancel, Real.exp_zero, Complex.ofReal_one]
  calc ∫ v : ℝ, shiftKer x α v * cexp ((y : ℂ) * v * I)
      = (Real.exp (α * y) : ℂ) * ((Real.exp (-(α * y)) : ℂ) *
          ∫ v : ℝ, shiftKer x α v * cexp ((y : ℂ) * v * I)) := by
        rw [← mul_assoc, he, one_mul]
    _ = 2 * Real.exp (α * y) * kIm x y := by rw [h2, kIm]; ring

/-- The same for all `|α| < π/2`. -/
theorem integral_shiftKer_mul_exp' {x : ℝ} (hx : 0 < x) {α : ℝ} (hα : |α| < Real.pi / 2)
    (y : ℝ) :
    ∫ v : ℝ, shiftKer x α v * cexp ((y : ℂ) * v * I) = 2 * Real.exp (α * y) * kIm x y := by
  rcases le_or_gt 0 α with h | h
  · exact integral_shiftKer_mul_exp hx h (by rwa [abs_of_nonneg h] at hα) y
  · have hα' : -α < Real.pi / 2 := by rwa [abs_of_neg h] at hα
    have := integral_shiftKer_mul_exp hx (neg_nonneg.2 h.le) hα' (-y)
    rw [kIm_neg, show -α * -y = α * y by ring] at this
    rw [← this, ← integral_neg_eq_self]
    refine integral_congr_ae (Eventually.of_forall fun v => ?_)
    simp only
    rw [show α = -(-α) by ring, shiftKer_neg, neg_neg, neg_neg]
    congr 2
    push_cast
    ring

/-- **The Fourier transform of the shifted kernel**: `𝓕(e^{−x cosh(·+iα)})(ξ) = 2e^{−2παξ}K_{2πiξ}(x)`. -/
theorem fourier_shiftKer {x : ℝ} (hx : 0 < x) {α : ℝ} (hα : |α| < Real.pi / 2) (ξ : ℝ) :
    𝓕 (shiftKer x α) ξ = 2 * Real.exp (-(2 * Real.pi * α * ξ)) * kIm x (2 * Real.pi * ξ) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  have h := integral_shiftKer_mul_exp' hx hα (-(2 * Real.pi * ξ))
  rw [kIm_neg] at h
  rw [show -(2 * Real.pi * α * ξ) = α * -(2 * Real.pi * ξ) by ring, ← h]
  refine integral_congr_ae (Eventually.of_forall fun v => ?_)
  simp only [smul_eq_mul]
  rw [mul_comm]
  congr 2
  push_cast
  ring

/-! ## The transform `F(v + iα) = ∫ f(t) e^{−t cosh(v+iα)} dt` -/

variable {f : ℝ → ℂ}

/-- `F(v + iα) = ∫ f(t) e^{−t cosh(v + iα)} dt`. -/
def lapShift (f : ℝ → ℂ) (α v : ℝ) : ℂ := ∫ t, f t * shiftKer t α v

theorem hasDerivAt_shiftKer_left (α v t : ℝ) :
    HasDerivAt (fun s : ℝ => shiftKer s α v)
      (-Complex.cosh ((v : ℂ) + (α : ℂ) * I) * shiftKer t α v) t := by
  unfold shiftKer
  have h := ((hasDerivAt_id t).ofReal_comp.neg.mul_const
    (Complex.cosh ((v : ℂ) + (α : ℂ) * I))).cexp
  convert h using 1
  · funext s; simp
  · simp; ring

theorem continuous_shiftKer_left (α v : ℝ) : Continuous (fun s : ℝ => shiftKer s α v) := by
  unfold shiftKer; fun_prop

/-- One integration by parts: `∫ f' e^{−t z} = z ∫ f e^{−t z}`, `z = cosh(v+iα)`. -/
theorem lapShift_deriv (hf : IsKLTest f) (α v : ℝ) :
    lapShift (deriv f) α v = Complex.cosh ((v : ℂ) + (α : ℂ) * I) * lapShift f α v := by
  set z := Complex.cosh ((v : ℂ) + (α : ℂ) * I)
  have hc := continuous_shiftKer_left α v
  have hfc := hf.continuous
  have hf'c := hf.deriv.continuous
  have h := integral_mul_deriv_eq_deriv_mul_of_integrable (u := f) (u' := deriv f)
    (v := fun s : ℝ => shiftKer s α v) (v' := fun s : ℝ => -z * shiftKer s α v)
    (fun t _ => hf.hasDerivAt t) (fun t _ => hasDerivAt_shiftKer_left α v t)
    ((hfc.mul (continuous_const.mul hc)).integrable_of_hasCompactSupport
      hf.hasCompactSupport.mul_right)
    ((hf'c.mul hc).integrable_of_hasCompactSupport hf.deriv.hasCompactSupport.mul_right)
    ((hfc.mul hc).integrable_of_hasCompactSupport hf.hasCompactSupport.mul_right)
  unfold lapShift
  have h2 : ∫ t, f t * (-z * shiftKer t α v) = -z * ∫ t, f t * shiftKer t α v := by
    rw [← integral_const_mul]; congr 1; funext t; ring
  rw [h2] at h
  linear_combination h

theorem norm_lapShift_le (hf : IsKLTest f) {α : ℝ} (hα : |α| ≤ Real.pi / 2) (v : ℝ) :
    ‖lapShift f α v‖ ≤ ∫ t, ‖f t‖ := by
  obtain ⟨a, b, ha, -, hsupp⟩ := hf.exists_Icc
  refine norm_integral_le_of_norm_le hf.integrable.norm (Eventually.of_forall fun t => ?_)
  by_cases ht : t ∈ Icc a b
  · rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _)
      (norm_shiftKer_le (ha.le.trans ht.1) hα v)
  · simp [eq_zero_of_tsupport_subset hsupp ht]

theorem sinh_sq_le_normSq_cosh (α v : ℝ) :
    Real.sinh v ^ 2 ≤ ‖Complex.cosh ((v : ℂ) + (α : ℂ) * I)‖ ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.cosh_add, Complex.cosh_mul_I,
    Complex.sinh_mul_I]
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, ← Complex.ofReal_cosh,
    ← Complex.ofReal_sinh, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im]
  nlinarith [Real.cosh_sq v, Real.sin_sq_add_cos_sq α, sq_nonneg (Real.cos α),
    sq_nonneg (Real.sinh v), sq_nonneg (Real.sin α)]

/-- **Uniform decay of `F` on the strip**: `‖F(v + iα)‖ ≤ C cosh⁻² v` for `|α| ≤ π/2`. -/
theorem exists_bound_lapShift (hf : IsKLTest f) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ α : ℝ, |α| ≤ Real.pi / 2 → ∀ v : ℝ,
      ‖lapShift f α v‖ ≤ C / Real.cosh v ^ 2 := by
  have hf2 := hf.deriv.deriv
  set B₀ := ∫ t, ‖f t‖
  set B₂ := ∫ t, ‖deriv (deriv f) t‖
  have hB₀ : 0 ≤ B₀ := integral_nonneg fun _ => norm_nonneg _
  have hB₂ : 0 ≤ B₂ := integral_nonneg fun _ => norm_nonneg _
  refine ⟨B₀ + B₂, by positivity, fun α hα v => ?_⟩
  have hc := Real.cosh_pos v
  rw [le_div_iff₀ (by positivity)]
  have h2 : lapShift (deriv (deriv f)) α v =
      Complex.cosh ((v : ℂ) + (α : ℂ) * I) ^ 2 * lapShift f α v := by
    rw [lapShift_deriv hf.deriv, lapShift_deriv hf]; ring
  have hn2 := norm_lapShift_le hf2 hα v
  rw [h2, norm_mul, norm_pow] at hn2
  have hn0 := norm_lapShift_le hf hα v
  have hs := sinh_sq_le_normSq_cosh α v
  have hcs : Real.cosh v ^ 2 = 1 + Real.sinh v ^ 2 := by
    have := Real.cosh_sq v; linarith
  rw [hcs]
  have hL := norm_nonneg (lapShift f α v)
  nlinarith [mul_le_mul_of_nonneg_left hs hL]

theorem continuous_lapShift_left (hf : IsKLTest f) (α : ℝ) : Continuous (lapShift f α) := by
  obtain ⟨a, b, -, -, hsupp⟩ := hf.exists_Icc
  have heq : lapShift f α = fun v => ∫ t in Icc a b, f t * shiftKer t α v := by
    funext v
    rw [lapShift, setIntegral_eq_integral_of_forall_compl_eq_zero]
    intro t ht
    rw [eq_zero_of_tsupport_subset hsupp ht, zero_mul]
  rw [heq]
  refine continuous_parametric_integral_of_continuous ?_ isCompact_Icc
  have : Continuous (fun p : ℝ × ℝ => shiftKer p.2 α p.1) := by unfold shiftKer; fun_prop
  exact (hf.continuous.comp continuous_snd).mul this

/-- **The Fourier transform of `F(· + iα)`**: `2 e^{−2παξ} g(2πξ)` for `|α| < π/2`. -/
theorem fourier_lapShift (hf : IsKLTest f) {α : ℝ} (hα : |α| < Real.pi / 2) (ξ : ℝ) :
    𝓕 (lapShift f α) ξ = 2 * Real.exp (-(2 * Real.pi * α * ξ)) * klTransform f (2 * Real.pi * ξ) := by
  obtain ⟨a, b, ha, -, hsupp⟩ := hf.exists_Icc
  rw [Real.fourier_real_eq_integral_exp_smul]
  set e : ℝ → ℂ := fun v => cexp (((-2 * Real.pi * v * ξ : ℝ) : ℂ) * I)
  have hswap : Integrable (Function.uncurry fun (v t : ℝ) => e v * (f t * shiftKer t α v))
      (volume.prod volume) := by
    have hbound : Integrable (fun p : ℝ × ℝ => ‖shiftKer a α p.1‖ * ‖f p.2‖)
        (volume.prod volume) :=
      (integrable_shiftKer ha hα).norm.mul_prod hf.integrable.norm
    refine hbound.mono' ?_ (Eventually.of_forall fun p => ?_)
    · have : Continuous (fun p : ℝ × ℝ => shiftKer p.2 α p.1) := by unfold shiftKer; fun_prop
      exact (Continuous.aestronglyMeasurable (by
        have := hf.continuous; unfold e; fun_prop))
    · simp only [Function.uncurry, e, norm_mul]
      rw [Complex.norm_exp_ofReal_mul_I, one_mul]
      by_cases ht : p.2 ∈ Icc a b
      · rw [mul_comm]
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg (f p.2))
        rw [norm_shiftKer, norm_shiftKer]
        apply Real.exp_le_exp.mpr
        have hc : 0 ≤ Real.cosh p.1 * Real.cos α := mul_nonneg (Real.cosh_pos _).le
          (Real.cos_nonneg_of_mem_Icc ⟨by linarith [neg_abs_le α], by linarith [le_abs_self α]⟩)
        nlinarith [ht.1]
      · simp [eq_zero_of_tsupport_subset hsupp ht]
  simp only [smul_eq_mul, lapShift]
  have h1 : (∫ v : ℝ, e v * ∫ t : ℝ, f t * shiftKer t α v) =
      ∫ v : ℝ, ∫ t : ℝ, e v * (f t * shiftKer t α v) := by
    congr 1; funext v; rw [integral_const_mul]
  rw [show (fun v : ℝ => cexp (((-2 * Real.pi * v * ξ : ℝ) : ℂ) * I) *
      ∫ t : ℝ, f t * shiftKer t α v) = fun v => e v * ∫ t : ℝ, f t * shiftKer t α v from rfl, h1,
    integral_integral_swap hswap]
  have h2 : ∀ t : ℝ, (∫ v : ℝ, e v * (f t * shiftKer t α v)) =
      f t * (2 * Real.exp (-(2 * Real.pi * α * ξ)) * kIm t (2 * Real.pi * ξ)) := fun t => by
    by_cases ht : t ∈ Icc a b
    · have ht0 : 0 < t := lt_of_lt_of_le ha ht.1
      rw [← fourier_shiftKer ht0 hα ξ, Real.fourier_real_eq_integral_exp_smul, ← integral_const_mul]
      congr 1; funext v; simp only [smul_eq_mul, e]; ring
    · simp [eq_zero_of_tsupport_subset hsupp ht]
  simp_rw [h2]
  rw [klTransform, ← integral_const_mul]
  congr 1; funext t; simp only [kIm]; ring

/-! ## Elementary decay bounds -/

theorem pow_mul_exp_neg_le {c : ℝ} (hc : 0 < c) (k : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    t ^ k * Real.exp (-(c * t)) ≤ k.factorial / c ^ k := by
  have h := Real.pow_div_factorial_le_exp (c * t) (mul_nonneg hc.le ht) k
  rw [div_le_iff₀ (by positivity)] at h
  rw [le_div_iff₀ (by positivity), Real.exp_neg]
  have he := Real.exp_pos (c * t)
  rw [mul_pow] at h
  calc t ^ k * (Real.exp (c * t))⁻¹ * c ^ k = (c ^ k * t ^ k) * (Real.exp (c * t))⁻¹ := by ring
    _ ≤ (Real.exp (c * t) * k.factorial) * (Real.exp (c * t))⁻¹ :=
        mul_le_mul_of_nonneg_right h (inv_nonneg.2 he.le)
    _ = k.factorial := by field_simp

theorem exists_poly_exp_le_inv_one_add_sq_of_pos {c : ℝ} (hc : 0 < c) (m : ℕ) :
    ∃ D, 0 ≤ D ∧ ∀ t : ℝ, (1 + |t|) ^ m * Real.exp (-(c * |t|)) ≤ D * (1 + t ^ 2)⁻¹ := by
  refine ⟨Real.exp c * ((m + 2).factorial / c ^ (m + 2)), by positivity, fun t => ?_⟩
  set x := 1 + |t|
  have hx : 1 ≤ x := by simp only [x]; linarith [abs_nonneg t]
  have hsq : 1 + t ^ 2 ≤ x ^ 2 := by simp only [x]; nlinarith [abs_nonneg t, sq_abs t]
  have h1 := pow_mul_exp_neg_le hc (m + 2) (by linarith : (0 : ℝ) ≤ x)
  have hexp : Real.exp (-(c * |t|)) = Real.exp c * Real.exp (-(c * x)) := by
    rw [← Real.exp_add]; congr 1; simp only [x]; ring
  have hpos : 0 < 1 + t ^ 2 := by positivity
  rw [hexp, le_mul_inv_iff₀ hpos]
  calc x ^ m * (Real.exp c * Real.exp (-(c * x))) * (1 + t ^ 2)
      ≤ x ^ m * (Real.exp c * Real.exp (-(c * x))) * x ^ 2 := by gcongr
    _ = Real.exp c * (x ^ (m + 2) * Real.exp (-(c * x))) := by rw [pow_add]; ring
    _ ≤ Real.exp c * ((m + 2).factorial / c ^ (m + 2)) := by gcongr

theorem cosh_mul_exp_neg_le {c : ℝ} (hc : 0 < c) (v : ℝ) :
    Real.cosh v * Real.exp (-(c * Real.cosh v)) ≤ 2 / c * Real.exp (-(c / 2 * Real.cosh v)) := by
  have hu := Real.cosh_pos v
  have h := pow_mul_exp_neg_le (half_pos hc) 1 hu.le
  simp only [pow_one, Nat.factorial_one, Nat.cast_one] at h
  have hsplit : Real.exp (-(c * Real.cosh v)) =
      Real.exp (-(c / 2 * Real.cosh v)) * Real.exp (-(c / 2 * Real.cosh v)) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [hsplit, ← mul_assoc]
  have he := Real.exp_pos (-(c / 2 * Real.cosh v))
  calc Real.cosh v * Real.exp (-(c / 2 * Real.cosh v)) * Real.exp (-(c / 2 * Real.cosh v))
      ≤ 1 / (c / 2) * Real.exp (-(c / 2 * Real.cosh v)) := mul_le_mul_of_nonneg_right h he.le
    _ = 2 / c * Real.exp (-(c / 2 * Real.cosh v)) := by field_simp

theorem integrable_exp_neg_mul_cosh {c : ℝ} (hc : 0 < c) :
    Integrable (fun v : ℝ => Real.exp (-(c * Real.cosh v))) := by
  refine (integrable_besselOrderExpKernel hc 0).norm.congr (Eventually.of_forall fun v => ?_)
  simp [besselOrderExpKernel, Complex.norm_exp, Complex.cosh_ofReal_re]

/-! ## The odd kernel `h_α` and its derivative -/

/-- `v ↦ −x sinh(v + iα) e^{−x cosh(v+iα)}`, the derivative of the shifted kernel. -/
def dShift (x α v : ℝ) : ℂ := -(x : ℂ) * Complex.sinh ((v : ℂ) + (α : ℂ) * I) * shiftKer x α v

theorem hasDerivAt_shiftKer (x α v : ℝ) : HasDerivAt (shiftKer x α) (dShift x α v) v := by
  unfold shiftKer dShift
  have h := ((((hasDerivAt_id ((v : ℂ))).add_const ((α : ℂ) * I)).ccosh).const_mul
    (-(x : ℂ))).cexp.comp_ofReal
  exact h.congr_deriv (by simp only [id_eq, mul_one, shiftKer]; ring)

theorem norm_sinh_le_cosh (α v : ℝ) :
    ‖Complex.sinh ((v : ℂ) + (α : ℂ) * I)‖ ≤ Real.cosh v := by
  have h : ‖Complex.sinh ((v : ℂ) + (α : ℂ) * I)‖ ^ 2 ≤ Real.cosh v ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.sinh_add, Complex.cosh_mul_I,
      Complex.sinh_mul_I]
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      ← Complex.ofReal_cosh, ← Complex.ofReal_sinh, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    nlinarith [Real.cosh_sq v, Real.sin_sq_add_cos_sq α, sq_nonneg (Real.cos α),
      sq_nonneg (Real.sinh v), sq_nonneg (Real.sin α)]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (Real.cosh_pos v).le two_ne_zero).1 h

theorem norm_dShift_le {x : ℝ} (hx : 0 ≤ x) (α v : ℝ) :
    ‖dShift x α v‖ ≤ x * Real.cosh v * Real.exp (-x * (Real.cosh v * Real.cos α)) := by
  unfold dShift
  rw [norm_mul, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx,
    norm_shiftKer]
  gcongr
  exact norm_sinh_le_cosh α v

theorem continuous_dShift (x α : ℝ) : Continuous (dShift x α) := by
  unfold dShift shiftKer; fun_prop

theorem integrable_dShift {x : ℝ} (hx : 0 < x) {α : ℝ} (hα : |α| < Real.pi / 2) :
    Integrable (dShift x α) := by
  have hcα : 0 < Real.cos α := Real.cos_pos_of_mem_Ioo ⟨by linarith [neg_abs_le α],
    by linarith [le_abs_self α]⟩
  set c := x * Real.cos α
  have hc : 0 < c := mul_pos hx hcα
  refine ((integrable_exp_neg_mul_cosh (half_pos hc)).const_mul (x * (2 / c))).mono'
    (continuous_dShift x α).aestronglyMeasurable (Eventually.of_forall fun v => ?_)
  refine (norm_dShift_le hx.le α v).trans ?_
  have h := cosh_mul_exp_neg_le hc v
  have he : Real.exp (-x * (Real.cosh v * Real.cos α)) = Real.exp (-(c * Real.cosh v)) := by
    congr 1; simp only [c]; ring
  calc x * Real.cosh v * Real.exp (-x * (Real.cosh v * Real.cos α))
      = x * (Real.cosh v * Real.exp (-(c * Real.cosh v))) := by rw [he]; ring
    _ ≤ x * (2 / c * Real.exp (-(c / 2 * Real.cosh v))) := mul_le_mul_of_nonneg_left h hx.le
    _ = x * (2 / c) * Real.exp (-(c / 2 * Real.cosh v)) := by ring

/-- The odd kernel `h_α = ½(e^{−x cosh(·+iα)} − e^{−x cosh(·−iα)})`. -/
def hKer (x α v : ℝ) : ℂ := (shiftKer x α v - shiftKer x (-α) v) / 2

/-- Its derivative `D_α`. -/
def dKer (x α v : ℝ) : ℂ := (dShift x α v - dShift x (-α) v) / 2

theorem hasDerivAt_hKer (x α v : ℝ) : HasDerivAt (hKer x α) (dKer x α v) v :=
  ((hasDerivAt_shiftKer x α v).sub (hasDerivAt_shiftKer x (-α) v)).div_const 2

theorem deriv_hKer (x α : ℝ) : deriv (hKer x α) = dKer x α := by
  funext v; exact (hasDerivAt_hKer x α v).deriv

theorem dShift_neg (x α v : ℝ) : dShift x α (-v) = -dShift x (-α) v := by
  unfold dShift
  rw [← shiftKer_neg x α v,
    show ((((-v : ℝ)) : ℂ) + (α : ℂ) * I) = -(((v : ℝ) : ℂ) + (((-α : ℝ)) : ℂ) * I) by
      push_cast; ring, Complex.sinh_neg]
  ring

theorem dKer_neg (x α v : ℝ) : dKer x α (-v) = dKer x α v := by
  unfold dKer
  rw [dShift_neg, dShift_neg, neg_neg]
  ring

theorem integrable_hKer {x : ℝ} (hx : 0 < x) {α : ℝ} (hα : |α| < Real.pi / 2) :
    Integrable (hKer x α) :=
  ((integrable_shiftKer hx hα).sub (integrable_shiftKer hx (by rwa [abs_neg]))).div_const 2

theorem integrable_dKer {x : ℝ} (hx : 0 < x) {α : ℝ} (hα : |α| < Real.pi / 2) :
    Integrable (dKer x α) :=
  ((integrable_dShift hx hα).sub (integrable_dShift hx (by rwa [abs_neg]))).div_const 2

theorem continuous_dKer (x α : ℝ) : Continuous (dKer x α) :=
  ((continuous_dShift x α).sub (continuous_dShift x (-α))).div_const 2

theorem integrable_exp_mul {g : ℝ → ℂ} (hg : Integrable g) (ξ : ℝ) :
    Integrable (fun v : ℝ => cexp (((-2 * Real.pi * v * ξ : ℝ) : ℂ) * I) * g v) :=
  hg.norm.mono' ((Continuous.aestronglyMeasurable (by fun_prop)).mul hg.1)
    (Eventually.of_forall fun v => by rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul])

theorem fourier_sub_div_two {g h : ℝ → ℂ} (hg : Integrable g) (hh : Integrable h) (ξ : ℝ) :
    𝓕 (fun v => (g v - h v) / 2) ξ = (𝓕 g ξ - 𝓕 h ξ) / 2 := by
  simp only [Real.fourier_real_eq_integral_exp_smul, smul_eq_mul]
  rw [← integral_sub (integrable_exp_mul hg ξ) (integrable_exp_mul hh ξ), ← integral_div]
  congr 1; funext v; ring

theorem fourier_add_div_two {g h : ℝ → ℂ} (hg : Integrable g) (hh : Integrable h) (ξ : ℝ) :
    𝓕 (fun v => (g v + h v) / 2) ξ = (𝓕 g ξ + 𝓕 h ξ) / 2 := by
  simp only [Real.fourier_real_eq_integral_exp_smul, smul_eq_mul]
  rw [← integral_add (integrable_exp_mul hg ξ) (integrable_exp_mul hh ξ), ← integral_div]
  congr 1; funext v; ring

/-- `𝓕h_α(ξ) = −2 sinh(2παξ) K_{2πiξ}(x)`. -/
theorem fourier_hKer {x : ℝ} (hx : 0 < x) {α : ℝ} (hα : |α| < Real.pi / 2) (ξ : ℝ) :
    𝓕 (hKer x α) ξ = -(2 * Real.sinh (2 * Real.pi * α * ξ)) * kIm x (2 * Real.pi * ξ) := by
  have hα' : |-α| < Real.pi / 2 := by rwa [abs_neg]
  rw [show hKer x α = fun v => (shiftKer x α v - shiftKer x (-α) v) / 2 from rfl,
    fourier_sub_div_two (integrable_shiftKer hx hα) (integrable_shiftKer hx hα'),
    fourier_shiftKer hx hα, fourier_shiftKer hx hα', Real.sinh_eq]
  push_cast
  ring_nf

/-- `𝓕D_α(ξ) = −4πiξ sinh(2παξ) K_{2πiξ}(x)`. -/
theorem fourier_dKer {x : ℝ} (hx : 0 < x) {α : ℝ} (hα : |α| < Real.pi / 2) (ξ : ℝ) :
    𝓕 (dKer x α) ξ =
      -(4 * Real.pi * I * ξ * Real.sinh (2 * Real.pi * α * ξ)) * kIm x (2 * Real.pi * ξ) := by
  have h := Real.fourier_deriv (integrable_hKer hx hα)
    (fun v => (hasDerivAt_hKer x α v).differentiableAt) (by rw [deriv_hKer]; exact integrable_dKer hx hα)
  rw [deriv_hKer] at h
  rw [h]
  dsimp only
  rw [smul_eq_mul, fourier_hKer hx hα]
  push_cast
  ring

/-! ## The even kernel `A_α` -/

theorem one_add_sq_le_cosh_sq (v : ℝ) : 1 + v ^ 2 ≤ Real.cosh v ^ 2 := by
  have h1 : |v| ≤ |Real.sinh v| := by
    rw [Real.abs_sinh]; exact Real.self_le_sinh_iff.2 (abs_nonneg v)
  have h2 : v ^ 2 ≤ Real.sinh v ^ 2 := by
    rw [← sq_abs v, ← sq_abs (Real.sinh v)]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
  rw [Real.cosh_sq]; linarith

theorem one_div_cosh_sq_le (v : ℝ) : 1 / Real.cosh v ^ 2 ≤ (1 + v ^ 2)⁻¹ := by
  rw [one_div]
  exact inv_anti₀ (by positivity) (one_add_sq_le_cosh_sq v)

theorem integrable_one_div_cosh_sq : Integrable (fun v : ℝ => 1 / Real.cosh v ^ 2) :=
  integrable_inv_one_add_sq.mono'
    (continuous_const.div (Real.continuous_cosh.pow 2)
      (fun v => (pow_pos (Real.cosh_pos v) 2).ne')).aestronglyMeasurable
    (Eventually.of_forall fun v => by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]; exact one_div_cosh_sq_le v)

/-- `A_α = ½(F(·+iα) + F(·−iα))`. -/
def aKer (f : ℝ → ℂ) (α v : ℝ) : ℂ := (lapShift f α v + lapShift f (-α) v) / 2

/-- `𝓕A_α(ξ) = 2 cosh(2παξ) g(2πξ)`. -/
theorem fourier_aKer (hf : IsKLTest f) {α : ℝ} (hα : |α| < Real.pi / 2) (ξ : ℝ) :
    𝓕 (aKer f α) ξ = 2 * Real.cosh (2 * Real.pi * α * ξ) * klTransform f (2 * Real.pi * ξ) := by
  have hα' : |-α| < Real.pi / 2 := by rwa [abs_neg]
  obtain ⟨C, hC, hb⟩ := exists_bound_lapShift hf
  have hint : ∀ β : ℝ, |β| ≤ Real.pi / 2 → Integrable (lapShift f β) := fun β hβ => by
    refine (integrable_one_div_cosh_sq.const_mul C).mono'
      (continuous_lapShift_left hf β).aestronglyMeasurable (Eventually.of_forall fun v => ?_)
    rw [mul_one_div]; exact hb β hβ v
  rw [show aKer f α = fun v => (lapShift f α v + lapShift f (-α) v) / 2 from rfl,
    fourier_add_div_two (hint α hα.le) (hint (-α) hα'.le),
    fourier_lapShift hf hα, fourier_lapShift hf hα', Real.cosh_eq]
  push_cast
  ring_nf

/-! ## The regularized identity -/

theorem norm_sinh_le_exp_abs (z : ℝ) : |Real.sinh z| ≤ Real.exp |z| := by
  rw [Real.abs_sinh, Real.sinh_eq]
  linarith [Real.exp_pos (-|z|), Real.exp_pos |z|]

theorem norm_kIm_le {x : ℝ} (hx : 0 < x) (y : ℝ) :
    ‖kIm x y‖ ≤ Real.exp 2 * (|Real.log x| + Real.log (2 + |y|) + 3) *
      Real.exp (-(Real.pi * |y|) / 2) :=
  norm_modifiedBesselKOrder_I_mul_le_log hx y

theorem log_two_add_abs_le (y : ℝ) : Real.log (2 + |y|) ≤ 1 + |y| := by
  have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 + |y| by positivity)
  linarith

theorem integrable_fourier_dKer {x : ℝ} (hx : 0 < x) {α : ℝ} (hα : |α| < Real.pi / 2) :
    Integrable (𝓕 (dKer x α)) := by
  set δ : ℝ := Real.pi ^ 2 - 2 * Real.pi * |α|
  have hδ : 0 < δ := by
    simp only [δ]; nlinarith [Real.pi_pos]
  obtain ⟨D, hD0, hD⟩ := exists_poly_exp_le_inv_one_add_sq_of_pos hδ 2
  set M : ℝ := 4 * Real.pi * Real.exp 2 * (|Real.log x| + 10)
  have hM : 0 ≤ M := by positivity
  refine (integrable_inv_one_add_sq.const_mul (M * D)).mono'
    ((Continuous.aestronglyMeasurable (VectorFourier.fourierIntegral_continuous
      Real.continuous_fourierChar (by fun_prop) (integrable_dKer hx hα))))
    (Eventually.of_forall fun ξ => ?_)
  rw [fourier_dKer hx hα ξ, norm_mul, norm_neg, norm_mul, norm_mul, norm_mul, norm_mul,
    Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos Real.pi_pos, Complex.norm_ofNat]
  have hk := norm_kIm_le hx (2 * Real.pi * ξ)
  have hs := norm_sinh_le_exp_abs (2 * Real.pi * α * ξ)
  have hl := log_two_add_abs_le (2 * Real.pi * ξ)
  have habs1 : |2 * Real.pi * α * ξ| = 2 * Real.pi * |α| * |ξ| := by
    rw [abs_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
      abs_of_pos Real.pi_pos]
  have habs2 : |2 * Real.pi * ξ| = 2 * Real.pi * |ξ| := by
    rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_pos Real.pi_pos]
  rw [habs1] at hs
  rw [habs2] at hk hl
  have hξ : |ξ| ≤ 1 + |ξ| := by linarith
  have hlog : |Real.log x| + Real.log (2 + 2 * Real.pi * |ξ|) + 3 ≤
      (|Real.log x| + 10) * (1 + |ξ|) := by
    have hπ4 := Real.pi_lt_four
    have : Real.log (2 + 2 * Real.pi * |ξ|) ≤ 1 + 2 * Real.pi * |ξ| := hl
    nlinarith [abs_nonneg ξ, abs_nonneg (Real.log x), Real.pi_pos]
  have hexp : Real.exp (2 * Real.pi * |α| * |ξ|) * Real.exp (-(Real.pi * (2 * Real.pi * |ξ|)) / 2) =
      Real.exp (-(δ * |ξ|)) := by
    rw [← Real.exp_add]; congr 1; simp only [δ]; ring
  have hD' := hD ξ
  calc 4 * Real.pi * |ξ| * |Real.sinh (2 * Real.pi * α * ξ)| * ‖kIm x (2 * Real.pi * ξ)‖
      ≤ 4 * Real.pi * |ξ| * Real.exp (2 * Real.pi * |α| * |ξ|) *
          (Real.exp 2 * (|Real.log x| + Real.log (2 + 2 * Real.pi * |ξ|) + 3) *
            Real.exp (-(Real.pi * (2 * Real.pi * |ξ|)) / 2)) := by gcongr
    _ = 4 * Real.pi * Real.exp 2 * |ξ| * (|Real.log x| + Real.log (2 + 2 * Real.pi * |ξ|) + 3) *
          (Real.exp (2 * Real.pi * |α| * |ξ|) *
            Real.exp (-(Real.pi * (2 * Real.pi * |ξ|)) / 2)) := by ring
    _ ≤ 4 * Real.pi * Real.exp 2 * (1 + |ξ|) * ((|Real.log x| + 10) * (1 + |ξ|)) *
          Real.exp (-(δ * |ξ|)) := by
        have hl0 : 0 ≤ Real.log (2 + 2 * Real.pi * |ξ|) :=
          Real.log_nonneg (by nlinarith [abs_nonneg ξ, Real.pi_pos])
        rw [hexp]; gcongr
    _ = M * ((1 + |ξ|) ^ 2 * Real.exp (-(δ * |ξ|))) := by simp only [M]; ring
    _ ≤ M * (D * (1 + ξ ^ 2)⁻¹) := mul_le_mul_of_nonneg_left hD' hM
    _ = M * D * (1 + ξ ^ 2)⁻¹ := by ring

theorem fourier_fourier_dKer {x : ℝ} (hx : 0 < x) {α : ℝ} (hα : |α| < Real.pi / 2) (v : ℝ) :
    𝓕 (𝓕 (dKer x α)) v = dKer x α v := by
  have hinv := Continuous.fourierInv_fourier_eq (continuous_dKer x α) (integrable_dKer hx hα)
    (integrable_fourier_dKer hx hα)
  have h := Real.fourierInv_eq_fourier_neg (𝓕 (dKer x α)) (-v)
  rw [neg_neg, hinv, dKer_neg] at h
  exact h.symm

theorem integrable_aKer (hf : IsKLTest f) (α : ℝ) (hα : |α| ≤ Real.pi / 2) :
    Integrable (aKer f α) := by
  obtain ⟨C, hC, hb⟩ := exists_bound_lapShift hf
  have hα' : |-α| ≤ Real.pi / 2 := by rwa [abs_neg]
  refine (integrable_one_div_cosh_sq.const_mul C).mono'
    (((continuous_lapShift_left hf α).add (continuous_lapShift_left hf (-α))).div_const
      2).aestronglyMeasurable (Eventually.of_forall fun v => ?_)
  unfold aKer
  rw [norm_div, Complex.norm_two, mul_one_div]
  have h1 := hb α hα v
  have h2 := hb (-α) hα' v
  have := norm_add_le (lapShift f α v) (lapShift f (-α) v)
  linarith

/-- **The regularized identity** `∫ y sinh(2αy) K_{iy}(x) g(y) dy = iπ ∫ A_α D_α` for `|α| < π/2`. -/
theorem integral_sinh_kIm_klTransform (hf : IsKLTest f) {x : ℝ} (hx : 0 < x) {α : ℝ}
    (hα : |α| < Real.pi / 2) :
    ∫ y : ℝ, (y : ℂ) * Real.sinh (2 * α * y) * kIm x y * klTransform f y =
      I * Real.pi * ∫ v : ℝ, aKer f α v * dKer x α v := by
  have hmul := Kuznetsov.integral_fourier_mul_eq (aKer f α) (𝓕 (dKer x α))
    (integrable_aKer hf α hα.le) (integrable_fourier_dKer hx hα)
  simp_rw [fourier_fourier_dKer hx hα] at hmul
  rw [← hmul]
  set G : ℝ → ℂ := fun y => (y : ℂ) * Real.sinh (2 * α * y) * kIm x y * klTransform f y
  have hpt : ∀ ξ : ℝ, 𝓕 (aKer f α) ξ * 𝓕 (dKer x α) ξ = -(2 * I) * G (2 * Real.pi * ξ) := by
    intro ξ
    rw [fourier_aKer hf hα, fourier_dKer hx hα]
    simp only [G]
    rw [show 2 * α * (2 * Real.pi * ξ) = 2 * (2 * Real.pi * α * ξ) by ring, Real.sinh_two_mul]
    push_cast
    ring
  simp_rw [hpt]
  rw [integral_const_mul, Measure.integral_comp_mul_left G (2 * Real.pi),
    abs_of_pos (inv_pos.2 (by positivity : (0 : ℝ) < 2 * Real.pi)), Complex.real_smul]
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  push_cast
  field_simp
  ring_nf
  rw [Complex.I_sq]
  ring

/-! ## The limit `α → π/2` on the spectral side -/

theorem pow_le_one_add_pow {t : ℝ} (ht : 0 ≤ t) {k n : ℕ} (hkn : k ≤ n) : t ^ k ≤ 1 + t ^ n := by
  rcases le_or_gt t 1 with h | h
  · have := pow_le_one₀ ht h (n := k); have := pow_nonneg ht n; linarith
  · have := pow_le_pow_right₀ h.le hkn; linarith

theorem one_add_pow_three_mul_le {t : ℝ} (ht : 0 ≤ t) :
    (1 + t) ^ 3 * (1 + t ^ 2) ≤ 16 * (1 + t ^ 8) := by
  have h1 : (1 + t) ^ 3 ≤ 4 * (1 + t ^ 3) := by
    nlinarith [mul_nonneg (sq_nonneg (1 - t)) (by linarith : (0 : ℝ) ≤ 1 + t)]
  have h2 := pow_le_one_add_pow ht (show 2 ≤ 8 by norm_num)
  have h3 := pow_le_one_add_pow ht (show 3 ≤ 8 by norm_num)
  have h5 := pow_le_one_add_pow ht (show 5 ≤ 8 by norm_num)
  have h2' : (1 + t ^ 3) * (1 + t ^ 2) = 1 + t ^ 2 + t ^ 3 + t ^ 5 := by ring
  have hp : 0 ≤ 1 + t ^ 2 := by positivity
  calc (1 + t) ^ 3 * (1 + t ^ 2) ≤ 4 * (1 + t ^ 3) * (1 + t ^ 2) :=
        mul_le_mul_of_nonneg_right h1 hp
    _ = 4 * (1 + t ^ 2 + t ^ 3 + t ^ 5) := by rw [mul_assoc, h2']
    _ ≤ 16 * (1 + t ^ 8) := by linarith [pow_nonneg ht 8]

/-- The spectral integrand is dominated by `C (1 + y²)⁻¹`. -/
theorem exists_bound_spectral (hf : IsKLTest f) {x : ℝ} (hx : 0 < x) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : ℝ, |y| * Real.exp (Real.pi * |y|) * ‖kIm x y‖ * ‖klTransform f y‖ ≤
      C * (1 + y ^ 2)⁻¹ := by
  obtain ⟨C₄, hC₄, hb⟩ := exists_bound_klTransform hf 4
  set K : ℝ := 2 * Real.exp 2 * (|Real.log x| + 4) * C₄
  refine ⟨16 * K, by positivity, fun y => ?_⟩
  set t := |y|
  have ht : 0 ≤ t := abs_nonneg y
  have hk := norm_kIm_le hx y
  have hg := hb y
  have hl := log_two_add_abs_le y
  have hl0 : 0 ≤ Real.log (2 + |y|) := Real.log_nonneg (by linarith)
  have hy8 : y ^ (2 * 4) = t ^ 8 := by
    simp only [t]; rw [show (8 : ℕ) = 2 * 4 from rfl, pow_mul, pow_mul, sq_abs]
  have hpos8 : 0 < 1 + y ^ (2 * 4) := by rw [hy8]; positivity
  have hy2 : y ^ 2 = t ^ 2 := by simp only [t]; rw [sq_abs]
  rw [hy8] at hg hpos8
  have he : Real.exp (Real.pi * t) * (Real.exp (-(Real.pi * t) / 2) *
      Real.exp (-(Real.pi * t) / 2)) = 1 := by
    rw [← Real.exp_add, ← Real.exp_add]; ring_nf; exact Real.exp_zero
  have hk' : ‖kIm x y‖ ≤ Real.exp 2 * (|Real.log x| + 4) * (1 + t) *
      Real.exp (-(Real.pi * t) / 2) := by
    refine hk.trans (le_of_le_of_eq (b := Real.exp 2 * ((|Real.log x| + 4) * (1 + t)) *
      Real.exp (-(Real.pi * t) / 2)) ?_ (by ring))
    gcongr
    nlinarith [abs_nonneg (Real.log x)]
  have hg' : ‖klTransform f y‖ ≤ C₄ * (2 * (1 + t)) * Real.exp (-(Real.pi * t) / 2) /
      (1 + t ^ 8) := by
    refine hg.trans ?_
    gcongr
    linarith
  have hprod : |y| * Real.exp (Real.pi * |y|) * ‖kIm x y‖ * ‖klTransform f y‖ ≤
      K * ((1 + t) ^ 3 / (1 + t ^ 8)) := by
    calc |y| * Real.exp (Real.pi * |y|) * ‖kIm x y‖ * ‖klTransform f y‖
        ≤ t * Real.exp (Real.pi * t) * (Real.exp 2 * (|Real.log x| + 4) * (1 + t) *
            Real.exp (-(Real.pi * t) / 2)) * (C₄ * (2 * (1 + t)) *
              Real.exp (-(Real.pi * t) / 2) / (1 + t ^ 8)) := by gcongr
      _ = K * (t * (1 + t) ^ 2 / (1 + t ^ 8)) *
            (Real.exp (Real.pi * t) * (Real.exp (-(Real.pi * t) / 2) *
              Real.exp (-(Real.pi * t) / 2))) := by simp only [K]; ring
      _ = K * (t * (1 + t) ^ 2 / (1 + t ^ 8)) := by rw [he, mul_one]
      _ ≤ K * ((1 + t) ^ 3 / (1 + t ^ 8)) := by
          gcongr
          nlinarith [sq_nonneg (1 + t)]
  refine hprod.trans ?_
  rw [hy2]
  have h16 := one_add_pow_three_mul_le ht
  have hK : 0 ≤ K := by positivity
  rw [div_eq_mul_inv]
  have hinv : (1 + t) ^ 3 * (1 + t ^ 8)⁻¹ ≤ 16 * (1 + t ^ 2)⁻¹ := by
    rw [mul_inv_le_iff₀ hpos8, mul_comm (16 : ℝ), mul_assoc, ← div_eq_inv_mul,
      le_div_iff₀ (by positivity)]
    linarith
  calc K * ((1 + t) ^ 3 * (1 + t ^ 8)⁻¹) ≤ K * (16 * (1 + t ^ 2)⁻¹) :=
        mul_le_mul_of_nonneg_left hinv hK
    _ = 16 * K * (1 + t ^ 2)⁻¹ := by ring

theorem abs_sinh_le_exp_pi {α : ℝ} (hα : |α| ≤ Real.pi / 2) (y : ℝ) :
    |Real.sinh (2 * α * y)| ≤ Real.exp (Real.pi * |y|) := by
  refine (norm_sinh_le_exp_abs _).trans (Real.exp_le_exp.mpr ?_)
  rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  nlinarith [abs_nonneg y]

theorem continuous_kIm {x : ℝ} (hx : 0 < x) : Continuous (kIm x) :=
  (differentiable_modifiedBesselKOrder hx).continuous.comp (by fun_prop)

theorem norm_kIm_le_zero {x : ℝ} (hx : 0 < x) (y : ℝ) :
    ‖kIm x y‖ ≤ ∫ u in Ioi (0 : ℝ), Real.exp (-x * Real.cosh u) := by
  have h := norm_modifiedBesselKOrder_I_mul_le_shifted hx y le_rfl (by positivity)
  simp only [mul_zero, Real.exp_zero, one_mul, Real.cos_zero, mul_one] at h
  exact h

theorem continuous_mul_kIm (hf : IsKLTest f) (y : ℝ) :
    Continuous (fun t : ℝ => f t * modifiedBesselKOrder t ((y : ℂ) * I)) := by
  obtain ⟨a, b, ha, -, hsupp⟩ := hf.exists_Icc
  refine continuous_iff_continuousAt.2 fun t => ?_
  rcases lt_or_ge 0 t with ht | ht
  · have hK : ContinuousAt (fun s : ℝ => modifiedBesselKOrder s ((y : ℂ) * I)) t :=
      (MaassWhittaker.hasDerivAt_besK ((y : ℂ) * I) ht).continuousAt
    exact hf.continuous.continuousAt.mul hK
  · have hev : (fun s : ℝ => f s * modifiedBesselKOrder s ((y : ℂ) * I)) =ᶠ[𝓝 t] fun _ => 0 := by
      filter_upwards [Iio_mem_nhds (show t < a by linarith)] with s hs
      rw [eq_zero_of_tsupport_subset hsupp (fun h => absurd h.1 (not_le.2 hs)), zero_mul]
    exact (continuousAt_const).congr hev.symm

theorem continuous_klTransform (hf : IsKLTest f) : Continuous (klTransform f) := by
  obtain ⟨a, b, ha, -, hsupp⟩ := hf.exists_Icc
  refine continuous_of_dominated (bound := fun t => ‖f t‖ *
      ∫ u in Ioi (0 : ℝ), Real.exp (-a * Real.cosh u))
    (fun y => (continuous_mul_kIm hf y).aestronglyMeasurable)
    (fun y => Eventually.of_forall fun t => ?_) (hf.integrable.norm.mul_const _)
    (Eventually.of_forall fun t => ?_)
  · by_cases ht : t ∈ Icc a b
    · have ht0 : 0 < t := lt_of_lt_of_le ha ht.1
      rw [norm_mul]
      refine mul_le_mul_of_nonneg_left ((norm_kIm_le_zero ht0 y).trans ?_) (norm_nonneg _)
      refine setIntegral_mono_on (integrableOn_exp_neg_mul_cosh_Ioi ht0)
        (integrableOn_exp_neg_mul_cosh_Ioi ha) measurableSet_Ioi (fun u _ => ?_)
      apply Real.exp_le_exp.mpr
      nlinarith [Real.cosh_pos u, ht.1]
    · simp [eq_zero_of_tsupport_subset hsupp ht]
  · by_cases ht : 0 < t
    · exact continuous_const.mul (continuous_kIm ht)
    · have : f t = 0 := eq_zero_of_tsupport_subset hsupp (fun h => absurd (lt_of_lt_of_le ha h.1) ht)
      simp only [this, zero_mul]
      exact continuous_const

/-- **Dominated convergence on the spectral side.** -/
theorem tendsto_integral_spectral (hf : IsKLTest f) {x : ℝ} (hx : 0 < x) :
    Tendsto (fun α : ℝ => ∫ y : ℝ, (y : ℂ) * Real.sinh (2 * α * y) * kIm x y * klTransform f y)
      (𝓝[<] (Real.pi / 2))
      (𝓝 (∫ y : ℝ, (y : ℂ) * Real.sinh (Real.pi * y) * kIm x y * klTransform f y)) := by
  obtain ⟨C, hC, hb⟩ := exists_bound_spectral hf hx
  have hkc := continuous_kIm hx
  have hgc := continuous_klTransform hf
  have hev : ∀ᶠ α in 𝓝[<] (Real.pi / 2), α ∈ Ioo 0 (Real.pi / 2) :=
    Ioo_mem_nhdsLT (by positivity)
  refine tendsto_integral_filter_of_dominated_convergence (fun y => C * (1 + y ^ 2)⁻¹)
    (Eventually.of_forall fun α => (Continuous.aestronglyMeasurable (by fun_prop)))
    (hev.mono fun α hα => Eventually.of_forall fun y => ?_)
    (integrable_inv_one_add_sq.const_mul C) (Eventually.of_forall fun y => ?_)
  · have hα' : |α| ≤ Real.pi / 2 := by rw [abs_of_pos hα.1]; exact hα.2.le
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs]
    refine le_trans ?_ (hb y)
    gcongr
    exact abs_sinh_le_exp_pi hα' y
  · have hc : Continuous (fun α : ℝ => (y : ℂ) * Real.sinh (2 * α * y) * kIm x y *
        klTransform f y) := by fun_prop
    have h := (hc.tendsto (Real.pi / 2)).mono_left (nhdsWithin_le_nhds (s := Iio (Real.pi / 2)))
    rwa [show 2 * (Real.pi / 2) * y = Real.pi * y by ring] at h
/-! ## The limit `α → π/2` on the kernel side -/

theorem continuous_lapShift_right (hf : IsKLTest f) (v : ℝ) :
    Continuous (fun α : ℝ => lapShift f α v) := by
  obtain ⟨a, b, -, -, hsupp⟩ := hf.exists_Icc
  have heq : (fun α : ℝ => lapShift f α v) = fun α => ∫ t in Icc a b, f t * shiftKer t α v := by
    funext α
    rw [lapShift, setIntegral_eq_integral_of_forall_compl_eq_zero]
    intro t ht
    rw [eq_zero_of_tsupport_subset hsupp ht, zero_mul]
  rw [heq]
  refine continuous_parametric_integral_of_continuous ?_ isCompact_Icc
  have : Continuous (fun p : ℝ × ℝ => shiftKer p.2 p.1 v) := by unfold shiftKer; fun_prop
  exact (hf.continuous.comp continuous_snd).mul this

theorem one_add_sq_div_four_le_cosh (v : ℝ) : 1 + v ^ 2 / 4 ≤ Real.cosh v := by
  rw [← Real.cosh_abs, Real.cosh_eq]
  have h1 := Real.quadratic_le_exp_of_nonneg (abs_nonneg v)
  have h2 := Real.add_one_le_exp (-|v|)
  have h3 : |v| ^ 2 = v ^ 2 := sq_abs v
  nlinarith

theorem integrable_one_div_cosh : Integrable (fun v : ℝ => 1 / Real.cosh v) := by
  refine (integrable_inv_one_add_sq.const_mul 4).mono'
    (continuous_const.div Real.continuous_cosh (fun v => (Real.cosh_pos v).ne')).aestronglyMeasurable
    (Eventually.of_forall fun v => ?_)
  have hc := Real.cosh_pos v
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), div_le_iff₀ hc]
  have h := one_add_sq_div_four_le_cosh v
  have hp : 0 < 1 + v ^ 2 := by positivity
  rw [← div_eq_mul_inv, div_mul_eq_mul_div, le_div_iff₀ hp]
  nlinarith

theorem norm_dKer_le {x : ℝ} (hx : 0 ≤ x) {α : ℝ} (hα : |α| ≤ Real.pi / 2) (v : ℝ) :
    ‖dKer x α v‖ ≤ x * Real.cosh v := by
  have hcos : ∀ β : ℝ, |β| ≤ Real.pi / 2 →
      ‖dShift x β v‖ ≤ x * Real.cosh v := fun β hβ => by
    refine (norm_dShift_le hx β v).trans ?_
    have hc : 0 ≤ Real.cos β := Real.cos_nonneg_of_mem_Icc ⟨by linarith [neg_abs_le β],
      by linarith [le_abs_self β]⟩
    have he : Real.exp (-x * (Real.cosh v * Real.cos β)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have := mul_nonneg (Real.cosh_pos v).le hc
      nlinarith
    have := mul_nonneg hx (Real.cosh_pos v).le
    nlinarith
  unfold dKer
  rw [norm_div, Complex.norm_two]
  have h1 := hcos α hα
  have h2 := hcos (-α) (by rwa [abs_neg])
  have := norm_sub_le (dShift x α v) (dShift x (-α) v)
  linarith

/-- **Dominated convergence on the kernel side.** -/
theorem tendsto_integral_kernel (hf : IsKLTest f) {x : ℝ} (hx : 0 < x) :
    Tendsto (fun α : ℝ => ∫ v : ℝ, aKer f α v * dKer x α v) (𝓝[<] (Real.pi / 2))
      (𝓝 (∫ v : ℝ, aKer f (Real.pi / 2) v * dKer x (Real.pi / 2) v)) := by
  obtain ⟨C, hC, hb⟩ := exists_bound_lapShift hf
  have hev : ∀ᶠ α in 𝓝[<] (Real.pi / 2), α ∈ Ioo 0 (Real.pi / 2) :=
    Ioo_mem_nhdsLT (by positivity)
  have hca : ∀ α, Continuous (aKer f α) := fun α =>
    ((continuous_lapShift_left hf α).add (continuous_lapShift_left hf (-α))).div_const 2
  refine tendsto_integral_filter_of_dominated_convergence (fun v => C * x * (1 / Real.cosh v))
    (Eventually.of_forall fun α => ((hca α).mul (continuous_dKer x α)).aestronglyMeasurable)
    (hev.mono fun α hα => Eventually.of_forall fun v => ?_)
    (integrable_one_div_cosh.const_mul (C * x)) (Eventually.of_forall fun v => ?_)
  · have hα' : |α| ≤ Real.pi / 2 := by rw [abs_of_pos hα.1]; exact hα.2.le
    have hα'' : |-α| ≤ Real.pi / 2 := by rwa [abs_neg]
    have hA : ‖aKer f α v‖ ≤ C / Real.cosh v ^ 2 := by
      unfold aKer
      rw [norm_div, Complex.norm_two]
      have := norm_add_le (lapShift f α v) (lapShift f (-α) v)
      linarith [hb α hα' v, hb (-α) hα'' v]
    have hD := norm_dKer_le hx.le hα' v
    have hc := Real.cosh_pos v
    rw [norm_mul]
    calc ‖aKer f α v‖ * ‖dKer x α v‖ ≤ C / Real.cosh v ^ 2 * (x * Real.cosh v) :=
          mul_le_mul hA hD (norm_nonneg _) (by positivity)
      _ = C * x * (1 / Real.cosh v) := by field_simp
  · have hc : Continuous (fun α : ℝ => aKer f α v * dKer x α v) := by
      have h1 := continuous_lapShift_right hf v
      have h2 : Continuous (fun α : ℝ => lapShift f (-α) v) := h1.comp continuous_neg
      have h3 : Continuous (fun α : ℝ => dKer x α v) := by
        unfold dKer dShift shiftKer; fun_prop
      exact ((h1.add h2).div_const 2).mul h3
    exact (hc.tendsto (Real.pi / 2)).mono_left (nhdsWithin_le_nhds (s := Iio (Real.pi / 2)))

/-! ## The kernels on the boundary line -/

theorem cosh_add_pi_div_two_mul_I (v : ℝ) :
    Complex.cosh ((v : ℂ) + ((Real.pi / 2 : ℝ) : ℂ) * I) = Real.sinh v * I := by
  rw [Complex.cosh_add, Complex.cosh_mul_I, Complex.sinh_mul_I, ← Complex.ofReal_cos,
    ← Complex.ofReal_sin, Real.cos_pi_div_two, Real.sin_pi_div_two, ← Complex.ofReal_sinh]
  push_cast; ring

theorem sinh_add_pi_div_two_mul_I (v : ℝ) :
    Complex.sinh ((v : ℂ) + ((Real.pi / 2 : ℝ) : ℂ) * I) = Real.cosh v * I := by
  rw [Complex.sinh_add, Complex.cosh_mul_I, Complex.sinh_mul_I, ← Complex.ofReal_cos,
    ← Complex.ofReal_sin, Real.cos_pi_div_two, Real.sin_pi_div_two, ← Complex.ofReal_cosh]
  push_cast; ring

theorem shiftKer_pi_div_two (t v : ℝ) :
    shiftKer t (Real.pi / 2) v = cexp (((-(t * Real.sinh v) : ℝ) : ℂ) * I) := by
  unfold shiftKer
  rw [cosh_add_pi_div_two_mul_I]
  push_cast; ring_nf

theorem shiftKer_neg_pi_div_two (t v : ℝ) :
    shiftKer t (-(Real.pi / 2)) v = cexp (((t * Real.sinh v : ℝ) : ℂ) * I) := by
  rw [shiftKer_neg, shiftKer_pi_div_two, Real.sinh_neg]
  congr 2; push_cast; ring

theorem dShift_pi_div_two (x v : ℝ) :
    dShift x (Real.pi / 2) v =
      -((x * Real.cosh v : ℝ) : ℂ) * I * cexp (((-(x * Real.sinh v) : ℝ) : ℂ) * I) := by
  unfold dShift
  rw [sinh_add_pi_div_two_mul_I, shiftKer_pi_div_two]
  push_cast; ring

theorem dShift_neg_pi_div_two (x v : ℝ) :
    dShift x (-(Real.pi / 2)) v =
      ((x * Real.cosh v : ℝ) : ℂ) * I * cexp (((x * Real.sinh v : ℝ) : ℂ) * I) := by
  have h := dShift_neg x (-(Real.pi / 2)) (-v)
  rw [neg_neg, neg_neg] at h
  rw [h, dShift_pi_div_two, Real.cosh_neg, Real.sinh_neg, mul_neg, neg_neg]
  ring

theorem lapShift_pi_div_two (f : ℝ → ℂ) (v : ℝ) :
    lapShift f (Real.pi / 2) v = 𝓕 f (Real.sinh v / (2 * Real.pi)) := by
  rw [lapShift, Real.fourier_real_eq_integral_exp_smul]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  simp only [smul_eq_mul]
  rw [shiftKer_pi_div_two, mul_comm]
  congr 2
  push_cast
  field_simp

theorem lapShift_neg_pi_div_two (f : ℝ → ℂ) (v : ℝ) :
    lapShift f (-(Real.pi / 2)) v = 𝓕 f (-(Real.sinh v / (2 * Real.pi))) := by
  rw [lapShift, Real.fourier_real_eq_integral_exp_smul]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  simp only [smul_eq_mul]
  rw [shiftKer_neg_pi_div_two, mul_comm]
  congr 2
  push_cast
  field_simp

/-! ## Evaluation on the boundary line -/

theorem integrable_fourier_of_isKLTest (hf : IsKLTest f) : Integrable (𝓕 f) := by
  set S := hf.hasCompactSupport.toSchwartzMap hf.smooth
  have h : 𝓕 f = ⇑(𝓕 S : SchwartzMap ℝ ℂ) := by rw [SchwartzMap.fourier_coe]; rfl
  rw [h]
  exact (𝓕 S : SchwartzMap ℝ ℂ).integrable

/-- `E_y(w) = e^{2πiwy}`. -/
def expChar (y w : ℝ) : ℂ := cexp (((2 * Real.pi * w * y : ℝ) : ℂ) * I)

theorem norm_expChar (y w : ℝ) : ‖expChar y w‖ = 1 := Complex.norm_exp_ofReal_mul_I _

theorem continuous_expChar (y : ℝ) : Continuous (expChar y) := by unfold expChar; fun_prop

/-- **Fourier inversion** for test functions: `∫ 𝓕f(w) e^{2πiwy} dw = f(y)`. -/
theorem integral_fourier_mul_expChar (hf : IsKLTest f) (y : ℝ) :
    ∫ w : ℝ, 𝓕 f w * expChar y w = f y := by
  have hinv := Continuous.fourierInv_fourier_eq hf.continuous hf.integrable
    (integrable_fourier_of_isKLTest hf)
  have h := congrFun hinv y
  rw [Real.fourierInv_eq_fourier_neg, Real.fourier_real_eq_integral_exp_smul] at h
  rw [← h]
  congr 1; funext w
  simp only [smul_eq_mul, expChar]
  rw [mul_comm]
  congr 3
  push_cast; ring

theorem integrable_fourier_mul_expChar (hf : IsKLTest f) (y : ℝ) :
    Integrable (fun w : ℝ => 𝓕 f w * expChar y w) :=
  (integrable_fourier_of_isKLTest hf).norm.mono'
    ((integrable_fourier_of_isKLTest hf).1.mul (continuous_expChar y).aestronglyMeasurable)
    (Eventually.of_forall fun w => by rw [norm_mul, norm_expChar, mul_one])

theorem integrable_fourier_neg_mul_expChar (hf : IsKLTest f) (y : ℝ) :
    Integrable (fun w : ℝ => 𝓕 f (-w) * expChar y w) := by
  have h := (integrable_fourier_mul_expChar hf (-y)).comp_neg
  refine h.congr (Eventually.of_forall fun w => ?_)
  simp only [expChar]
  congr 3; push_cast; ring

theorem integral_fourier_neg_mul_expChar (hf : IsKLTest f) (y : ℝ) :
    ∫ w : ℝ, 𝓕 f (-w) * expChar y w = f (-y) := by
  rw [← integral_fourier_mul_expChar hf (-y), ← integral_neg_eq_self]
  congr 1; funext w
  simp only [neg_neg, expChar]
  congr 3; push_cast; ring

/-- **The boundary pairing** `∫ A D = −iπ x f(x)`. -/
theorem integral_aKer_mul_dKer_pi_div_two (hf : IsKLTest f) {x : ℝ} (hx : 0 < x) :
    ∫ v : ℝ, aKer f (Real.pi / 2) v * dKer x (Real.pi / 2) v = -(I * Real.pi * x * f x) := by
  have hfx : f (-x) = 0 := image_eq_zero_of_notMem_tsupport fun h =>
    absurd (hf.tsupport_subset h) (by simp only [mem_Ioi, Left.neg_pos_iff, not_lt]; exact hx.le)
  set G : ℝ → ℂ := fun s => -(I * x / 4) *
    ((𝓕 f (s / (2 * Real.pi)) + 𝓕 f (-(s / (2 * Real.pi)))) *
      (cexp (((-(x * s)) : ℝ) * I) + cexp (((x * s : ℝ) : ℂ) * I)))
  have hpt : ∀ v : ℝ, aKer f (Real.pi / 2) v * dKer x (Real.pi / 2) v =
      (Real.cosh v : ℂ) * G (Real.sinh v) := fun v => by
    simp only [aKer, dKer, G]
    rw [lapShift_pi_div_two, lapShift_neg_pi_div_two, dShift_pi_div_two, dShift_neg_pi_div_two]
    push_cast
    ring
  simp_rw [hpt]
  -- the substitution `s = sinh v`
  have hsub : ∫ v : ℝ, (Real.cosh v : ℂ) * G (Real.sinh v) = ∫ s : ℝ, G s := by
    have h := integral_image_eq_integral_abs_deriv_smul (s := univ) (f := Real.sinh)
      (f' := Real.cosh) MeasurableSet.univ (fun v _ => (Real.hasDerivAt_sinh v).hasDerivWithinAt)
      Real.sinh_injective.injOn G
    rw [image_univ, Real.sinh_surjective.range_eq, setIntegral_univ, setIntegral_univ] at h
    rw [h]
    congr 1; funext v
    rw [abs_of_pos (Real.cosh_pos v), Complex.real_smul]
  rw [hsub]
  -- the substitution `s = 2πw`
  have hscale : ∫ s : ℝ, G s = 2 * Real.pi * ∫ w : ℝ, G (2 * Real.pi * w) := by
    rw [Measure.integral_comp_mul_left G (2 * Real.pi),
      abs_of_pos (inv_pos.2 (by positivity : (0 : ℝ) < 2 * Real.pi)), Complex.real_smul]
    have hπ : (2 * Real.pi : ℂ) ≠ 0 := by exact_mod_cast (by positivity : (2 * Real.pi) ≠ 0)
    push_cast
    field_simp
  rw [hscale]
  have hG : ∀ w : ℝ, G (2 * Real.pi * w) = -(I * x / 4) *
      (𝓕 f w * expChar (-x) w + 𝓕 f w * expChar x w + 𝓕 f (-w) * expChar (-x) w +
        𝓕 f (-w) * expChar x w) := fun w => by
    have h2π : (2 * Real.pi * w) / (2 * Real.pi) = w := by field_simp
    simp only [G, expChar]
    rw [h2π]
    have e1 : (((-(x * (2 * Real.pi * w))) : ℝ) : ℂ) = ((2 * Real.pi * w * -x : ℝ) : ℂ) := by
      push_cast; ring
    have e2 : (((x * (2 * Real.pi * w)) : ℝ) : ℂ) = ((2 * Real.pi * w * x : ℝ) : ℂ) := by
      push_cast; ring
    rw [e1, e2]
    ring
  simp_rw [hG]
  have i1 := integrable_fourier_mul_expChar hf (-x)
  have i2 := integrable_fourier_mul_expChar hf x
  have i3 := integrable_fourier_neg_mul_expChar hf (-x)
  have i4 := integrable_fourier_neg_mul_expChar hf x
  have i12 : Integrable (fun w : ℝ => 𝓕 f w * expChar (-x) w + 𝓕 f w * expChar x w) := i1.add i2
  have i123 : Integrable (fun w : ℝ => 𝓕 f w * expChar (-x) w + 𝓕 f w * expChar x w +
      𝓕 f (-w) * expChar (-x) w) := i12.add i3
  rw [integral_const_mul, integral_add i123 i4, integral_add i12 i3, integral_add i1 i2,
    integral_fourier_mul_expChar hf, integral_fourier_mul_expChar hf,
    integral_fourier_neg_mul_expChar hf, integral_fourier_neg_mul_expChar hf, neg_neg, hfx]
  ring

/-! ## The inversion formula -/

/-- **Kontorovich–Lebedev inversion**: for a smooth `f` with compact support in `(0, ∞)` and `x > 0`,
`∫_ℝ y sinh(πy) K_{iy}(x) g(y) dy = π² x f(x)` with `g(y) = ∫ f(t) K_{iy}(t) dt`. -/
theorem kontorovichLebedev_inversion (hf : IsKLTest f) {x : ℝ} (hx : 0 < x) :
    ∫ y : ℝ, (y : ℂ) * Real.sinh (Real.pi * y) * kIm x y * klTransform f y =
      (Real.pi : ℂ) ^ 2 * x * f x := by
  have hspec := tendsto_integral_spectral hf hx
  have hker := (tendsto_integral_kernel hf hx).const_mul (I * Real.pi)
  have hev : (fun α : ℝ => I * Real.pi * ∫ v : ℝ, aKer f α v * dKer x α v) =ᶠ[𝓝[<] (Real.pi / 2)]
      fun α => ∫ y : ℝ, (y : ℂ) * Real.sinh (2 * α * y) * kIm x y * klTransform f y := by
    filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < Real.pi / 2 by positivity)] with α hα
    have hα' : |α| < Real.pi / 2 := by rw [abs_of_pos hα.1]; exact hα.2
    exact (integral_sinh_kIm_klTransform hf hx hα').symm
  have := tendsto_nhds_unique (hker.congr' hev) hspec
  rw [← this, integral_aKer_mul_dKer_pi_div_two hf hx]
  ring_nf
  rw [Complex.I_sq]
  ring

end

end GaloisForLFunctions.RHTower.KontorovichLebedev
