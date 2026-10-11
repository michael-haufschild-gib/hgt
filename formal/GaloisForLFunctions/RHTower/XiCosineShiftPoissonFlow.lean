import GaloisForLFunctions.RHTower.XiCosineShiftSechHandoff
import GaloisForLFunctions.RHTower.WeilPrimeFreeTest

/-!
# The Poisson flow of the cosine producer

For depths `0 ≤ h < H` the producer at depth `h` is a positive smoothing of the producer at depth
`H`:

  `A_h(t) = ∫ P_{h,H}(t − v) A_H(v) dv`,   `P_{h,H}(w) = (1/(2H)) Re sech(π(w + ih)/(2H))`

(`cosProducer_eq_integral_poissonPort_mul`). The kernel is positive (`poissonPort_pos`), has unit
mass, and its Fourier transform is `cosh(hu)/cosh(Hu)` (`integral_poissonPort_mul_cexp`). At `h = 0`
it is the sech port `κ_H` of `XiCosineShiftSechHandoff`.

With `H = ½`, every producer `A_h`, `0 ≤ h < ½`, including `A_0 = Ξ`, is the Poisson average of the
horizon producer `A_½(v) = Re ξ(1 + iv)`. That function is Laguerre–Pólya unconditionally. The PTR
family is therefore one positive flow out of the horizon line, and RH says the flow never trades a
real zero for a conjugate pair.

**Proof.**
* `cosh(hu)/cosh(Hu) ≤ 1/cosh((H − h)u)` because `cosh(Hu) ≥ cosh((H − h)u) cosh(hu)`, so the
  multiplier is integrable.
* Its Fourier transform splits along `cosh(hu) = (e^{hu} + e^{−hu})/2`. The substitution `u = s/H`
  and `∫ e^{−izs}/cosh s ds = π/cosh(πz/2)` with `z = (ω ± ih)/H`, `|Im z| < 1`, give the two sech
  terms.
* Fourier inversion recovers the multiplier as the transform of the kernel. Fubini, as in the sech
  handoff, finishes.
-/

open Complex MeasureTheory Filter Topology Set
open GaloisForLFunctions.HTGeometry
open scoped FourierTransform

namespace RHTower

noncomputable section

/-! ## The multiplier `cosh(hu)/cosh(Hu)` -/

/-- `m_{h,H}(u) = cosh(hu)/cosh(Hu)`. -/
def poissonMultiplier (h H u : ℝ) : ℝ := Real.cosh (h * u) / Real.cosh (H * u)

theorem poissonMultiplier_pos (h H u : ℝ) : 0 < poissonMultiplier h H u :=
  div_pos (Real.cosh_pos _) (Real.cosh_pos _)

theorem continuous_poissonMultiplier (h H : ℝ) : Continuous (poissonMultiplier h H) := by
  unfold poissonMultiplier
  exact (Real.continuous_cosh.comp (by fun_prop)).div (Real.continuous_cosh.comp (by fun_prop))
    (fun u => (Real.cosh_pos _).ne')

theorem cosh_mul_cosh_le_cosh {a b : ℝ} (hab : 0 ≤ a * b) :
    Real.cosh a * Real.cosh b ≤ Real.cosh (a + b) := by
  rw [Real.cosh_add]
  have : 0 ≤ Real.sinh a * Real.sinh b := by
    rcases le_total 0 a with ha | ha <;> rcases le_total 0 b with hb | hb
    · exact mul_nonneg (Real.sinh_nonneg_iff.mpr ha) (Real.sinh_nonneg_iff.mpr hb)
    · rcases eq_or_lt_of_le ha with h0 | h0
      · rw [← h0, Real.sinh_zero, zero_mul]
      · have : b = 0 := by nlinarith
        rw [this, Real.sinh_zero, mul_zero]
    · rcases eq_or_lt_of_le hb with h0 | h0
      · rw [← h0, Real.sinh_zero, mul_zero]
      · have : a = 0 := by nlinarith
        rw [this, Real.sinh_zero, zero_mul]
    · exact mul_nonneg_of_nonpos_of_nonpos (Real.sinh_nonpos_iff.mpr ha) (Real.sinh_nonpos_iff.mpr hb)
  linarith

theorem poissonMultiplier_le {h H : ℝ} (hh : 0 ≤ h) (hhH : h ≤ H) (u : ℝ) :
    poissonMultiplier h H u ≤ 1 / Real.cosh ((H - h) * u) := by
  unfold poissonMultiplier
  have hc := Real.cosh_pos ((H - h) * u)
  have hc' := Real.cosh_pos (H * u)
  rw [div_le_div_iff₀ hc' hc, one_mul]
  have key := cosh_mul_cosh_le_cosh (a := (H - h) * u) (b := h * u)
    (by nlinarith [sq_nonneg u, mul_nonneg (sub_nonneg.mpr hhH) hh])
  rw [show (H - h) * u + h * u = H * u by ring] at key
  linarith [mul_comm (Real.cosh (h * u)) (Real.cosh ((H - h) * u))]

theorem integrable_one_div_cosh_mul {c : ℝ} (hc : 0 < c) :
    Integrable (fun u : ℝ => 1 / Real.cosh (c * u)) := by
  have hmaj : Integrable (fun u : ℝ => 2 * (1 + (c * u) ^ 2)⁻¹) :=
    (integrable_inv_one_add_sq.comp_mul_left' hc.ne').const_mul 2
  refine hmaj.mono' ((continuous_const.div (Real.continuous_cosh.comp (by fun_prop))
    (fun u => (Real.cosh_pos _).ne')).aestronglyMeasurable) (Eventually.of_forall fun u => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr (Real.cosh_pos _))]
  exact inv_cosh_le _

theorem integrable_poissonMultiplier {h H : ℝ} (hh : 0 ≤ h) (hhH : h < H) :
    Integrable (fun u => (poissonMultiplier h H u : ℂ)) := by
  refine ((integrable_one_div_cosh_mul (sub_pos.mpr hhH)).ofReal).mono'
    ((Complex.continuous_ofReal.comp (continuous_poissonMultiplier h H)).aestronglyMeasurable)
    (Eventually.of_forall fun u => ?_)
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (poissonMultiplier_pos h H u)]
  exact poissonMultiplier_le hh hhH.le u

/-! ## The complex secant -/

theorem re_cosh_add_mul_I (x y : ℝ) :
    (Complex.cosh ((x : ℂ) + (y : ℂ) * I)).re = Real.cosh x * Real.cos y := by
  rw [Complex.cosh_add, Complex.cosh_mul_I, Complex.sinh_mul_I]
  simp [Complex.mul_re, Complex.cosh_ofReal_re, Complex.cos_ofReal_re, Complex.cosh_ofReal_im,
    Complex.cos_ofReal_im, Complex.sinh_ofReal_re, Complex.sinh_ofReal_im, Complex.sin_ofReal_re,
    Complex.sin_ofReal_im]

/-- `‖cosh(x + iy)‖ ≥ cosh x · cos y`. -/
theorem cosh_mul_cos_le_norm_cosh (x y : ℝ) :
    Real.cosh x * Real.cos y ≤ ‖Complex.cosh ((x : ℂ) + (y : ℂ) * I)‖ := by
  rw [← re_cosh_add_mul_I]
  exact (le_abs_self _).trans (Complex.abs_re_le_norm _)

theorem norm_inv_cosh_le {x y : ℝ} (hy : 0 < Real.cos y) :
    ‖1 / Complex.cosh ((x : ℂ) + (y : ℂ) * I)‖ ≤ 1 / (Real.cos y * Real.cosh x) := by
  have hpos : 0 < Real.cosh x * Real.cos y := mul_pos (Real.cosh_pos x) hy
  have hle := cosh_mul_cos_le_norm_cosh x y
  have h1 : 1 / ‖Complex.cosh ((x : ℂ) + (y : ℂ) * I)‖ ≤ 1 / (Real.cosh x * Real.cos y) :=
    one_div_le_one_div_of_le hpos hle
  rw [norm_div, norm_one]
  rwa [mul_comm (Real.cos y)]

/-! ## The Fourier transform of the multiplier -/

/-- `∫ e^{−iωv} e^{±hv}/cosh(Hv) dv = (π/H)/cosh(π(ω ± ih)/(2H))`. -/
theorem integral_cexp_mul_exp_div_cosh {h H : ℝ} (hH : 0 < H) (hhH : |h| < H) (ω : ℝ) :
    ∫ v : ℝ, Complex.exp (-(I * (ω : ℂ)) * (v : ℂ)) * ((Real.exp (h * v) / Real.cosh (H * v) : ℝ) : ℂ) =
      ((Real.pi / H : ℝ) : ℂ) / Complex.cosh (Real.pi * (((ω : ℂ) + h * I) / H) / 2) := by
  set z : ℂ := ((ω : ℂ) + h * I) / H with hz
  have hzim : |z.im| < 1 := by
    have : z.im = h / H := by
      rw [hz, Complex.div_ofReal_im]; simp
    rw [this, abs_div, abs_of_pos hH, div_lt_one hH]; exact hhH
  have hint := integral_cexp_div_cosh hzim
  set g : ℝ → ℂ := fun v => Complex.exp (-(I * (ω : ℂ)) * (v : ℂ)) *
    ((Real.exp (h * v) / Real.cosh (H * v) : ℝ) : ℂ) with hg
  have hsub := Measure.integral_comp_mul_left g H⁻¹
  have hgs : ∀ s : ℝ, g (H⁻¹ * s) = Complex.exp (-(z * (s : ℂ)) * I) / (Real.cosh s : ℂ) := by
    intro s
    simp only [hg]
    have e1 : H * (H⁻¹ * s) = s := by field_simp
    rw [e1]
    push_cast
    have hH0 : (H : ℂ) ≠ 0 := by exact_mod_cast hH.ne'
    rw [div_eq_mul_inv, ← mul_assoc, ← Complex.exp_add]
    congr 2
    rw [hz]; field_simp; ring_nf; rw [I_sq]; ring
  simp_rw [hgs] at hsub
  rw [hint, inv_inv, abs_of_pos hH] at hsub
  have hH0 : (H : ℂ) ≠ 0 := by exact_mod_cast hH.ne'
  have key : ∫ v, g v = ((H : ℝ)⁻¹ : ℂ) * ((Real.pi : ℂ) / Complex.cosh (Real.pi * z / 2)) := by
    rw [hsub, Complex.real_smul, ← mul_assoc, inv_mul_cancel₀ hH0, one_mul]
  rw [key]
  push_cast
  field_simp

/-- **The Fourier transform of `cosh(hu)/cosh(Hu)`.** -/
theorem fourier_poissonMultiplier {h H : ℝ} (hh : 0 ≤ h) (hhH : h < H) (ξ : ℝ) :
    𝓕 (fun u => (poissonMultiplier h H u : ℂ)) ξ =
      ((Real.pi / (2 * H) : ℝ) : ℂ) *
        (1 / Complex.cosh (Real.pi * ((((2 * Real.pi * ξ : ℝ) : ℂ) + h * I) / H) / 2) +
          1 / Complex.cosh (Real.pi * ((((2 * Real.pi * ξ : ℝ) : ℂ) + (-h : ℝ) * I) / H) / 2)) := by
  have hH : 0 < H := lt_of_le_of_lt hh hhH
  rw [WeilDeletion.fourier_eq_integral_cexp]
  set ω : ℝ := 2 * Real.pi * ξ with hω
  have hsplit : ∀ v : ℝ, Complex.exp (-(I * (ω : ℂ)) * (v : ℂ)) * (poissonMultiplier h H v : ℂ) =
      (1 / 2 : ℂ) * (Complex.exp (-(I * (ω : ℂ)) * (v : ℂ)) *
        ((Real.exp (h * v) / Real.cosh (H * v) : ℝ) : ℂ)) +
      (1 / 2 : ℂ) * (Complex.exp (-(I * (ω : ℂ)) * (v : ℂ)) *
        ((Real.exp ((-h) * v) / Real.cosh (H * v) : ℝ) : ℂ)) := by
    intro v
    unfold poissonMultiplier
    rw [Real.cosh_eq (h * v)]
    push_cast
    ring_nf
  simp_rw [hsplit]
  have hintg : ∀ k : ℝ, |k| ≤ h → Integrable (fun v : ℝ =>
      Complex.exp (-(I * (ω : ℂ)) * (v : ℂ)) * ((Real.exp (k * v) / Real.cosh (H * v) : ℝ) : ℂ)) := by
    intro k hk
    have hmaj : Integrable (fun v : ℝ => 2 * (1 / Real.cosh ((H - h) * v))) :=
      (integrable_one_div_cosh_mul (sub_pos.mpr hhH)).const_mul 2
    refine hmaj.mono' (Continuous.aestronglyMeasurable (by
      refine (by fun_prop : Continuous fun v : ℝ => Complex.exp (-(I * (ω : ℂ)) * (v : ℂ))).mul
        (Complex.continuous_ofReal.comp ?_)
      exact (Real.continuous_exp.comp (by fun_prop)).div (Real.continuous_cosh.comp (by fun_prop))
        (fun v => (Real.cosh_pos _).ne'))) (Eventually.of_forall fun v => ?_)
    rw [norm_mul, Complex.norm_exp]
    have h1 : (-(I * (ω : ℂ)) * (v : ℂ)).re = 0 := by simp
    rw [h1, Real.exp_zero, one_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (div_pos (Real.exp_pos _) (Real.cosh_pos _))]
    have hexp : Real.exp (k * v) ≤ 2 * Real.cosh (h * v) := by
      rw [Real.cosh_eq]
      have : k * v ≤ |h * v| := by
        calc k * v ≤ |k * v| := le_abs_self _
          _ = |k| * |v| := abs_mul _ _
          _ ≤ h * |v| := mul_le_mul_of_nonneg_right hk (abs_nonneg _)
          _ = |h * v| := by rw [abs_mul, abs_of_nonneg hh]
      rcases le_total 0 (h * v) with hv | hv
      · rw [abs_of_nonneg hv] at this
        have := Real.exp_le_exp.mpr this
        linarith [Real.exp_pos (-(h * v))]
      · rw [abs_of_nonpos hv] at this
        have := Real.exp_le_exp.mpr this
        linarith [Real.exp_pos (h * v)]
    have hm := poissonMultiplier_le hh hhH.le v
    unfold poissonMultiplier at hm
    calc Real.exp (k * v) / Real.cosh (H * v) ≤ 2 * Real.cosh (h * v) / Real.cosh (H * v) :=
          div_le_div_of_nonneg_right hexp (Real.cosh_pos _).le
      _ = 2 * (Real.cosh (h * v) / Real.cosh (H * v)) := by ring
      _ ≤ 2 * (1 / Real.cosh ((H - h) * v)) := by gcongr
  rw [integral_add ((hintg h (by rw [abs_of_nonneg hh])).const_mul _)
    ((hintg (-h) (by rw [abs_neg, abs_of_nonneg hh])).const_mul _),
    integral_const_mul, integral_const_mul,
    integral_cexp_mul_exp_div_cosh hH (by rw [abs_of_nonneg hh]; exact hhH),
    integral_cexp_mul_exp_div_cosh hH (by rw [abs_neg, abs_of_nonneg hh]; exact hhH)]
  push_cast
  ring

/-! ## The Poisson port -/

/-- The Poisson port `P_{h,H}(w) = (1/(2H)) Re sech(π(w + ih)/(2H))`. -/
def poissonPort (h H w : ℝ) : ℝ :=
  1 / (2 * H) * (1 / Complex.cosh (Real.pi * (((w : ℂ) + h * I) / H) / 2)).re

theorem poissonArg_eq (h H w : ℝ) (hH : H ≠ 0) :
    (Real.pi : ℂ) * (((w : ℂ) + h * I) / H) / 2 =
      ((Real.pi * w / (2 * H) : ℝ) : ℂ) + ((Real.pi * h / (2 * H) : ℝ) : ℂ) * I := by
  have hH' : (H : ℂ) ≠ 0 := by exact_mod_cast hH
  push_cast; field_simp

theorem poissonPort_pos {h H : ℝ} (hh : 0 ≤ h) (hhH : h < H) (w : ℝ) : 0 < poissonPort h H w := by
  have hH : 0 < H := lt_of_le_of_lt hh hhH
  unfold poissonPort
  refine mul_pos (by positivity) ?_
  rw [poissonArg_eq h H w hH.ne']
  set c := Complex.cosh (((Real.pi * w / (2 * H) : ℝ) : ℂ) + ((Real.pi * h / (2 * H) : ℝ) : ℂ) * I)
  have hy : 0 < Real.cos (Real.pi * h / (2 * H)) := by
    apply Real.cos_pos_of_mem_Ioo
    constructor
    · have : 0 ≤ Real.pi * h / (2 * H) := by positivity
      linarith [Real.pi_pos]
    · rw [div_lt_iff₀ (by positivity)]
      nlinarith [Real.pi_pos]
  have hre : 0 < c.re := by
    rw [re_cosh_add_mul_I]; exact mul_pos (Real.cosh_pos _) hy
  have hc0 : c ≠ 0 := fun h0 => by rw [h0, Complex.zero_re] at hre; exact lt_irrefl _ hre
  rw [one_div, Complex.inv_re]
  exact div_pos hre (Complex.normSq_pos.mpr hc0)

theorem norm_poissonSech_le {h H : ℝ} (hh : 0 ≤ h) (hhH : h < H) (k w : ℝ) (hk : |k| ≤ h) :
    ‖1 / Complex.cosh (Real.pi * (((w : ℂ) + k * I) / H) / 2)‖ ≤
      1 / (Real.cos (Real.pi * h / (2 * H)) * Real.cosh (Real.pi * w / (2 * H))) := by
  have hH : 0 < H := lt_of_le_of_lt hh hhH
  rw [poissonArg_eq k H w hH.ne']
  have hyk : 0 < Real.cos (Real.pi * k / (2 * H)) := by
    apply Real.cos_pos_of_mem_Ioo
    have hk' : |Real.pi * k / (2 * H)| < Real.pi / 2 := by
      rw [abs_div, abs_mul, abs_of_pos Real.pi_pos, abs_of_pos (by positivity : (0 : ℝ) < 2 * H),
        div_lt_iff₀ (by positivity)]
      nlinarith [Real.pi_pos]
    exact ⟨by linarith [neg_abs_le (Real.pi * k / (2 * H))],
      lt_of_le_of_lt (le_abs_self _) hk'⟩
  have hcos : Real.cos (Real.pi * h / (2 * H)) ≤ Real.cos (Real.pi * k / (2 * H)) := by
    rw [← Real.cos_abs (Real.pi * k / (2 * H))]
    apply Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _)
    · have : Real.pi * h / (2 * H) ≤ Real.pi / 2 := by
        rw [div_le_iff₀ (by positivity)]; nlinarith [Real.pi_pos]
      linarith [Real.pi_pos]
    · rw [abs_div, abs_mul, abs_of_pos Real.pi_pos, abs_of_pos (by positivity : (0 : ℝ) < 2 * H)]
      gcongr
  have hyh : 0 < Real.cos (Real.pi * h / (2 * H)) := by
    apply Real.cos_pos_of_mem_Ioo
    constructor
    · have : 0 ≤ Real.pi * h / (2 * H) := by positivity
      linarith [Real.pi_pos]
    · rw [div_lt_iff₀ (by positivity)]; nlinarith [Real.pi_pos]
  refine (norm_inv_cosh_le hyk).trans ?_
  apply one_div_le_one_div_of_le (mul_pos hyh (Real.cosh_pos _))
  exact mul_le_mul_of_nonneg_right hcos (Real.cosh_pos _).le

/-- The transform of the multiplier, as the kernel: `𝓕m(ξ) = 2π P(2πξ)`. -/
theorem fourier_poissonMultiplier_eq_port {h H : ℝ} (hh : 0 ≤ h) (hhH : h < H) (ξ : ℝ) :
    𝓕 (fun u => (poissonMultiplier h H u : ℂ)) ξ =
      ((2 * Real.pi * poissonPort h H (2 * Real.pi * ξ) : ℝ) : ℂ) := by
  rw [fourier_poissonMultiplier hh hhH]
  set a : ℂ := 1 / Complex.cosh (Real.pi * ((((2 * Real.pi * ξ : ℝ) : ℂ) + h * I) / H) / 2) with ha
  have hconj : 1 / Complex.cosh (Real.pi * ((((2 * Real.pi * ξ : ℝ) : ℂ) + (-h : ℝ) * I) / H) / 2) =
      (starRingEnd ℂ) a := by
    rw [ha, map_div₀, map_one, ← Complex.cosh_conj]
    congr 2
    simp only [map_div₀, map_mul, map_add, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
    push_cast
    ring
  rw [hconj, Complex.add_conj]
  unfold poissonPort
  rw [← ha]
  push_cast
  have hH : (H : ℂ) ≠ 0 := by exact_mod_cast (lt_of_le_of_lt hh hhH).ne'
  field_simp

theorem integrable_poissonPort {h H : ℝ} (hh : 0 ≤ h) (hhH : h < H) :
    Integrable (poissonPort h H) := by
  have hH : 0 < H := lt_of_le_of_lt hh hhH
  have hmaj : Integrable (fun w : ℝ => 1 / (2 * H) *
      (1 / Real.cos (Real.pi * h / (2 * H)) * (1 / Real.cosh (Real.pi / (2 * H) * w)))) :=
    ((integrable_one_div_cosh_mul (by positivity)).const_mul _).const_mul _
  refine hmaj.mono' ?_ (Eventually.of_forall fun w => ?_)
  · refine Continuous.aestronglyMeasurable ?_
    unfold poissonPort
    refine continuous_const.mul (Complex.continuous_re.comp ?_)
    refine continuous_const.div (Complex.continuous_cosh.comp (by fun_prop)) fun w => ?_
    intro h0
    have := (poissonPort_pos hh hhH w)
    unfold poissonPort at this
    rw [h0, div_zero, Complex.zero_re, mul_zero] at this
    exact lt_irrefl _ this
  · rw [Real.norm_eq_abs, abs_of_pos (poissonPort_pos hh hhH w)]
    unfold poissonPort
    have hb := norm_poissonSech_le hh hhH h w (by rw [abs_of_nonneg hh])
    have hre := Complex.re_le_norm (1 / Complex.cosh (Real.pi * (((w : ℂ) + h * I) / H) / 2))
    have e : Real.pi / (2 * H) * w = Real.pi * w / (2 * H) := by ring
    rw [e]
    have hcpos : 0 < Real.cos (Real.pi * h / (2 * H)) := by
      apply Real.cos_pos_of_mem_Ioo
      constructor
      · have : 0 ≤ Real.pi * h / (2 * H) := by positivity
        linarith [Real.pi_pos]
      · rw [div_lt_iff₀ (by positivity)]; nlinarith [Real.pi_pos]
    have e2 : 1 / (Real.cos (Real.pi * h / (2 * H)) * Real.cosh (Real.pi * w / (2 * H))) =
        1 / Real.cos (Real.pi * h / (2 * H)) * (1 / Real.cosh (Real.pi * w / (2 * H))) := by
      rw [one_div_mul_one_div]
    rw [← e2]
    exact mul_le_mul_of_nonneg_left (hre.trans hb) (by positivity)

/-- **The kernel's Fourier transform:** `∫ P(w) e^{−iwu} dw = cosh(hu)/cosh(Hu)`. -/
theorem integral_poissonPort_mul_cexp {h H : ℝ} (hh : 0 ≤ h) (hhH : h < H) (u : ℝ) :
    ∫ w : ℝ, (poissonPort h H w : ℂ) * Complex.exp (-(I * (w : ℂ) * u)) =
      (poissonMultiplier h H u : ℂ) := by
  set G : ℝ → ℂ := fun u => (poissonMultiplier h H u : ℂ) with hG
  have hGc : Continuous G := Complex.continuous_ofReal.comp (continuous_poissonMultiplier h H)
  have hGi : Integrable G := integrable_poissonMultiplier hh hhH
  have hFG : Integrable (𝓕 G) := by
    have : 𝓕 G = fun ξ => ((2 * Real.pi * poissonPort h H (2 * Real.pi * ξ) : ℝ) : ℂ) := by
      funext ξ; exact fourier_poissonMultiplier_eq_port hh hhH ξ
    rw [this]
    refine Integrable.ofReal ?_
    exact ((integrable_poissonPort hh hhH).comp_mul_left' (by positivity)).const_mul _
  have hinv := Continuous.fourierInv_fourier_eq hGc hGi hFG
  have hu : 𝓕 (𝓕 G) u = G (-u) := by
    have h2 : 𝓕 (𝓕 G) u = 𝓕⁻ (𝓕 G) (-u) := by
      rw [Real.fourierInv_eq_fourier_neg, neg_neg]
    rw [h2, hinv]
  have hGeven : G (-u) = G u := by
    simp only [hG, poissonMultiplier, mul_neg, Real.cosh_neg]
  rw [hGeven] at hu
  show _ = G u
  rw [← hu, WeilDeletion.fourier_eq_integral_cexp]
  -- substitute `w = 2πξ`
  set F : ℝ → ℂ := fun w => (poissonPort h H w : ℂ) * Complex.exp (-(I * (w : ℂ) * u)) with hF
  have hsub := Measure.integral_comp_mul_left F (2 * Real.pi)
  have hFs : ∀ ξ : ℝ, F (2 * Real.pi * ξ) = (1 / (2 * Real.pi) : ℂ) *
      (Complex.exp ((-(I * ((2 * Real.pi * u : ℝ) : ℂ))) * (ξ : ℂ)) * 𝓕 G ξ) := by
    intro ξ
    simp only [hF]
    rw [fourier_poissonMultiplier_eq_port hh hhH ξ]
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    push_cast
    field_simp
  simp_rw [hFs, integral_const_mul] at hsub
  rw [abs_of_pos (by positivity : (0 : ℝ) < (2 * Real.pi)⁻¹)] at hsub
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hc : (1 / (2 * (Real.pi : ℂ))) ≠ 0 := one_div_ne_zero (mul_ne_zero two_ne_zero hpi)
  have hsub' : (1 / (2 * (Real.pi : ℂ))) * (∫ ξ : ℝ,
      Complex.exp ((-(I * ((2 * Real.pi * u : ℝ) : ℂ))) * (ξ : ℂ)) * 𝓕 G ξ) =
      (1 / (2 * (Real.pi : ℂ))) * ∫ w, F w := by
    rw [hsub, Complex.real_smul]; push_cast; ring
  have key := mul_left_cancel₀ hc hsub'
  show ∫ w, F w = _
  rw [← key]

/-- The Poisson port is a probability density. -/
theorem integral_poissonPort {h H : ℝ} (hh : 0 ≤ h) (hhH : h < H) :
    ∫ w : ℝ, poissonPort h H w = 1 := by
  have h0 := integral_poissonPort_mul_cexp hh hhH 0
  simp only [Complex.ofReal_zero, mul_zero, neg_zero, Complex.exp_zero, mul_one] at h0
  rw [integral_complex_ofReal] at h0
  have : poissonMultiplier h H 0 = 1 := by simp [poissonMultiplier]
  rw [this] at h0
  exact_mod_cast h0

/-! ## The flow -/

/-- **The Poisson flow of the cosine producer.** For `0 ≤ h < H` and real `t`,
`A_h(t) = ∫ P_{h,H}(t − v) A_H(v) dv`. -/
theorem cosProducer_eq_integral_poissonPort_mul {h H : ℝ} (hh : 0 ≤ h) (hhH : h < H) (t : ℝ) :
    cosProducer h t = ∫ v : ℝ, (poissonPort h H (t - v) : ℂ) * cosProducer H v := by
  set g : ℝ → ℝ := fun x => riemannKernelReal x * Real.cosh (H * x) with hg
  have hgk : DeBruijn.SuperExpKernel g := DeBruijn.riemannKernel_mul_cosh_superExp H
  have hA : ∀ v : ℝ, cosProducer H v = ∫ u : ℝ, (g u : ℂ) * Complex.exp (I * (v : ℂ) * u) := by
    intro v
    rw [cosProducer, ← DeBruijn.cosTransform_riemannKernel_mul_cosh]; rfl
  simp_rw [hA, ← integral_const_mul]
  have hint : Integrable (Function.uncurry fun (v u : ℝ) =>
      (poissonPort h H (t - v) : ℂ) * ((g u : ℂ) * Complex.exp (I * (v : ℂ) * u)))
      (volume.prod volume) := by
    have hprod : Integrable (fun p : ℝ × ℝ => poissonPort h H (t - p.1) * g p.2)
        (volume.prod volume) :=
      ((integrable_poissonPort hh hhH).comp_sub_left t).mul_prod
        (by simpa using hgk.integrable_mul_exp 0)
    refine hprod.mono' ?_ (Eventually.of_forall fun p => ?_)
    · refine Continuous.aestronglyMeasurable ?_
      have hPc : Continuous (poissonPort h H) := by
        refine continuous_iff_continuousAt.mpr fun w => ?_
        unfold poissonPort
        refine continuousAt_const.mul (Complex.continuous_re.continuousAt.comp ?_)
        refine continuousAt_const.div (Complex.continuous_cosh.continuousAt.comp
          (by fun_prop)) ?_
        intro h0
        have := poissonPort_pos hh hhH w
        unfold poissonPort at this
        rw [h0, div_zero, Complex.zero_re, mul_zero] at this
        exact lt_irrefl _ this
      exact (Complex.continuous_ofReal.comp (hPc.comp (continuous_const.sub continuous_fst))).mul
        ((Complex.continuous_ofReal.comp (hgk.continuous.comp continuous_snd)).mul (by fun_prop))
    · change ‖(poissonPort h H (t - p.1) : ℂ) * ((g p.2 : ℂ) * Complex.exp (I * (p.1 : ℂ) * p.2))‖ ≤
        poissonPort h H (t - p.1) * g p.2
      rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
        Real.norm_eq_abs, abs_of_pos (poissonPort_pos hh hhH _), abs_of_nonneg (hgk.nonneg _)]
      have : ‖Complex.exp (I * (p.1 : ℂ) * p.2)‖ = 1 := by
        rw [Complex.norm_exp]; simp
      rw [this, mul_one]
  rw [integral_integral_swap hint]
  have hinner : ∀ u : ℝ, ∫ v : ℝ, (poissonPort h H (t - v) : ℂ) * ((g u : ℂ) *
      Complex.exp (I * (v : ℂ) * u)) = (g u : ℂ) * (Complex.exp (I * (t : ℂ) * u) *
        (poissonMultiplier h H u : ℂ)) := by
    intro u
    have e : ∀ v : ℝ, (poissonPort h H (t - v) : ℂ) * ((g u : ℂ) * Complex.exp (I * (v : ℂ) * u)) =
        (g u : ℂ) * Complex.exp (I * (t : ℂ) * u) *
          ((poissonPort h H (t - v) : ℂ) * Complex.exp (-(I * ((t - v : ℝ) : ℂ) * u))) := by
      intro v
      have : Complex.exp (I * (v : ℂ) * u) = Complex.exp (I * (t : ℂ) * u) *
          Complex.exp (-(I * ((t - v : ℝ) : ℂ) * u)) := by
        rw [← Complex.exp_add]; congr 1; push_cast; ring
      rw [this]; ring
    simp_rw [e]
    rw [integral_const_mul]
    rw [integral_sub_left_eq_self (fun w : ℝ => (poissonPort h H w : ℂ) *
      Complex.exp (-(I * (w : ℂ) * u))) (μ := volume) t]
    rw [integral_poissonPort_mul_cexp hh hhH]
    ring
  simp_rw [hinner]
  rw [cosProducer, ← DeBruijn.cosTransform_riemannKernel_mul_cosh]
  unfold DeBruijn.cosTransform
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  have e : ((Real.cosh (H * u) : ℝ) : ℂ) * (poissonMultiplier h H u : ℂ) =
      ((Real.cosh (h * u) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul]; congr 1
    unfold poissonMultiplier
    field_simp [(Real.cosh_pos (H * u)).ne']
  show ((riemannKernelReal u * Real.cosh (h * u) : ℝ) : ℂ) * Complex.exp (I * (t : ℂ) * u) =
    ((riemannKernelReal u * Real.cosh (H * u) : ℝ) : ℂ) *
      (Complex.exp (I * (t : ℂ) * u) * (poissonMultiplier h H u : ℂ))
  rw [Complex.ofReal_mul, Complex.ofReal_mul]
  linear_combination (-((riemannKernelReal u : ℂ) * Complex.exp (I * (t : ℂ) * u))) * e

/-- **Every producer below the horizon is a Poisson average of the horizon producer.** For
`0 ≤ h < ½`, `cos(hD)Ξ(t) = ∫ P_{h,½}(t − v) Re ξ(1 + iv) dv`. -/
theorem cosProducer_eq_integral_poissonPort_mul_re_xi_one {h : ℝ} (hh : 0 ≤ h) (hh2 : h < 1 / 2)
    (t : ℝ) :
    cosProducer h t = ∫ v : ℝ, (poissonPort h (1 / 2) (t - v) : ℂ) * ((xi (1 + v * I)).re : ℂ) := by
  rw [cosProducer_eq_integral_poissonPort_mul hh hh2 t]
  refine integral_congr_ae (Eventually.of_forall fun v => ?_)
  simp only
  rw [cosProducer_ofReal]
  congr 4
  push_cast; ring

end

end RHTower
