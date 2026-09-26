import GaloisForLFunctions.RHTower.ThetaPowerFamily
import GaloisForLFunctions.RHTower.StripSourceHardyTransfer

/-!
# Hardy's theorem for the theta-power family below the cusp-order wall

For `0 < a < 1/2` the form `F_a = θ₃ h^{a/4}` vanishes at the cusp `1` (cusp order `m = 2a - 1 < 0`).
Its axis transform `Λ_a(u) = ∫ e^{-iux} T_a(x) dx`, `T_a(x) = e^{x/2} F_a(ie^{2x})/2`, has real zeros
beyond every height.

The proof is a short Hardy argument that uses only the inversion law and the cusp values:

* the complex tail `T_a(z) = e^{z/2} F_a(ie^{2z})/2` is holomorphic, even and real on the strip
  `|Im z| < π/4` and decays in the real direction (cusp decay at the rate `πa/4`);
* on the imaginary axis `T_a(iy)` stays bounded as `y → π/4`, because `ie^{2iy}` runs along the unit
  circle into the cusp `±1`, where `|F_a| ≍ |v|^{1/2} e^{-(1-2a)π Im v/4}` by the window law;
* if `Λ_a` kept one sign on a half-line, the strip transfer would bound `T_a` on the whole strip,
  i.e. `|F_a(p)| ≤ B |p|^{-1/4}` on the upper half-plane;
* but `τ_k = -1/(i + 2k)` has `|τ_k|^{1/4} |F_a(τ_k)| = |i + 2k|^{1/4} |F_a(i)| → ∞` by the inversion
  law and the two-periodicity of `|F_a|`.

The axis bound is exactly where `a < 1/2` enters: at `a = 1/2` the form has a nonzero value at the
cusp `1`, the axis values blow up like the transferred bound, and the argument stops.
-/

open Complex MeasureTheory Filter Topology Set
open scoped Real FourierTransform

namespace RHTower

noncomputable section

open Bottcher

/-! ## Strip decay at a general cusp rate -/

section Rate

variable {F : ℂ → ℂ} {M r : ℝ}

theorem norm_chargeTailC_le_cusp_rate (hr : 0 < r)
    (hS : ∀ τ : ℂ, 0 < τ.im → F (-1 / τ) = (-Complex.I * τ) ^ (1 / 2 : ℂ) * F τ)
    (hdec : ∀ τ : ℂ, 1 ≤ τ.im → ‖F τ‖ ≤ M * Real.exp (-r * τ.im))
    {β : ℝ} (hβ : β < π / 4) {z : ℂ} (hz : |z.im| ≤ β) :
    (1 ≤ Real.exp (2 * z.re) * Real.cos (2 * β) →
      ‖chargeTailC F z‖ ≤ M / 2 * Real.exp (z.re / 2) *
        Real.exp (-r * (Real.exp (2 * z.re) * Real.cos (2 * β)))) ∧
    (1 ≤ Real.exp (-2 * z.re) * Real.cos (2 * β) →
      ‖chargeTailC F z‖ ≤ M / 2 * Real.exp (-z.re / 2) *
        Real.exp (-r * (Real.exp (-2 * z.re) * Real.cos (2 * β)))) := by
  have hcos := cos_two_le_of_abs_le hβ hz
  have hM : 0 ≤ M := by
    have h := hdec Complex.I (by simp)
    have h1 : (0:ℝ) ≤ M * Real.exp (-r * Complex.I.im) := le_trans (norm_nonneg _) h
    exact nonneg_of_mul_nonneg_left h1 (Real.exp_pos _)
  constructor
  · intro h1
    have him : Real.exp (2 * z.re) * Real.cos (2 * β) ≤ (Complex.I * Complex.exp (2 * z)).im := by
      rw [im_I_mul_cexp_two_mul]
      exact mul_le_mul_of_nonneg_left hcos (Real.exp_pos _).le
    have hb := hdec _ (le_trans h1 him)
    have hb' : ‖F (Complex.I * Complex.exp (2 * z))‖ ≤
        M * Real.exp (-r * (Real.exp (2 * z.re) * Real.cos (2 * β))) := by
      refine le_trans hb (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hM)
      nlinarith
    unfold chargeTailC
    rw [norm_div, norm_mul, norm_cexp_half, Complex.norm_ofNat]
    have := mul_le_mul_of_nonneg_left hb' (Real.exp_pos (z.re / 2)).le
    nlinarith [this]
  · intro h1
    have him : Real.exp (-2 * z.re) * Real.cos (2 * β) ≤
        (Complex.I * Complex.exp (-2 * z)).im := by
      rw [show -2 * z = 2 * (-z) by ring, im_I_mul_cexp_two_mul]
      simp only [Complex.neg_re, Complex.neg_im, mul_neg]
      rw [Real.cos_neg, show -(2 * z.re) = -2 * z.re by ring]
      exact mul_le_mul_of_nonneg_left hcos (Real.exp_pos _).le
    have hpos : 0 < (Complex.I * Complex.exp (-2 * z)).im :=
      lt_of_lt_of_le one_pos (le_trans h1 him)
    have hrefl := hS _ hpos
    rw [neg_one_div_I_mul_cexp] at hrefl
    have hb := hdec _ (le_trans h1 him)
    have hb' : ‖F (Complex.I * Complex.exp (-2 * z))‖ ≤
        M * Real.exp (-r * (Real.exp (-2 * z.re) * Real.cos (2 * β))) := by
      refine le_trans hb (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hM)
      nlinarith
    unfold chargeTailC
    rw [hrefl, norm_div, norm_mul, norm_mul, norm_cexp_half, norm_cpow_half_cexp_neg,
      Complex.norm_ofNat]
    have hx : Real.exp (z.re / 2) * Real.exp (-z.re) = Real.exp (-z.re / 2) := by
      rw [← Real.exp_add]; congr 1; ring
    have := mul_le_mul_of_nonneg_left hb' (Real.exp_pos (-z.re / 2)).le
    calc Real.exp (z.re / 2) * (Real.exp (-z.re) * ‖F (Complex.I * Complex.exp (-2 * z))‖) / 2
        = Real.exp (-z.re / 2) * ‖F (Complex.I * Complex.exp (-2 * z))‖ / 2 := by
          rw [← hx]; ring
      _ ≤ M / 2 * Real.exp (-z.re / 2) *
          Real.exp (-r * (Real.exp (-2 * z.re) * Real.cos (2 * β))) := by nlinarith [this]

theorem exp_half_mul_exp_neg_rate_le {x κ : ℝ} (hr : 0 < r) (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (h1 : 1 ≤ Real.exp (2 * x) * κ) :
    Real.exp (x / 2) * Real.exp (-r * (Real.exp (2 * x) * κ)) ≤ 1 / (r * κ) * Real.exp (-x) := by
  have hx0 : 0 ≤ x := by
    by_contra hneg
    push Not at hneg
    have : Real.exp (2 * x) < 1 := by
      rw [← Real.exp_zero]; exact Real.exp_lt_exp.mpr (by linarith)
    nlinarith
  have hle : Real.exp (x / 2) * Real.exp x ≤ Real.exp (2 * x) := by
    rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by linarith)
  have hexpY : r * (Real.exp (2 * x) * κ) ≤ Real.exp (r * (Real.exp (2 * x) * κ)) := by
    have := Real.add_one_le_exp (r * (Real.exp (2 * x) * κ)); linarith
  have hkey : Real.exp (x / 2) * Real.exp x * Real.exp (-r * (Real.exp (2 * x) * κ)) ≤
      1 / (r * κ) := by
    rw [show -r * (Real.exp (2 * x) * κ) = -(r * (Real.exp (2 * x) * κ)) by ring, Real.exp_neg]
    rw [mul_inv_le_iff₀ (Real.exp_pos _)]
    calc Real.exp (x / 2) * Real.exp x ≤ Real.exp (2 * x) := hle
      _ = 1 / (r * κ) * (r * (Real.exp (2 * x) * κ)) := by field_simp
      _ ≤ 1 / (r * κ) * Real.exp (r * (Real.exp (2 * x) * κ)) :=
          mul_le_mul_of_nonneg_left hexpY (by positivity)
  have hex : Real.exp x * Real.exp (-x) = 1 := by rw [← Real.exp_add]; simp
  have hm := mul_le_mul_of_nonneg_right hkey (Real.exp_pos (-x)).le
  calc Real.exp (x / 2) * Real.exp (-r * (Real.exp (2 * x) * κ))
      = Real.exp (x / 2) * Real.exp (-r * (Real.exp (2 * x) * κ)) *
          (Real.exp x * Real.exp (-x)) := by rw [hex, mul_one]
    _ = Real.exp (x / 2) * Real.exp x * Real.exp (-r * (Real.exp (2 * x) * κ)) *
          Real.exp (-x) := by ring
    _ ≤ 1 / (r * κ) * Real.exp (-x) := hm

/-- Existential decay of the complex tail on every closed substrip, at a general cusp rate. -/
theorem exists_norm_chargeTailC_le_rate (hr : 0 < r) (hF : DifferentiableOn ℂ F modUpperSet)
    (hS : ∀ τ : ℂ, 0 < τ.im → F (-1 / τ) = (-Complex.I * τ) ^ (1 / 2 : ℂ) * F τ)
    (hdec : ∀ τ : ℂ, 1 ≤ τ.im → ‖F τ‖ ≤ M * Real.exp (-r * τ.im))
    {β : ℝ} (hβ0 : 0 ≤ β) (hβ : β < π / 4) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, |z.im| ≤ β → ‖chargeTailC F z‖ ≤ C * Real.exp (-|z.re|) := by
  have hM : 0 ≤ M := by
    have h := hdec Complex.I (by simp)
    have h1 : (0:ℝ) ≤ M * Real.exp (-r * Complex.I.im) := le_trans (norm_nonneg _) h
    exact nonneg_of_mul_nonneg_left h1 (Real.exp_pos _)
  set κ := Real.cos (2 * β) with hκ
  have hκpos : 0 < κ := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith⟩
  have hκ1 : κ ≤ 1 := Real.cos_le_one _
  set X₀ : ℝ := Real.log (1 / κ) / 2 with hX₀
  set K : Set ℂ := {z : ℂ | |z.re| ≤ X₀ ∧ |z.im| ≤ β} with hK
  have hKc : IsCompact K := by
    have : K = (fun z : ℂ => (z.re, z.im)) ⁻¹' (Set.Icc (-X₀) X₀ ×ˢ Set.Icc (-β) β) := by
      ext z; simp [hK, abs_le]; tauto
    rw [this]
    exact (Complex.equivRealProdCLM.toHomeomorph.isCompact_preimage).mpr
      ((isCompact_Icc).prod isCompact_Icc)
  obtain ⟨B, hB⟩ := hKc.exists_bound_of_continuousOn
    ((continuousOn_chargeTailC hF hβ).mono (fun z hz => hz.2))
  set B' : ℝ := max B 0 with hB'
  refine ⟨max (B' * Real.exp X₀) (M / 2 * (1 / (r * κ))), le_max_of_le_left (by positivity), ?_⟩
  intro z hz
  obtain ⟨hA, hBc⟩ := norm_chargeTailC_le_cusp_rate hr hS hdec hβ hz
  by_cases h1 : 1 ≤ Real.exp (2 * z.re) * κ
  · have hx0 : 0 ≤ z.re := by
      by_contra hneg; push Not at hneg
      have : Real.exp (2 * z.re) < 1 := by
        rw [← Real.exp_zero]; exact Real.exp_lt_exp.mpr (by linarith)
      nlinarith
    have := hA h1
    have hkey := exp_half_mul_exp_neg_rate_le hr hκpos hκ1 h1
    rw [abs_of_nonneg hx0]
    calc ‖chargeTailC F z‖ ≤ M / 2 * (Real.exp (z.re / 2) *
          Real.exp (-r * (Real.exp (2 * z.re) * κ))) := by rw [← mul_assoc]; exact this
      _ ≤ M / 2 * (1 / (r * κ) * Real.exp (-z.re)) :=
          mul_le_mul_of_nonneg_left hkey (by positivity)
      _ ≤ max (B' * Real.exp X₀) (M / 2 * (1 / (r * κ))) * Real.exp (-z.re) := by
          rw [← mul_assoc]
          exact mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le
  by_cases h2 : 1 ≤ Real.exp (-2 * z.re) * κ
  · have hx0 : z.re ≤ 0 := by
      by_contra hneg; push Not at hneg
      have : Real.exp (-2 * z.re) < 1 := by
        rw [← Real.exp_zero]; exact Real.exp_lt_exp.mpr (by linarith)
      nlinarith
    have := hBc h2
    have hkey := exp_half_mul_exp_neg_rate_le (x := -z.re) hr hκpos hκ1
      (by rw [show 2 * -z.re = -2 * z.re by ring]; exact h2)
    rw [abs_of_nonpos hx0]
    calc ‖chargeTailC F z‖ ≤ M / 2 * (Real.exp (-z.re / 2) *
          Real.exp (-r * (Real.exp (-2 * z.re) * κ))) := by rw [← mul_assoc]; exact this
      _ = M / 2 * (Real.exp (-z.re / 2) *
          Real.exp (-r * (Real.exp (2 * -z.re) * κ))) := by ring_nf
      _ ≤ M / 2 * (1 / (r * κ) * Real.exp (- -z.re)) :=
          mul_le_mul_of_nonneg_left hkey (by positivity)
      _ ≤ max (B' * Real.exp X₀) (M / 2 * (1 / (r * κ))) * Real.exp (- -z.re) := by
          rw [← mul_assoc]
          exact mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le
  · push Not at h1 h2
    have hlog : Real.log (1 / κ) = -Real.log κ := by rw [one_div, Real.log_inv]
    have hre : |z.re| ≤ X₀ := by
      rw [abs_le]
      have hl1 : 2 * z.re + Real.log κ < 0 := by
        have := Real.log_lt_log (by positivity) h1
        rw [Real.log_mul (Real.exp_pos _).ne' hκpos.ne', Real.log_exp, Real.log_one] at this
        exact this
      have hl2 : -2 * z.re + Real.log κ < 0 := by
        have := Real.log_lt_log (by positivity) h2
        rw [Real.log_mul (Real.exp_pos _).ne' hκpos.ne', Real.log_exp, Real.log_one] at this
        exact this
      rw [hX₀, hlog]
      constructor <;> linarith
    have hbd := hB z ⟨hre, hz⟩
    have hexp : 1 ≤ Real.exp X₀ * Real.exp (-|z.re|) := by
      rw [← Real.exp_add]; exact Real.one_le_exp (by linarith)
    calc ‖chargeTailC F z‖ ≤ B' := le_trans hbd (le_max_left _ _)
      _ ≤ B' * (Real.exp X₀ * Real.exp (-|z.re|)) := le_mul_of_one_le_right (le_max_right _ _) hexp
      _ = B' * Real.exp X₀ * Real.exp (-|z.re|) := by ring
      _ ≤ max (B' * Real.exp X₀) (M / 2 * (1 / (r * κ))) * Real.exp (-|z.re|) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le

/-- The complex tail of a form with the theta inversion law is even on the strip. -/
theorem chargeTailC_neg_of_inversion
    (hS : ∀ τ : ℂ, 0 < τ.im → F (-1 / τ) = (-Complex.I * τ) ^ (1 / 2 : ℂ) * F τ)
    {z : ℂ} (hz : |z.im| < π / 4) : chargeTailC F (-z) = chargeTailC F z := by
  have hp := im_I_mul_cexp_pos hz
  have hinv : Complex.I * Complex.exp (2 * -z) = -1 / (Complex.I * Complex.exp (2 * z)) := by
    have h := neg_one_div_I_mul_cexp (-z)
    rw [show -2 * -z = 2 * z by ring] at h
    rw [h]
  have hroot : (-Complex.I * (Complex.I * Complex.exp (2 * z))) ^ (1 / 2 : ℂ) = Complex.exp z := by
    have e : -Complex.I * (Complex.I * Complex.exp (2 * z)) = Complex.exp (2 * z) := by
      rw [← mul_assoc, neg_mul, Complex.I_mul_I]; ring
    rw [e, Complex.cpow_def_of_ne_zero (Complex.exp_ne_zero _), Complex.log_exp]
    · congr 1; ring
    · have := neg_abs_le z.im
      simp only [Complex.mul_im, Complex.re_ofNat, Complex.im_ofNat, zero_mul, add_zero]
      nlinarith [Real.pi_pos]
    · have := le_abs_self z.im
      simp only [Complex.mul_im, Complex.re_ofNat, Complex.im_ofNat, zero_mul, add_zero]
      nlinarith [Real.pi_pos]
  unfold chargeTailC
  rw [hinv, hS _ hp, hroot]
  have e2 : Complex.exp (-z / 2) * Complex.exp z = Complex.exp (z / 2) := by
    rw [← Complex.exp_add]; congr 1; ring
  rw [← e2]
  ring

end Rate

/-! ## The complex tail of `F_a` on the strip -/

section Family

variable {a : ℝ}

/-- The axis transform `Λ_a(u) = ∫ e^{-iux} T_a(x) dx` of `F_a`. -/
def thetaPowerXi (a : ℝ) (u : ℝ) : ℂ :=
  ∫ x : ℝ, Complex.exp (-Complex.I * u * x) * modTail (thetaPowerForm a) 0 x

theorem thetaPowerForm_inversion (a : ℝ) :
    ∀ τ : ℂ, 0 < τ.im →
      thetaPowerForm a (-1 / τ) = (-Complex.I * τ) ^ (1 / 2 : ℂ) * thetaPowerForm a τ :=
  fun _ hτ => thetaPowerForm_S a hτ

theorem thetaPowerForm_cuspDecay (ha : 0 ≤ a) :
    ∀ τ : ℂ, 1 ≤ τ.im →
      ‖thetaPowerForm a τ‖ ≤ thetaPowerCuspConstant a * Real.exp (-(π * a / 4) * τ.im) :=
  fun _ hτ => norm_thetaPowerForm_le_cusp ha hτ

theorem thetaPowerTail_holo (a : ℝ) :
    ∀ z : ℂ, |z.im| < π / 4 → DifferentiableAt ℂ (chargeTailC (thetaPowerForm a)) z :=
  fun _ hz => differentiableAt_chargeTailC (differentiableOn_thetaPowerForm a) hz

theorem thetaPowerTail_decay (ha : 0 < a) :
    ∀ β : ℝ, 0 ≤ β → β < π / 4 → ∃ C : ℝ, 0 ≤ C ∧
      ∀ z : ℂ, |z.im| ≤ β → ‖chargeTailC (thetaPowerForm a) z‖ ≤ C * Real.exp (-|z.re|) :=
  fun _ hβ0 hβ => exists_norm_chargeTailC_le_rate (r := π * a / 4) (by positivity)
    (differentiableOn_thetaPowerForm a) (thetaPowerForm_inversion a)
    (thetaPowerForm_cuspDecay ha.le) hβ0 hβ

theorem thetaPowerTail_even (a : ℝ) :
    ∀ z : ℂ, |z.im| < π / 4 →
      chargeTailC (thetaPowerForm a) (-z) = chargeTailC (thetaPowerForm a) z :=
  fun _ hz => chargeTailC_neg_of_inversion (thetaPowerForm_inversion a) hz

theorem thetaPowerTail_real (a : ℝ) :
    ∀ x : ℝ, (chargeTailC (thetaPowerForm a) (x : ℂ)).im = 0 := by
  intro x
  rw [chargeTailC_ofReal]
  unfold modTail modAxisPoint
  rw [sub_zero, thetaPowerForm_I_mul_real a (Real.exp_pos (2 * x))]
  simp only [← Complex.ofReal_mul, Complex.div_ofNat_im, Complex.ofReal_im, zero_div]

theorem fourier_thetaPowerTail (a : ℝ) (w : ℝ) :
    𝓕 (fun x : ℝ => chargeTailC (thetaPowerForm a) (x : ℂ)) w = thetaPowerXi a (2 * π * w) := by
  rw [fourier_real_eq_integral_exp]
  unfold thetaPowerXi
  refine integral_congr_ae ?_
  filter_upwards with v
  rw [chargeTailC_ofReal]
  congr 2
  push_cast
  ring

/-! ## The axis values stay bounded below the wall -/

theorem exp_neg_le_inv {x : ℝ} (hx : 0 < x) : Real.exp (-x) ≤ 1 / x := by
  rw [Real.exp_neg, inv_eq_one_div]
  exact one_div_le_one_div_of_le hx (by linarith [Real.add_one_le_exp x])

theorem thetaPowerForm_window_norm_le {a : ℝ} (ha0 : 0 ≤ a) {v : ℂ} (hv : 5 + 480 * (1 + a) ≤ v.im)
    (hre : v.re = 1 / 2) :
    ‖thetaPowerForm a (1 + -1 / v)‖ ≤
      9 / 8 * (2 : ℝ) ^ (1 - 2 * a) * (2 * v.im) * Real.exp (-((1 - 2 * a) * π / 4 * v.im)) := by
  have hv4 : 4 < v.im := by nlinarith
  have hv1 : 1 ≤ v.im := by linarith
  rw [thetaPowerForm_window a hv4]
  have herr : ‖powerChargeErr a v‖ ≤ 1 / 8 := by
    have hx : 0 < π / 2 * v.im := by positivity
    have he : Real.exp (-(π / 2 * v.im)) ≤ 1 / v.im := by
      refine (exp_neg_le_inv hx).trans ?_
      apply one_div_le_one_div_of_le (by linarith)
      nlinarith [Real.pi_gt_three]
    have hsm : 60 * (1 + a) * Real.exp (-(π / 2 * v.im)) ≤ 1 / 8 := by
      have h1 : 60 * (1 + a) * Real.exp (-(π / 2 * v.im)) ≤ 60 * (1 + a) * (1 / v.im) :=
        mul_le_mul_of_nonneg_left he (by positivity)
      have h2 : 60 * (1 + a) * (1 / v.im) ≤ 1 / 8 := by
        rw [mul_one_div, div_le_iff₀ (by linarith)]; nlinarith
      linarith
    exact (norm_powerChargeErr_le ha0 hv4.le (by linarith)).trans hsm
  have hcpow : ‖(-Complex.I * v) ^ (1 / 2 : ℂ)‖ = ‖v‖ ^ (1 / 2 : ℝ) := by
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring, Complex.norm_cpow_real,
      norm_mul, norm_neg, Complex.norm_I, one_mul]
  have hnv : ‖v‖ ≤ 2 * v.im := by
    have := Complex.norm_le_abs_re_add_abs_im v
    rw [hre, abs_of_pos (by linarith : (0:ℝ) < v.im)] at this
    norm_num at this; linarith
  have hsq : ‖v‖ ^ (1 / 2 : ℝ) ≤ 2 * v.im := by
    have h1 : ‖v‖ ^ (1 / 2 : ℝ) ≤ (2 * v.im) ^ (1 / 2 : ℝ) :=
      Real.rpow_le_rpow (norm_nonneg _) hnv (by norm_num)
    have h2 : (2 * v.im) ^ (1 / 2 : ℝ) ≤ (2 * v.im) ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
    rw [Real.rpow_one] at h2
    linarith
  have hphase : ‖Complex.exp (π * Complex.I * a / 4)‖ = 1 := by
    rw [Complex.norm_exp]; simp [Complex.mul_re]
  have hexp : ‖Complex.exp ((1 - 2 * a) * π * Complex.I * v / 4)‖ =
      Real.exp (-((1 - 2 * a) * π / 4 * v.im)) := by
    rw [Complex.norm_exp]; congr 1
    simp [Complex.mul_re, Complex.mul_im]; ring
  have h1e : ‖(1 : ℂ) + powerChargeErr a v‖ ≤ 9 / 8 := by
    have := norm_add_le (1 : ℂ) (powerChargeErr a v); rw [norm_one] at this; linarith
  rw [norm_mul, norm_mul, norm_mul, norm_mul, hphase, hcpow, Complex.norm_real,
    Real.norm_of_nonneg (by positivity), hexp, one_mul]
  have hE := Real.exp_pos (-((1 - 2 * a) * π / 4 * v.im))
  have h2p : 0 < (2 : ℝ) ^ (1 - 2 * a) := by positivity
  calc ‖v‖ ^ (1 / 2 : ℝ) * (2 : ℝ) ^ (1 - 2 * a) * Real.exp (-((1 - 2 * a) * π / 4 * v.im)) *
        ‖(1 : ℂ) + powerChargeErr a v‖
      ≤ (2 * v.im) * (2 : ℝ) ^ (1 - 2 * a) * Real.exp (-((1 - 2 * a) * π / 4 * v.im)) * (9 / 8) := by
        gcongr
    _ = 9 / 8 * (2 : ℝ) ^ (1 - 2 * a) * (2 * v.im) * Real.exp (-((1 - 2 * a) * π / 4 * v.im)) := by
        ring

/-- **`F_a` is bounded on the quarter of the unit circle when `a < 1/2`.** -/
theorem exists_bound_thetaPowerForm_arc {a : ℝ} (ha0 : 0 ≤ a) (ha : a < 1 / 2) :
    ∃ B : ℝ, ∀ p : ℂ, ‖p‖ = 1 → 0 ≤ p.re → 0 < p.im → ‖thetaPowerForm a p‖ ≤ B := by
  set Y₀ : ℝ := 5 + 480 * (1 + a) with hY₀
  have hY₀pos : 0 < Y₀ := by positivity
  set δ : ℝ := 1 / (2 * Y₀) with hδ
  have hδpos : 0 < δ := by positivity
  set K : Set ℂ := Metric.closedBall (0 : ℂ) 1 ∩ {p : ℂ | δ ≤ p.im} with hK
  have hKc : IsCompact K :=
    (isCompact_closedBall 0 1).inter_right (isClosed_le continuous_const Complex.continuous_im)
  have hKsub : K ⊆ modUpperSet := fun p hp => by
    show 0 < p.im; exact lt_of_lt_of_le hδpos hp.2
  obtain ⟨BK, hBK⟩ := hKc.exists_bound_of_continuousOn
    ((differentiableOn_thetaPowerForm a).continuousOn.mono hKsub)
  set c : ℝ := (1 - 2 * a) * π / 4 with hc
  have hcpos : 0 < c := by rw [hc]; have := Real.pi_pos; nlinarith
  refine ⟨max BK (9 / 8 * (2 : ℝ) ^ (1 - 2 * a) * (2 / c)), fun p hp1 hre him => ?_⟩
  by_cases hbig : δ ≤ p.im
  · refine (hBK p ⟨?_, hbig⟩).trans (le_max_left _ _)
    rw [Metric.mem_closedBall, dist_zero_right, hp1]
  · push Not at hbig
    have hsq : p.re ^ 2 + p.im ^ 2 = 1 := by
      have h := Complex.normSq_eq_norm_sq p
      rw [Complex.normSq_apply, hp1] at h; nlinarith
    have hre1 : p.re < 1 := by nlinarith
    have hone : 1 - p.re ≤ p.im ^ 2 := by nlinarith
    have hne : (1 : ℂ) - p ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith
    set v : ℂ := 1 / (1 - p) with hvdef
    have hN : Complex.normSq (1 - p) = 2 * (1 - p.re) := by
      rw [Complex.normSq_apply]; simp; nlinarith
    have hvre : v.re = 1 / 2 := by
      have h1 : (1 - p.re) ≠ 0 := by linarith
      rw [hvdef, one_div, Complex.inv_re, hN]; simp
      field_simp
    have hvim : v.im = p.im / (2 * (1 - p.re)) := by
      rw [hvdef, one_div, Complex.inv_im, hN]; simp
    have hvimge : 1 / (2 * p.im) ≤ v.im := by
      rw [hvim, div_le_div_iff₀ (by positivity) (by linarith)]
      nlinarith
    have hvY : Y₀ ≤ v.im := by
      refine le_trans ?_ hvimge
      rw [hδ] at hbig
      rw [le_div_iff₀ (by positivity)]
      rw [lt_div_iff₀ (by positivity)] at hbig
      linarith
    have hpv : 1 + -1 / v = p := by
      rw [hvdef]; field_simp; ring
    have hw := thetaPowerForm_window_norm_le ha0 (v := v) (by rw [← hY₀]; exact hvY) hvre
    rw [hpv] at hw
    refine hw.trans (le_trans ?_ (le_max_right _ _))
    have hYexp : v.im * Real.exp (-(c * v.im)) ≤ 1 / c := by
      have h := Real.add_one_le_exp (c * v.im)
      have hE := Real.exp_pos (c * v.im)
      rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ hE, one_div_mul_eq_div, le_div_iff₀ hcpos]
      nlinarith
    have e : Real.exp (-((1 - 2 * a) * π / 4 * v.im)) = Real.exp (-(c * v.im)) := by rw [hc]
    rw [e]
    have h2p : 0 < (2 : ℝ) ^ (1 - 2 * a) := by positivity
    calc 9 / 8 * (2 : ℝ) ^ (1 - 2 * a) * (2 * v.im) * Real.exp (-(c * v.im))
        = 9 / 8 * (2 : ℝ) ^ (1 - 2 * a) * 2 * (v.im * Real.exp (-(c * v.im))) := by ring
      _ ≤ 9 / 8 * (2 : ℝ) ^ (1 - 2 * a) * 2 * (1 / c) := by gcongr
      _ = 9 / 8 * (2 : ℝ) ^ (1 - 2 * a) * (2 / c) := by ring

/-- **Axis bound.**  Below the wall the complex tail stays bounded on the imaginary axis. -/
theorem exists_axis_bound_thetaPowerTail {a : ℝ} (ha0 : 0 ≤ a) (ha : a < 1 / 2) :
    ∃ B₁ : ℝ, ∀ y : ℝ, 0 ≤ y → y < π / 4 →
      ‖chargeTailC (thetaPowerForm a) ((y : ℂ) * Complex.I)‖ ≤ B₁ := by
  obtain ⟨B, hB⟩ := exists_bound_thetaPowerForm_arc ha0 ha
  refine ⟨B / 2, fun y hy0 hy => ?_⟩
  have hmem : |((y : ℂ) * Complex.I).im| < π / 4 := by
    simp; rw [abs_of_nonneg hy0]; exact hy
  rw [← thetaPowerTail_even a _ hmem]
  set p : ℂ := Complex.I * Complex.exp (2 * -((y : ℂ) * Complex.I)) with hp
  have hpval : p = ((Real.sin (2 * y) : ℝ) : ℂ) + ((Real.cos (2 * y) : ℝ) : ℂ) * Complex.I := by
    rw [hp, show 2 * -((y : ℂ) * Complex.I) = ((-(2 * y) : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.exp_mul_I]
    rw [← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg, Real.sin_neg]
    push_cast
    ring_nf
    rw [Complex.I_sq]
    ring
  have hre : p.re = Real.sin (2 * y) := by
    rw [hpval, Complex.add_re, Complex.ofReal_re, Complex.re_ofReal_mul, Complex.I_re, mul_zero,
      add_zero]
  have him : p.im = Real.cos (2 * y) := by
    rw [hpval, Complex.add_im, Complex.ofReal_im, Complex.im_ofReal_mul, Complex.I_im, mul_one,
      zero_add]
  have h2y : 2 * y < π / 2 := by linarith
  have hsin : 0 ≤ Real.sin (2 * y) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [Real.pi_pos])
  have hcos : 0 < Real.cos (2 * y) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], h2y⟩
  have hnorm : ‖p‖ = 1 := by
    have h := Complex.normSq_eq_norm_sq p
    rw [Complex.normSq_apply, hre, him] at h
    have h1 : Real.sin (2 * y) * Real.sin (2 * y) + Real.cos (2 * y) * Real.cos (2 * y) = 1 := by
      nlinarith [Real.sin_sq_add_cos_sq (2 * y)]
    rw [h1] at h
    have := norm_nonneg p
    nlinarith
  have hbd := hB p hnorm (by rw [hre]; exact hsin) (by rw [him]; exact hcos)
  unfold chargeTailC
  rw [← hp, norm_div, norm_mul, norm_cexp_half, Complex.norm_ofNat]
  have hre0 : (-((y : ℂ) * Complex.I)).re = 0 := by simp
  rw [hre0, zero_div, Real.exp_zero, one_mul]
  linarith

/-! ## The modular growth of the tail -/

theorem norm_thetaPowerForm_I_add_two_mul (a : ℝ) (k : ℕ) :
    ‖thetaPowerForm a (Complex.I + 2 * k)‖ = ‖thetaPowerForm a Complex.I‖ := by
  induction k with
  | zero => simp
  | succ k ih =>
    have him : 0 < (Complex.I + 2 * (k : ℂ)).im := by simp
    rw [show Complex.I + 2 * ((k + 1 : ℕ) : ℂ) = (Complex.I + 2 * k) + 2 by push_cast; ring,
      norm_thetaPowerForm_add_two a him, ih]

/-- The strip point over `p` in the upper half-plane. -/
def stripPointOver (p : ℂ) : ℂ := Complex.log (-Complex.I * p) / 2

theorem stripPointOver_im {p : ℂ} (hp : 0 < p.im) : |(stripPointOver p).im| < π / 4 := by
  have hre : 0 < (-Complex.I * p).re := by simp [Complex.mul_re]; exact hp
  have harg := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hre)
  unfold stripPointOver
  rw [Complex.div_ofNat_im, Complex.log_im, abs_div, abs_two]
  linarith

theorem norm_chargeTailC_stripPointOver {F : ℂ → ℂ} {p : ℂ} (hp : 0 < p.im) :
    ‖chargeTailC F (stripPointOver p)‖ = ‖p‖ ^ (1 / 4 : ℝ) * ‖F p‖ / 2 := by
  have hne : -Complex.I * p ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp [Complex.mul_re] at this; linarith
  have hpt : Complex.I * Complex.exp (2 * stripPointOver p) = p := by
    unfold stripPointOver
    rw [show 2 * (Complex.log (-Complex.I * p) / 2) = Complex.log (-Complex.I * p) by ring,
      Complex.exp_log hne, ← mul_assoc, mul_neg, Complex.I_mul_I]
    ring
  unfold chargeTailC
  rw [hpt, norm_div, norm_mul, norm_cexp_half, Complex.norm_ofNat]
  have hre : (stripPointOver p).re = Real.log ‖p‖ / 2 := by
    unfold stripPointOver
    rw [Complex.div_ofNat_re, Complex.log_re, norm_mul, norm_neg, Complex.norm_I, one_mul]
  rw [hre]
  have hpn : 0 < ‖p‖ := norm_pos_iff.mpr (fun h => by rw [h] at hp; simp at hp)
  rw [Real.rpow_def_of_pos hpn]
  congr 2
  ring_nf

/-- **The complex tail of a nonzero `F_a` is unbounded on the strip.** -/
theorem thetaPowerTail_unbounded (a : ℝ) :
    ∀ M : ℝ, ∃ z : ℂ, |z.im| < π / 4 ∧ M < ‖chargeTailC (thetaPowerForm a) z‖ := by
  intro M
  set c : ℝ := ‖thetaPowerForm a Complex.I‖ with hc
  have hcpos : 0 < c := norm_pos_iff.mpr (thetaPowerForm_ne_zero a (by simp))
  set X : ℝ := 2 * |M| / c + 1 with hX
  have hX1 : 1 ≤ X := by
    have : 0 ≤ 2 * |M| / c := by positivity
    rw [hX]; linarith
  obtain ⟨k, hk⟩ := exists_nat_ge (X ^ 4)
  set σ : ℂ := Complex.I + 2 * (k : ℂ) with hσ
  have hσim : 0 < σ.im := by simp [hσ]
  have hσne : σ ≠ 0 := fun h => by rw [h] at hσim; simp at hσim
  set τ : ℂ := -1 / σ with hτ
  have hτim : 0 < τ.im := neg_one_div_im_pos hσim
  refine ⟨stripPointOver τ, stripPointOver_im hτim, ?_⟩
  rw [norm_chargeTailC_stripPointOver hτim]
  have hFτ : ‖thetaPowerForm a τ‖ = ‖σ‖ ^ (1 / 2 : ℝ) * c := by
    rw [hτ, thetaPowerForm_S a hσim, norm_mul, hσ, norm_thetaPowerForm_I_add_two_mul, ← hσ, ← hc,
      show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring, Complex.norm_cpow_real, norm_mul,
      norm_neg, Complex.norm_I, one_mul]
  have hσn : 0 < ‖σ‖ := norm_pos_iff.mpr hσne
  have hτn : ‖τ‖ = ‖σ‖⁻¹ := by rw [hτ, norm_div, norm_neg, norm_one, one_div]
  rw [hFτ, hτn]
  have hsplit : ‖σ‖⁻¹ ^ (1 / 4 : ℝ) * (‖σ‖ ^ (1 / 2 : ℝ) * c) / 2 = ‖σ‖ ^ (1 / 4 : ℝ) * c / 2 := by
    rw [Real.inv_rpow hσn.le, show (1 / 2 : ℝ) = 1 / 4 + 1 / 4 by norm_num,
      Real.rpow_add hσn]
    have : 0 < ‖σ‖ ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos hσn _
    field_simp
  rw [hsplit]
  have hσk : (k : ℝ) ≤ ‖σ‖ := by
    have h := Complex.abs_re_le_norm σ
    have hre : σ.re = 2 * k := by simp [hσ]
    rw [hre, abs_of_nonneg (by positivity)] at h
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith
  have hX4 : X ^ 4 ≤ ‖σ‖ := le_trans hk hσk
  have hroot : X ≤ ‖σ‖ ^ (1 / 4 : ℝ) := by
    have h := Real.rpow_le_rpow (by positivity) hX4 (by norm_num : (0:ℝ) ≤ 1 / 4)
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)] at h
    norm_num at h
    exact h
  have hM : M ≤ |M| := le_abs_self M
  have hXc : 2 * |M| < X * c := by
    rw [hX, add_mul, div_mul_cancel₀ _ hcpos.ne']; linarith
  have := mul_le_mul_of_nonneg_right hroot hcpos.le
  linarith

/-! ## Hardy's theorem for `0 < a < 1/2` -/

/-- **Hardy's theorem below the cusp-order wall.**  For `0 < a < 1/2` the axis transform of
`F_a = θ₃ h^{a/4}` has real zeros beyond every height. -/
theorem thetaPowerXi_exists_zero_ge {a : ℝ} (ha0 : 0 < a) (ha : a < 1 / 2) (U : ℝ) :
    ∃ u : ℝ, U ≤ u ∧ thetaPowerXi a u = 0 := by
  obtain ⟨B₁, hax⟩ := exists_axis_bound_thetaPowerTail ha0.le ha
  obtain ⟨w, hw, h0⟩ := exists_fourier_zero_ge_of_strip_unbounded (T := chargeTailC (thetaPowerForm a))
    (c₀ := π / 4) (thetaPowerTail_holo a) (thetaPowerTail_decay ha0) (thetaPowerTail_even a)
    (thetaPowerTail_real a) (by positivity) hax (thetaPowerTail_unbounded a) (U / (2 * π))
  refine ⟨2 * π * w, ?_, ?_⟩
  · have hπ : 0 < 2 * π := by positivity
    rw [div_le_iff₀ hπ] at hw; linarith
  · rw [← fourier_thetaPowerTail]; exact h0

theorem thetaPowerXi_real_zeros_infinite {a : ℝ} (ha0 : 0 < a) (ha : a < 1 / 2) :
    {u : ℝ | thetaPowerXi a u = 0}.Infinite := by
  apply Set.infinite_of_not_bddAbove
  rintro ⟨U, hU⟩
  obtain ⟨u, hu, h0⟩ := thetaPowerXi_exists_zero_ge ha0 ha (U + 1)
  have := hU h0
  linarith

end Family

end

end RHTower
