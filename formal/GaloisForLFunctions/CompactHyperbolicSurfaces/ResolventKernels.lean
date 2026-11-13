import GaloisForLFunctions.CompactHyperbolicSurfaces.HorocyclicSlices
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# The resolvent kernels of the hyperbolic plane

For real `s > ½` put `ρ(w) = √(1 + w) − √w`, `F_s(w) = ρ(w)^{2s−1}/√(w(1 + w))` and

  `k_s(u) = (1/4π) ∫_{w > u} F_s(w) (w − u)^{−½} dw`,

the Green function `Q_{s−1}(1 + 2u)/2π` written as an inverse Abel transform.  Since
`ρ(sinh²(x/2)) = e^{−x/2}`, the substitution `w = sinh²(x/2)` turns `F_s(w) dw` into `e^{−(s−½)x} dx`,
and the arcsine integral `∫_{η²/4 < A} (A − η²/4)^{−½} dη = 2π` gives

  `𝒜k_s(τ) = e^{−(s−½)|τ|}/(2s − 1)`   (`abelL_resKernel`).

The kernels satisfy `k_s(u) ≤ C u^{−s}` and `k_s(u) ≤ C u^{−¼}` (`exists_resKernel_le_rpow_neg`,
`exists_resKernel_le_rpow_quarter`).
-/

open MeasureTheory Set Filter Real
open scoped ENNReal

namespace GaloisForLFunctions.CompactHyperbolicSurfaces

noncomputable section

/-- `ρ(w) = √(1 + w) − √w`. -/
def rho (w : ℝ) : ℝ := Real.sqrt (1 + w) - Real.sqrt w

theorem continuous_rho : Continuous rho := by unfold rho; fun_prop

theorem rho_eq_inv {w : ℝ} (hw : 0 ≤ w) : rho w = (Real.sqrt (1 + w) + Real.sqrt w)⁻¹ := by
  have h1 : 0 < Real.sqrt (1 + w) + Real.sqrt w :=
    add_pos_of_pos_of_nonneg (Real.sqrt_pos.mpr (by linarith)) (Real.sqrt_nonneg _)
  refine eq_inv_of_mul_eq_one_left ?_
  calc rho w * (Real.sqrt (1 + w) + Real.sqrt w) = Real.sqrt (1 + w) ^ 2 - Real.sqrt w ^ 2 := by
        rw [rho]; ring
    _ = 1 := by rw [Real.sq_sqrt (by linarith), Real.sq_sqrt hw]; ring

theorem rho_pos {w : ℝ} (hw : 0 ≤ w) : 0 < rho w := by
  rw [rho_eq_inv hw]
  exact inv_pos.mpr (add_pos_of_pos_of_nonneg (Real.sqrt_pos.mpr (by linarith)) (Real.sqrt_nonneg _))

theorem rho_le_inv_sqrt {w : ℝ} (hw : 0 ≤ w) : rho w ≤ (Real.sqrt (1 + w))⁻¹ := by
  rw [rho_eq_inv hw]
  exact inv_anti₀ (Real.sqrt_pos.mpr (by linarith)) (le_add_of_nonneg_right (Real.sqrt_nonneg _))

theorem rho_sinh_sq {x : ℝ} (hx : 0 ≤ x) : rho (Real.sinh (x / 2) ^ 2) = Real.exp (-(x / 2)) := by
  have hs : 0 ≤ Real.sinh (x / 2) := Real.sinh_nonneg_iff.mpr (by linarith)
  rw [rho, show 1 + Real.sinh (x / 2) ^ 2 = Real.cosh (x / 2) ^ 2 by rw [Real.cosh_sq]; ring,
    Real.sqrt_sq (Real.cosh_pos _).le, Real.sqrt_sq hs, Real.cosh_sub_sinh]

/-- The Green density `F_s(w) = ρ(w)^{2s−1}/√(w(1 + w))`. -/
def greenDensity (s w : ℝ) : ℝ := rho w ^ (2 * s - 1) / Real.sqrt (w * (1 + w))

theorem measurable_greenDensity (s : ℝ) : Measurable (greenDensity s) :=
  (continuous_rho.measurable.pow_const _).div (by fun_prop)

theorem greenDensity_nonneg (s : ℝ) {w : ℝ} (hw : 0 ≤ w) : 0 ≤ greenDensity s w :=
  div_nonneg (Real.rpow_nonneg (rho_pos hw).le _) (Real.sqrt_nonneg _)

theorem greenDensity_sinh_sq (s : ℝ) {x : ℝ} (hx : 0 < x) :
    greenDensity s (Real.sinh (x / 2) ^ 2) =
      Real.exp (-((s - 1 / 2) * x)) / (Real.sinh (x / 2) * Real.cosh (x / 2)) := by
  have hs : 0 < Real.sinh (x / 2) := Real.sinh_pos_iff.mpr (by linarith)
  rw [greenDensity, rho_sinh_sq hx.le, Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp,
    show Real.sinh (x / 2) ^ 2 * (1 + Real.sinh (x / 2) ^ 2) =
      (Real.sinh (x / 2) * Real.cosh (x / 2)) ^ 2 by rw [mul_pow, Real.cosh_sq]; ring,
    Real.sqrt_sq (mul_pos hs (Real.cosh_pos _)).le]
  congr 2; ring

/-- `F_s(w) ≤ w^{−½} (1 + w)^{−s}`. -/
theorem greenDensity_le {s : ℝ} (hs : 1 / 2 < s) {w : ℝ} (hw : 0 < w) :
    greenDensity s w ≤ w ^ (-(1 / 2 : ℝ)) * (1 + w) ^ (-s) := by
  have hw1 : 0 < 1 + w := by linarith
  have h1 : rho w ^ (2 * s - 1) ≤ (1 + w) ^ ((1 - 2 * s) / 2) := by
    calc rho w ^ (2 * s - 1) ≤ ((Real.sqrt (1 + w))⁻¹) ^ (2 * s - 1) :=
          Real.rpow_le_rpow (rho_pos hw.le).le (rho_le_inv_sqrt hw.le) (by linarith)
      _ = (1 + w) ^ ((1 - 2 * s) / 2) := by
          rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hw1.le, ← Real.rpow_mul hw1.le]; congr 1; ring
  rw [greenDensity, div_le_iff₀ (Real.sqrt_pos.mpr (mul_pos hw hw1)), Real.sqrt_mul hw.le,
    Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
  calc rho w ^ (2 * s - 1) ≤ (1 + w) ^ ((1 - 2 * s) / 2) := h1
    _ = w ^ (-(1 / 2 : ℝ)) * (1 + w) ^ (-s) * (w ^ (1 / 2 : ℝ) * (1 + w) ^ (1 / 2 : ℝ)) := by
        rw [show w ^ (-(1 / 2 : ℝ)) * (1 + w) ^ (-s) * (w ^ (1 / 2 : ℝ) * (1 + w) ^ (1 / 2 : ℝ)) =
          (w ^ (-(1 / 2 : ℝ)) * w ^ (1 / 2 : ℝ)) * ((1 + w) ^ (-s) * (1 + w) ^ (1 / 2 : ℝ)) by ring,
          ← Real.rpow_add hw, ← Real.rpow_add hw1]
        norm_num
        congr 1; ring

/-! ### Two integrals -/

/-- `∫_{w > sinh²(τ₀/2)} F_s(w) dw = e^{−(s−½)τ₀}/(s − ½)` for `τ₀ ≥ 0`. -/
theorem lintegral_greenDensity_Ioi {s : ℝ} (hs : 1 / 2 < s) {τ₀ : ℝ} (hτ₀ : 0 ≤ τ₀) :
    ∫⁻ w in Ioi (Real.sinh (τ₀ / 2) ^ 2), ENNReal.ofReal (greenDensity s w) =
      ENNReal.ofReal (Real.exp (-((s - 1 / 2) * τ₀)) / (s - 1 / 2)) := by
  set φ : ℝ → ℝ := fun x => Real.sinh (x / 2) ^ 2
  have hd : ∀ x ∈ Ioi τ₀, HasDerivWithinAt φ (Real.sinh (x / 2) * Real.cosh (x / 2)) (Ioi τ₀) x := by
    intro x _
    have := ((Real.hasDerivAt_sinh (x / 2)).comp x ((hasDerivAt_id x).div_const 2)).pow 2
    refine (this.congr_deriv ?_).hasDerivWithinAt
    simp; ring
  have hmono : StrictMonoOn φ (Ici 0) := by
    intro a ha b hb hab
    have h0 : 0 ≤ Real.sinh (a / 2) := Real.sinh_nonneg_iff.mpr (by have : (0:ℝ) ≤ a := ha; linarith)
    have h1 : Real.sinh (a / 2) < Real.sinh (b / 2) := Real.sinh_strictMono (by linarith)
    exact pow_lt_pow_left₀ h1 h0 two_ne_zero
  have hinj : InjOn φ (Ioi τ₀) :=
    (hmono.mono fun x (hx : τ₀ < x) => show (0:ℝ) ≤ x by linarith).injOn
  have himage : φ '' Ioi τ₀ = Ioi (Real.sinh (τ₀ / 2) ^ 2) := by
    ext w
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hmono (show (0:ℝ) ≤ τ₀ from hτ₀) (show (0:ℝ) ≤ x by have : τ₀ < x := hx; linarith) hx
    · intro hw
      have hw0 : 0 ≤ w := le_trans (sq_nonneg _) (le_of_lt hw)
      refine ⟨2 * Real.arsinh (Real.sqrt w), ?_, ?_⟩
      · have h0 : 0 ≤ Real.sinh (τ₀ / 2) := Real.sinh_nonneg_iff.mpr (by linarith)
        have h1 : Real.sinh (τ₀ / 2) < Real.sqrt w := by
          rw [← Real.sqrt_sq h0]; exact Real.sqrt_lt_sqrt (sq_nonneg _) hw
        have h2 : τ₀ / 2 < Real.arsinh (Real.sqrt w) := by
          rw [← Real.arsinh_sinh (τ₀ / 2)]; exact Real.arsinh_strictMono h1
        show τ₀ < 2 * Real.arsinh (Real.sqrt w)
        linarith
      · simp only [φ]
        rw [mul_div_cancel_left₀ _ two_ne_zero, Real.sinh_arsinh, Real.sq_sqrt hw0]
  rw [← himage, lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioi hd hinj]
  have hpt : ∀ x ∈ Ioi τ₀, ENNReal.ofReal |Real.sinh (x / 2) * Real.cosh (x / 2)| *
      ENNReal.ofReal (greenDensity s (φ x)) = ENNReal.ofReal (Real.exp ((-(s - 1 / 2)) * x)) := by
    intro x hx
    have hx0 : 0 < x := lt_of_le_of_lt hτ₀ hx
    have hpos : 0 < Real.sinh (x / 2) * Real.cosh (x / 2) :=
      mul_pos (Real.sinh_pos_iff.mpr (by linarith)) (Real.cosh_pos _)
    rw [← ENNReal.ofReal_mul (abs_nonneg _), abs_of_pos hpos, greenDensity_sinh_sq s hx0,
      mul_div_cancel₀ _ hpos.ne']
    congr 2; ring
  rw [setLIntegral_congr_fun measurableSet_Ioi hpt, ← ofReal_integral_eq_lintegral_ofReal
    (integrableOn_exp_mul_Ioi (by linarith) τ₀) (Eventually.of_forall fun _ => (Real.exp_pos _).le),
    integral_exp_mul_Ioi (by linarith)]
  congr 1
  rw [neg_div_neg_eq]; congr 2; ring

/-- **The arcsine integral.**  `∫_{η²/4 < A} (A − η²/4)^{−½} dη = 2π` for `A > 0`. -/
theorem lintegral_arcsine {A : ℝ} (hA : 0 < A) :
    ∫⁻ η : ℝ, (Ioo (-(2 * Real.sqrt A)) (2 * Real.sqrt A)).indicator
      (fun η => ENNReal.ofReal (Real.sqrt (A - η ^ 2 / 4))⁻¹) η = ENNReal.ofReal (2 * π) := by
  have hsA : 0 < Real.sqrt A := Real.sqrt_pos.mpr hA
  rw [lintegral_indicator measurableSet_Ioo]
  set f : ℝ → ℝ := fun θ => 2 * Real.sqrt A * Real.sin θ
  set I := Ioo (-(π / 2)) (π / 2)
  have hd : ∀ θ ∈ I, HasDerivWithinAt f (2 * Real.sqrt A * Real.cos θ) I θ :=
    fun θ _ => ((Real.hasDerivAt_sin θ).const_mul _).hasDerivWithinAt
  have hinj : InjOn f I := fun a ha b hb hab => by
    have : Real.sin a = Real.sin b := by
      have := mul_left_cancel₀ (by positivity : (2 * Real.sqrt A) ≠ 0) hab; exact this
    exact Real.injOn_sin (Ioo_subset_Icc_self ha) (Ioo_subset_Icc_self hb) this
  have himage : f '' I = Ioo (-(2 * Real.sqrt A)) (2 * Real.sqrt A) := by
    ext η
    constructor
    · rintro ⟨θ, ⟨h1, h2⟩, rfl⟩
      have hs1 : Real.sin θ < 1 := by
        rw [← Real.sin_pi_div_two]
        exact Real.sin_lt_sin_of_lt_of_le_pi_div_two (by linarith) le_rfl h2
      have hs2 : -1 < Real.sin θ := by
        have : Real.sin (-θ) < 1 := by
          rw [← Real.sin_pi_div_two]
          exact Real.sin_lt_sin_of_lt_of_le_pi_div_two (by linarith) le_rfl (by linarith)
        rw [Real.sin_neg] at this; linarith
      constructor <;> simp only [f] <;> nlinarith
    · rintro ⟨h1, h2⟩
      have hx1 : -1 < η / (2 * Real.sqrt A) := by rw [lt_div_iff₀ (by positivity)]; linarith
      have hx2 : η / (2 * Real.sqrt A) < 1 := by rw [div_lt_iff₀ (by positivity)]; linarith
      refine ⟨Real.arcsin (η / (2 * Real.sqrt A)),
        ⟨Real.neg_pi_div_two_lt_arcsin.mpr hx1, Real.arcsin_lt_pi_div_two.mpr hx2⟩, ?_⟩
      simp only [f]
      rw [Real.sin_arcsin hx1.le hx2.le]
      field_simp
  rw [← himage, lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioo hd hinj]
  have hpt : ∀ θ ∈ I, ENNReal.ofReal |2 * Real.sqrt A * Real.cos θ| *
      ENNReal.ofReal (Real.sqrt (A - f θ ^ 2 / 4))⁻¹ = ENNReal.ofReal 2 := by
    intro θ hθ
    have hc : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo hθ
    have hroot : Real.sqrt (A - f θ ^ 2 / 4) = Real.sqrt A * Real.cos θ := by
      have : A - f θ ^ 2 / 4 = (Real.sqrt A * Real.cos θ) ^ 2 := by
        simp only [f]
        have h := Real.sq_sqrt hA.le
        have h2 := Real.sin_sq_add_cos_sq θ
        linear_combination (-1 : ℝ) * h - Real.sqrt A ^ 2 * h2
      rw [this, Real.sqrt_sq (by positivity)]
    rw [hroot, ← ENNReal.ofReal_mul (abs_nonneg _), abs_of_pos (by positivity)]
    congr 1
    field_simp
  rw [setLIntegral_congr_fun measurableSet_Ioo hpt, setLIntegral_const, Real.volume_Ioo,
    ← ENNReal.ofReal_mul (by norm_num)]
  congr 1; ring

/-! ### The kernels -/

/-- The resolvent kernel `k_s(u) = (1/4π) ∫_{w > u} F_s(w) (w − u)^{−½} dw`. -/
def resKernel (s u : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (1 / (4 * π)) *
    ∫⁻ w : ℝ, (Ioi u).indicator (fun w => ENNReal.ofReal (greenDensity s w * (Real.sqrt (w - u))⁻¹)) w

theorem measurable_resKernel (s : ℝ) : Measurable (resKernel s) := by
  have hj : Measurable fun p : ℝ × ℝ => (Ioi p.1).indicator
      (fun w => ENNReal.ofReal (greenDensity s w * (Real.sqrt (w - p.1))⁻¹)) p.2 := by
    have hset : MeasurableSet {p : ℝ × ℝ | p.1 < p.2} := measurableSet_lt measurable_fst measurable_snd
    have : (fun p : ℝ × ℝ => (Ioi p.1).indicator
        (fun w => ENNReal.ofReal (greenDensity s w * (Real.sqrt (w - p.1))⁻¹)) p.2) =
        {p : ℝ × ℝ | p.1 < p.2}.indicator
          (fun p => ENNReal.ofReal (greenDensity s p.2 * (Real.sqrt (p.2 - p.1))⁻¹)) := by
      funext p; simp only [indicator_apply, mem_Ioi, mem_setOf_eq]
    rw [this]
    refine Measurable.indicator ?_ hset
    exact ENNReal.measurable_ofReal.comp
      (((measurable_greenDensity s).comp measurable_snd).mul (by fun_prop))
  exact hj.lintegral_prod_right'.const_mul _

/-- **The Abel transform of `k_s`.**  `𝒜k_s(τ) = e^{−(s−½)|τ|}/(2s − 1)`. -/
theorem abelL_resKernel {s : ℝ} (hs : 1 / 2 < s) (τ : ℝ) :
    abelL (resKernel s) τ = ENNReal.ofReal (Real.exp (-((s - 1 / 2) * |τ|)) / (2 * s - 1)) := by
  set c := Real.sinh (τ / 2) ^ 2 with hc
  have hc' : c = Real.sinh (|τ| / 2) ^ 2 := by
    rcases abs_choice τ with h | h <;> rw [h]
    rw [neg_div, Real.sinh_neg, neg_sq]
  have hc0 : 0 ≤ c := sq_nonneg _
  set J : ℝ → ℝ → ℝ≥0∞ := fun η w => (Ioi (η ^ 2 / 4 + c)).indicator
    (fun w => ENNReal.ofReal (greenDensity s w * (Real.sqrt (w - (η ^ 2 / 4 + c)))⁻¹)) w
  have hJ : Measurable (Function.uncurry J) := by
    have hset : MeasurableSet {p : ℝ × ℝ | p.1 ^ 2 / 4 + c < p.2} :=
      measurableSet_lt (by fun_prop) measurable_snd
    have : Function.uncurry J = {p : ℝ × ℝ | p.1 ^ 2 / 4 + c < p.2}.indicator
        (fun p => ENNReal.ofReal (greenDensity s p.2 * (Real.sqrt (p.2 - (p.1 ^ 2 / 4 + c)))⁻¹)) := by
      funext p; simp only [Function.uncurry, J, indicator_apply, mem_Ioi, mem_setOf_eq]
    rw [this]
    exact (ENNReal.measurable_ofReal.comp
      (((measurable_greenDensity s).comp measurable_snd).mul (by fun_prop))).indicator hset
  have hinner : ∀ w : ℝ, ∫⁻ η : ℝ, J η w = (Ioi c).indicator
      (fun w => ENNReal.ofReal (greenDensity s w) * ENNReal.ofReal (2 * π)) w := by
    intro w
    by_cases hw : c < w
    · rw [indicator_of_mem (show w ∈ Ioi c from hw)]
      have hA : 0 < w - c := by linarith
      rw [← lintegral_arcsine hA, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine lintegral_congr fun η => ?_
      simp only [J, indicator_apply, mem_Ioi, mem_Ioo]
      by_cases hη : η ^ 2 / 4 < w - c
      · have h1 : η ^ 2 / 4 + c < w := by linarith
        have h2 : -(2 * Real.sqrt (w - c)) < η ∧ η < 2 * Real.sqrt (w - c) := by
          have h3 : η ^ 2 < (2 * Real.sqrt (w - c)) ^ 2 := by
            rw [mul_pow, Real.sq_sqrt hA.le]; linarith
          exact abs_lt.mp (abs_lt_of_sq_lt_sq h3 (by positivity))
        rw [if_pos h1, if_pos h2, ← ENNReal.ofReal_mul (greenDensity_nonneg s (by linarith))]
        congr 2; ring_nf
      · have h1 : ¬ η ^ 2 / 4 + c < w := by intro h; exact hη (by linarith)
        have h2 : ¬ (-(2 * Real.sqrt (w - c)) < η ∧ η < 2 * Real.sqrt (w - c)) := by
          rintro ⟨h4, h5⟩
          have h6 : |η| < 2 * Real.sqrt (w - c) := abs_lt.mpr ⟨h4, h5⟩
          have h7 : η ^ 2 < (2 * Real.sqrt (w - c)) ^ 2 := by
            rw [← sq_abs]; exact pow_lt_pow_left₀ h6 (abs_nonneg _) two_ne_zero
          rw [mul_pow, Real.sq_sqrt hA.le] at h7
          exact hη (by linarith)
        rw [if_neg h1, if_neg h2, mul_zero]
    · rw [indicator_of_notMem (show w ∉ Ioi c from hw)]
      refine lintegral_eq_zero_of_ae_eq_zero (Eventually.of_forall fun η => ?_)
      have : ¬ η ^ 2 / 4 + c < w := by intro h; exact hw (by nlinarith [sq_nonneg η])
      simp only [J, indicator_apply, mem_Ioi, this, if_false, Pi.zero_apply]
  have habel : abelL (resKernel s) τ = ENNReal.ofReal (1 / (4 * π)) * ∫⁻ η : ℝ, ∫⁻ w : ℝ, J η w := by
    simp only [abelL, resKernel]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  rw [habel, lintegral_lintegral_swap hJ.aemeasurable]
  simp_rw [hinner]
  rw [lintegral_indicator measurableSet_Ioi, lintegral_mul_const' _ _ ENNReal.ofReal_ne_top, hc', lintegral_greenDensity_Ioi hs (abs_nonneg τ),
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  have hπ : π ≠ 0 := Real.pi_ne_zero
  have hs' : 2 * s - 1 ≠ 0 := by linarith
  field_simp
  ring

end

end GaloisForLFunctions.CompactHyperbolicSurfaces
