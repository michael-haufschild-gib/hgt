import GaloisForLFunctions.ZeroConfigurationGeometry.TheCameraAndTheTilt
import GaloisForLFunctions.RHTower.RiemannKernelStripPlancherel

/-!
# The squared gap is read at second order

An FE-symmetric pair of points `c ± w` (`c` real, `w²` real) is a real pair when `w² > 0`, a
collision when `w = 0`, and an off-line pair of depth `δ` when `w = iδ`. The camera sees the pair
through the window `2cos(wu)·f` (`paperFT_add_add_sub`); its **pair signal** — the pair minus the
doubled centre — is the centre seen through `2(cos(wu) − 1)·f` (`pairSignal_eq`).

* **Second-order law** (`norm_pairSignal_add_sq_mul_secondMoment_le`). At aperture `r` with
  `|w| r ≤ 1`,
  `|pairSignal f c w + w² M₂(f, c)| ≤ (5/48)|w|⁴ r⁴ ∫|f|`, `M₂(f, c) = (u² f)^(c)`.
  Near a collision the image is the doubled centre minus `w²` times the second-moment image: the
  camera reads the squared gap linearly, and nothing else at first order.
* **Reality is the sign of a second-order coefficient** (`norm_realPair_sub_tiltedPair_le`). A real
  pair of gap `Δ` and a tilted pair of depth `Δ` with the same centre have images that differ by
  `−2Δ² M₂ + O(Δ⁴r⁴)`. To decide whether a near-collision is real or tilted a camera must resolve
  the second-moment image to relative precision `(Δr)²`; below the resolution scale this is the
  coalescent channel of the field.
* **The second moment is the height curvature** (`deriv_deriv_paperFT_eq_neg_secondMoment`,
  `norm_pairSignal_sub_sq_mul_curvature_le`). `M₂(f, c) = −(f̂)''(c)`: near a collision the pair
  is seen as `2f̂(c) + w² f̂''(c) + O(|w|⁴r⁴)`. Reality of a near-collision is the sign of the
  coefficient of the curvature of the image in the height variable.
* The depth signal is the pair signal at `w = iδ` (`depthSignal_eq_pairSignal`).
-/

open MeasureTheory Complex
open scoped ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.ZeroConfigurationGeometry

open Zeta23

/-- The **pair signal**: the pair `c ± w` minus the doubled centre `c`. -/
def pairSignal (f : ℝ → ℂ) (c w : ℂ) : ℂ :=
  paperFT f (c + w) + paperFT f (c - w) - 2 * paperFT f c

/-- The **second-moment image** `(u² f)^(c)`. -/
def secondMoment (f : ℝ → ℂ) (c : ℂ) : ℂ := paperFT (fun u => (u : ℂ) ^ 2 * f u) c

theorem pairSignal_neg (f : ℝ → ℂ) (c w : ℂ) : pairSignal f c (-w) = pairSignal f c w := by
  simp only [pairSignal, sub_neg_eq_add, ← sub_eq_add_neg]; ring

theorem depthSignal_eq_pairSignal (f : ℝ → ℂ) (x δ : ℝ) :
    depthSignal f x δ = pairSignal f x (I * δ) := by
  simp only [depthSignal, pairSignal]; ring

/-- The pair signal is the centre seen through `2(cos(wu) − 1)`. -/
theorem pairSignal_eq {f : ℝ → ℂ} (hf : Continuous f) (hfc : HasCompactSupport f) (c w : ℂ) :
    pairSignal f c w = paperFT (fun u => 2 * (Complex.cos (w * u) - 1) * f u) c := by
  have hc : Continuous fun u : ℝ => 2 * Complex.cos (w * u) * f u := by fun_prop
  rw [pairSignal, paperFT_add_add_sub hf hfc, paperFT_def, paperFT_def, paperFT_def,
    ← integral_const_mul, ← integral_sub (integrable_mul_cexp hc hfc.mul_left _)
      ((integrable_mul_cexp hf hfc _).const_mul _)]
  congr 1 with u; ring

/-- **The second-order law.** -/
theorem norm_pairSignal_add_sq_mul_secondMoment_le {f : ℝ → ℂ} (hf : Continuous f)
    (hfc : HasCompactSupport f) {r : ℝ} (hsupp : tsupport f ⊆ Set.Icc (-r) r) (c : ℝ) {w : ℂ}
    (hw : ‖w‖ * r ≤ 1) :
    ‖pairSignal f c w + w ^ 2 * secondMoment f c‖ ≤ 5 / 48 * ‖w‖ ^ 4 * r ^ 4 * ∫ u, ‖f u‖ := by
  have hm : Continuous fun u : ℝ => (u : ℂ) ^ 2 * f u := by fun_prop
  have hk : Continuous fun u : ℝ => 2 * (Complex.cos (w * u) - 1) * f u := by fun_prop
  have hint1 := integrable_mul_cexp hk (hfc.mul_left) (c : ℂ)
  have hint2 := (integrable_mul_cexp hm (hfc.mul_left) (c : ℂ)).const_mul (w ^ 2)
  rw [pairSignal_eq hf hfc, secondMoment, paperFT_def, paperFT_def, ← integral_const_mul,
    ← integral_add hint1 hint2]
  have hbound : ∀ u : ℝ, ‖2 * (Complex.cos (w * u) - 1) * f u * cexp (I * c * u) +
      w ^ 2 * ((u : ℂ) ^ 2 * f u * cexp (I * c * u))‖ ≤ 5 / 48 * ‖w‖ ^ 4 * r ^ 4 * ‖f u‖ := by
    intro u
    have he : ‖cexp (I * c * u)‖ = 1 := by
      rw [show I * (c : ℂ) * (u : ℂ) = ((c * u : ℝ) : ℂ) * I by push_cast; ring,
        Complex.norm_exp_ofReal_mul_I]
    rw [show 2 * (Complex.cos (w * u) - 1) * f u * cexp (I * c * u) +
        w ^ 2 * ((u : ℂ) ^ 2 * f u * cexp (I * c * u)) =
        2 * (Complex.cos (w * u) - (1 - (w * u) ^ 2 / 2)) * f u * cexp (I * c * u) by ring,
      norm_mul, norm_mul, norm_mul, he, mul_one, Complex.norm_two]
    by_cases hu : f u = 0
    · rw [hu, norm_zero, mul_zero, mul_zero]
    · obtain ⟨h1, h2⟩ := hsupp (subset_tsupport _ hu)
      have hur : |u| ≤ r := abs_le.mpr ⟨h1, h2⟩
      have hwu : ‖w * u‖ = ‖w‖ * |u| := by rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have hwu1 : ‖w * u‖ ≤ 1 := by
        rw [hwu]; exact (mul_le_mul_of_nonneg_left hur (norm_nonneg w)).trans hw
      have hcb := Complex.cos_bound hwu1
      have hr4 : ‖w * u‖ ^ 4 ≤ ‖w‖ ^ 4 * r ^ 4 := by
        rw [hwu, mul_pow]
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg u) hur 4)
          (by positivity)
      have := mul_le_mul_of_nonneg_left hcb (by norm_num : (0 : ℝ) ≤ 2)
      calc 2 * ‖Complex.cos (w * u) - (1 - (w * u) ^ 2 / 2)‖ * ‖f u‖
          ≤ 2 * (‖w * u‖ ^ 4 * (5 / 96)) * ‖f u‖ :=
            mul_le_mul_of_nonneg_right this (norm_nonneg _)
        _ ≤ 2 * (‖w‖ ^ 4 * r ^ 4 * (5 / 96)) * ‖f u‖ := by gcongr
        _ = 5 / 48 * ‖w‖ ^ 4 * r ^ 4 * ‖f u‖ := by ring
  calc ‖∫ u : ℝ, 2 * (Complex.cos (w * u) - 1) * f u * cexp (I * c * u) +
        w ^ 2 * ((u : ℂ) ^ 2 * f u * cexp (I * c * u))‖
      ≤ ∫ u : ℝ, 5 / 48 * ‖w‖ ^ 4 * r ^ 4 * ‖f u‖ :=
        norm_integral_le_of_norm_le
          ((hf.norm.integrable_of_hasCompactSupport hfc.norm).const_mul _)
          (Filter.Eventually.of_forall hbound)
    _ = 5 / 48 * ‖w‖ ^ 4 * r ^ 4 * ∫ u, ‖f u‖ := integral_const_mul _ _

/-- **Reality of a near-collision is the sign of a second-order coefficient.** A real pair of gap
`Δ` and a tilted pair of depth `Δ` around the same centre have images differing by
`−2Δ² M₂ + O(Δ⁴r⁴)`. -/
theorem norm_realPair_sub_tiltedPair_le {f : ℝ → ℂ} (hf : Continuous f)
    (hfc : HasCompactSupport f) {r : ℝ} (hsupp : tsupport f ⊆ Set.Icc (-r) r) (c Δ : ℝ)
    (hΔ : |Δ| * r ≤ 1) :
    ‖pairSignal f c Δ - pairSignal f c (I * Δ) + 2 * (Δ : ℂ) ^ 2 * secondMoment f c‖ ≤
      5 / 24 * Δ ^ 4 * r ^ 4 * ∫ u, ‖f u‖ := by
  have h1 := norm_pairSignal_add_sq_mul_secondMoment_le hf hfc hsupp c (w := (Δ : ℂ))
    (by rw [Complex.norm_real, Real.norm_eq_abs]; exact hΔ)
  have h2 := norm_pairSignal_add_sq_mul_secondMoment_le hf hfc hsupp c (w := I * Δ)
    (by rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]; exact hΔ)
  have hn1 : ‖(Δ : ℂ)‖ ^ 4 = Δ ^ 4 := by
    rw [Complex.norm_real, Real.norm_eq_abs, show (4 : ℕ) = 2 * 2 from rfl, pow_mul, sq_abs,
      ← pow_mul]
  have hn2 : ‖I * (Δ : ℂ)‖ ^ 4 = Δ ^ 4 := by rw [norm_mul, Complex.norm_I, one_mul, hn1]
  rw [hn1] at h1
  rw [hn2] at h2
  have heq : pairSignal f c Δ - pairSignal f c (I * Δ) + 2 * (Δ : ℂ) ^ 2 * secondMoment f c =
      (pairSignal f c Δ + (Δ : ℂ) ^ 2 * secondMoment f c) -
        (pairSignal f c (I * Δ) + (I * Δ) ^ 2 * secondMoment f c) := by
    rw [mul_pow, Complex.I_sq]; ring
  rw [heq]
  calc _ ≤ ‖pairSignal f c Δ + (Δ : ℂ) ^ 2 * secondMoment f c‖ +
        ‖pairSignal f c (I * Δ) + (I * Δ) ^ 2 * secondMoment f c‖ := norm_sub_le _ _
    _ ≤ _ := by linarith

/-! ### The second moment is the height curvature of the image -/

/-- **The second-moment image is minus the height curvature of the transform.** -/
theorem deriv_deriv_paperFT_eq_neg_secondMoment {f : ℝ → ℂ} (hf : Continuous f)
    (hfc : HasCompactSupport f) (c : ℝ) :
    deriv (deriv fun x : ℝ => paperFT f x) c = -secondMoment f c := by
  have hi : ∀ g : ℝ → ℂ, Continuous g → HasCompactSupport g → Integrable g := fun g hg hgc =>
    hg.integrable_of_hasCompactSupport hgc
  have hc1 : Continuous fun u : ℝ => I * u * f u := by fun_prop
  have hcs1 : HasCompactSupport fun u : ℝ => I * u * f u := hfc.mul_left
  have hc2 : Continuous fun u : ℝ => (u : ℂ) * f u := by fun_prop
  have hc3 : Continuous fun u : ℝ => (u : ℂ) * (I * u * f u) := by fun_prop
  have hd1 : deriv (fun x : ℝ => paperFT f x) = fun x : ℝ => paperFT (fun u => I * u * f u) x :=
    funext fun x => (_root_.RHTower.KernelStrip.hasDerivAt_paperFT (hi f hf hfc)
      (hi _ hc2 hfc.mul_left) x).deriv
  rw [hd1, (_root_.RHTower.KernelStrip.hasDerivAt_paperFT (hi _ hc1 hcs1)
    (hi _ hc3 hcs1.mul_left) c).deriv, secondMoment, paperFT_def, paperFT_def, ← integral_neg]
  congr 1 with u
  have hI : I * I = -1 := Complex.I_mul_I
  linear_combination ((u : ℂ) ^ 2 * f u * cexp (I * c * u)) * hI

/-- **Near a collision the image of a pair is the doubled centre plus `w²` times the height
curvature.** -/
theorem norm_pairSignal_sub_sq_mul_curvature_le {f : ℝ → ℂ} (hf : Continuous f)
    (hfc : HasCompactSupport f) {r : ℝ} (hsupp : tsupport f ⊆ Set.Icc (-r) r) (c : ℝ) {w : ℂ}
    (hw : ‖w‖ * r ≤ 1) :
    ‖pairSignal f c w - w ^ 2 * deriv (deriv fun x : ℝ => paperFT f x) c‖ ≤
      5 / 48 * ‖w‖ ^ 4 * r ^ 4 * ∫ u, ‖f u‖ := by
  rw [deriv_deriv_paperFT_eq_neg_secondMoment hf hfc, mul_neg, sub_neg_eq_add]
  exact norm_pairSignal_add_sq_mul_secondMoment_le hf hfc hsupp c hw

end GaloisForLFunctions.ZeroConfigurationGeometry
