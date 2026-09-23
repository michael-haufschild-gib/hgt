import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Exact weighted interval energy and endpoint resistance

Integral square completion gives weighted real and complex Cauchy control, then
actual FTC bounds finite-family endpoint chords. The resistance is the literal
integral of the reciprocal weight. Its value and possible degeneration remain
explicit; no regulator-uniform or congruence-uniform constant is assumed.
-/

open Set Filter Topology MeasureTheory Complex
namespace GaloisForLFunctions.RHTower.SelbergWeightedPathEnergy
noncomputable section

/-- Exact inverse-weight resistance along an oriented real interval. -/
def resistance (w : ℝ → ℝ) (a b : ℝ) : ℝ := ∫ x in a..b, 1 / w x

/-- A positive continuous weight has strictly positive resistance on a nondegenerate interval. -/
theorem resistance_pos {w : ℝ → ℝ} (hw : Continuous w) (hwp : ∀ x, 0 < w x)
    {a b : ℝ} (hab : a < b) : 0 < resistance w a b := by
  exact intervalIntegral.integral_pos hab
    (continuous_const.div hw (fun x => (hwp x).ne')).continuousOn
    (fun x _ => (one_div_pos.mpr (hwp x)).le)
    ⟨a, ⟨le_rfl, hab.le⟩, one_div_pos.mpr (hwp a)⟩

/-- Exact integral square completion with its resistance and total-current terms retained. -/
theorem integral_square_completion {g w : ℝ → ℝ} (hg : Continuous g) (hw : Continuous w)
    (hwp : ∀ x, 0 < w x) (a b c : ℝ) :
    (∫ x in a..b, w x * (g x - c / w x) ^ (2 : ℕ)) =
      (∫ x in a..b, w x * g x ^ (2 : ℕ)) - 2 * c * (∫ x in a..b, g x) +
        c ^ (2 : ℕ) * resistance w a b := by
  have hi₁ : IntervalIntegrable (fun x => w x * g x ^ (2 : ℕ)) volume a b :=
    (hw.mul (hg.pow 2)).intervalIntegrable a b
  have hi₂ : IntervalIntegrable (fun x => (2 * c) * g x) volume a b :=
    (continuous_const.mul hg).intervalIntegrable a b
  have hi₃ : IntervalIntegrable (fun x => c ^ (2 : ℕ) * (1 / w x)) volume a b :=
    (continuous_const.mul (continuous_const.div hw (fun x => (hwp x).ne'))).intervalIntegrable a b
  calc
    _ = ∫ x in a..b, (w x * g x ^ (2 : ℕ) - (2 * c) * g x) + c ^ (2 : ℕ) * (1 / w x) := by
      apply intervalIntegral.integral_congr
      intro x _
      have hx := (hwp x).ne'
      field_simp
      ring
    _ = _ := by
      rw [intervalIntegral.integral_add (hi₁.sub hi₂) hi₃, intervalIntegral.integral_sub hi₁ hi₂,
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
      rfl

/-- The interval counterpart of reciprocal-weight square completion gives exact weighted Cauchy control. -/
theorem integral_sq_le_resistance_energy {g w : ℝ → ℝ} (hg : Continuous g) (hw : Continuous w)
    (hwp : ∀ x, 0 < w x) {a b : ℝ} (hab : a ≤ b) :
    (∫ x in a..b, g x) ^ (2 : ℕ) ≤ resistance w a b * (∫ x in a..b, w x * g x ^ (2 : ℕ)) := by
  rcases hab.eq_or_lt with heq | hlt
  · subst b
    simp [resistance]
  · have hR := resistance_pos hw hwp hlt
    have h := intervalIntegral.integral_nonneg_of_forall (μ := volume) hlt.le
      (fun x => mul_nonneg (hwp x).le (sq_nonneg (g x - (∫ t in a..b, g t) / resistance w a b / w x)))
    rw [integral_square_completion hg hw hwp] at h
    have he :
        (∫ x in a..b, w x * g x ^ (2 : ℕ)) - 2 * ((∫ x in a..b, g x) / resistance w a b) *
          (∫ x in a..b, g x) + ((∫ x in a..b, g x) / resistance w a b) ^ (2 : ℕ) * resistance w a b =
        (∫ x in a..b, w x * g x ^ (2 : ℕ)) - (∫ x in a..b, g x) ^ (2 : ℕ) / resistance w a b := by
      field_simp
      ring
    rw [he] at h
    have hdiv : (∫ x in a..b, g x) ^ (2 : ℕ) / resistance w a b ≤ ∫ x in a..b, w x * g x ^ (2 : ℕ) := by linarith
    have hh := (div_le_iff₀ hR).mp hdiv
    nlinarith

/-- Weighted complex integral control keeps both real-coordinate energies. -/
theorem normSq_integral_le_resistance_energy {g : ℝ → ℂ} {w : ℝ → ℝ}
    (hg : Continuous g) (hw : Continuous w) (hwp : ∀ x, 0 < w x) {a b : ℝ} (hab : a ≤ b) :
    normSq (∫ x in a..b, g x) ≤ resistance w a b * (∫ x in a..b, w x * normSq (g x)) := by
  have hr := integral_sq_le_resistance_energy (Complex.continuous_re.comp hg) hw hwp hab
  have hi := integral_sq_le_resistance_energy (Complex.continuous_im.comp hg) hw hwp hab
  simp only [Function.comp_apply] at hr hi
  have hre := Complex.reCLM.intervalIntegral_comp_comm (hg.intervalIntegrable (μ := volume) a b)
  have him := Complex.imCLM.intervalIntegral_comp_comm (hg.intervalIntegrable (μ := volume) a b)
  simp only [Complex.reCLM_apply] at hre
  simp only [Complex.imCLM_apply] at him
  rw [hre] at hr
  rw [him] at hi
  have hs : (∫ x in a..b, w x * normSq (g x)) =
      (∫ x in a..b, w x * (g x).re ^ (2 : ℕ)) + ∫ x in a..b, w x * (g x).im ^ (2 : ℕ) := by
    simp only [normSq_apply, ← pow_two, mul_add]
    exact intervalIntegral.integral_add
      ((hw.mul ((Complex.continuous_re.comp hg).pow 2)).intervalIntegrable (μ := volume) a b)
      ((hw.mul ((Complex.continuous_im.comp hg).pow 2)).intervalIntegrable (μ := volume) a b)
  rw [hs, mul_add, normSq_apply]
  nlinarith

/-- Actual FTC converts the weighted integral inequality into an endpoint chord bound. -/
theorem normSq_sub_le_resistance_energy {F D : ℝ → ℂ} {w : ℝ → ℝ}
    (hD : Continuous D) (hw : Continuous w) (hwp : ∀ x, 0 < w x)
    {a b : ℝ} (hab : a ≤ b) (hF : ∀ x ∈ Icc a b, HasDerivAt F (D x) x) :
    normSq (F b - F a) ≤ resistance w a b * (∫ x in a..b, w x * normSq (D x)) := by
  have h := normSq_integral_le_resistance_energy hD hw hwp hab
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x hx => hF x (by simpa [uIcc_of_le hab] using hx)) (hD.intervalIntegrable (μ := volume) a b)] at h
  exact h

/-- Actual endpoint control for a finite complex family, with a single shared resistance. -/
theorem sum_normSq_sub_le_resistance_energy {ι : Type*} [Fintype ι]
    {F D : ι → ℝ → ℂ} {w : ℝ → ℝ}
    (hD : ∀ j, Continuous (D j)) (hw : Continuous w) (hwp : ∀ x, 0 < w x)
    {a b : ℝ} (hab : a ≤ b) (hF : ∀ j x, x ∈ Icc a b → HasDerivAt (F j) (D j x) x) :
    (∑ j, normSq (F j b - F j a)) ≤
      resistance w a b * (∫ x in a..b, w x * ∑ j, normSq (D j x)) := by
  have h := Finset.sum_le_sum (s := Finset.univ) (fun j _ =>
    normSq_sub_le_resistance_energy (hD j) hw hwp hab (hF j))
  rw [← Finset.mul_sum] at h
  have he : (∑ j, ∫ x in a..b, w x * normSq (D j x)) =
      ∫ x in a..b, w x * ∑ j, normSq (D j x) := by
    rw [← intervalIntegral.integral_finsetSum]
    · simp only [Finset.mul_sum]
    · intro j _
      exact (hw.mul (Complex.continuous_normSq.comp (hD j))).intervalIntegrable a b
  rw [he] at h
  exact h

/-- A finite family's squared endpoint chord is bounded by its literal squared coordinate variations, without a resistance factor. -/
theorem sum_normSq_sub_le_sum_sq_variation {ι : Type*} [Fintype ι]
    {F D : ι → ℝ → ℂ} (hD : ∀ j, Continuous (D j))
    {a b : ℝ} (hab : a ≤ b) (hF : ∀ j x, x ∈ Icc a b → HasDerivAt (F j) (D j x) x) :
    (∑ j, normSq (F j b - F j a)) ≤ ∑ j, (∫ x in a..b, ‖D j x‖) ^ (2 : ℕ) := by
  apply Finset.sum_le_sum
  intro j _
  have h := intervalIntegral.norm_integral_le_integral_norm (f := D j) (μ := volume) hab
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x hx => hF j x (by simpa [uIcc_of_le hab] using hx)) ((hD j).intervalIntegrable a b)] at h
  rw [Complex.normSq_eq_norm_sq]
  have hn := norm_nonneg (F j b - F j a)
  have hp := mul_nonneg (sub_nonneg.mpr h) (add_nonneg hn (hn.trans h))
  nlinarith

end
end GaloisForLFunctions.RHTower.SelbergWeightedPathEnergy
