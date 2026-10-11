import GaloisForLFunctions.RHTower.WeilLogShiftLogNodalDistortion
import Mathlib.Algebra.Order.Ring.Pow

/-! Bernoulli converts local nodal distortion into an additive modulus. -/

noncomputable section
namespace RHTower

theorem finiteWeilLogNodalDistortion_bernoulli_cross {r : ℕ} (x : Fin (r + 2) → ℝ)
    (hx : ∀ i, 0 < x i) (hinj : Function.Injective x)
    (i j : Fin (r + 2)) (hij : i ≠ j) (horder : x i ≤ x j) :
    (x j - (r : ℝ) * (x j - x i)) * finiteWeilLogNodalDistortion x j ≤
      x j * finiteWeilLogNodalDistortion x i := by
  let ai := finiteWeilLogNodalDistortion x i
  let aj := finiteWeilLogNodalDistortion x j
  have haj : 0 < aj := finiteWeilLogNodalDistortion_pos x hx hinj j
  have hp : 0 < x j ^ r := pow_pos (hx j) r
  have hc := (finiteWeilLogNodalDistortion_local_bounds x hx hinj i j hij horder).2
  have hq : (x i / x j) ^ r * aj ≤ ai := by
    rw [div_pow]
    apply (mul_le_mul_iff_right₀ hp).mp
    calc
      _ = x i ^ r * aj := by field_simp
      _ ≤ x j ^ r * ai := hc
  have hfrac : (x j - x i) / x j ≤ 1 := (div_le_iff₀ (hx j)).mpr (by linarith [hx i])
  have hb := one_add_mul_le_pow (a := -((x j - x i) / x j)) (by linarith) r
  have heq : 1 + -((x j - x i) / x j) = x i / x j := by
    have hj := hx j
    field_simp
    ring
  rw [heq] at hb
  have hl := (mul_le_mul_of_nonneg_right hb haj.le).trans hq
  have hm := mul_le_mul_of_nonneg_left hl (hx j).le
  have hid : x j * ((1 + (r : ℝ) * -((x j - x i) / x j)) * aj) =
      (x j - (r : ℝ) * (x j - x i)) * aj := by
    have hj := hx j
    field_simp
    ring
  rwa [hid] at hm

theorem finiteWeilLogNodalDistortion_ordered_error {r : ℕ} (x : Fin (r + 2) → ℝ)
    (hx : ∀ i, 0 < x i) (hinj : Function.Injective x)
    (i j : Fin (r + 2)) (hij : i ≠ j) (horder : x i ≤ x j)
    (hwidth : 2 * (r : ℝ) * (x j - x i) ≤ x j) :
    x j * (finiteWeilLogNodalDistortion x j - finiteWeilLogNodalDistortion x i) ≤
      2 * (r : ℝ) * (x j - x i) * finiteWeilLogNodalDistortion x i := by
  have hc := finiteWeilLogNodalDistortion_bernoulli_cross x hx hinj i j hij horder
  have hmono := (finiteWeilLogNodalDistortion_local_bounds x hx hinj i j hij horder).1
  have hfactor : x j ≤ 2 * (x j - (r : ℝ) * (x j - x i)) := by linarith only [hwidth]
  have hm := mul_le_mul_of_nonneg_right hfactor (sub_nonneg.mpr hmono)
  nlinarith only [hc, hm]

/-- The cross-multiplied modulus needs no separate positivity premise on A. -/
theorem finiteWeilLogNodalDistortion_relative_modulus {r : ℕ} (x : Fin (r + 2) → ℝ)
    (hx : ∀ i, 0 < x i) (hinj : Function.Injective x)
    (A : ℝ) (i j : Fin (r + 2)) (hAi : A ≤ x i) (hAj : A ≤ x j)
    (hwidth : 2 * (r : ℝ) * |x i - x j| ≤ A) :
    A * |finiteWeilLogNodalDistortion x i / finiteWeilLogNodalDistortion x j - 1| ≤
      2 * (r : ℝ) * |x i - x j| := by
  have hi := finiteWeilLogNodalDistortion_pos x hx hinj i
  have hj := finiteWeilLogNodalDistortion_pos x hx hinj j
  by_cases hij : i = j
  · subst j
    simp [div_self hi.ne']
  let ai := finiteWeilLogNodalDistortion x i
  let aj := finiteWeilLogNodalDistortion x j
  have hne : i ≠ j := hij
  change 0 < aj at hj
  change A * |ai / aj - 1| ≤ 2 * (r : ℝ) * |x i - x j|
  by_cases horder : x i ≤ x j
  · have hmono := (finiteWeilLogNodalDistortion_local_bounds x hx hinj i j hij horder).1
    have hq : ai / aj ≤ 1 := (div_le_iff₀ hj).mpr (by simpa only [one_mul] using hmono)
    have hc := finiteWeilLogNodalDistortion_bernoulli_cross x hx hinj i j hij horder
    change (x j - (r : ℝ) * (x j - x i)) * aj ≤ x j * ai at hc
    have ht : x j * (1 - ai / aj) ≤ (r : ℝ) * (x j - x i) := by
      apply (mul_le_mul_iff_right₀ hj).mp
      have heq : aj * (x j * (1 - ai / aj)) = x j * (aj - ai) := by
        field_simp
      rw [heq]
      nlinarith only [hc]
    have hA := mul_le_mul_of_nonneg_right hAj (sub_nonneg.mpr hq)
    have hnonneg : 0 ≤ (r : ℝ) * (x j - x i) := mul_nonneg (by positivity) (sub_nonneg.mpr horder)
    rw [abs_of_nonpos (sub_nonpos.mpr hq), abs_of_nonpos (sub_nonpos.mpr horder)]
    nlinarith only [hA, ht, hnonneg]
  · have horder' : x j ≤ x i := le_of_not_ge horder
    have hmono := (finiteWeilLogNodalDistortion_local_bounds x hx hinj j i hne.symm horder').1
    have hq : 1 ≤ ai / aj := (le_div_iff₀ hj).mpr (by simpa only [one_mul] using hmono)
    have hgap : |x i - x j| = x i - x j := abs_of_nonneg (sub_nonneg.mpr horder')
    have hw : 2 * (r : ℝ) * (x i - x j) ≤ x i := by rw [← hgap]; exact hwidth.trans hAi
    have hc := finiteWeilLogNodalDistortion_ordered_error x hx hinj j i hne.symm horder' hw
    change x i * (ai - aj) ≤ 2 * (r : ℝ) * (x i - x j) * aj at hc
    have hA := mul_le_mul_of_nonneg_right hAi (sub_nonneg.mpr hmono)
    rw [abs_of_nonneg (sub_nonneg.mpr hq), hgap]
    apply (mul_le_mul_iff_right₀ hj).mp
    have heq : aj * (A * (ai / aj - 1)) = A * (ai - aj) := by
      field_simp
    rw [heq]
    nlinarith only [hA, hc]

end RHTower
