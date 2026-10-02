import GaloisForLFunctions.RHTower.XiMassNearDiagonalStationaryNoGo
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Bilinear flattening of the timelike mass phase

The timelike action has an exact nonnegative tangent defect: the sum of
the squared frequency displacement and squared shell displacement.
On a logarithmic block inside the light cone, removing the tangent phase
leaves a uniformly small phase. Thus generic bilinear cancellation cannot
replace cancellation of the actual arithmetic coefficients.
-/

open Complex Real
open scoped BigOperators

namespace RHTower
noncomputable section

theorem xiMassTimelikeAction_tangent_energy {u h k : ℝ}
    (hh : h ^ 2 ≤ u ^ 2) (hk : k ^ 2 ≤ u ^ 2) :
    2 * xiMassTimelikeAction u h *
        (xiMassTimelikeAction u h - xiMassTimelikeAction u k) -
      2 * h * (k - h) =
        (k - h) ^ 2 + (xiMassTimelikeAction u h - xiMassTimelikeAction u k) ^ 2 := by
  have hsq := Real.sq_sqrt (sub_nonneg.mpr hh)
  have ksq := Real.sq_sqrt (sub_nonneg.mpr hk)
  unfold xiMassTimelikeAction
  nlinarith

private theorem shell_block {u h : ℝ} (hu : 0 < u) (hh : |h| ≤ 3 * u / 4) :
    h ^ 2 ≤ u ^ 2 ∧ u / 2 ≤ xiMassTimelikeAction u h := by
  have ha := abs_le.mp hh
  have hp := mul_nonneg (sub_nonneg.mpr ha.2)
    (show 0 ≤ 3 * u / 4 + h by linarith)
  have hr : 0 ≤ u ^ 2 - h ^ 2 := by nlinarith
  have hs := Real.sq_sqrt hr
  have hn := Real.sqrt_nonneg (u ^ 2 - h ^ 2)
  unfold xiMassTimelikeAction
  constructor <;> nlinarith

theorem xiMassTimelikeAction_block_chord {u h k : ℝ} (hu : 0 < u)
    (hh : |h| ≤ 3 * u / 4) (hk : |k| ≤ 3 * u / 4) :
    |xiMassTimelikeAction u h - xiMassTimelikeAction u k| ≤ 2 * |k - h| := by
  obtain ⟨hh2, hhq⟩ := shell_block hu hh
  obtain ⟨hk2, hkq⟩ := shell_block hu hk
  let q := xiMassTimelikeAction u h
  let r := xiMassTimelikeAction u k
  have hq : 0 ≤ q := Real.sqrt_nonneg _
  have hr : 0 ≤ r := Real.sqrt_nonneg _
  have hsum : u ≤ q + r := by dsimp [q, r]; linarith
  have hfac : (q - r) * (q + r) = (k - h) * (k + h) := by
    have hs := Real.sq_sqrt (sub_nonneg.mpr hh2)
    have ht := Real.sq_sqrt (sub_nonneg.mpr hk2)
    dsimp [q, r, xiMassTimelikeAction]
    nlinarith
  have ha : |q - r| * (q + r) = |k - h| * |k + h| := by
    simpa only [abs_mul, abs_of_nonneg (add_nonneg hq hr)] using congrArg abs hfac
  have hkh : |k + h| ≤ 2 * u := (abs_add_le _ _).trans (by linarith)
  have hbound : |q - r| * u ≤ (2 * |k - h|) * u := calc
    _ ≤ |q - r| * (q + r) := mul_le_mul_of_nonneg_left hsum (abs_nonneg _)
    _ = |k - h| * |k + h| := ha
    _ ≤ |k - h| * (2 * u) := mul_le_mul_of_nonneg_left hkh (abs_nonneg _)
    _ = _ := by ring
  by_contra hnot
  have hp := mul_pos (sub_pos.mpr (lt_of_not_ge hnot)) hu
  nlinarith

/-- Uniform tangent remainder on an interior timelike block. -/
theorem xiMassTimelikeAction_block_tangent {u h k : ℝ} (hu : 0 < u)
    (hh : |h| ≤ 3 * u / 4) (hk : |k| ≤ 3 * u / 4) :
    |xiMassTimelikeAction u k - xiMassTimelikeAction u h +
        h / xiMassTimelikeAction u h * (k - h)| ≤ 5 * (k - h) ^ 2 / u := by
  obtain ⟨hh2, hhq⟩ := shell_block hu hh
  obtain ⟨hk2, _⟩ := shell_block hu hk
  let q := xiMassTimelikeAction u h
  let r := xiMassTimelikeAction u k
  have hq : 0 < q := by dsimp [q]; linarith
  have he := xiMassTimelikeAction_tangent_energy hh2 hk2
  have hc := xiMassTimelikeAction_block_chord hu hh hk
  have hsq : (q - r) ^ 2 ≤ 4 * (k - h) ^ 2 := by
    have hp := mul_nonneg (sub_nonneg.mpr hc)
      (show 0 ≤ 2 * |k - h| + |q - r| by positivity)
    nlinarith [sq_abs (q - r), sq_abs (k - h)]
  have hid : r - q + h / q * (k - h) =
      -((k - h) ^ 2 + (q - r) ^ 2) / (2 * q) := by
    apply (eq_div_iff (mul_ne_zero (by norm_num) hq.ne')).mpr
    field_simp
    dsimp [q, r] at *
    nlinarith
  change |r - q + h / q * (k - h)| ≤ _
  rw [hid, abs_div, abs_neg,
    abs_of_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _)),
    abs_of_pos (mul_pos (by norm_num) hq)]
  apply (div_le_div_iff₀ (mul_pos (by norm_num) hq) hu).mpr
  have hnum := mul_le_mul_of_nonneg_right
    (show (k - h) ^ 2 + (q - r) ^ 2 ≤ 5 * (k - h) ^ 2 by linarith) hu.le
  have hden := mul_le_mul_of_nonneg_left
    (show u ≤ 2 * q by dsimp [q]; linarith) (show 0 ≤ 5 * (k - h) ^ 2 by positivity)
  exact hnum.trans hden

/-- The actual two-factor action after removing its constant and two tangent phases. -/
def xiMassTimelikeBilinearFlatKernel (a u h x y : ℝ) : ℂ :=
  Complex.exp (I * (a * xiMassTimelikeAction u (h + x + y) : ℝ)) *
    Complex.exp (-I * (a * xiMassTimelikeAction u h : ℝ)) *
      Complex.exp (I * (a * h / xiMassTimelikeAction u h * x : ℝ)) *
        Complex.exp (I * (a * h / xiMassTimelikeAction u h * y : ℝ))

theorem xiMassTimelikeBilinearFlatKernel_eq (a u h x y : ℝ) :
    xiMassTimelikeBilinearFlatKernel a u h x y =
      Complex.exp (I * (a * (xiMassTimelikeAction u (h + x + y) -
        xiMassTimelikeAction u h + h / xiMassTimelikeAction u h * (x + y)) : ℝ)) := by
  unfold xiMassTimelikeBilinearFlatKernel
  rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem norm_xiMassTimelikeBilinearFlatKernel_sub_one_le
    {a u h x y L : ℝ} (hu : 0 < u) (hh : |h| ≤ 3 * u / 4)
    (hk : |h + x + y| ≤ 3 * u / 4) (hL : |x + y| ≤ L) :
    ‖xiMassTimelikeBilinearFlatKernel a u h x y - 1‖ ≤ 5 * |a| * L ^ 2 / u := by
  rw [xiMassTimelikeBilinearFlatKernel_eq]
  have ht := xiMassTimelikeAction_block_tangent hu hh hk
  have he : h + x + y - h = x + y := by ring
  rw [he] at ht
  have hL0 : 0 ≤ L := (abs_nonneg _).trans hL
  have hsq : (x + y) ^ 2 ≤ L ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hL) (add_nonneg hL0 (abs_nonneg (x + y))),
      sq_abs (x + y)]
  calc
    _ ≤ ‖a * (xiMassTimelikeAction u (h + x + y) -
        xiMassTimelikeAction u h + h / xiMassTimelikeAction u h * (x + y))‖ :=
      Real.norm_exp_I_mul_ofReal_sub_one_le
    _ = |a| * |xiMassTimelikeAction u (h + x + y) -
        xiMassTimelikeAction u h + h / xiMassTimelikeAction u h * (x + y)| := by
      rw [Real.norm_eq_abs, abs_mul]
    _ ≤ |a| * (5 * (x + y) ^ 2 / u) := mul_le_mul_of_nonneg_left ht (abs_nonneg _)
    _ ≤ 5 * |a| * L ^ 2 / u := by
      have hmul := mul_le_mul_of_nonneg_left hsq (show 0 ≤ 5 * |a| / u by positivity)
      calc
        _ = (5 * |a| / u) * (x + y) ^ 2 := by ring
        _ ≤ (5 * |a| / u) * L ^ 2 := hmul
        _ = _ := by ring

/-- The complete coefficient-weighted packet retains its rank-one main term.
No coefficient is replaced by its norm in that main term. -/
theorem xiMassTimelikeBilinearFlatKernel_packet_error
    {ι κ : Type*} (s : Finset ι) (t : Finset κ)
    (x : ι → ℝ) (y : κ → ℝ) (A : ι → ℂ) (B : κ → ℂ)
    {a u h L : ℝ} (hu : 0 < u) (hh : |h| ≤ 3 * u / 4)
    (hk : ∀ i ∈ s, ∀ j ∈ t, |h + x i + y j| ≤ 3 * u / 4)
    (hL : ∀ i ∈ s, ∀ j ∈ t, |x i + y j| ≤ L) :
    ‖(∑ i ∈ s, ∑ j ∈ t,
        A i * B j * xiMassTimelikeBilinearFlatKernel a u h (x i) (y j)) -
      (∑ i ∈ s, A i) * (∑ j ∈ t, B j)‖ ≤
      (5 * |a| * L ^ 2 / u) * (∑ i ∈ s, ‖A i‖) * (∑ j ∈ t, ‖B j‖) := by
  let E := 5 * |a| * L ^ 2 / u
  have heq : (∑ i ∈ s, ∑ j ∈ t,
        A i * B j * xiMassTimelikeBilinearFlatKernel a u h (x i) (y j)) -
      (∑ i ∈ s, A i) * (∑ j ∈ t, B j) =
      ∑ i ∈ s, ∑ j ∈ t,
        A i * B j * (xiMassTimelikeBilinearFlatKernel a u h (x i) (y j) - 1) := by
    rw [Finset.sum_mul]
    simp only [mul_sub, mul_one, Finset.sum_sub_distrib, Finset.mul_sum]
  rw [heq]
  calc
    _ ≤ ∑ i ∈ s, ‖∑ j ∈ t,
        A i * B j * (xiMassTimelikeBilinearFlatKernel a u h (x i) (y j) - 1)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ i ∈ s, ∑ j ∈ t, ‖A i‖ * ‖B j‖ * E := by
      apply Finset.sum_le_sum
      intro i hi
      refine (norm_sum_le _ _).trans ?_
      apply Finset.sum_le_sum
      intro j hj
      rw [norm_mul, norm_mul]
      exact mul_le_mul_of_nonneg_left
        (norm_xiMassTimelikeBilinearFlatKernel_sub_one_le hu hh (hk i hi j hj) (hL i hi j hj))
        (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = (∑ i ∈ s, ‖A i‖) * ((∑ j ∈ t, ‖B j‖) * E) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      simp only [Finset.sum_mul, Finset.mul_sum, mul_assoc]
    _ = _ := by dsimp [E]; ring

/-- Unit coefficient vectors remain coherent after undoing the two tangent phases.
The lower bound is uniform over the size and placement of the finite block. -/
theorem xiMassTimelikeBilinearFlatKernel_coherent_lower
    {ι κ : Type*} (s : Finset ι) (t : Finset κ)
    (x : ι → ℝ) (y : κ → ℝ)
    {a u h L : ℝ} (hu : 0 < u) (hh : |h| ≤ 3 * u / 4)
    (hk : ∀ i ∈ s, ∀ j ∈ t, |h + x i + y j| ≤ 3 * u / 4)
    (hL : ∀ i ∈ s, ∀ j ∈ t, |x i + y j| ≤ L) :
    (1 - 5 * |a| * L ^ 2 / u) * (s.card : ℝ) * (t.card : ℝ) ≤
      (∑ i ∈ s, ∑ j ∈ t,
        xiMassTimelikeBilinearFlatKernel a u h (x i) (y j)).re := by
  have he := xiMassTimelikeBilinearFlatKernel_packet_error
    s t x y (fun _ => 1) (fun _ => 1) (a := a) hu hh hk hL
  simp only [one_mul, norm_one, Finset.sum_const, nsmul_eq_mul, mul_one] at he
  have hr := (Complex.abs_re_le_norm _).trans he
  simp only [Complex.sub_re, Complex.mul_re, Complex.natCast_re,
    Complex.natCast_im, mul_zero, sub_zero] at hr
  have hlo := (abs_le.mp hr).1
  nlinarith

end
end RHTower
