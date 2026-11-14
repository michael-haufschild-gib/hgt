import GaloisForLFunctions.TransThresholdPairCorrelation.CosineTransformLogarithmicTransport
import Mathlib.NumberTheory.Zsqrtd.GaussianInt

/-!
# Uniform decay on the punctured Gaussian lattice

A telescoping reciprocal-square envelope controls a positive integer ray at
both the inverse-scale and inverse-square-scale rates. Separating the two
coordinates then bounds the fourth-order planar decay kernel uniformly after
multiplication by the squared scale. Removing the origin is essential.
-/

noncomputable section
open scoped Classical
open Finset Filter

namespace GaloisForLFunctions.MetaplecticMobiusDescent.QuarticPoisson

/-- A strictly positive lattice frequency scale. -/
abbrev PositiveScale := {s : ℝ // 0 < s}

private def natTailTerm (s : PositiveScale) (n : ℕ) : ℝ :=
  1 / (1 + s.val * ((n : ℝ) + 1)) ^ 2

/-- Mass of the positive reciprocal-square ray. -/
def positiveTail (s : PositiveScale) : ℝ := ∑' n : ℕ, natTailTerm s n

private theorem summable_natTailTerm (s : PositiveScale) : Summable (natTailTerm s) := by
  apply summable_of_sum_range_le (fun n => by unfold natTailTerm; positivity)
  intro N
  exact TransThresholdPairCorrelation.sum_inverse_square_affine_le s.property N

/-- The positive ray is bounded by the reciprocal scale. -/
theorem positiveTail_le_inv (s : PositiveScale) : positiveTail s ≤ 1 / s.val :=
  le_of_tendsto (summable_natTailTerm s).hasSum.tendsto_sum_nat
    (Eventually.of_forall (fun N =>
      TransThresholdPairCorrelation.sum_inverse_square_affine_le s.property N))

private theorem reciprocal_nat_square_bound :
    Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2) ∧
      (∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ 2) ≤ 2 := by
  let u : PositiveScale := ⟨1, zero_lt_one⟩
  let g : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) ^ 2
  have hshift : (fun n => g (n + 1)) = natTailTerm u := by
    funext n
    simp [g, natTailTerm, u, add_comm, add_left_comm]
  have hg : Summable g := (summable_nat_add_iff 1).mp (hshift.symm ▸ summable_natTailTerm u)
  refine ⟨hg, ?_⟩
  have hsum := hg.sum_add_tsum_nat_add 1
  rw [hshift] at hsum
  have hb := positiveTail_le_inv u
  change positiveTail u ≤ 1 / 1 at hb
  simp only [g, sum_range_one, Nat.cast_zero, zero_add, one_pow, div_one] at hsum
  change 1 + positiveTail u = ∑' n, g n at hsum
  change (∑' n, g n) ≤ 2
  linarith only [hsum, hb]

/-- The same ray also has inverse-square decay at large scales. -/
theorem positiveTail_le_two_inv_sq (s : PositiveScale) :
    positiveTail s ≤ 2 / s.val ^ 2 := by
  obtain ⟨hg, hgsum⟩ := reciprocal_nat_square_bound
  have hs : 0 < s.val := s.property
  have hterm (n : ℕ) : natTailTerm s n ≤
      (1 / s.val ^ 2) * (1 / ((n : ℝ) + 1) ^ 2) := by
    have hn : 0 < (n : ℝ) + 1 := by positivity
    calc
      natTailTerm s n ≤ 1 / (s.val * ((n : ℝ) + 1)) ^ 2 := by
        apply one_div_le_one_div_of_le (sq_pos_of_pos (mul_pos hs hn))
        exact pow_le_pow_left₀ (mul_nonneg hs.le hn.le) (by linarith) 2
      _ = _ := by simp only [mul_pow, one_div, mul_inv_rev]; ring
  calc
    positiveTail s ≤ ∑' n : ℕ, (1 / s.val ^ 2) * (1 / ((n : ℝ) + 1) ^ 2) :=
      Summable.tsum_le_tsum hterm (summable_natTailTerm s) (hg.mul_left _)
    _ = (1 / s.val ^ 2) * ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ 2 := tsum_mul_left
    _ ≤ (1 / s.val ^ 2) * 2 := mul_le_mul_of_nonneg_left hgsum (by positivity)
    _ = _ := by ring

/-- Reciprocal-square envelope on the full integer lattice. -/
def integerEnvelope (s : PositiveScale) (n : ℤ) : ℝ :=
  1 / (1 + s.val * |(n : ℝ)|) ^ 2

private theorem integerEnvelope_nat (s : PositiveScale) (n : ℕ) :
    integerEnvelope s n = 1 / (1 + s.val * (n : ℝ)) ^ 2 := by
  simp only [integerEnvelope, Int.cast_natCast,
    abs_of_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]

private theorem integerEnvelope_nat_succ (s : PositiveScale) (n : ℕ) :
    integerEnvelope s ((n : ℤ) + 1) = natTailTerm s n := by
  rw [show (n : ℤ) + 1 = ((n + 1 : ℕ) : ℤ) by simp, integerEnvelope_nat]
  simp only [natTailTerm, Nat.cast_add, Nat.cast_one]

private theorem integerEnvelope_neg (s : PositiveScale) (n : ℤ) :
    integerEnvelope s (-n) = integerEnvelope s n := by
  simp only [integerEnvelope, Int.cast_neg, abs_neg]

private theorem summable_integerEnvelope_nat (s : PositiveScale) :
    Summable (fun n : ℕ => integerEnvelope s n) := by
  apply (summable_nat_add_iff 1).mp
  simpa only [Nat.cast_add, Nat.cast_one, integerEnvelope_nat_succ] using
    summable_natTailTerm s

/-- The integer envelope is genuinely summable at every positive scale. -/
theorem summable_integerEnvelope (s : PositiveScale) : Summable (integerEnvelope s) := by
  rw [summable_int_iff_summable_nat_and_neg]
  refine ⟨summable_integerEnvelope_nat s, ?_⟩
  simpa only [integerEnvelope_neg] using summable_integerEnvelope_nat s

/-- Splitting the two integer rays separates their mass from the zero frequency. -/
theorem tsum_integerEnvelope (s : PositiveScale) :
    (∑' n : ℤ, integerEnvelope s n) = 1 + 2 * positiveTail s := by
  have hn := summable_integerEnvelope_nat s
  have hneg : (fun n : ℕ => integerEnvelope s (-((n : ℤ) + 1))) = natTailTerm s := by
    funext n
    rw [show -((n : ℤ) + 1) = -((n + 1 : ℕ) : ℤ) by simp,
      integerEnvelope_neg, integerEnvelope_nat]
    simp only [natTailTerm, Nat.cast_add, Nat.cast_one]
  have hnatsum : (∑' n : ℕ, integerEnvelope s n) = 1 + positiveTail s := by
    rw [← hn.sum_add_tsum_nat_add 1]
    simp only [sum_range_one, Nat.cast_add, Nat.cast_one, integerEnvelope_nat_succ,
      integerEnvelope_nat, Nat.cast_zero, mul_zero, add_zero, one_pow, div_one]
    rfl
  rw [tsum_of_nat_of_neg_add_one hn (hneg.symm ▸ summable_natTailTerm s), hnatsum, hneg]
  change 1 + positiveTail s + positiveTail s = _
  ring

private def offEnvelope (s : PositiveScale) (p : ℤ × ℤ) : ℝ :=
  if p = 0 then 0 else integerEnvelope s p.1 * integerEnvelope s p.2

private theorem offEnvelope_eq_sub (s : PositiveScale) :
    offEnvelope s = fun p : ℤ × ℤ => integerEnvelope s p.1 * integerEnvelope s p.2 -
      if p = 0 then 1 else 0 := by
  funext p
  by_cases hp : p = 0 <;> simp [offEnvelope, hp, integerEnvelope]

private theorem summable_envelope_product (s : PositiveScale) :
    Summable (fun p : ℤ × ℤ => integerEnvelope s p.1 * integerEnvelope s p.2) :=
  (summable_integerEnvelope s).mul_of_nonneg (summable_integerEnvelope s)
    (fun _ => by unfold integerEnvelope; positivity)
    (fun _ => by unfold integerEnvelope; positivity)

private theorem summable_offEnvelope (s : PositiveScale) : Summable (offEnvelope s) := by
  rw [offEnvelope_eq_sub]
  exact (summable_envelope_product s).sub (hasSum_ite_eq (0 : ℤ × ℤ) (1 : ℝ)).summable

private theorem tsum_offEnvelope (s : PositiveScale) :
    (∑' p : ℤ × ℤ, offEnvelope s p) = 4 * positiveTail s + 4 * positiveTail s ^ 2 := by
  have hd := hasSum_ite_eq (0 : ℤ × ℤ) (1 : ℝ)
  rw [offEnvelope_eq_sub, (summable_envelope_product s).tsum_sub hd.summable,
    hd.tsum_eq, (summable_envelope_product s).tsum_prod]
  simp_rw [tsum_mul_left]
  rw [tsum_mul_right, tsum_integerEnvelope]
  ring

private theorem scaled_offEnvelope_le (s : PositiveScale) :
    s.val ^ 2 * (∑' p : ℤ × ℤ, offEnvelope s p) ≤ 12 := by
  have hB : 0 ≤ positiveTail s := tsum_nonneg (fun n => by unfold natTailTerm; positivity)
  have hs : 0 < s.val := s.property
  have hlin := (le_div_iff₀ hs).mp (positiveTail_le_inv s)
  have hquad := (le_div_iff₀ (sq_pos_of_pos hs)).mp (positiveTail_le_two_inv_sq s)
  have hlin' : s.val * positiveTail s ≤ 1 := by linarith only [hlin]
  have hsq : s.val ^ 2 * positiveTail s ^ 2 ≤ 1 := by
    simpa only [mul_pow, one_pow] using
      pow_le_pow_left₀ (mul_nonneg hs.le hB) hlin' 2
  rw [tsum_offEnvelope]
  nlinarith only [hquad, hsq]

private theorem complex_fourth_envelope (s : PositiveScale) (z : ℂ) :
    1 / (1 + s.val * ‖z‖) ^ 4 ≤
      (1 / (1 + s.val * |z.re|) ^ 2) * (1 / (1 + s.val * |z.im|) ^ 2) := by
  have hs : 0 < s.val := s.property
  have hx : 0 < 1 + s.val * |z.re| := by positivity
  have hy : 0 < 1 + s.val * |z.im| := by positivity
  have hre : 1 + s.val * |z.re| ≤ 1 + s.val * ‖z‖ := by
    linarith only [mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm z) hs.le]
  have him : 1 + s.val * |z.im| ≤ 1 + s.val * ‖z‖ := by
    linarith only [mul_le_mul_of_nonneg_left (Complex.abs_im_le_norm z) hs.le]
  have hprod : (1 + s.val * |z.re|) ^ 2 * (1 + s.val * |z.im|) ^ 2 ≤
      (1 + s.val * ‖z‖) ^ 4 := by
    have h := mul_le_mul (pow_le_pow_left₀ hx.le hre 2) (pow_le_pow_left₀ hy.le him 2)
      (sq_nonneg (1 + s.val * |z.im|)) (sq_nonneg (1 + s.val * ‖z‖))
    simpa only [← pow_add] using h
  calc
    _ ≤ 1 / ((1 + s.val * |z.re|) ^ 2 * (1 + s.val * |z.im|) ^ 2) :=
      one_div_le_one_div_of_le (mul_pos (sq_pos_of_pos hx) (sq_pos_of_pos hy)) hprod
    _ = _ := by simp only [one_div, mul_inv_rev]; ring

private def gaussianCoordinates : GaussianInt ≃ ℤ × ℤ where
  toFun z := (z.re, z.im)
  invFun p := ⟨p.1, p.2⟩
  left_inv z := by cases z; rfl
  right_inv p := by cases p; rfl

/-- Fourth-order decay with the zero Gaussian frequency removed. -/
def gaussianTail (s : PositiveScale) (z : GaussianInt) : ℝ :=
  if z = 0 then 0 else 1 / (1 + s.val * ‖(z : ℂ)‖) ^ 4

/-- Every term of the punctured Gaussian envelope is nonnegative. -/
theorem gaussianTail_nonneg (s : PositiveScale) (z : GaussianInt) : 0 ≤ gaussianTail s z := by
  unfold gaussianTail
  split_ifs <;> positivity

private theorem gaussianTail_coordinates_le (s : PositiveScale) (p : ℤ × ℤ) :
    gaussianTail s (gaussianCoordinates.symm p) ≤ offEnvelope s p := by
  by_cases hp : p = 0
  · subst p
    change gaussianTail s (0 : GaussianInt) ≤ offEnvelope s (0 : ℤ × ℤ)
    simp [gaussianTail, offEnvelope]
  · have hz : gaussianCoordinates.symm p ≠ 0 := by
      intro h
      apply hp
      have he := congrArg gaussianCoordinates h
      change p = (0, 0)
      simpa [gaussianCoordinates] using he
    rw [gaussianTail, if_neg hz, offEnvelope, if_neg hp]
    simpa [integerEnvelope, gaussianCoordinates, GaussianInt.toComplex_def] using
      complex_fourth_envelope s (gaussianCoordinates.symm p : ℂ)

private theorem summable_gaussianTail_coordinates (s : PositiveScale) :
    Summable (fun p : ℤ × ℤ => gaussianTail s (gaussianCoordinates.symm p)) := by
  exact Summable.of_nonneg_of_le (fun p => gaussianTail_nonneg s _)
    (gaussianTail_coordinates_le s) (summable_offEnvelope s)

/-- Summability holds for every positive scale, without a lattice-sum premise. -/
theorem summable_gaussianTail (s : PositiveScale) : Summable (gaussianTail s) :=
  (gaussianCoordinates.symm.summable_iff (f := gaussianTail s)).mp
    (summable_gaussianTail_coordinates s)

/-- The punctured Gaussian lattice has a uniform fourth-order bound at every scale. -/
theorem scaled_gaussianTail_le (s : PositiveScale) :
    s.val ^ 2 * (∑' z : GaussianInt, gaussianTail s z) ≤ 12 := by
  have hsum := Summable.tsum_le_tsum (gaussianTail_coordinates_le s)
    (summable_gaussianTail_coordinates s)
    (summable_offEnvelope s)
  rw [gaussianCoordinates.symm.tsum_eq (gaussianTail s)] at hsum
  exact (mul_le_mul_of_nonneg_left hsum (sq_nonneg s.val)).trans (scaled_offEnvelope_le s)

/-- The norm-scale form used after planar Poisson summation is independent of the scale ratio. -/
theorem gaussian_norm_scale_bound (ρ : PositiveScale) :
    ρ.val * (∑' z : GaussianInt, if z = 0 then 0 else
      1 / (1 + ‖(z : ℂ)‖ * Real.sqrt ρ.val) ^ 4) ≤ 12 := by
  have h := scaled_gaussianTail_le (⟨Real.sqrt ρ.val, Real.sqrt_pos.mpr ρ.property⟩ : PositiveScale)
  simpa only [gaussianTail, Real.sq_sqrt ρ.property.le,
    mul_comm (Real.sqrt ρ.val)] using h

/-- Restoring the origin adds exactly its unit mass to the summable envelope. -/
theorem gaussian_full_mass (s : PositiveScale) :
    (∑' z : GaussianInt, 1 / (1 + s.val * ‖(z : ℂ)‖) ^ 4) =
      1 + ∑' z : GaussianInt, gaussianTail s z := by
  have hd := hasSum_ite_eq (0 : GaussianInt) (1 : ℝ)
  have he : (fun z : GaussianInt => 1 / (1 + s.val * ‖(z : ℂ)‖) ^ 4) =
      fun z => (if z = 0 then 1 else 0) + gaussianTail s z := by
    funext z
    by_cases hz : z = 0 <;> simp [gaussianTail, hz]
  rw [he, hd.summable.tsum_add (summable_gaussianTail s), hd.tsum_eq]

/-- The entire scale growth of the full lattice is confined to its zero frequency. -/
theorem scaled_gaussian_full_bounds (s : PositiveScale) :
    s.val ^ 2 ≤ s.val ^ 2 * (∑' z : GaussianInt, 1 / (1 + s.val * ‖(z : ℂ)‖) ^ 4) ∧
      s.val ^ 2 * (∑' z : GaussianInt, 1 / (1 + s.val * ‖(z : ℂ)‖) ^ 4) ≤ s.val ^ 2 + 12 := by
  have hpos : 0 ≤ s.val ^ 2 * (∑' z : GaussianInt, gaussianTail s z) :=
    mul_nonneg (sq_nonneg s.val) (tsum_nonneg (gaussianTail_nonneg s))
  have hb := scaled_gaussianTail_le s
  rw [gaussian_full_mass]
  constructor <;> nlinarith only [hpos, hb]

end GaloisForLFunctions.MetaplecticMobiusDescent.QuarticPoisson
