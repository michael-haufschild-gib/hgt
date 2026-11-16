import GaloisForLFunctions.HTGeometry.Sl2AdjointIrreducible
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic

/-!
# The projective clock of an upper–lower unipotent crossing

The upper-right matrix entry determines a unique compensating clock away
from its Gauss-chart pole. Its derivative is the inverse square of the
denominator; its next two jets have zero Schwarzian combination.
-/

noncomputable section
open Matrix GaloisForLFunctions.HTGeometry
namespace GaloisForLFunctions.BiarithmeticGeometry

/-- The diagonal element in the real split torus. -/
def splitDiagonal (p : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.exp p, 0; 0, Real.exp (-p)]

/-- The denominator of the Gauss chart after following the upper orbit. -/
def crossingDenominator (z p t : ℝ) : ℝ := Real.exp (-p) - z * Real.exp p * t

/-- Compensating upper-unipotent clock. -/
def crossingClock (z p t : ℝ) : ℝ := t * Real.exp p / crossingDenominator z p t

/-- The upper-right entry is the exact obstruction to the lower-diagonal chart. -/
theorem unipotent_crossing_upperRight (z p s t : ℝ) :
    (unipotentUpper s * unipotentLower z * splitDiagonal p * unipotentUpper (-t)) 0 1 =
      s * crossingDenominator z p t - t * Real.exp p := by
  simp only [unipotentUpper, unipotentLower, splitDiagonal, crossingDenominator,
    Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one]
  ring

/-- A non-polar crossing has exactly one compensating upper clock; a pole has none. -/
theorem unipotent_crossing_clock_iff (z p s t : ℝ) :
    (unipotentUpper s * unipotentLower z * splitDiagonal p * unipotentUpper (-t)) 0 1 = 0 ↔
      crossingDenominator z p t ≠ 0 ∧ s = crossingClock z p t := by
  rw [unipotent_crossing_upperRight]
  constructor
  · intro h
    have hd : crossingDenominator z p t ≠ 0 := by
      intro hd
      have ht : t = 0 := by
        have he := Real.exp_ne_zero p
        rw [hd, mul_zero, zero_sub, neg_eq_zero, mul_eq_zero] at h
        exact h.resolve_right he
      simp only [crossingDenominator, ht, mul_zero, sub_zero] at hd
      exact Real.exp_ne_zero (-p) hd
    exact ⟨hd, (eq_div_iff hd).mpr (sub_eq_zero.mp h)⟩
  · rintro ⟨hd, rfl⟩
    rw [crossingClock, div_mul_cancel₀ _ hd, sub_self]

/-- The full crossing identity, with the sole obstruction displayed explicitly. -/
theorem unipotent_crossing_gauss (z p t : ℝ) :
    crossingDenominator z p t = 0 ∨
      unipotentUpper (crossingClock z p t) * unipotentLower z * splitDiagonal p *
        unipotentUpper (-t) =
      unipotentLower (z * Real.exp p * crossingDenominator z p t) *
        !![(crossingDenominator z p t)⁻¹, 0; 0, crossingDenominator z p t] := by
  by_cases hd : crossingDenominator z p t = 0
  · exact Or.inl hd
  · right
    have he : Real.exp p * Real.exp (-p) = 1 := by rw [← Real.exp_add]; simp only [add_neg_cancel, Real.exp_zero]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [unipotentUpper, unipotentLower, splitDiagonal, Matrix.mul_apply,
        Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one, crossingClock]
    all_goals
      field_simp [hd] <;> dsimp only [crossingDenominator] <;> nlinarith only [he]

private theorem crossingClock_hasDerivAt (z p t : ℝ) (hd : crossingDenominator z p t ≠ 0) :
    HasDerivAt (crossingClock z p) ((crossingDenominator z p t)⁻¹ ^ 2) t := by
  have hD : HasDerivAt (crossingDenominator z p) (-(z * Real.exp p)) t := by
    unfold crossingDenominator
    convert ((hasDerivAt_id t).const_mul (z * Real.exp p)).const_sub (Real.exp (-p)) using 1 <;>
      first | rfl | simp only [mul_one]
  have h := ((hasDerivAt_id t).mul_const (Real.exp p)).div hD hd
  apply h.congr_deriv
  have he : Real.exp p * Real.exp (-p) = 1 := by rw [← Real.exp_add]; simp only [add_neg_cancel, Real.exp_zero]
  field_simp [hd]
  dsimp only [crossingDenominator, id_eq]
  nlinarith only [he]

/-- Clock velocity is positive at every point of the Gauss chart. -/
theorem crossingClock_pole_or_positive_derivative (z p t : ℝ) :
    crossingDenominator z p t = 0 ∨
      deriv (crossingClock z p) t = (crossingDenominator z p t)⁻¹ ^ 2 ∧
        0 < deriv (crossingClock z p) t := by
  by_cases hd : crossingDenominator z p t = 0
  · exact Or.inl hd
  · right
    have h := (crossingClock_hasDerivAt z p t hd).deriv
    exact ⟨h, h.symm ▸ sq_pos_of_ne_zero (inv_ne_zero hd)⟩

/-- At the initial point, the clock speed reads the split-torus coordinate exactly. -/
theorem crossingClock_deriv_zero (z p : ℝ) :
    deriv (crossingClock z p) 0 = Real.exp (2 * p) := by
  have hd : crossingDenominator z p 0 ≠ 0 := by
    simpa only [crossingDenominator, mul_zero, sub_zero] using Real.exp_ne_zero (-p)
  rw [(crossingClock_hasDerivAt z p 0 hd).deriv]
  simp only [crossingDenominator, mul_zero, sub_zero, Real.exp_neg, inv_inv,
    pow_two, ← Real.exp_add, two_mul]

/-- Differences of clock values have an exact divided-difference formula off the poles. -/
theorem crossingClock_difference (z p s t : ℝ) :
    crossingDenominator z p s = 0 ∨ crossingDenominator z p t = 0 ∨
      crossingClock z p s - crossingClock z p t =
        (s - t) / (crossingDenominator z p s * crossingDenominator z p t) := by
  by_cases hs : crossingDenominator z p s = 0
  · exact Or.inl hs
  · right
    by_cases ht : crossingDenominator z p t = 0
    · exact Or.inl ht
    · right
      have he : Real.exp p * Real.exp (-p) = 1 := by
        rw [← Real.exp_add]; simp only [add_neg_cancel, Real.exp_zero]
      unfold crossingClock
      field_simp [hs, ht]
      dsimp only [crossingDenominator]
      linear_combination (s - t) * he

/-- A projective crossing clock determines both its lower-unipotent and split-torus coordinates. -/
theorem crossingClock_eq_iff (z p w q : ℝ) :
    crossingClock z p = crossingClock w q ↔ z = w ∧ p = q := by
  constructor
  · intro h
    have hv := congrArg (fun f : ℝ → ℝ => deriv f 0) h
    rw [crossingClock_deriv_zero, crossingClock_deriv_zero] at hv
    have hpq : p = q := by
      have hh := Real.exp_injective hv
      linarith only [hh]
    subst q
    have h1 := congrFun h 1
    simp only [crossingClock, one_mul, div_eq_mul_inv] at h1
    have hD := inv_injective (mul_left_cancel₀ (Real.exp_ne_zero p) h1)
    simp only [crossingDenominator, mul_one] at hD
    have hz : (z - w) * Real.exp p = 0 := by linear_combination -hD
    exact ⟨sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_right (Real.exp_ne_zero p)), rfl⟩
  · rintro ⟨rfl, rfl⟩
    rfl

/-- The first three projective jet formulas have vanishing Schwarzian numerator. -/
theorem crossingClock_schwarzian_numerator (z p t : ℝ) :
    2 * ((crossingDenominator z p t)⁻¹ ^ 2) *
        (6 * (z * Real.exp p) ^ 2 * (crossingDenominator z p t)⁻¹ ^ 4) -
      3 * (2 * z * Real.exp p * (crossingDenominator z p t)⁻¹ ^ 3) ^ 2 = 0 := by
  ring

/-- The explicit velocity and acceleration are genuine successive derivatives on the chart. -/
theorem crossingClock_pole_or_derivative_jets (z p t : ℝ) :
    crossingDenominator z p t = 0 ∨
      HasDerivAt (crossingClock z p) ((crossingDenominator z p t)⁻¹ ^ 2) t ∧
      HasDerivAt (fun s => (crossingDenominator z p s)⁻¹ ^ 2)
        (2 * z * Real.exp p * (crossingDenominator z p t)⁻¹ ^ 3) t ∧
      HasDerivAt (fun s => 2 * z * Real.exp p * (crossingDenominator z p s)⁻¹ ^ 3)
        (6 * (z * Real.exp p) ^ 2 * (crossingDenominator z p t)⁻¹ ^ 4) t := by
  by_cases hd : crossingDenominator z p t = 0
  · exact Or.inl hd
  · right
    have hD : HasDerivAt (crossingDenominator z p) (-(z * Real.exp p)) t := by
      unfold crossingDenominator
      convert ((hasDerivAt_id t).const_mul (z * Real.exp p)).const_sub (Real.exp (-p)) using 1 <;>
        first | rfl | simp only [mul_one]
    have hi := hD.inv hd
    refine ⟨crossingClock_hasDerivAt z p t hd, ?_, ?_⟩
    · apply (hi.pow 2).congr_deriv
      simp only [Pi.inv_apply, neg_neg, div_eq_mul_inv, inv_pow]
      ring
    · apply ((hi.pow 3).const_mul (2 * z * Real.exp p)).congr_deriv
      simp only [Pi.inv_apply, neg_neg, div_eq_mul_inv, inv_pow]
      ring

end GaloisForLFunctions.BiarithmeticGeometry
