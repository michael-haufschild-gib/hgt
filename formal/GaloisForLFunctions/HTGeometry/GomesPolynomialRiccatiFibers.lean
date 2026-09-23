import GaloisForLFunctions.HTGeometry.GomesFinitePolynomialHamiltonianReconstruction

/-!
# Exact fibers of the real polynomial Riccati map

The derivative-divisibility obstruction prevents cancellation between the derivative
and square parts of a polynomial Riccati image. Its only nontrivial fibers are pairs
of opposite constant polynomials. This is the algebraic reconstruction boundary behind
the exceptional polynomial Hamiltonian coincidences in the Gomes experiment.
-/

noncomputable section
open Polynomial

namespace GaloisForLFunctions.HTGeometry

/-- A polynomial logarithmic derivative can be polynomial only in the constant-solution case. -/
theorem gomesPolynomialDerivative_multiple_iff (A B : ℝ[X]) :
    B.derivative = A * B ↔ B = 0 ∨ (A = 0 ∧ B.derivative = 0) := by
  constructor
  · intro h
    have hd : B.derivative = 0 := dvd_derivative_iff.mp ⟨A, by rw [h, mul_comm]⟩
    have hp : A * B = 0 := h.symm.trans hd
    rcases mul_eq_zero.mp hp with ha | hb
    · exact Or.inr ⟨ha, hd⟩
    · exact Or.inl hb
  · rintro (rfl | ⟨ha, hb⟩)
    · rw [derivative_zero, mul_zero]
    · rw [ha, hb, zero_mul]

/-- The polynomial Riccati image of a polynomial connection coefficient. -/
def gomesPolynomialRiccati (U : ℝ[X]) : ℝ[X] := U.derivative + U ^ (2 : ℕ)

/-- Derivative and square contributions cannot compensate in equal polynomial Riccati images. -/
theorem gomesPolynomialRiccati_eq_iff_parts (U V : ℝ[X]) :
    gomesPolynomialRiccati U = gomesPolynomialRiccati V ↔
      U.derivative = V.derivative ∧ U ^ (2 : ℕ) = V ^ (2 : ℕ) := by
  constructor
  · intro h
    have hdvd : (U - V) ∣ (U - V).derivative := by
      refine ⟨-(U + V), ?_⟩
      simp only [derivative_sub]
      unfold gomesPolynomialRiccati at h
      linear_combination h
    have hd := dvd_derivative_iff.mp hdvd
    simp only [derivative_sub] at hd
    have hder : U.derivative = V.derivative := sub_eq_zero.mp hd
    refine ⟨hder, ?_⟩
    unfold gomesPolynomialRiccati at h
    rw [hder] at h
    exact add_left_cancel h
  · rintro ⟨hd, hs⟩
    unfold gomesPolynomialRiccati
    rw [hd, hs]

/-- Equal Riccati images have identical inputs, or opposite inputs with zero derivative. -/
theorem gomesPolynomialRiccati_eq_iff (U V : ℝ[X]) :
    gomesPolynomialRiccati U = gomesPolynomialRiccati V ↔
      U = V ∨ (U = -V ∧ U.derivative = 0) := by
  rw [gomesPolynomialRiccati_eq_iff_parts]
  constructor
  · rintro ⟨hd, hs⟩
    have hp : (U - V) * (U + V) = 0 := by linear_combination hs
    rcases mul_eq_zero.mp hp with hsame | hopp
    · exact Or.inl (sub_eq_zero.mp hsame)
    · refine Or.inr ⟨eq_neg_of_add_eq_zero_left hopp, ?_⟩
      have hsum := congrArg Polynomial.derivative hopp
      simp only [derivative_add, derivative_zero] at hsum
      apply Polynomial.funext
      intro x
      have hx := congrArg (Polynomial.eval x) hsum
      have hy := congrArg (Polynomial.eval x) hd
      simp only [eval_add, eval_zero] at hx ⊢
      linarith
  · rintro (rfl | ⟨hu, hd⟩)
    · exact ⟨rfl, rfl⟩
    · have hv : V.derivative = 0 := by
        have hh := congrArg Polynomial.derivative hu
        rw [derivative_neg, hd] at hh
        exact neg_eq_zero.mp hh.symm
      refine ⟨hd.trans hv.symm, ?_⟩
      rw [hu]
      ring

/-- The only nontrivial polynomial Riccati fibers consist of opposite constants. -/
theorem gomesPolynomialRiccati_eq_iff_constants (U V : ℝ[X]) :
    gomesPolynomialRiccati U = gomesPolynomialRiccati V ↔
      U = V ∨ ∃ c : ℝ, U = C c ∧ V = C (-c) := by
  rw [gomesPolynomialRiccati_eq_iff]
  constructor
  · rintro (h | ⟨hu, hd⟩)
    · exact Or.inl h
    · let c := U.coeff 0
      have hc : U = C c := eq_C_of_derivative_eq_zero hd
      refine Or.inr ⟨c, hc, ?_⟩
      rw [← neg_eq_iff_eq_neg] at hu
      rw [← hu, hc, map_neg]
  · rintro (h | ⟨c, rfl, rfl⟩)
    · exact Or.inl h
    · refine Or.inr ⟨?_, derivative_C⟩
      rw [map_neg, neg_neg]

/-- A constant Riccati image forces a constant input, with its exact squared value. -/
theorem gomesPolynomialRiccati_constant_iff (U : ℝ[X]) (k : ℝ) :
    gomesPolynomialRiccati U = C k ↔ ∃ c : ℝ, U = C c ∧ c ^ (2 : ℕ) = k := by
  constructor
  · intro h
    have hd := congrArg Polynomial.derivative h
    simp only [gomesPolynomialRiccati, derivative_add, pow_two, derivative_mul, derivative_C] at hd
    have hode : U.derivative.derivative = (-2 * U) * U.derivative := by
      linear_combination hd
    have hu : U.derivative = 0 := by
      rcases (gomesPolynomialDerivative_multiple_iff (-2 * U) U.derivative).mp hode with hz | ⟨hz, _⟩
      · exact hz
      · rcases mul_eq_zero.mp hz with htwo | hzero
        · exact False.elim ((neg_ne_zero.mpr (two_ne_zero : (2 : ℝ[X]) ≠ 0)) htwo)
        · rw [hzero, derivative_zero]
    let c := U.coeff 0
    have hc : U = C c := eq_C_of_derivative_eq_zero hu
    refine ⟨c, hc, ?_⟩
    rw [hc] at h
    simp only [gomesPolynomialRiccati, derivative_C, zero_add, ← map_pow] at h
    exact C_injective h
  · rintro ⟨c, rfl, rfl⟩
    simp only [gomesPolynomialRiccati, derivative_C, zero_add, map_pow]

/-- A prescribed square has exactly the two expected constant preimages. -/
theorem gomesPolynomialRiccati_square_fiber (U : ℝ[X]) (r : ℝ) :
    gomesPolynomialRiccati U = C (r ^ (2 : ℕ)) ↔ U = C r ∨ U = C (-r) := by
  rw [gomesPolynomialRiccati_constant_iff]
  constructor
  · rintro ⟨c, hc, hs⟩
    have hp : (c - r) * (c + r) = 0 := by nlinarith
    rcases mul_eq_zero.mp hp with hm | hp
    · exact Or.inl (hc.trans (congrArg C (sub_eq_zero.mp hm)))
    · exact Or.inr (hc.trans (congrArg C (eq_neg_of_add_eq_zero_left hp)))
  · rintro (rfl | rfl)
    · exact ⟨r, rfl, rfl⟩
    · exact ⟨-r, rfl, by ring⟩

/-- Constant images of polynomial Riccati coefficients are exactly the nonnegative constants. -/
theorem gomesPolynomialRiccati_constant_image_iff (k : ℝ) :
    (∃ U : ℝ[X], gomesPolynomialRiccati U = C k) ↔ 0 ≤ k := by
  constructor
  · rintro ⟨U, h⟩
    obtain ⟨c, _, hc⟩ := (gomesPolynomialRiccati_constant_iff U k).mp h
    rw [← hc]
    exact sq_nonneg c
  · intro h
    refine ⟨C (Real.sqrt k), (gomesPolynomialRiccati_constant_iff _ _).mpr ?_⟩
    exact ⟨Real.sqrt k, rfl, Real.sq_sqrt h⟩

end GaloisForLFunctions.HTGeometry
