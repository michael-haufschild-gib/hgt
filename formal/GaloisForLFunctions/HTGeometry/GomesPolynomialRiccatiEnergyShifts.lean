import GaloisForLFunctions.HTGeometry.GomesForcedPolynomialODE

/-!
# Complete constant-energy shifts of real polynomial Riccati images

The reconstruction experiment associated with arXiv:2607.24901v1 section 4 extends
from exact equality to equality up to a constant energy reference. The only polynomial
possibilities are identical inputs, constant inputs, and opposite affine inputs.
-/

noncomputable section
open Polynomial

namespace GaloisForLFunctions.HTGeometry

/-- Equal derivatives and a constant difference of squares force equality or two constant inputs. -/
theorem gomesPolynomialDerivative_square_shift_iff (U V : ℝ[X]) (k : ℝ) :
    (U.derivative = V.derivative ∧ U ^ 2 = V ^ 2 + C k) ↔
      (U = V ∧ k = 0) ∨ ∃ a b : ℝ, U = C a ∧ V = C b ∧ a ^ 2 = b ^ 2 + k := by
  constructor
  · rintro ⟨hd, hs⟩
    have ht := congrArg Polynomial.derivative hs
    simp only [pow_two, derivative_mul, derivative_add, derivative_C, add_zero, hd] at ht
    have hp : 2 * (V.derivative * (U - V)) = 0 := by linear_combination ht
    have hz : V.derivative * (U - V) = 0 := (mul_eq_zero.mp hp).resolve_left two_ne_zero
    rcases mul_eq_zero.mp hz with hv | he
    · let a := U.coeff 0
      let b := V.coeff 0
      have ha : U = C a := eq_C_of_derivative_eq_zero (hd.trans hv)
      have hb : V = C b := eq_C_of_derivative_eq_zero hv
      refine Or.inr ⟨a, b, ha, hb, ?_⟩
      rw [ha, hb] at hs
      have hx := congrArg (Polynomial.eval 0) hs
      simpa only [eval_pow, eval_add, eval_C] using hx
    · have he : U = V := sub_eq_zero.mp he
      refine Or.inl ⟨he, ?_⟩
      have hx := congrArg (Polynomial.eval 0) hs
      simp only [eval_pow, eval_add, eval_C, he] at hx
      linarith
  · rintro (⟨rfl, rfl⟩ | ⟨a, b, rfl, rfl, hs⟩)
    · simp
    · refine ⟨by simp, ?_⟩
      apply Polynomial.funext
      intro x
      simpa only [eval_pow, eval_add, eval_C] using hs

/-- Constant Riccati differences either preserve the derivative or reverse the whole input. -/
theorem gomesPolynomialRiccati_shifted_parts_iff (U V : ℝ[X]) (k : ℝ) :
    gomesPolynomialRiccati U = gomesPolynomialRiccati V + C k ↔
      (U.derivative = V.derivative ∧ U ^ 2 = V ^ 2 + C k) ∨
        (U = -V ∧ (U - V).derivative = C k) := by
  constructor
  · intro h
    have hode : (U - V).derivative = -(U + V) * (U - V) + C k := by
      simp only [derivative_sub]
      unfold gomesPolynomialRiccati at h
      linear_combination h
    rcases (gomesPolynomialDerivative_forced_iff (-(U + V)) (U - V) k).mp hode with
      ⟨hd, hp⟩ | ⟨ha, hd⟩
    · left
      simp only [derivative_sub] at hd
      exact ⟨sub_eq_zero.mp hd, by linear_combination -hp⟩
    · exact Or.inr ⟨eq_neg_of_add_eq_zero_left (neg_eq_zero.mp ha), hd⟩
  · rintro (⟨hd, hs⟩ | ⟨hu, hd⟩)
    · unfold gomesPolynomialRiccati
      rw [hd, hs]
      ring
    · have hs : U ^ 2 = V ^ 2 := by rw [hu]; ring
      simp only [derivative_sub] at hd
      unfold gomesPolynomialRiccati
      linear_combination hd + hs

/-- Complete trichotomy for arbitrary polynomial Riccati images differing by a constant. -/
theorem gomesPolynomialRiccati_shifted_iff (U V : ℝ[X]) (k : ℝ) :
    gomesPolynomialRiccati U = gomesPolynomialRiccati V + C k ↔
      (U = V ∧ k = 0) ∨
        (∃ a b : ℝ, U = C a ∧ V = C b ∧ a ^ 2 = b ^ 2 + k) ∨
          (U = -V ∧ U.derivative = C (k / 2)) := by
  rw [gomesPolynomialRiccati_shifted_parts_iff, gomesPolynomialDerivative_square_shift_iff]
  constructor
  · rintro ((he | hc) | ⟨hu, hd⟩)
    · exact Or.inl he
    · exact Or.inr (Or.inl hc)
    · refine Or.inr (Or.inr ⟨hu, ?_⟩)
      apply Polynomial.funext
      intro x
      have hx := congrArg (Polynomial.eval x) hd
      have hy := congrArg (fun P : ℝ[X] => P.derivative.eval x) hu
      simp only [derivative_sub, derivative_neg, eval_sub, eval_neg, eval_C] at hx hy ⊢
      linarith
  · rintro (he | hc | ⟨hu, hd⟩)
    · exact Or.inl (Or.inl he)
    · exact Or.inl (Or.inr hc)
    · refine Or.inr ⟨hu, ?_⟩
      apply Polynomial.funext
      intro x
      have hx := congrArg (Polynomial.eval x) hd
      have hy := congrArg (fun P : ℝ[X] => P.derivative.eval x) hu
      simp only [derivative_sub, derivative_neg, eval_sub, eval_neg, eval_C] at hx hy ⊢
      linarith

/-- Every nonconstant exceptional input is explicitly affine with slope fixed by the energy shift. -/
theorem gomesPolynomialRiccati_shifted_profiles_iff (U V : ℝ[X]) (k : ℝ) :
    gomesPolynomialRiccati U = gomesPolynomialRiccati V + C k ↔
      (U = V ∧ k = 0) ∨
        (∃ a b : ℝ, U = C a ∧ V = C b ∧ a ^ 2 = b ^ 2 + k) ∨
          ∃ a : ℝ, U = C (k / 2) * X + C a ∧ V = -U := by
  rw [gomesPolynomialRiccati_shifted_iff]
  constructor
  · rintro (he | hc | ⟨hu, hd⟩)
    · exact Or.inl he
    · exact Or.inr (Or.inl hc)
    · obtain ⟨a, ha⟩ := (gomesDilatonDerivative_constant_iff U (k / 2)).mp hd
      exact Or.inr (Or.inr ⟨a, ha, ((neg_eq_iff_eq_neg).mpr hu).symm⟩)
  · rintro (he | hc | ⟨a, ha, hv⟩)
    · exact Or.inl he
    · exact Or.inr (Or.inl hc)
    · refine Or.inr (Or.inr ⟨?_, (gomesDilatonDerivative_constant_iff U (k / 2)).mpr ⟨a, ha⟩⟩)
      rw [hv, neg_neg]

/-- Every real energy offset is realized by a pair of opposite affine Riccati coefficients. -/
theorem gomesPolynomialRiccati_energy_shift_surjective (k : ℝ) :
    ∃ U V : ℝ[X], gomesPolynomialRiccati U = gomesPolynomialRiccati V + C k := by
  let U : ℝ[X] := C (k / 2) * X
  refine ⟨U, -U, (gomesPolynomialRiccati_shifted_profiles_iff U (-U) k).mpr ?_⟩
  exact Or.inr (Or.inr ⟨0, by rw [map_zero, add_zero], rfl⟩)

end GaloisForLFunctions.HTGeometry
