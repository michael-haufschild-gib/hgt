import GaloisForLFunctions.ArithmeticKunnethTheory.WeightFamilies.KloostermanProbabilityLaw
import GaloisForLFunctions.MultiscaleMollifiedZetaField.ThePrimeFieldIsGaussian
import GaloisForLFunctions.HTGeometry.CentralizerBudgetSplit

/-!
# Uniform replacement of Kloosterman characteristic functions

Exact centering and variance identify the quadratic Taylor polynomial.
The uniform third absolute moment controls the cubic remainder. Telescoping
products then allows every prime to be replaced by a fixed reference prime.
-/

open Finset MeasureTheory ProbabilityTheory Complex
open GaloisForLFunctions.MultiscaleMollifiedZetaField

namespace GaloisForLFunctions.ArithmeticKunnethTheory.WeightFamilies
noncomputable section

/-- A prime-independent cubic Taylor estimate for the standardized empirical law. -/
theorem norm_charFun_primeKloostermanLaw_sub_quadratic (p : Nat.Primes) (t : ℝ) :
    ‖charFun (primeKloostermanLaw p) t - (1 - (t : ℂ) ^ 2 / 2)‖ ≤ |t| ^ 3 / 3 := by
  have hpoly : ∫ x, (1 + ((t * x : ℝ) : ℂ) * I -
      ((t ^ 2 / 2 * x ^ 2 : ℝ) : ℂ)) ∂primeKloostermanLaw p =
      1 - (t : ℂ) ^ 2 / 2 := by
    rw [integral_sub (integrable_primeKloostermanLaw p _)
      (integrable_primeKloostermanLaw p _),
      integral_add (integrable_primeKloostermanLaw p _)
        (integrable_primeKloostermanLaw p _),
      integral_mul_const, integral_complex_ofReal, integral_complex_ofReal,
      integral_const_mul, integral_const_mul, integral_primeKloostermanLaw_id,
      integral_primeKloostermanLaw_sq]
    simp
  have hrem (x : ℝ) : ‖cexp (((t * x : ℝ) : ℂ) * I) -
      (1 + ((t * x : ℝ) : ℂ) * I - ((t ^ 2 / 2 * x ^ 2 : ℝ) : ℂ))‖ ≤
      |t| ^ 3 / 6 * |x| ^ 3 := by
    have h := norm_cexp_sub_sum_le 3 (t * x)
    have hexpand : expRemainder 3 (t * x) =
        cexp (((t * x : ℝ) : ℂ) * I) -
          (1 + ((t * x : ℝ) : ℂ) * I - ((t ^ 2 / 2 * x ^ 2 : ℝ) : ℂ)) := by
      unfold expRemainder
      simp only [sum_range_succ, sum_range_zero, Nat.factorial]
      push_cast
      ring_nf
      rw [Complex.I_sq]
      ring
    rw [hexpand] at h
    convert h using 1
    norm_num [Nat.factorial, abs_mul, mul_pow]
    ring
  have hbound : ‖charFun (primeKloostermanLaw p) t - (1 - (t : ℂ) ^ 2 / 2)‖ ≤
      |t| ^ 3 / 6 * ∫ x, |x| ^ 3 ∂primeKloostermanLaw p := by
    rw [charFun_apply_real, ← hpoly]
    simp only [← Complex.ofReal_mul]
    rw [← integral_sub (integrable_primeKloostermanLaw p _)
      (integrable_primeKloostermanLaw p _)]
    refine (norm_integral_le_integral_norm _).trans ?_
    rw [← integral_const_mul]
    exact integral_mono (integrable_primeKloostermanLaw p _)
      (integrable_primeKloostermanLaw p _) hrem
  have hthird := mul_le_mul_of_nonneg_left
    (integral_primeKloostermanLaw_abs_cube_le p) (by positivity : 0 ≤ |t| ^ 3 / 6)
  linarith only [hbound, hthird]

/-- Two primes have matching quadratic Taylor terms, independently of their sizes. -/
theorem norm_charFun_primeKloostermanLaw_sub (p q : Nat.Primes) (t : ℝ) :
    ‖charFun (primeKloostermanLaw p) t - charFun (primeKloostermanLaw q) t‖ ≤
      2 * |t| ^ 3 / 3 := by
  have h := norm_sub_le (charFun (primeKloostermanLaw p) t - (1 - (t : ℂ)^2 / 2))
    (charFun (primeKloostermanLaw q) t - (1 - (t : ℂ)^2 / 2))
  rw [sub_sub_sub_cancel_right] at h
  linarith only [h, norm_charFun_primeKloostermanLaw_sub_quadratic p t,
    norm_charFun_primeKloostermanLaw_sub_quadratic q t]

/-- Replacing all primes by one reference prime costs at most the sum of cubic errors. -/
theorem norm_prod_charFun_primeKloostermanLaw_sub_pow
    (p : ℕ → Nat.Primes) (q : Nat.Primes) (n : ℕ) (t : ℝ) :
    ‖(∏ i ∈ range n, charFun (primeKloostermanLaw (p i)) t) -
      charFun (primeKloostermanLaw q) t ^ n‖ ≤ (n : ℝ) * (2 * |t| ^ 3 / 3) := by
  let f := fun i => charFun (primeKloostermanLaw (p i)) t
  let g := fun _ : ℕ => charFun (primeKloostermanLaw q) t
  have h := HTGeometry.norm_listProd_sub_le
    ((range n).toList.map f) ((range n).toList.map g)
    (by
      intro a ha
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp ha
      exact norm_charFun_le_one t)
    (by
      intro a ha
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp ha
      exact norm_charFun_le_one t)
    (by simp only [List.length_map])
  have hzip (l : List ℕ) :
      List.zipWith (fun a b : ℂ => ‖a - b‖) (l.map f) (l.map g) =
      l.map (fun i => ‖f i - g i‖) := by
    induction l with
    | nil => rfl
    | cons i l ih => simp only [List.map_cons, List.zipWith_cons_cons, ih]
  rw [hzip] at h
  simp only [prod_map_toList, sum_map_toList, f, g, prod_const, card_range] at h
  exact h.trans ((sum_le_sum fun i _ => norm_charFun_primeKloostermanLaw_sub (p i) q t).trans_eq
    (by simp only [sum_const, card_range, nsmul_eq_mul]))

#print axioms norm_charFun_primeKloostermanLaw_sub_quadratic
#print axioms norm_prod_charFun_primeKloostermanLaw_sub_pow

end
end GaloisForLFunctions.ArithmeticKunnethTheory.WeightFamilies
