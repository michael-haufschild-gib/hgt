import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import GaloisForLFunctions.Bottcher.EntirePolyGrowth

open Polynomial Complex

namespace Bottcher

theorem coeff_comp_neg_X (p : ℂ[X]) (n : ℕ) :
    (p.comp (-X)).coeff n = (-1)^n * p.coeff n := by
  rw [Polynomial.comp_eq_sum_left, Polynomial.sum, Polynomial.finsetSum_coeff]
  rw [Finset.sum_eq_single n]
  · have h1 : ((-X : ℂ[X]))^n = C ((-1)^n) * X^n := by
      rw [neg_pow, C_pow, map_neg, map_one]
    rw [h1, ← mul_assoc, ← C_mul, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      if_pos rfl, mul_one, mul_comm]
  · intro e _ hne
    have h1 : ((-X : ℂ[X]))^e = C ((-1)^e) * X^e := by
      rw [neg_pow, C_pow, map_neg, map_one]
    rw [h1, ← mul_assoc, ← C_mul, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      if_neg (by omega : ¬ n = e), mul_zero]
  · intro hns
    have hz : p.coeff n = 0 := by rwa [Polynomial.mem_support_iff, not_not] at hns
    rw [hz, map_zero, zero_mul, Polynomial.coeff_zero]

/-- **An even polynomial factors through squaring.**  If `Q(-X) = Q`, then `Q = P(X²)` for some `P`. -/
theorem exists_comp_sq_of_even {Q : ℂ[X]} (hev : Q.comp (-X) = Q) :
    ∃ P : ℂ[X], Q = P.comp (X ^ (2 : ℕ)) := by
  have hodd : ∀ m, ¬ 2 ∣ m → Q.coeff m = 0 := by
    intro m hm
    have h := congrArg (fun p => Polynomial.coeff p m) hev
    simp only [coeff_comp_neg_X] at h
    rw [Odd.neg_one_pow (Nat.odd_iff.mpr (by omega))] at h
    linear_combination (-1/2 : ℂ) * h
  set P : ℂ[X] := ∑ k ∈ Finset.range (Q.natDegree + 1), C (Q.coeff (2*k)) * X^k with hPdef
  have hPcoeff : ∀ j, P.coeff j = Q.coeff (2*j) := by
    intro j
    rw [hPdef, Polynomial.finsetSum_coeff, Finset.sum_eq_single j]
    · rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_pos rfl, mul_one]
    · intro k _ hkj
      rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg (by omega : ¬ j = k), mul_zero]
    · intro hjs
      rw [Finset.mem_range, not_lt] at hjs
      rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_pos rfl, mul_one]
      exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  refine ⟨P, ?_⟩
  ext m
  rw [← Polynomial.expand_eq_comp_X_pow, coeff_expand (by norm_num : 0 < 2)]
  split_ifs with hdvd
  · rw [hPcoeff, show 2 * (m / 2) = m from by omega]
  · exact hodd m hdvd

/-- **Entire even classification (task02).**  If `h` is entire, even, of polynomial growth, satisfies
`h(t²) = h(t)² + c·t²`, and `h(0)=1`, then `c ∈ {0,-2}`.  This is the exact statement the
arc-continuation step produces; it factors the even polynomial `h` (via `exists_polynomial_of_entire_polyGrowth`
+ `exists_comp_sq_of_even`) into `P(X²)`, transfers the functional equation to `P(s²)=P(s)²+c·s`
(using that every `w` is a square in `ℂ`), and applies `c_mem_of_poly_functional_eq`. -/
theorem c_mem_of_entire_even_functional_eq {h : ℂ → ℂ} {C : ℝ} {n : ℕ} {c : ℂ}
    (hh : Differentiable ℂ h)
    (hgrowth : ∀ z, ‖h z‖ ≤ C * (max 1 ‖z‖) ^ n)
    (heven : ∀ z, h (-z) = h z)
    (hfe : ∀ t : ℂ, h (t ^ (2 : ℕ)) = (h t) ^ (2 : ℕ) + c * t ^ (2 : ℕ))
    (h0 : h 0 = 1) :
    c = 0 ∨ c = -2 := by
  obtain ⟨Qh, hQh⟩ := exists_polynomial_of_entire_polyGrowth hh hgrowth
  have hQheven : Qh.comp (-X) = Qh := by
    apply Polynomial.funext; intro z
    rw [Polynomial.eval_comp, Polynomial.eval_neg, Polynomial.eval_X, ← hQh, ← hQh, heven]
  obtain ⟨P, hP⟩ := exists_comp_sq_of_even hQheven
  have e1 : ∀ s : ℂ, P.eval (s ^ (2 : ℕ)) = h s := by
    intro s
    rw [hQh s, hP, Polynomial.eval_comp, Polynomial.eval_pow, Polynomial.eval_X]
  have hPfe : P.comp (X ^ (2 : ℕ)) = P ^ (2 : ℕ) + Polynomial.C c * X := by
    apply Polynomial.funext; intro w
    obtain ⟨t, ht⟩ := IsAlgClosed.exists_pow_nat_eq w (n := 2) (by norm_num)
    rw [← ht]
    simp only [Polynomial.eval_comp, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]
    rw [e1 (t ^ (2 : ℕ)), e1 t]
    exact hfe t
  have hP0 : P.coeff 0 = 1 := by
    rw [Polynomial.coeff_zero_eq_eval_zero]
    have he0 := e1 0
    rw [show ((0 : ℂ) ^ (2 : ℕ)) = 0 from by ring] at he0
    rw [he0, h0]
  exact c_mem_of_poly_functional_eq hPfe hP0

end Bottcher
