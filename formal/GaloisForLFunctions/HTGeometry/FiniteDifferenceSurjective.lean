import Mathlib

/-!
# The difference operator is surjective on polynomials

`p ↦ p (X + 1) - p` lowers degree by exactly one and multiplies the leading coefficient by the
degree, so every complex polynomial is a difference.  This is the polynomial half of the
description of the shift defects of `C(X)`.
-/

open Polynomial

namespace HTGeometry

theorem natDegree_shiftPow_sub_le (m : ℕ) :
    (((X + 1 : ℂ[X]) ^ (m + 1) - X ^ (m + 1))).natDegree ≤ m := by
  refine Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun k hk => ?_
  rw [Polynomial.coeff_sub, Polynomial.coeff_X_add_one_pow, Polynomial.coeff_X_pow]
  rcases eq_or_ne k (m + 1) with rfl | hne
  · simp
  · rw [if_neg hne, sub_zero]
    exact_mod_cast Nat.choose_eq_zero_of_lt (by omega)

theorem coeff_shiftPow_sub_top (m : ℕ) :
    (((X + 1 : ℂ[X]) ^ (m + 1) - X ^ (m + 1))).coeff m = ((m + 1 : ℕ) : ℂ) := by
  rw [Polynomial.coeff_sub, Polynomial.coeff_X_add_one_pow, Polynomial.coeff_X_pow,
    if_neg (by omega : ¬ m = m + 1), sub_zero]
  have hch : (m + 1).choose m = m + 1 := by
    have h := Nat.choose_symm (n := m + 1) (k := m) (by omega)
    simp only [Nat.add_sub_cancel_left] at h
    rw [← h]
    simp
  rw [hch]

/-- **Every complex polynomial is a finite difference.** -/
theorem exists_comp_sub_eq (p : ℂ[X]) :
    ∃ q : ℂ[X], q.comp (X + 1) - q = p := by
  classical
  induction hn : p.natDegree using Nat.strong_induction_on generalizing p with
  | _ n ih =>
    subst hn
    rcases eq_or_ne p 0 with rfl | hp0
    · exact ⟨0, by simp⟩
    rcases Nat.eq_zero_or_pos p.natDegree with h0 | hpos
    · refine ⟨Polynomial.C (p.coeff 0) * X, ?_⟩
      conv_rhs => rw [Polynomial.eq_C_of_natDegree_eq_zero h0]
      simp only [Polynomial.mul_comp, Polynomial.C_comp, Polynomial.X_comp]
      ring
    · obtain ⟨m, hpm⟩ : ∃ m : ℕ, p.natDegree = m + 1 := ⟨p.natDegree - 1, by omega⟩
      set a : ℂ := p.coeff (m + 1) with ha
      have hane : a ≠ 0 := by
        rw [ha, ← hpm]
        exact Polynomial.leadingCoeff_ne_zero.mpr hp0
      have hmne : ((m + 2 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      set q₀ : ℂ[X] := Polynomial.C (a / ((m + 2 : ℕ) : ℂ)) * X ^ (m + 2) with hq₀
      have hstep : q₀.comp (X + 1) - q₀
          = Polynomial.C (a / ((m + 2 : ℕ) : ℂ)) * ((X + 1) ^ (m + 2) - X ^ (m + 2)) := by
        rw [hq₀]
        simp only [Polynomial.mul_comp, Polynomial.C_comp, Polynomial.pow_comp,
          Polynomial.X_comp]
        ring
      set r : ℂ[X] := p - (q₀.comp (X + 1) - q₀) with hr
      have hrdeg : r.natDegree < m + 1 := by
        refine Nat.lt_of_le_of_lt (Polynomial.natDegree_le_iff_coeff_eq_zero.mpr ?_)
          (by omega : m < m + 1)
        intro k hk
        rw [hr, Polynomial.coeff_sub, hstep, Polynomial.coeff_C_mul]
        rcases eq_or_ne k (m + 1) with rfl | hne
        · rw [coeff_shiftPow_sub_top (m + 1), ← ha,
            show (((m + 1) + 1 : ℕ) : ℂ) = ((m + 2 : ℕ) : ℂ) from by push_cast; ring,
            div_mul_cancel₀ _ hmne, sub_self]
        · have hk1 : p.coeff k = 0 :=
            Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
          have hk2 : (((X + 1 : ℂ[X]) ^ (m + 2) - X ^ (m + 2))).coeff k = 0 :=
            Polynomial.coeff_eq_zero_of_natDegree_lt
              (lt_of_le_of_lt (natDegree_shiftPow_sub_le (m + 1)) (by omega))
          rw [hk1, hk2, mul_zero, sub_zero]
      obtain ⟨q₁, hq₁⟩ := ih r.natDegree (by omega) r rfl
      refine ⟨q₀ + q₁, ?_⟩
      rw [Polynomial.add_comp]
      have hrq : q₁.comp (X + 1) - q₁ = p - (q₀.comp (X + 1) - q₀) := by rw [hq₁, hr]
      linear_combination hrq

end HTGeometry
