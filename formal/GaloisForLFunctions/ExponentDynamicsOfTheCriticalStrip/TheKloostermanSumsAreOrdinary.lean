import GaloisForLFunctions.ExponentDynamicsOfTheCriticalStrip.TheGaussSumsOfAPrimeFieldCarryStickelbergersValuation
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# The Kloosterman sums are ordinary

E4 asks whether a lever built from complete exponential sums of bounded rank is non-centred. At rank
one the Gauss sums carry Stickelberger's valuation, and the Möbius sign costs half a unit of weight
at some place. At rank two the Kloosterman sum `K(a) = Σ_{x ≠ 0} ψ(x + a/x)` over `𝔽_p`,
`ψ(y) = ζ^y` in `K = PadicAlgCl p`, has Frobenius eigenvalues `α, β` with `α + β = −K(a)` and
`αβ = p`.

* **`K(a)` is a `p`-adic unit** (`norm_kloosterman_eq_one`): every `ψ(y)` is `1` modulo `ζ − 1`, so
  `K(a) ≡ p − 1 ≡ −1`.
* **Ordinarity** (`norm_kloosterman_eigenvalues`): `α, β` are integral, their product has norm `1/p`
  and their sum is a unit, so one is a unit and the other has norm `1/p`.
* **The price** (`kloostermanDefect_monomial`): normalized by `√p`, `α` and `β` have defects `±1/2`,
  and `α^m β^n` has defect `±(m − n)/2`. Rank two carries the half-integral price of rank one; a
  Kloosterman monomial is pure only when it is a power of `p`.
-/

open Finset

namespace GaloisForLFunctions.ExponentDynamicsOfTheCriticalStrip.Stickelberger

variable (p : ℕ) [hp : Fact p.Prime]

attribute [local instance] neZero_p

/-- The Kloosterman sum `K(a) = Σ_{x ∈ 𝔽_p^×} ψ(x + a x⁻¹)`. -/
noncomputable def kloosterman {ζ : PadicAlgCl p} (hζ : IsPrimitiveRoot ζ p) (a : ZMod p) :
    PadicAlgCl p :=
  ∑ x : (ZMod p)ˣ, AddChar.zmodChar p hζ.pow_eq_one ((x : ZMod p) + a * ((x⁻¹ : (ZMod p)ˣ) : ZMod p))

theorem norm_natCast_p : ‖(p : PadicAlgCl p)‖ = (p : ℝ)⁻¹ := by
  rw [← map_natCast (algebraMap ℚ_[p] (PadicAlgCl p)), PadicAlgCl.norm_extends, Padic.norm_p]

variable {p}

theorem norm_add_one_kloosterman_lt_one {ζ : PadicAlgCl p} (hζ : IsPrimitiveRoot ζ p) (a : ZMod p) :
    ‖kloosterman p hζ a + 1‖ < 1 := by
  set f : (ZMod p)ˣ → PadicAlgCl p := fun x =>
    AddChar.zmodChar p hζ.pow_eq_one ((x : ZMod p) + a * ((x⁻¹ : (ZMod p)ˣ) : ZMod p)) - 1
  have hsum : kloosterman p hζ a + 1 = ∑ x, f x + (p : PadicAlgCl p) := by
    simp only [kloosterman, f, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      ZMod.card_units p, nsmul_eq_mul, mul_one]
    rw [Nat.cast_sub hp.out.one_le, Nat.cast_one]
    ring
  rw [hsum]
  refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ?_ ?_)
  · refine lt_of_le_of_lt (norm_sum_le_of_forall_le _ _ (norm_nonneg (ζ - 1)) fun x _ => ?_)
      (norm_sub_one_lt_one hζ)
    simp only [f, AddChar.zmodChar_apply]
    exact norm_pow_sub_one_le hζ _
  · rw [norm_natCast_p p]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.out.one_lt)

/-- **The Kloosterman sum is a `p`-adic unit.** -/
theorem norm_kloosterman_eq_one {ζ : PadicAlgCl p} (hζ : IsPrimitiveRoot ζ p) (a : ZMod p) :
    ‖kloosterman p hζ a‖ = 1 := by
  have h := norm_add_one_kloosterman_lt_one hζ a
  have e : kloosterman p hζ a = (kloosterman p hζ a + 1) + (-1) := by ring
  rw [e, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [norm_neg, norm_one]; exact h.ne),
    norm_neg, norm_one]
  exact max_eq_right h.le

/-- A root of `X² + KX + p` with `‖K‖ ≤ 1` is integral. -/
theorem norm_le_one_of_quadratic {K α : PadicAlgCl p} (hK : ‖K‖ ≤ 1)
    (h : α ^ 2 + K * α + p = 0) : ‖α‖ ≤ 1 := by
  by_contra hα
  push Not at hα
  have hp1 : ‖(p : PadicAlgCl p)‖ < 1 := by
    rw [norm_natCast_p p]; exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.out.one_lt)
  have h1 : ‖K * α + p‖ < ‖α ^ 2‖ := by
    refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ?_ ?_)
    · rw [norm_mul, norm_pow, sq]
      exact mul_lt_mul_of_pos_right (lt_of_le_of_lt hK hα) (by linarith)
    · rw [norm_pow, sq]
      nlinarith
  have h2 : ‖α ^ 2 + (K * α + p)‖ = ‖α ^ 2‖ := by
    rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h1.ne', max_eq_left h1.le]
  rw [← add_assoc, h, norm_zero, norm_pow] at h2
  nlinarith

/-- **Ordinarity.** If `α + β = −K(a)` and `αβ = p`, one of `α, β` is a unit and the other has norm
`1/p`. -/
theorem norm_kloosterman_eigenvalues {ζ : PadicAlgCl p} (hζ : IsPrimitiveRoot ζ p) (a : ZMod p)
    {α β : PadicAlgCl p} (hsum : α + β = -kloosterman p hζ a) (hprod : α * β = p) :
    (‖α‖ = 1 ∧ ‖β‖ = (p : ℝ)⁻¹) ∨ (‖α‖ = (p : ℝ)⁻¹ ∧ ‖β‖ = 1) := by
  set K := kloosterman p hζ a
  have hK := norm_kloosterman_eq_one hζ a
  have hα : ‖α‖ ≤ 1 := norm_le_one_of_quadratic hK.le (by linear_combination α * hsum - hprod)
  have hβ : ‖β‖ ≤ 1 := norm_le_one_of_quadratic hK.le (by linear_combination β * hsum - hprod)
  have hnp : ‖α‖ * ‖β‖ = (p : ℝ)⁻¹ := by rw [← norm_mul, hprod, norm_natCast_p p]
  have hmax : 1 ≤ max ‖α‖ ‖β‖ := by
    have := IsUltrametricDist.norm_add_le_max α β
    rw [hsum, norm_neg, hK] at this
    exact this
  rcases le_max_iff.mp hmax with h | h
  · have h1 : ‖α‖ = 1 := le_antisymm hα h
    left
    refine ⟨h1, ?_⟩
    rw [h1, one_mul] at hnp
    exact hnp
  · have h1 : ‖β‖ = 1 := le_antisymm hβ h
    right
    refine ⟨?_, h1⟩
    rw [h1, mul_one] at hnp
    exact hnp

/-- Frobenius eigenvalues exist: `X² + K(a)X + p` splits over `PadicAlgCl p`. -/
theorem exists_kloosterman_eigenvalues {ζ : PadicAlgCl p} (hζ : IsPrimitiveRoot ζ p) (a : ZMod p) :
    ∃ α β : PadicAlgCl p, α + β = -kloosterman p hζ a ∧ α * β = p := by
  set K := kloosterman p hζ a
  have hdeg : (Polynomial.X ^ 2 + Polynomial.C K * Polynomial.X +
      Polynomial.C (p : PadicAlgCl p)).degree ≠ 0 := by
    rw [show Polynomial.X ^ 2 + Polynomial.C K * Polynomial.X + Polynomial.C (p : PadicAlgCl p) =
      Polynomial.X ^ 2 + (Polynomial.C K * Polynomial.X + Polynomial.C (p : PadicAlgCl p)) by ring,
      Polynomial.degree_add_eq_left_of_degree_lt, Polynomial.degree_X_pow]
    · norm_num
    · rw [Polynomial.degree_X_pow]
      refine lt_of_le_of_lt (Polynomial.degree_add_le _ _) (max_lt ?_ ?_)
      · exact lt_of_le_of_lt (Polynomial.degree_C_mul_X_le K) (by norm_num)
      · exact lt_of_le_of_lt Polynomial.degree_C_le (by norm_num)
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_root _ hdeg
  refine ⟨α, -K - α, by ring, ?_⟩
  simp only [Polynomial.IsRoot, Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_mul, Polynomial.eval_C] at hα
  linear_combination -hα

/-- The defect `½ + log_p ‖x‖` of an eigenvalue normalized by `√p`. -/
noncomputable def kloostermanDefect (x : PadicAlgCl p) : ℝ := 1 / 2 + Real.logb p ‖x‖

/-- **The price of a Kloosterman monomial**: `α^m β^n` has defect `±(m − n)/2` in total. -/
theorem kloostermanDefect_monomial {ζ : PadicAlgCl p} (hζ : IsPrimitiveRoot ζ p) (a : ZMod p)
    {α β : PadicAlgCl p} (hsum : α + β = -kloosterman p hζ a) (hprod : α * β = p) (m n : ℕ) :
    (m : ℝ) * kloostermanDefect α + n * kloostermanDefect β = ((m : ℝ) - n) / 2 ∨
      (m : ℝ) * kloostermanDefect α + n * kloostermanDefect β = ((n : ℝ) - m) / 2 := by
  have hlog : Real.logb p (p : ℝ)⁻¹ = -1 := by
    rw [Real.logb_inv, Real.logb_self_eq_one (by exact_mod_cast hp.out.one_lt)]
  rcases norm_kloosterman_eigenvalues hζ a hsum hprod with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · left
    simp only [kloostermanDefect, h1, h2, Real.logb_one, hlog]
    ring
  · right
    simp only [kloostermanDefect, h1, h2, Real.logb_one, hlog]
    ring

end GaloisForLFunctions.ExponentDynamicsOfTheCriticalStrip.Stickelberger
