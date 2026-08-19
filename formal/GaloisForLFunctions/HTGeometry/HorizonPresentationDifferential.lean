import GaloisForLFunctions.HTGeometry.HorizonFibrePresentation

/-!
# The differential of the critical fibre presentation

Differentiating the truncated compatibility equations in the low unknowns gives the Sylvester block
of the completed jet and its reciprocal.  A raw unknown occurs only in the raw coefficients and a
reciprocal unknown only in the reciprocal ones, so each derivative is a single Kronecker delta and
the sum over the convolution collapses to one term:

```text
pderiv_horizonRawCoeff_recipVar, pderiv_horizonRecipCoeff_rawVar     the mixed derivatives vanish
pderiv_horizonRawCoeff_rawVar, pderiv_horizonRecipCoeff_recipVar     the pure ones are deltas
pderiv_horizonRelation_rawVar
    ** ∂ f_k / ∂ a_{i₀} = Y_{k - i₀}  for i₀ ≤ k, and 0 otherwise **
pderiv_horizonRelation_recipVar
    ** ∂ f_k / ∂ b_{j₀} = A_{k - j₀}  for j₀ ≤ k, and 0 otherwise **
```

So the presentation differential is the Sylvester matrix `[T(Y) | T(A)]` of the completed raw jet
and its reciprocal, truncated at the horizon — the concrete form of the Jacobian that the
Jacobian–different bridge consumes.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open Polynomial MvPolynomial

variable {A : Type*} [CommRing A] {m n : ℕ} {P Q : A[X]}

/-- A reciprocal variable does not occur in a raw coefficient. -/
theorem pderiv_horizonRawCoeff_recipVar (j₀ : ℕ) (hj₀ : j₀ < n) (i : ℕ) :
    pderiv (⟨m + j₀, by omega⟩ : Fin (m + n)) (horizonRawCoeff A m n P i) = 0 := by
  classical
  rw [horizonRawCoeff]
  split_ifs with hi
  · rw [map_add, MvPolynomial.pderiv_C, add_zero, MvPolynomial.pderiv_X_of_ne]
    intro hcon
    have := congrArg Fin.val hcon
    simp at this
    omega
  · exact MvPolynomial.pderiv_C

/-- A raw variable does not occur in a reciprocal coefficient. -/
theorem pderiv_horizonRecipCoeff_rawVar (i₀ : ℕ) (hi₀ : i₀ < m) (j : ℕ) :
    pderiv (⟨i₀, by omega⟩ : Fin (m + n)) (horizonRecipCoeff A m n Q j) = 0 := by
  classical
  rw [horizonRecipCoeff]
  split_ifs with hj
  · rw [map_add, MvPolynomial.pderiv_C, add_zero, MvPolynomial.pderiv_X_of_ne]
    intro hcon
    have := congrArg Fin.val hcon
    simp at this
    omega
  · exact MvPolynomial.pderiv_C

/-- The raw derivative of a raw coefficient is the Kronecker delta. -/
theorem pderiv_horizonRawCoeff_rawVar (i₀ : ℕ) (hi₀ : i₀ < m) (i : ℕ) :
    pderiv (⟨i₀, by omega⟩ : Fin (m + n)) (horizonRawCoeff A m n P i)
      = if i = i₀ then 1 else 0 := by
  classical
  rw [horizonRawCoeff]
  split_ifs with hi hii
  · subst hii
    rw [map_add, MvPolynomial.pderiv_C, add_zero, MvPolynomial.pderiv_X_self]
  · rw [map_add, MvPolynomial.pderiv_C, add_zero, MvPolynomial.pderiv_X_of_ne]
    intro hcon
    exact hii (congrArg Fin.val hcon)
  · omega
  · exact MvPolynomial.pderiv_C

/-- The reciprocal derivative of a reciprocal coefficient is the Kronecker delta. -/
theorem pderiv_horizonRecipCoeff_recipVar (j₀ : ℕ) (hj₀ : j₀ < n) (j : ℕ) :
    pderiv (⟨m + j₀, by omega⟩ : Fin (m + n)) (horizonRecipCoeff A m n Q j)
      = if j = j₀ then 1 else 0 := by
  classical
  rw [horizonRecipCoeff]
  split_ifs with hj hjj
  · subst hjj
    rw [map_add, MvPolynomial.pderiv_C, add_zero, MvPolynomial.pderiv_X_self]
  · rw [map_add, MvPolynomial.pderiv_C, add_zero, MvPolynomial.pderiv_X_of_ne]
    intro hcon
    exact hjj (by
      have hv : m + j = m + j₀ := by simpa using congrArg Fin.val hcon
      omega)
  · omega
  · exact MvPolynomial.pderiv_C

/-- **The raw column of the presentation differential.**  Differentiating the `k`-th compatibility
equation in a raw unknown returns a reciprocal coefficient. -/
theorem pderiv_horizonRelation_rawVar (i₀ : ℕ) (hi₀ : i₀ < m) (k : Fin (m + n)) :
    pderiv (⟨i₀, by omega⟩ : Fin (m + n)) (horizonRelation A m n P Q k)
      = if i₀ ≤ (k : ℕ) then horizonRecipCoeff A m n Q ((k : ℕ) - i₀) else 0 := by
  classical
  rw [horizonRelation, map_sub]
  have hconst : pderiv (⟨i₀, by omega⟩ : Fin (m + n))
      (if (k : ℕ) = 0 then (1 : MvPolynomial (Fin (m + n)) A) else 0) = 0 := by
    split_ifs <;> simp
  rw [hconst, sub_zero, map_sum]
  have hterm : ∀ i ∈ Finset.range ((k : ℕ) + 1),
      pderiv (⟨i₀, by omega⟩ : Fin (m + n))
          (horizonRawCoeff A m n P i * horizonRecipCoeff A m n Q ((k : ℕ) - i))
        = if i = i₀ then horizonRecipCoeff A m n Q ((k : ℕ) - i₀) else 0 := by
    intro i _
    rw [MvPolynomial.pderiv_mul, pderiv_horizonRecipCoeff_rawVar i₀ hi₀, mul_zero, add_zero,
      pderiv_horizonRawCoeff_rawVar i₀ hi₀]
    split_ifs with h
    · rw [h, one_mul]
    · rw [zero_mul]
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq' (Finset.range ((k : ℕ) + 1)) i₀]
  by_cases hle : i₀ ≤ (k : ℕ)
  · rw [if_pos (Finset.mem_range.mpr (by omega)), if_pos hle]
  · rw [if_neg (by simpa [Finset.mem_range] using by omega : i₀ ∉ Finset.range ((k : ℕ) + 1)),
      if_neg hle]

/-- **The reciprocal column of the presentation differential.** -/
theorem pderiv_horizonRelation_recipVar (j₀ : ℕ) (hj₀ : j₀ < n) (k : Fin (m + n)) :
    pderiv (⟨m + j₀, by omega⟩ : Fin (m + n)) (horizonRelation A m n P Q k)
      = if j₀ ≤ (k : ℕ) then horizonRawCoeff A m n P ((k : ℕ) - j₀) else 0 := by
  classical
  rw [horizonRelation, map_sub]
  have hconst : pderiv (⟨m + j₀, by omega⟩ : Fin (m + n))
      (if (k : ℕ) = 0 then (1 : MvPolynomial (Fin (m + n)) A) else 0) = 0 := by
    split_ifs <;> simp
  rw [hconst, sub_zero, map_sum]
  have hterm : ∀ i ∈ Finset.range ((k : ℕ) + 1),
      pderiv (⟨m + j₀, by omega⟩ : Fin (m + n))
          (horizonRawCoeff A m n P i * horizonRecipCoeff A m n Q ((k : ℕ) - i))
        = if i = (k : ℕ) - j₀ ∧ j₀ ≤ (k : ℕ) then horizonRawCoeff A m n P ((k : ℕ) - j₀)
          else 0 := by
    intro i hi
    have hik : i ≤ (k : ℕ) := by have := Finset.mem_range.mp hi; omega
    rw [MvPolynomial.pderiv_mul, pderiv_horizonRawCoeff_recipVar j₀ hj₀, zero_mul, zero_add,
      pderiv_horizonRecipCoeff_recipVar j₀ hj₀]
    by_cases hj : (k : ℕ) - i = j₀
    · rw [if_pos hj, mul_one, if_pos ⟨by omega, by omega⟩]
      congr 1
      omega
    · rw [if_neg hj, mul_zero, if_neg]
      rintro ⟨h1, h2⟩
      exact hj (by omega)
  rw [Finset.sum_congr rfl hterm]
  by_cases hle : j₀ ≤ (k : ℕ)
  · rw [if_pos hle]
    have hrw : ∀ i ∈ Finset.range ((k : ℕ) + 1),
        (if i = (k : ℕ) - j₀ ∧ j₀ ≤ (k : ℕ) then horizonRawCoeff A m n P ((k : ℕ) - j₀) else 0)
          = if i = (k : ℕ) - j₀ then horizonRawCoeff A m n P ((k : ℕ) - j₀) else 0 := by
      intro i _
      by_cases h : i = (k : ℕ) - j₀
      · rw [if_pos ⟨h, hle⟩, if_pos h]
      · rw [if_neg (fun hc => h hc.1), if_neg h]
    rw [Finset.sum_congr rfl hrw,
      Finset.sum_ite_eq' (Finset.range ((k : ℕ) + 1)) ((k : ℕ) - j₀),
      if_pos (Finset.mem_range.mpr (by omega))]
  · rw [if_neg hle]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [if_neg]
    rintro ⟨-, h2⟩
    exact hle h2

end

end GaloisForLFunctions.HTGeometry
