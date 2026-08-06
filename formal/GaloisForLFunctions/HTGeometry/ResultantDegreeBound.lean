import GaloisForLFunctions.HTGeometry.IteratedTotalDegree
import GaloisForLFunctions.HTGeometry.WeightedDeterminantDegree
import GaloisForLFunctions.HTGeometry.TwoVariableResultantBridge

/-!
# The degree of a resultant in the remaining variable

For two polynomials in two variables, the resultant that eliminates the second variable is a
polynomial in the first, and its degree is bounded by the weighted determinant estimate applied to
the Sylvester matrix: the entry in row `i` of a column belonging to one of the two polynomials is a
coefficient of that polynomial, whose degree falls off as the row index grows.

The bound is the classical one — `m b + n a - m n` for declared degrees `m, n` and total degrees
`a, b` — stated in the shifted form that avoids truncated subtraction.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

variable {S : Type*} [CommRing S]

/-- The column weights of the Sylvester matrix: the total degree of the polynomial the column
carries, shifted by the position of the column in its block. -/
noncomputable def sylvesterWeight (a b m n : ℕ) : Fin (m + n) → ℕ :=
  Fin.addCases (fun j : Fin m => b + (j : ℕ)) (fun j : Fin n => a + (j : ℕ))

theorem sylvesterWeight_castAdd (a b m n : ℕ) (j : Fin m) :
    sylvesterWeight a b m n (Fin.castAdd n j) = b + (j : ℕ) := by
  rw [sylvesterWeight, Fin.addCases_left]

theorem sylvesterWeight_natAdd (a b m n : ℕ) (j : Fin n) :
    sylvesterWeight a b m n (Fin.natAdd m j) = a + (j : ℕ) := by
  rw [sylvesterWeight, Fin.addCases_right]

/-- **The entries of the Sylvester matrix obey the shifted degree bound.** -/
theorem degree_sylvester_add_le {f g : (S[X])[X]} {a b : ℕ}
    (hf : ∀ k, (f.coeff k).degree + ((k : ℕ) : WithBot ℕ) ≤ ((a : ℕ) : WithBot ℕ))
    (hg : ∀ k, (g.coeff k).degree + ((k : ℕ) : WithBot ℕ) ≤ ((b : ℕ) : WithBot ℕ))
    (m n : ℕ) (i j : Fin (m + n)) :
    (Polynomial.sylvester f g m n i j).degree + (((i : ℕ) : ℕ) : WithBot ℕ)
      ≤ ((sylvesterWeight a b m n j : ℕ) : WithBot ℕ) := by
  classical
  refine Fin.addCases (fun j₁ => ?_) (fun j₁ => ?_) j
  · rw [sylvesterWeight_castAdd, Polynomial.sylvester, Matrix.of_apply, Fin.addCases_left]
    by_cases hmem : (i : ℕ) ∈ Set.Icc ((j₁ : ℕ)) ((j₁ : ℕ) + n)
    · rw [if_pos hmem]
      have hji : (j₁ : ℕ) ≤ (i : ℕ) := hmem.1
      calc (g.coeff ((i : ℕ) - (j₁ : ℕ))).degree + (((i : ℕ) : ℕ) : WithBot ℕ)
          = ((g.coeff ((i : ℕ) - (j₁ : ℕ))).degree
              + ((((i : ℕ) - (j₁ : ℕ) : ℕ) : ℕ) : WithBot ℕ))
              + (((j₁ : ℕ) : ℕ) : WithBot ℕ) := by
            rw [add_assoc, ← Nat.cast_add, Nat.sub_add_cancel hji]
        _ ≤ ((b : ℕ) : WithBot ℕ) + (((j₁ : ℕ) : ℕ) : WithBot ℕ) := by
            gcongr
            exact hg ((i : ℕ) - (j₁ : ℕ))
        _ = ((b + (j₁ : ℕ) : ℕ) : WithBot ℕ) := by rw [Nat.cast_add]
    · rw [if_neg hmem, Polynomial.degree_zero, WithBot.bot_add]
      exact bot_le
  · rw [sylvesterWeight_natAdd, Polynomial.sylvester, Matrix.of_apply, Fin.addCases_right]
    by_cases hmem : (i : ℕ) ∈ Set.Icc ((j₁ : ℕ)) ((j₁ : ℕ) + m)
    · rw [if_pos hmem]
      have hji : (j₁ : ℕ) ≤ (i : ℕ) := hmem.1
      calc (f.coeff ((i : ℕ) - (j₁ : ℕ))).degree + (((i : ℕ) : ℕ) : WithBot ℕ)
          = ((f.coeff ((i : ℕ) - (j₁ : ℕ))).degree
              + ((((i : ℕ) - (j₁ : ℕ) : ℕ) : ℕ) : WithBot ℕ))
              + (((j₁ : ℕ) : ℕ) : WithBot ℕ) := by
            rw [add_assoc, ← Nat.cast_add, Nat.sub_add_cancel hji]
        _ ≤ ((a : ℕ) : WithBot ℕ) + (((j₁ : ℕ) : ℕ) : WithBot ℕ) := by
            gcongr
            exact hf ((i : ℕ) - (j₁ : ℕ))
        _ = ((a + (j₁ : ℕ) : ℕ) : WithBot ℕ) := by rw [Nat.cast_add]
    · rw [if_neg hmem, Polynomial.degree_zero, WithBot.bot_add]
      exact bot_le

/-- **The degree of the resultant in the remaining variable.**  Stated in shifted form: the
resultant's degree plus the sum of the row indices is at most the sum of the column weights. -/
theorem degree_resultant_add_le {f g : (S[X])[X]} {a b : ℕ}
    (hf : ∀ k, (f.coeff k).degree + ((k : ℕ) : WithBot ℕ) ≤ ((a : ℕ) : WithBot ℕ))
    (hg : ∀ k, (g.coeff k).degree + ((k : ℕ) : WithBot ℕ) ≤ ((b : ℕ) : WithBot ℕ))
    (m n : ℕ) :
    (Polynomial.resultant f g m n).degree + ((∑ i : Fin (m + n), (i : ℕ) : ℕ) : WithBot ℕ)
      ≤ ((∑ j : Fin (m + n), sylvesterWeight a b m n j : ℕ) : WithBot ℕ) :=
  degree_det_add_le _ _ (degree_sylvester_add_le hf hg m n)

/-- The sum of the column weights. -/
theorem sum_sylvesterWeight (a b m n : ℕ) :
    ∑ j : Fin (m + n), sylvesterWeight a b m n j
      = (m * b + ∑ j : Fin m, (j : ℕ)) + (n * a + ∑ j : Fin n, (j : ℕ)) := by
  rw [Fin.sum_univ_add]
  congr 1
  · rw [Finset.sum_congr rfl (fun j (_ : j ∈ Finset.univ) => sylvesterWeight_castAdd a b m n j),
      Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul]
  · rw [Finset.sum_congr rfl (fun j (_ : j ∈ Finset.univ) => sylvesterWeight_natAdd a b m n j),
      Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul]

/-! ## The sums in closed form -/

theorem sum_fin_val_add (m n : ℕ) :
    (∑ i : Fin (m + n), (i : ℕ)) = (∑ i : Fin m, (i : ℕ)) + (n * m + ∑ i : Fin n, (i : ℕ)) := by
  rw [Fin.sum_univ_add]
  simp [Finset.sum_add_distrib, mul_comm]

/-- **The weight sum against the row sum**: their difference is the classical `m b + n a - m n`,
stated without subtraction. -/
theorem sum_sylvesterWeight_add (a b m n : ℕ) :
    (∑ j : Fin (m + n), sylvesterWeight a b m n j) + m * n
      = (∑ i : Fin (m + n), (i : ℕ)) + (m * b + n * a) := by
  rw [sum_sylvesterWeight, sum_fin_val_add]
  ring

/-- **The resultant's degree in the remaining variable, in natural degrees.** -/
theorem natDegree_resultant_add_le {K : Type*} [Field K] {f g : (K[X])[X]} {a b : ℕ}
    (hf : ∀ k, (f.coeff k).degree + ((k : ℕ) : WithBot ℕ) ≤ ((a : ℕ) : WithBot ℕ))
    (hg : ∀ k, (g.coeff k).degree + ((k : ℕ) : WithBot ℕ) ≤ ((b : ℕ) : WithBot ℕ))
    (m n : ℕ) (hres : Polynomial.resultant f g m n ≠ 0) :
    (Polynomial.resultant f g m n).natDegree + m * n + (∑ i : Fin (m + n), (i : ℕ))
      ≤ (∑ i : Fin (m + n), (i : ℕ)) + (m * b + n * a) := by
  have hdeg := degree_resultant_add_le hf hg (a := a) (b := b) m n
  rw [Polynomial.degree_eq_natDegree hres, ← Nat.cast_add, Nat.cast_le] at hdeg
  rw [← sum_sylvesterWeight_add a b m n]
  omega

/-- **The number of first coordinates of common zeros of a two-variable system, bounded by the
classical eliminant degree.**  This is the affine Bézout estimate for a plane system: the count plus
`m n` is at most `m b + n a`. -/
theorem card_first_coords_le_of_degrees {K : Type*} [Field K] {f g : (K[X])[X]} {a b : ℕ}
    (hf : ∀ k, (f.coeff k).degree + ((k : ℕ) : WithBot ℕ) ≤ ((a : ℕ) : WithBot ℕ))
    (hg : ∀ k, (g.coeff k).degree + ((k : ℕ) : WithBot ℕ) ≤ ((b : ℕ) : WithBot ℕ))
    {m n : ℕ} (hfm : f.natDegree ≤ m) (hgn : g.natDegree ≤ n) (H : m ≠ 0 ∨ n ≠ 0)
    (hres : Polynomial.resultant f g m n ≠ 0) (s : Finset K)
    (hs : ∀ x ∈ s, ∃ y : K, evalPairHom x y f = 0 ∧ evalPairHom x y g = 0) :
    s.card + m * n ≤ m * b + n * a := by
  have hcard := card_first_coords_le hfm hgn H hres s hs
  have hdeg := natDegree_resultant_add_le hf hg m n hres
  omega


/-- **The plane elimination count in terms of total degrees.**  For a two-variable system whose two
members have total degrees `a` and `b`, the number of first coordinates of common zeros plus `a * b`
is at most `a * b + b * a - a * b`, that is, the Bézout number `a * b`. -/
theorem card_first_coords_le_of_totalDeg {K : Type*} [Field K] {f g : (K[X])[X]} {a b : ℕ}
    (hf : TotalDegLE f a) (hg : TotalDegLE g b) (H : a ≠ 0 ∨ b ≠ 0)
    (hres : Polynomial.resultant f g a b ≠ 0) (s : Finset K)
    (hs : ∀ x ∈ s, ∃ y : K, evalPairHom x y f = 0 ∧ evalPairHom x y g = 0) :
    s.card ≤ a * b := by
  have hbound := card_first_coords_le_of_degrees hf hg hf.natDegree_le hg.natDegree_le H hres s hs
  have hcomm : b * a = a * b := mul_comm b a
  omega

end GaloisForLFunctions.HTGeometry
