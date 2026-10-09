import GaloisForLFunctions.HTGeometry.PaperWeightOrderIdeals
import GaloisForLFunctions.HTGeometry.HankelGradedDegeneration
import GaloisForLFunctions.HTGeometry.HankelDiagonalWeight

/-!
# Exact ideal order of canonical Hankel determinants

The paper's nonnegative weights bound every power of the native Hankel
secant ideal. The principal `(r+1)`-minor in any `2*r+1+extra` moment
variables has ideal order exactly one; its `n`th power has ideal order
exactly `n`, uniformly in the rank, window size and coefficient field.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial RHTower

noncomputable section

variable (K : Type*) [Field K]

/-- Every element of the Hankel ideal has total degree at least `r+1` in each monomial. -/
theorem paperHankelIdeal_weightOrder (N r : ℕ) :
    finiteHankelSecantIdeal K N r ≤
      paperWeightOrderIdeal (fun _ : Fin N => (1 : ℤ)) (by intro _; exact zero_le_one)
        (r + 1 : ℕ) := by
  rw [finiteHankelSecantIdeal, Ideal.span_le]
  rintro p ⟨c, hbound, _, rfl⟩
  exact paperWeightOrderIdeal_mem_of_homogeneous _ _
    (paperIsWeightedHomogeneous_int (isHomogeneous_finiteHankelMaximalMinorOver K c hbound))

/-- The lower total-degree bound is multiplied by the power of the Hankel ideal. -/
theorem paperHankelIdeal_pow_weightOrder (N r n : ℕ) :
    finiteHankelSecantIdeal K N r ^ n ≤
      paperWeightOrderIdeal (fun _ : Fin N => (1 : ℤ)) (by intro _; exact zero_le_one)
        ((n : ℤ) * (r + 1 : ℕ)) :=
  paperWeightOrderIdeal_pow_le _ _ _ _ (paperHankelIdeal_weightOrder K N r) n

/-- The principal maximal Hankel minor, with arbitrarily many extra moment variables. -/
def paperHankelPrincipalMinor (r : ℕ) (extra : ℕ := 0) : MvPolynomial (Fin (2 * r + 1 + extra)) K :=
  finiteHankelMaximalMinorOver K (fun j : Fin (r + 1) => (j : ℕ))
    (by intro j; have := j.isLt; omega)

/-- The selected determinant is an actual generator of the existing native rank ideal. -/
theorem paperHankelPrincipalMinor_mem (r : ℕ) (extra : ℕ := 0) :
    paperHankelPrincipalMinor K r extra ∈ finiteHankelSecantIdeal K (2 * r + 1 + extra) r := by
  apply Ideal.subset_span
  exact ⟨_, _, (by intro i j hij; exact hij), rfl⟩

/-- Diagonal monicity proves nonvanishing in every characteristic. -/
theorem paperHankelPrincipalMinor_ne_zero (r : ℕ) (extra : ℕ := 0) :
    paperHankelPrincipalMinor K r extra ≠ 0 :=
  finiteHankelMaximalMinorOver_ne_zero K _ (by intro i j hij; exact hij)

/-- The determinant's total degree is precisely `r+1`. -/
theorem paperHankelPrincipalMinor_homogeneous (r : ℕ) (extra : ℕ := 0) :
    (paperHankelPrincipalMinor K r extra).IsWeightedHomogeneous
      (fun _ => (1 : ℤ)) (r + 1 : ℕ) :=
  paperIsWeightedHomogeneous_int (isHomogeneous_finiteHankelMaximalMinorOver K _ _)

/-- Every power has its expected native ideal membership. -/
theorem paperHankelPrincipalMinor_pow_mem (r n : ℕ) (extra : ℕ := 0) :
    paperHankelPrincipalMinor K r extra ^ n ∈ finiteHankelSecantIdeal K (2 * r + 1 + extra) r ^ n :=
  Ideal.pow_mem_pow (paperHankelPrincipalMinor_mem K r extra) n

/-- No power of the principal minor gains one extra order in the Hankel ideal. -/
theorem paperHankelPrincipalMinor_pow_not_mem_succ (r n : ℕ) (extra : ℕ := 0) :
    paperHankelPrincipalMinor K r extra ^ n ∉
      finiteHankelSecantIdeal K (2 * r + 1 + extra) r ^ (n + 1) := by
  intro h
  have hh : (paperHankelPrincipalMinor K r extra ^ n).IsWeightedHomogeneous
      (fun _ => (1 : ℤ)) ((n : ℤ) * (r + 1 : ℕ)) := by
    simpa only [nsmul_eq_mul] using (paperHankelPrincipalMinor_homogeneous K r extra).pow n
  have hlt : (n : ℤ) * (r + 1 : ℕ) < ((n + 1 : ℕ) : ℤ) * (r + 1 : ℕ) := by
    push_cast
    nlinarith
  exact paperWeightOrderIdeal_not_mem_of_homogeneous _ _ hh
    (pow_ne_zero n (paperHankelPrincipalMinor_ne_zero K r extra)) hlt
    (paperHankelIdeal_pow_weightOrder K _ r (n + 1) h)

/-- All successive Hankel ideal powers are distinct, with an explicit determinant witness. -/
theorem paperHankelIdeal_powers_ne (r n : ℕ) (extra : ℕ := 0) :
    finiteHankelSecantIdeal K (2 * r + 1 + extra) r ^ n ≠
      finiteHankelSecantIdeal K (2 * r + 1 + extra) r ^ (n + 1) := by
  intro h
  exact paperHankelPrincipalMinor_pow_not_mem_succ K r n extra
    (h ▸ paperHankelPrincipalMinor_pow_mem K r n extra)

end

end GaloisForLFunctions.HTGeometry
