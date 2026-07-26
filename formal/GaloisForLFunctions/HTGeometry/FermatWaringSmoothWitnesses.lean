import GaloisForLFunctions.HTGeometry.MvPolynomialWaringSmoothHorizon

/-!
# The Fermat form is projectively smooth

The Waring form of the identity coefficient matrix is the Fermat form `∑ᵢ Xᵢ ^ d`.  Its `j`-th
partial derivative is `d · Xⱼ ^ (d-1)`, which is nonzero at every point with a nonzero `j`-th
coordinate, so in characteristic zero the Fermat form is projectively smooth for every positive
degree.  This is an unconditional realization of the smoothness interface in every degree.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

universe u

variable {K : Type u} [Field K] [CharZero K] {m : ℕ}

omit [CharZero K] in
theorem pderiv_fermat {d : ℕ} (j : Fin m) :
    MvPolynomial.pderiv j (∑ i : Fin m, (MvPolynomial.X i : MvPolynomial (Fin m) K) ^ d) =
      (d : MvPolynomial (Fin m) K) * MvPolynomial.X j ^ (d - 1) := by
  classical
  rw [map_sum, Finset.sum_eq_single j]
  · rw [MvPolynomial.pderiv_pow, MvPolynomial.pderiv_X_self]
    simp
  · intro i _ hij
    rw [MvPolynomial.pderiv_pow, MvPolynomial.pderiv_X]
    simp [Ne.symm hij]
  · intro hj
    exact absurd (Finset.mem_univ j) hj

/-- **The Fermat form is projectively smooth.** -/
theorem mvPolynomialProjectivelySmooth_fermat {d : ℕ} (hd : d ≠ 0) :
    MvPolynomialProjectivelySmooth
      (∑ i : Fin m, (MvPolynomial.X i : MvPolynomial (Fin m) K) ^ d) := by
  intro v hv _
  obtain ⟨j, hj⟩ : ∃ j, v j ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hv (funext hcon)
  refine ⟨j, ?_⟩
  rw [pderiv_fermat]
  simp only [map_mul, map_natCast, MvPolynomial.eval_pow, MvPolynomial.eval_X]
  have hdK : (d : K) ≠ 0 := Nat.cast_ne_zero.mpr hd
  exact mul_ne_zero hdK (pow_ne_zero _ hj)

omit [CharZero K] in
theorem mvWaringLinearPolynomial_one (i : Fin m) :
    mvWaringLinearPolynomial (1 : Matrix (Fin m) (Fin m) K) i =
      (MvPolynomial.X i : MvPolynomial (Fin m) K) := by
  classical
  rw [mvWaringLinearPolynomial, Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [Ne.symm hji]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

variable {d : ℕ} [NeZero d] [Fact (1 < d)]

omit [CharZero K] [NeZero d] [Fact (1 < d)] in
theorem mvWaringPolynomial_one_eq_fermat :
    mvWaringPolynomial d (1 : Matrix (Fin m) (Fin m) K) =
      ∑ i : Fin m, (MvPolynomial.X i : MvPolynomial (Fin m) K) ^ d := by
  rw [mvWaringPolynomial]
  exact Finset.sum_congr rfl fun i _ => by rw [mvWaringLinearPolynomial_one]

omit [Fact (1 < d)] in
/-- The identity Waring form is projectively smooth in every degree. -/
theorem mvPolynomialProjectivelySmooth_mvWaringPolynomial_one :
    MvPolynomialProjectivelySmooth (mvWaringPolynomial d (1 : Matrix (Fin m) (Fin m) K)) := by
  rw [mvWaringPolynomial_one_eq_fermat]
  exact mvPolynomialProjectivelySmooth_fermat (NeZero.ne d)

end

end GaloisForLFunctions.HTGeometry
