import GaloisForLFunctions.HTGeometry.RittAffineRigidity

/-!
# The affine dichotomy with the linear branch split

The branch of the affine dichotomy in which the coprime numerator has degree one is the only one
whose datum does not determine the solution.  Recorded here in full, it does: the solution is
`W = v·t + p` with both coefficients in the coefficient field, and the two coefficient identities

`φ v · a = c v + α`,   `φ v · b + φ p = c p + β`

hold.  The second is what the leading-coefficient equation alone discards.
-/

namespace GaloisForLFunctions.HTGeometry

open _root_.Polynomial

variable {E L : Type*} [Field E] [CharZero E] [Field L] [Algebra E L]

/-- **The affine dichotomy, with the degree-one branch split.** -/
theorem affine_eigen_dichotomy_split (σ : L →+* L) (φ : E →+* E)
    (hcomp : ∀ x : E, σ (algebraMap E L x) = algebraMap E L (φ x))
    {t : L} (ht : Transcendental E t) {a b c α β : E} (ha : a ≠ 0) (hc : c ≠ 0)
    (hσt : σ t = algebraMap E L a * t + algebraMap E L b)
    {W : L} (hW0 : W ≠ 0) (hW : W ∈ IntermediateField.adjoin E ({t} : Set L))
    (hrel : σ W = algebraMap E L c * W + (algebraMap E L α * t + algebraMap E L β)) :
    (α = 0 ∧ ∃ x : E, W = algebraMap E L x) ∨
    algebraMap E L b = 0 ∨
    (∃ (w : E) (N : ℕ), w ≠ 0 ∧ 1 ≤ N ∧ φ w + (N : E) * b = a * w) ∨
    (∃ v Z Y : E, v ≠ 0 ∧ α ≠ 0 ∧ φ v * a ^ (2 : ℕ) = c * v ∧
      φ Z = a * Z + a * α / (c * v) - 2 * b ∧
      φ Y = a ^ (2 : ℕ) * Y - a * b * Z + b ^ (2 : ℕ) + a * (a * β - α * b) / (c * v)) ∨
    (∃ v p : E, v ≠ 0 ∧ W = algebraMap E L v * t + algebraMap E L p ∧
      φ v * a = c * v + α ∧ φ v * b + φ p = c * p + β) := by
  classical
  obtain ⟨A, B, hB, hcop, hA0, hWeq, hcross, hden⟩ :=
    exists_denominator_relation_of_affine_mem_adjoin σ φ hcomp ht ha hc hσt hW0 hW hrel
  by_cases hBdeg : 1 ≤ B.natDegree
  · have hrel' := hden hBdeg
    by_cases hw0 : B.coeff (B.natDegree - 1) = 0
    · refine Or.inr (Or.inl ?_)
      rw [hw0, map_zero, zero_add, mul_zero] at hrel'
      have hN : ((B.natDegree : E)) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      rw [(mul_eq_zero.mp hrel').resolve_left hN, map_zero]
    · exact Or.inr (Or.inr (Or.inl ⟨B.coeff (B.natDegree - 1), B.natDegree, hw0, hBdeg, hrel'⟩))
  have hBone : B = 1 := eq_one_of_monic_natDegree_zero hB (by omega)
  set T : E[X] := C a * X + C b with hT
  have hone : twistComp φ T (1 : E[X]) = 1 := by simp [twistComp]
  have hnum : twistComp φ T A = C c * A + (C α * X + C β) := by
    rw [hBone, hone, mul_one, mul_one, one_mul] at hcross
    exact hcross
  have hWA : W = aeval t A := by rw [hWeq, hBone, map_one, div_one]
  set D : ℕ := A.natDegree with hD
  have hmapdeg : ∀ n : ℕ, D ≤ n → (A.map φ).natDegree ≤ n := by
    intro n hn
    exact le_trans (natDegree_map_le (f := φ) (p := A)) (by omega)
  have hLHS : ∀ n : ℕ, D ≤ n → (twistComp φ T A).coeff n = φ (A.coeff n) * a ^ n := by
    intro n hn
    simp only [twistComp, hT]
    rw [coeff_comp_linear_of_natDegree_le ha (hmapdeg n hn), coeff_map]
  have hRHS : ∀ n : ℕ, (C c * A + (C α * X + C β)).coeff n
      = c * A.coeff n + ((if 1 = n then α else 0) + (if n = 0 then β else 0)) := by
    intro n
    rw [coeff_add, coeff_C_mul, coeff_add, coeff_C_mul, coeff_X, coeff_C, mul_ite, mul_one,
      mul_zero]
  rcases Nat.lt_or_ge D 1 with hD0 | hD1
  · left
    have hcoeff1 := congrArg (fun R : E[X] => R.coeff 1) hnum
    rw [hLHS 1 (by omega), hRHS 1] at hcoeff1
    have hA1 : A.coeff 1 = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
    rw [hA1, map_zero, zero_mul, mul_zero, if_pos rfl, if_neg (by omega : ¬ (1 : ℕ) = 0),
      add_zero, zero_add] at hcoeff1
    refine ⟨hcoeff1.symm, A.coeff 0, ?_⟩
    have hAC : A = C (A.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero (by omega)
    rw [hWA]
    conv_lhs => rw [hAC]
    rw [aeval_C]
  rcases Nat.lt_or_ge D 2 with hD2 | hD2
  · -- degree one: split the solution and record both coefficient identities
    have hDone : D = 1 := by omega
    have hlead : A.coeff 1 ≠ 0 := by
      have : A.coeff D ≠ 0 := by
        rw [hD, ← leadingCoeff]
        exact leadingCoeff_ne_zero.mpr hA0
      rwa [hDone] at this
    have hAsplit : A = C (A.coeff 1) * X + C (A.coeff 0) := by
      ext n
      match n with
      | 0 => simp
      | 1 => simp
      | (k + 2) =>
          rw [coeff_add, coeff_C_mul, coeff_X, coeff_C,
            if_neg (by omega : ¬ (1 : ℕ) = k + 2), if_neg (by omega : ¬ (k + 2 : ℕ) = 0),
            mul_zero, add_zero]
          exact coeff_eq_zero_of_natDegree_lt (by omega)
    have hWsplit : W = algebraMap E L (A.coeff 1) * t + algebraMap E L (A.coeff 0) := by
      rw [hWA]
      conv_lhs => rw [hAsplit]
      simp
    have htw : twistComp φ T A = C (φ (A.coeff 1) * a) * X + C (φ (A.coeff 1) * b + φ (A.coeff 0)) := by
      simp only [twistComp, hT]
      conv_lhs => rw [hAsplit]
      rw [Polynomial.map_add, Polynomial.map_mul, map_C, map_X, map_C, add_comp, mul_comp, C_comp,
        X_comp, C_comp]
      simp only [C_mul, C_add]
      ring
    have hcoefftw1 : (twistComp φ T A).coeff 1 = φ (A.coeff 1) * a := by
      rw [htw]; simp
    have hcoefftw0 : (twistComp φ T A).coeff 0 = φ (A.coeff 1) * b + φ (A.coeff 0) := by
      rw [htw]; simp
    have hc1 : φ (A.coeff 1) * a = c * A.coeff 1 + α := by
      have h := congrArg (fun R : E[X] => R.coeff 1) hnum
      rw [hcoefftw1, hRHS 1] at h
      simpa using h
    have hc0 : φ (A.coeff 1) * b + φ (A.coeff 0) = c * A.coeff 0 + β := by
      have h := congrArg (fun R : E[X] => R.coeff 0) hnum
      rw [hcoefftw0, hRHS 0] at h
      simpa using h
    exact Or.inr (Or.inr (Or.inr (Or.inr ⟨A.coeff 1, A.coeff 0, hlead, hWsplit, hc1, hc0⟩)))
  · have hcoeffD := congrArg (fun R : E[X] => R.coeff D) hnum
    rw [hLHS D le_rfl, hRHS D] at hcoeffD
    have hlead : A.coeff D ≠ 0 := by
      rw [hD, ← leadingCoeff]
      exact leadingCoeff_ne_zero.mpr hA0
    rw [if_neg (by omega : ¬ (1 : ℕ) = D), if_neg (by omega : ¬ D = 0), add_zero,
      add_zero] at hcoeffD
    by_cases hcase : 3 ≤ D ∨ α = 0
    · have hαD : A.natDegree = 2 → α = 0 := by
        intro h2
        rcases hcase with h3 | h0
        · exact absurd h2 (by omega)
        · exact h0
      have hZ := ratio_connection_of_polynomial_cross φ ha (by omega : 2 ≤ A.natDegree) hαD hnum
      set Z : E := A.coeff (A.natDegree - 1) / A.leadingCoeff with hZdef
      by_cases hZ0 : Z = 0
      · refine Or.inr (Or.inl ?_)
        rw [hZ0, map_zero, zero_add, mul_zero] at hZ
        have hDne : ((A.natDegree : E)) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
        rw [(mul_eq_zero.mp hZ).resolve_left hDne, map_zero]
      · exact Or.inr (Or.inr (Or.inl ⟨Z, A.natDegree, hZ0, by omega, hZ⟩))
    · push Not at hcase
      have hD2' : A.natDegree = 2 := by omega
      refine Or.inr (Or.inr (Or.inr (Or.inl
        ⟨A.coeff D, A.coeff 1 / A.coeff 2, A.coeff 0 / A.coeff 2, hlead, hcase.2, ?_, ?_, ?_⟩)))
      · rw [← hD2']
        exact hcoeffD
      · have hq := ratio_quadratic_of_polynomial_cross φ ha hc hD2' hnum
        rw [hD, hD2']
        exact hq
      · have hq := ratio_quadratic_constant_of_polynomial_cross φ ha hc hD2' hnum
        rw [hD, hD2']
        exact hq

end GaloisForLFunctions.HTGeometry
