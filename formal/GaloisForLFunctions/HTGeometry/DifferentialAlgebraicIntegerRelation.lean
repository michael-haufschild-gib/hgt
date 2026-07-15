import GaloisForLFunctions.HTGeometry.DifferentialAlgebraicTransitivity

/-!
# Integer relations extracted from differential algebraicity over the rationals

Differential algebraicity is defined by dependence of the complete, infinitely indexed jet
family.  This file makes that dependence finite and arithmetic:

* `exists_rational_jet_relation_of_differentialAlgebraicOver` restricts a dependent jet
  polynomial to a finite initial jet segment;
* `clearRationalJetCoefficients` clears all rational denominators at once, without changing
  the zero set and without killing a nonzero polynomial;
* `exists_integer_jet_relation_of_differentialAlgebraicOver` transports the resulting integer
  polynomial to any characteristic-zero coefficient field.

The last theorem is the extraction half of Mahler normalization.  It is independent of any
analytic carrier: once an entire function has been descended to differential algebraicity over
`ℚ` in a meromorphic differential field, its integer jet annihilator is immediate.
-/

open scoped Differential

namespace GaloisForLFunctions

noncomputable section

/-- Differential algebraicity over `ℚ` is witnessed by a nonzero rational polynomial in a finite
initial segment of the jet family. -/
theorem exists_rational_jet_relation_of_differentialAlgebraicOver
    {K : Type*} [Field K] [Algebra ℚ K] [Differential K] {x : K}
    (hx : DifferentialAlgebraicOver ℚ x) :
    ∃ (n : ℕ) (Q : MvPolynomial (Fin (n + 1)) ℚ), Q ≠ 0 ∧
      MvPolynomial.aeval (fun j : Fin (n + 1) => differentialJet (j : ℕ) x) Q = 0 := by
  unfold DifferentialAlgebraicOver DifferentialIndependent at hx
  rw [algebraicIndependent_iff] at hx
  push Not at hx
  obtain ⟨P, hPann, hP0⟩ := hx
  obtain ⟨m, a, ha, Q, hP⟩ := MvPolynomial.exists_fin_rename P
  subst P
  have hQ0 : Q ≠ 0 := by
    intro hQ
    apply hP0
    simp [hQ]
  let N : ℕ := Finset.univ.sup fun i : Fin m => (a i).2
  have haN (i : Fin m) : (a i).2 ≤ N :=
    Finset.le_sup (f := fun i : Fin m => (a i).2) (Finset.mem_univ i)
  let e : Fin m → Fin (N + 1) := fun i => ⟨(a i).2, Nat.lt_succ_of_le (haN i)⟩
  have he : Function.Injective e := by
    intro i j hij
    apply ha
    apply Prod.ext
    · exact Subsingleton.elim _ _
    · exact congrArg Fin.val hij
  refine ⟨N, MvPolynomial.rename e Q, ?_, ?_⟩
  · exact fun h => hQ0 (MvPolynomial.rename_injective e he h)
  · rw [MvPolynomial.aeval_rename]
    rw [MvPolynomial.aeval_rename] at hPann
    simpa [e, Function.comp_def] using hPann

/-- Product of all reduced positive denominators of the nonzero coefficients of a rational
multivariate polynomial. -/
noncomputable def rationalJetCommonDenominator
    {σ : Type*} (Q : MvPolynomial σ ℚ) : ℤ :=
  ∏ d ∈ Q.support, ((MvPolynomial.coeff d Q).den : ℤ)

/-- Simultaneous rational denominator clearing, with coefficients kept canonically in `ℤ`. -/
noncomputable def clearRationalJetCoefficients
    {σ : Type*} [DecidableEq σ] (Q : MvPolynomial σ ℚ) : MvPolynomial σ ℤ :=
  ∑ d ∈ Q.support, MvPolynomial.monomial d
    ((MvPolynomial.coeff d Q).num *
      ∏ e ∈ Q.support.erase d, ((MvPolynomial.coeff e Q).den : ℤ))

theorem coeff_clearRationalJetCoefficients_of_mem
    {σ : Type*} [DecidableEq σ] (Q : MvPolynomial σ ℚ)
    {d : σ →₀ ℕ} (hd : d ∈ Q.support) :
    MvPolynomial.coeff d (clearRationalJetCoefficients Q) =
      (MvPolynomial.coeff d Q).num *
        ∏ e ∈ Q.support.erase d, ((MvPolynomial.coeff e Q).den : ℤ) := by
  classical
  simp only [clearRationalJetCoefficients, MvPolynomial.coeff_sum,
    MvPolynomial.coeff_monomial]
  rw [Finset.sum_eq_single d]
  · simp
  · intro e he hne
    simp [hne]
  · intro hnot
    exact (hnot hd).elim

theorem coeff_clearRationalJetCoefficients_of_not_mem
    {σ : Type*} [DecidableEq σ] (Q : MvPolynomial σ ℚ)
    {d : σ →₀ ℕ} (hd : d ∉ Q.support) :
    MvPolynomial.coeff d (clearRationalJetCoefficients Q) = 0 := by
  classical
  simp only [clearRationalJetCoefficients, MvPolynomial.coeff_sum,
    MvPolynomial.coeff_monomial]
  rw [Finset.sum_eq_zero]
  intro e he
  rw [if_neg]
  intro hed
  exact hd (hed ▸ he)

/-- Exact denominator clearing preserves nonzeroness. -/
theorem clearRationalJetCoefficients_ne_zero
    {σ : Type*} [DecidableEq σ] (Q : MvPolynomial σ ℚ) (hQ : Q ≠ 0) :
    clearRationalJetCoefficients Q ≠ 0 := by
  classical
  obtain ⟨d, hd⟩ := MvPolynomial.support_nonempty.mpr hQ
  have hcoeff : MvPolynomial.coeff d Q ≠ 0 := MvPolynomial.mem_support_iff.mp hd
  have hprod :
      (∏ e ∈ Q.support.erase d, ((MvPolynomial.coeff e Q).den : ℤ)) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro e he
    exact_mod_cast (MvPolynomial.coeff e Q).den_ne_zero
  have hnum : (MvPolynomial.coeff d Q).num ≠ 0 := Rat.num_ne_zero.mpr hcoeff
  have hcleared : MvPolynomial.coeff d (clearRationalJetCoefficients Q) ≠ 0 := by
    rw [coeff_clearRationalJetCoefficients_of_mem Q hd]
    exact mul_ne_zero hnum hprod
  intro hzero
  rw [hzero, MvPolynomial.coeff_zero] at hcleared
  exact hcleared rfl

/-- Mapping the cleared integer polynomial back to `ℚ` multiplies the original polynomial by the
common denominator. -/
theorem map_clearRationalJetCoefficients
    {σ : Type*} [DecidableEq σ] (Q : MvPolynomial σ ℚ) :
    MvPolynomial.map (Int.castRingHom ℚ) (clearRationalJetCoefficients Q) =
      MvPolynomial.C ((rationalJetCommonDenominator Q : ℤ) : ℚ) * Q := by
  classical
  apply MvPolynomial.ext
  intro d
  rw [MvPolynomial.coeff_map, MvPolynomial.coeff_C_mul]
  by_cases hd : d ∈ Q.support
  · rw [coeff_clearRationalJetCoefficients_of_mem Q hd,
      rationalJetCommonDenominator,
      ← Finset.mul_prod_erase Q.support
        (fun e => ((MvPolynomial.coeff e Q).den : ℤ)) hd]
    let q := MvPolynomial.coeff d Q
    let A : ℤ := ∏ e ∈ Q.support.erase d, ((MvPolynomial.coeff e Q).den : ℤ)
    change (((q.num * A : ℤ) : ℚ)) = ((((q.den : ℤ) * A : ℤ) : ℚ)) * q
    push_cast
    rw [show (q.num : ℚ) = q * q.den by exact q.mul_den_eq_num.symm]
    ring
  · have hcoeff : MvPolynomial.coeff d Q = 0 := by
      exact not_ne_iff.mp (mt MvPolynomial.mem_support_iff.mpr hd)
    rw [hcoeff, mul_zero, coeff_clearRationalJetCoefficients_of_not_mem Q hd, map_zero]

/-- **Arithmetic extraction from rational differential algebraicity.**  In any characteristic-zero
coefficient field `C` sitting between `ℚ` and the ambient differential field, a differentially
algebraic element admits a nonzero finite jet relation whose every coefficient is an integer. -/
theorem exists_integer_jet_relation_of_differentialAlgebraicOver
    {C K : Type*} [Field C] [CharZero C] [Field K]
    [Algebra ℚ C] [Algebra C K] [Algebra ℚ K] [IsScalarTower ℚ C K]
    [Differential K] {x : K} (hx : DifferentialAlgebraicOver ℚ x) :
    ∃ (n : ℕ) (Q : MvPolynomial (Fin (n + 1)) C), Q ≠ 0 ∧
      (∀ m, ∃ z : ℤ, MvPolynomial.coeff m Q = (z : C)) ∧
      MvPolynomial.aeval (fun j : Fin (n + 1) => differentialJet (j : ℕ) x) Q = 0 := by
  obtain ⟨n, P, hP0, hPann⟩ :=
    exists_rational_jet_relation_of_differentialAlgebraicOver hx
  let Qz := clearRationalJetCoefficients P
  let Q : MvPolynomial (Fin (n + 1)) C := MvPolynomial.map (Int.castRingHom C) Qz
  have hQz0 : Qz ≠ 0 := clearRationalJetCoefficients_ne_zero P hP0
  have hQ0 : Q ≠ 0 := by
    intro h
    apply hQz0
    apply MvPolynomial.map_injective (Int.castRingHom C) Int.cast_injective
    change MvPolynomial.map (Int.castRingHom C) Qz = 0 at h
    simpa using h
  have hQcoeff : ∀ m, ∃ z : ℤ, MvPolynomial.coeff m Q = (z : C) := by
    intro m
    refine ⟨MvPolynomial.coeff m Qz, ?_⟩
    exact MvPolynomial.coeff_map _ _ _
  have hrat : MvPolynomial.aeval
      (fun j : Fin (n + 1) => differentialJet (j : ℕ) x)
      (MvPolynomial.map (Int.castRingHom ℚ) Qz) = 0 := by
    rw [map_clearRationalJetCoefficients P, map_mul, MvPolynomial.aeval_C,
      hPann, mul_zero]
  refine ⟨n, Q, hQ0, hQcoeff, ?_⟩
  change MvPolynomial.aeval
    (fun j : Fin (n + 1) => differentialJet (j : ℕ) x)
    (MvPolynomial.map (Int.castRingHom C) Qz) = 0
  rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_map]
  rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_map] at hrat
  have hcast : (algebraMap C K).comp (Int.castRingHom C) =
      (algebraMap ℚ K).comp (Int.castRingHom ℚ) := by
    ext z
    simp
  rw [hcast]
  exact hrat

end


end GaloisForLFunctions
