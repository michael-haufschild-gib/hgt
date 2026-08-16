import GaloisForLFunctions.HTGeometry.CoefficientwisePowerSeriesDerivation

/-!
# Normalizing a formal-parameter differential relation

A nonzero differential relation whose coefficients are polynomials in the formal parameter can be
divided by the largest common power of that parameter.  The quotient still annihilates the same
jets — the parameter is a nonzerodivisor in the power-series carrier — and its specialization at
zero is nonzero, which is exactly the hypothesis of the leading-coefficient receiver.

## Main results

* `exists_normalized_relation` — the common-parameter-power removal;
* `eval₂_of_eq_C_X_pow_mul` — the removed power factors out of the evaluation;
* `differentialAlgebraicOver_constantCoeff_of_formalRelation` — the assembled theorem: a nonzero
  formal-parameter relation on the coefficientwise jets of a power series forces its constant
  coefficient to be differentially algebraic.
-/

noncomputable section

open scoped Differential

namespace GaloisForLFunctions.HTGeometry

open PowerSeriesDeriv

/-! ### Removing the common parameter power -/

variable {F ι : Type*} [CommRing F]

/-- **Common-parameter-power removal.**  Every nonzero polynomial-coefficient relation is the
largest common power of the parameter times a relation whose zero-specialization is nonzero. -/
theorem exists_normalized_relation {Q : MvPolynomial ι (Polynomial F)} (hQ : Q ≠ 0) :
    ∃ (d : ℕ) (P : MvPolynomial ι (Polynomial F)),
      Q = MvPolynomial.C (Polynomial.X ^ d) * P ∧ formalParameterSpecialization P ≠ 0 := by
  classical
  have hne : Q.support.Nonempty := MvPolynomial.support_nonempty.mpr hQ
  set d : ℕ := Q.support.inf' hne (fun m => (MvPolynomial.coeff m Q).natTrailingDegree) with hd
  have hdvd : ∀ m, (Polynomial.X : Polynomial F) ^ d ∣ MvPolynomial.coeff m Q := by
    intro m
    by_cases hm : m ∈ Q.support
    · rw [Polynomial.X_pow_dvd_iff]
      intro k hk
      refine Polynomial.coeff_eq_zero_of_lt_natTrailingDegree ?_
      have hle : d ≤ (MvPolynomial.coeff m Q).natTrailingDegree :=
        Finset.inf'_le (f := fun m => (MvPolynomial.coeff m Q).natTrailingDegree) hm
      omega
    · rw [MvPolynomial.notMem_support_iff.mp hm]
      exact dvd_zero _
  set P : MvPolynomial ι (Polynomial F) :=
    ∑ m ∈ Q.support,
      MvPolynomial.monomial m ((MvPolynomial.coeff m Q) /ₘ (Polynomial.X ^ d)) with hP
  have hcoeff : ∀ m, MvPolynomial.coeff m P
      = (MvPolynomial.coeff m Q) /ₘ (Polynomial.X ^ d) := by
    intro m
    rw [hP, MvPolynomial.coeff_sum]
    have hsum : ∀ m' ∈ Q.support,
        MvPolynomial.coeff m
            (MvPolynomial.monomial m' ((MvPolynomial.coeff m' Q) /ₘ (Polynomial.X ^ d)))
          = if m' = m then (MvPolynomial.coeff m' Q) /ₘ (Polynomial.X ^ d) else 0 := by
      intro m' _
      rw [MvPolynomial.coeff_monomial]
    rw [Finset.sum_congr rfl hsum, Finset.sum_ite_eq' Q.support m
      (fun m' => (MvPolynomial.coeff m' Q) /ₘ (Polynomial.X ^ d))]
    by_cases hm : m ∈ Q.support
    · rw [if_pos hm]
    · rw [if_neg hm, MvPolynomial.notMem_support_iff.mp hm, Polynomial.zero_divByMonic]
  have hmul : Q = MvPolynomial.C (Polynomial.X ^ d) * P := by
    refine MvPolynomial.ext _ _ (fun m => ?_)
    rw [MvPolynomial.coeff_C_mul, hcoeff]
    have hmod := Polynomial.modByMonic_add_div (MvPolynomial.coeff m Q)
      ((Polynomial.X : Polynomial F) ^ d)
    have hzero : (MvPolynomial.coeff m Q) %ₘ (Polynomial.X ^ d) = 0 :=
      (Polynomial.modByMonic_eq_zero_iff_dvd (Polynomial.monic_X_pow (R := F) d)).mpr (hdvd m)
    rw [hzero, zero_add] at hmod
    exact hmod.symm
  obtain ⟨m₀, hm₀, hm₀eq⟩ := Finset.exists_mem_eq_inf' hne
    (fun m => (MvPolynomial.coeff m Q).natTrailingDegree)
  refine ⟨d, P, hmul, ?_⟩
  intro hspec
  have hQ0 : MvPolynomial.coeff m₀ Q ≠ 0 := MvPolynomial.mem_support_iff.mp hm₀
  have hcoeff0 : (MvPolynomial.coeff m₀ P).coeff 0 ≠ 0 := by
    have hmulQ : (Polynomial.X : Polynomial F) ^ d * (MvPolynomial.coeff m₀ P)
        = MvPolynomial.coeff m₀ Q := by
      have := congrArg (MvPolynomial.coeff m₀) hmul
      rw [MvPolynomial.coeff_C_mul] at this
      exact this.symm
    have hshift : (MvPolynomial.coeff m₀ Q).coeff d = (MvPolynomial.coeff m₀ P).coeff 0 := by
      rw [← hmulQ]
      simpa using Polynomial.coeff_X_pow_mul (MvPolynomial.coeff m₀ P) d 0
    have hdeq : d = (MvPolynomial.coeff m₀ Q).natTrailingDegree := hd.trans hm₀eq
    have htrail : (MvPolynomial.coeff m₀ Q).coeff d ≠ 0 := by
      rw [hdeq]
      exact Polynomial.trailingCoeff_nonzero_iff_nonzero.mpr hQ0
    rw [← hshift]
    exact htrail
  apply hcoeff0
  have := congrArg (MvPolynomial.coeff m₀) hspec
  rw [formalParameterSpecialization, MvPolynomial.coeff_map, MvPolynomial.coeff_zero] at this
  simpa [Polynomial.coeff_zero_eq_eval_zero] using this

/-- The removed parameter power factors out of the evaluation. -/
theorem eval₂_of_eq_C_X_pow_mul {K : Type*} [CommRing K] [Algebra F K]
    (jets : ι → PowerSeries K) {Q P : MvPolynomial ι (Polynomial F)} {d : ℕ}
    (h : Q = MvPolynomial.C (Polynomial.X ^ d) * P) :
    MvPolynomial.eval₂ polynomialFormalParameterMap jets Q
      = (PowerSeries.X : PowerSeries K) ^ d
        * MvPolynomial.eval₂ polynomialFormalParameterMap jets P := by
  rw [h, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_C]
  congr 1
  rw [polynomialFormalParameterMap]
  simp

/-! ### The assembled theorem -/

/-- **A nonzero formal-parameter relation forces the constant coefficient to be differentially
algebraic.**  This is the leading-coefficient descent, with the normalization step included. -/
theorem differentialAlgebraicOver_constantCoeff_of_formalRelation
    {K : Type*} [CommRing K] [IsDomain K] [Algebra F K] [Differential K]
    {n : ℕ} {Q : MvPolynomial (Fin (n + 1)) (Polynomial F)} (hQ : Q ≠ 0)
    (G : PowerSeries K)
    (hann : MvPolynomial.eval₂ polynomialFormalParameterMap
      (fun j : Fin (n + 1) => coeffwiseJet (j : ℕ) G) Q = 0) :
    GaloisForLFunctions.DifferentialAlgebraicOver F (PowerSeries.constantCoeff G) := by
  obtain ⟨d, P, hmul, hspec⟩ := exists_normalized_relation hQ
  have hfactor := eval₂_of_eq_C_X_pow_mul
    (jets := fun j : Fin (n + 1) => coeffwiseJet (j : ℕ) G) hmul
  rw [hann] at hfactor
  have hXne : (PowerSeries.X : PowerSeries K) ^ d ≠ 0 :=
    pow_ne_zero _ PowerSeries.X_ne_zero
  have hPzero : MvPolynomial.eval₂ polynomialFormalParameterMap
      (fun j : Fin (n + 1) => coeffwiseJet (j : ℕ) G) P = 0 := by
    rcases mul_eq_zero.mp hfactor.symm with h | h
    · exact absurd h hXne
    · exact h
  refine differentialAlgebraicOver_of_normalized_formalParameterRelation
    (fun j : Fin (n + 1) => coeffwiseJet (j : ℕ) G) (fun j => ?_) hspec hPzero
  exact constantCoeff_coeffwiseJet G (j : ℕ)

end GaloisForLFunctions.HTGeometry
