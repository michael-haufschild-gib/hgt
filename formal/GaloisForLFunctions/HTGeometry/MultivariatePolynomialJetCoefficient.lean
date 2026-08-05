import GaloisForLFunctions.HTGeometry.MultivariateEntirePolarizedJet
import GaloisForLFunctions.HTGeometry.MultivariateHermiteCRT
import Mathlib.Analysis.Analytic.Polynomial

/-!
# Multivariate polynomial jets and centered coefficients

This module identifies every ordered coordinate Frechet jet of a multivariate polynomial with
the corresponding centered coefficient, including the exact multi-index factorial.  Combining
that formula with multivariate Hermite interpolation gives unconditional surjectivity of every
finite symmetric mixed-jet packet on the compact-open entire-source carrier.
-/

open Function

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Iterate formal partial derivatives in the order encoded by a finite coordinate word. -/
def iteratedPDerivWord {d : ℕ} : {n : ℕ} →
    (Fin n → Fin d) → MvPolynomial (Fin d) ℂ → MvPolynomial (Fin d) ℂ
  | 0, _, P => P
  | n + 1, word, P =>
      iteratedPDerivWord (Fin.init word)
        (MvPolynomial.pderiv (word (Fin.last n)) P)

/-- The coefficient of one formal partial derivative, without a support hypothesis. -/
theorem coeff_pderiv_add_single {d : ℕ}
    (P : MvPolynomial (Fin d) ℂ) (a : Fin d →₀ ℕ) (i : Fin d) :
    MvPolynomial.coeff a (MvPolynomial.pderiv i P) =
      MvPolynomial.coeff (a + Finsupp.single i 1) P * (a i + 1 : ℂ) := by
  classical
  conv_lhs => rw [P.as_sum]
  simp only [map_sum, MvPolynomial.coeff_sum, MvPolynomial.pderiv_monomial,
    MvPolynomial.coeff_monomial]
  by_cases hmem : a + Finsupp.single i 1 ∈ P.support
  · rw [Finset.sum_eq_single (a + Finsupp.single i 1)]
    · simp [Finsupp.add_apply]
    · intro v hv hne
      by_cases hvi : v i = 0
      · simp [hvi]
      · have hsub : v - Finsupp.single i 1 ≠ a := by
          intro h
          apply hne
          have hadd := congrArg (· + Finsupp.single i 1) h
          simpa [Finsupp.sub_add_single_one_cancel hvi] using hadd
        simp [hsub]
    · exact fun hnot ↦ (hnot hmem).elim
  · have hcoeff : MvPolynomial.coeff (a + Finsupp.single i 1) P = 0 := by
      exact Finsupp.notMem_support_iff.mp hmem
    rw [hcoeff, zero_mul]
    apply Finset.sum_eq_zero
    intro v hv
    by_cases hvi : v i = 0
    · simp [hvi]
    · have hsub : v - Finsupp.single i 1 ≠ a := by
        intro h
        apply hmem
        have hadd := congrArg (· + Finsupp.single i 1) h
        have hv_eq : v = a + Finsupp.single i 1 := by
          simpa [Finsupp.sub_add_single_one_cancel hvi] using hadd
        simpa [hv_eq] using hv
      simp [hsub]

/-- Multiplicity of each coordinate in an ordered derivative word. -/
def wordMultiplicity {d n : ℕ} (word : Fin n → Fin d) : Fin d →₀ ℕ :=
  ∑ j, Finsupp.single (word j) 1

@[simp]
theorem wordMultiplicity_zero {d : ℕ} (word : Fin 0 → Fin d) :
    wordMultiplicity word = 0 := by
  simp [wordMultiplicity]

/-- Appending a coordinate slot adds one to its multiplicity. -/
theorem wordMultiplicity_succ {d n : ℕ} (word : Fin (n + 1) → Fin d) :
    wordMultiplicity word =
      wordMultiplicity (Fin.init word) + Finsupp.single (word (Fin.last n)) 1 := by
  simp [wordMultiplicity, Fin.sum_univ_castSucc, Fin.init]

/-- Adding one coordinate multiplicity multiplies the multi-index factorial by that successor. -/
theorem prod_factorial_add_single {d : ℕ} (a : Fin d →₀ ℕ) (i : Fin d) :
    (a i + 1 : ℂ) * ∏ j, ((a j).factorial : ℂ) =
      ∏ j : Fin d,
        ((((a + Finsupp.single i 1 : Fin d →₀ ℕ) j).factorial : ℕ) : ℂ) := by
  classical
  rw [Fintype.prod_eq_mul_prod_compl i, Fintype.prod_eq_mul_prod_compl i]
  have hrest :
      (∏ j ∈ ({i}ᶜ : Finset (Fin d)), ((a j).factorial : ℂ)) =
        ∏ j ∈ ({i}ᶜ : Finset (Fin d)),
          ((((a + Finsupp.single i 1 : Fin d →₀ ℕ) j).factorial : ℕ) : ℂ) := by
    apply Finset.prod_congr rfl
    intro j hj
    simp only [Finset.mem_compl, Finset.mem_singleton] at hj
    simp [hj]
  rw [← hrest]
  simp [Finsupp.add_apply, Nat.factorial_succ]
  ring

/-- Repeated formal partial differentiation extracts the coefficient indexed by the word,
multiplied by the exact product of coordinate factorials. -/
theorem constantCoeff_iteratedPDerivWord {d n : ℕ}
    (P : MvPolynomial (Fin d) ℂ) (word : Fin n → Fin d) :
    MvPolynomial.constantCoeff (iteratedPDerivWord word P) =
      MvPolynomial.coeff (wordMultiplicity word) P *
        ∏ i : Fin d, (((wordMultiplicity word i).factorial : ℕ) : ℂ) := by
  induction n generalizing P with
  | zero =>
      simp [iteratedPDerivWord, MvPolynomial.constantCoeff_eq]
  | succ n ih =>
      rw [iteratedPDerivWord, ih, coeff_pderiv_add_single,
        wordMultiplicity_succ]
      rw [← prod_factorial_add_single]
      ring

/-- Evaluating a translated multivariate polynomial translates its evaluation point. -/
@[simp]
theorem eval_mvPolynomialBaseTranslation {d : ℕ}
    (c y : Fin d → ℂ) (P : MvPolynomial (Fin d) ℂ) :
    MvPolynomial.eval y (mvPolynomialBaseTranslation c P) =
      MvPolynomial.eval (fun i ↦ y i + c i) P := by
  induction P using MvPolynomial.induction_on with
  | C a =>
      rw [MvPolynomial.eval_C]
      rw [← MvPolynomial.algebraMap_eq]
      rw [(mvPolynomialBaseTranslation c).commutes a]
      simp
  | add P Q hP hQ => simp [hP, hQ]
  | mul_X P i hP =>
      simp [hP, mvPolynomialBaseTranslation_X]

/-- An ordered coordinate Frechet jet of polynomial evaluation is the evaluation of the
corresponding iterated formal partial derivative. -/
theorem iteratedFDeriv_mvPolynomial_eval_coordinate_word {d n : ℕ}
    (P : MvPolynomial (Fin d) ℂ) (x : Fin d → ℂ) (word : Fin n → Fin d) :
    iteratedFDeriv ℂ n (fun y : Fin d → ℂ => MvPolynomial.eval y P) x
        (fun j ↦ coordinateJetDirection (word j)) =
      MvPolynomial.eval x (iteratedPDerivWord word P) := by
  induction n generalizing P with
  | zero =>
      simp [iteratedPDerivWord]
  | succ n ih =>
      rw [iteratedFDeriv_succ_apply_right]
      have hpoly : ContDiff ℂ (⊤ : WithTop ℕ∞)
          (fun y : Fin d → ℂ => MvPolynomial.eval y P) :=
        (AnalyticOnNhd.eval_mvPolynomial P).contDiff
      have hderiv : ContDiff ℂ n
          (fderiv ℂ (fun y : Fin d → ℂ => MvPolynomial.eval y P)) :=
        hpoly.fderiv_right (by simp)
      rw [← iteratedFDeriv_clm_apply_const_apply (i := n) hderiv
        (show (n : WithTop ℕ∞) ≤ (n : WithTop ℕ∞) from le_rfl)]
      have hcoord :
          (fun y : Fin d → ℂ =>
              fderiv ℂ (fun z : Fin d → ℂ => MvPolynomial.eval z P) y
                (coordinateJetDirection (word (Fin.last n)))) =
            fun y => MvPolynomial.eval y
              (MvPolynomial.pderiv (word (Fin.last n)) P) := by
        funext y
        rw [fderiv_mvPolynomial_eval_complex_apply]
        simp [coordinateJetDirection, Pi.single_apply]
      rw [hcoord]
      simpa [iteratedPDerivWord] using!
        ih (MvPolynomial.pderiv (word (Fin.last n)) P) (Fin.init word)

/-- Ordered coordinate Frechet jets are centered coefficients with their exact factorial
normalization. -/
theorem iteratedFDeriv_mvPolynomial_eval_coordinate_word_eq_centered_coeff
    {d n : ℕ} (P : MvPolynomial (Fin d) ℂ) (x : Fin d → ℂ)
    (word : Fin n → Fin d) :
    iteratedFDeriv ℂ n (fun y : Fin d → ℂ => MvPolynomial.eval y P) x
        (fun j ↦ coordinateJetDirection (word j)) =
      MvPolynomial.coeff (wordMultiplicity word)
          (mvPolynomialBaseTranslation x P) *
        ∏ i : Fin d, (((wordMultiplicity word i).factorial : ℕ) : ℂ) := by
  have hshift :
      iteratedFDeriv ℂ n
          (fun z : Fin d → ℂ => MvPolynomial.eval (x + z) P) 0 =
        iteratedFDeriv ℂ n
          (fun y : Fin d → ℂ => MvPolynomial.eval y P) x := by
    simpa using (iteratedFDeriv_comp_add_left
      (f := fun y : Fin d → ℂ => MvPolynomial.eval y P) n x 0)
  rw [← hshift]
  have hfun :
      (fun z : Fin d → ℂ => MvPolynomial.eval (x + z) P) =
        fun z => MvPolynomial.eval z (mvPolynomialBaseTranslation x P) := by
    funext z
    rw [eval_mvPolynomialBaseTranslation]
    apply congrArg (fun w : Fin d → ℂ => MvPolynomial.eval w P)
    funext i
    simp [add_comm]
  rw [hfun, iteratedFDeriv_mvPolynomial_eval_coordinate_word,
    MvPolynomial.eval_zero, constantCoeff_iteratedPDerivWord]

/-- Factorial normalization attached to a multivariate derivative index. -/
def multiIndexFactorial {d : ℕ} (a : Fin d →₀ ℕ) : ℂ :=
  ∏ i : Fin d, ((a i).factorial : ℂ)

/-- The multi-index factorial is nonzero over the complex numbers. -/
theorem multiIndexFactorial_ne_zero {d : ℕ} (a : Fin d →₀ ℕ) :
    multiIndexFactorial a ≠ 0 := by
  classical
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  exact_mod_cast Nat.factorial_ne_zero (a i)

/-- The continuous ordered mixed-jet observation on the polynomial source is its centered
coefficient with the exact multi-index factorial normalization. -/
theorem orderedPartialJetEvalCLM_mvPolynomial_eq_centered_coeff
    {d n : ℕ} (P : MvPolynomial (Fin d) ℂ) (x : Fin d → ℂ)
    (word : Fin n → Fin d) :
    orderedPartialJetEvalCLM x word (mvPolynomialMultivariateEntire P) =
      MvPolynomial.coeff (wordMultiplicity word)
          (mvPolynomialBaseTranslation x P) *
        multiIndexFactorial (wordMultiplicity word) := by
  rw [orderedPartialJetEvalCLM_eq_iteratedFDeriv
    x word (mvPolynomialMultivariateEntire P)]
  simpa [mvPolynomialMultivariateEntire, multiIndexFactorial] using
    iteratedFDeriv_mvPolynomial_eval_coordinate_word_eq_centered_coeff P x word

/-- **Arbitrary finite mixed-jet packet surjectivity.** At an injective finite packet of points,
every symmetric mixed-partial packet below the prescribed total orders is realized by one
multivariable polynomial, hence by one member of `MultivariateEntire`. -/
theorem exists_mvPolynomial_orderedPartialJetEvalCLM_eq_arbitrary
    {d : ℕ} {I : Type*} [Finite I]
    (w : I → Fin d → ℂ) (hw : Function.Injective w)
    (m : I → ℕ) (jet : I → (Fin d →₀ ℕ) → ℂ) :
    ∃ P : MvPolynomial (Fin d) ℂ,
      ∀ i n (word : Fin n → Fin d),
        Finsupp.degree (wordMultiplicity word) < m i →
          orderedPartialJetEvalCLM (w i) word
              (mvPolynomialMultivariateEntire P) =
            jet i (wordMultiplicity word) := by
  let coeffJet : I → (Fin d →₀ ℕ) → ℂ := fun i a =>
    jet i a / multiIndexFactorial a
  obtain ⟨P, hP⟩ := exists_mvPolynomial_centered_coeff_eq_arbitrary
    w hw m coeffJet
  refine ⟨P, fun i n word hword => ?_⟩
  rw [orderedPartialJetEvalCLM_mvPolynomial_eq_centered_coeff,
    hP i (wordMultiplicity word) hword]
  exact div_mul_cancel₀ _ (multiIndexFactorial_ne_zero (wordMultiplicity word))

end

end GaloisForLFunctions.HTGeometry
