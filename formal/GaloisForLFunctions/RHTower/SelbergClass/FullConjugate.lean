import GaloisForLFunctions.RHTower.SelbergClass.Full
import Mathlib.Analysis.Calculus.Deriv.Star

/-!
# Coefficientwise conjugation in the full Selberg carrier

This is ordinary complex-conjugate closure: coefficients, Euler-log data, gamma shifts, and root
number are conjugated, while the represented continuation is transported by
`s ↦ star (F (star s))`.  It is not a Rankin--Selberg construction and makes no orthogonality
claim.
-/

open scoped BigOperators
open Complex Filter Set

namespace RHTower

noncomputable section

/-- Coefficientwise complex conjugation of an arithmetic function. -/
def selbergArithmeticFunctionConjugate (f : ArithmeticFunction ℂ) : ArithmeticFunction ℂ :=
  ⟨fun n ↦ star (f n), by simp⟩

@[simp]
theorem selbergArithmeticFunctionConjugate_apply (f : ArithmeticFunction ℂ) (n : ℕ) :
    selbergArithmeticFunctionConjugate f n = star (f n) :=
  rfl

/-- Entire finite-order functions are stable under conjugation in both source and target. -/
def EntireFiniteOrder.conjugate (F : EntireFiniteOrder) : EntireFiniteOrder where
  toFun := fun z ↦ star (F (star z))
  analytic := by
    rw [Complex.analyticOnNhd_univ_iff_differentiable]
    intro z
    have hF := (F.analytic (star z) (mem_univ _)).differentiableAt
    change DifferentiableAt ℂ (star ∘ F.toFun ∘ (starRingEnd ℂ)) z
    simpa [Function.comp_def] using hF.star_conj
  growth := by
    obtain ⟨A, B, ρ, hA, hB, hρ, hgrowth⟩ := F.growth
    refine ⟨A, B, ρ, hA, hB, hρ, fun z ↦ ?_⟩
    simpa only [norm_star] using hgrowth (star z)

@[simp]
theorem EntireFiniteOrder.conjugate_apply (F : EntireFiniteOrder) (z : ℂ) :
    F.conjugate z = star (F (star z)) :=
  rfl

private theorem nat_cpow_conjugate (n : ℕ) (s : ℂ) :
    star ((n : ℂ) ^ (star s)) = (n : ℂ) ^ s := by
  symm
  have harg : (n : ℂ).arg ≠ Real.pi := by
    rw [Complex.natCast_arg]
    exact Real.pi_ne_zero.symm
  simpa using Complex.conj_cpow (n : ℂ) s harg

private theorem lseries_term_conjugate (f : ArithmeticFunction ℂ) (s : ℂ) (n : ℕ) :
    LSeries.term (selbergArithmeticFunctionConjugate f) s n =
      star (LSeries.term f (star s) n) := by
  rw [LSeries.term_def, LSeries.term_def]
  by_cases hn : n = 0
  · simp [hn]
  · simp only [if_neg hn, selbergArithmeticFunctionConjugate_apply]
    change star (f n) / (n : ℂ) ^ s =
      (starRingEnd ℂ) (f n / (n : ℂ) ^ (star s))
    have hdiv : (starRingEnd ℂ) (f n / (n : ℂ) ^ (star s)) =
        star (f n) / star ((n : ℂ) ^ (star s)) :=
      map_div₀ (starRingEnd ℂ) (f n) ((n : ℂ) ^ (star s))
    calc
      star (f n) / (n : ℂ) ^ s = star (f n) / star ((n : ℂ) ^ (star s)) := by
        rw [nat_cpow_conjugate]
      _ = (starRingEnd ℂ) (f n / (n : ℂ) ^ (star s)) := hdiv.symm

/-- Dirichlet series commute with coefficientwise conjugation after conjugating the variable. -/
theorem lSeries_conjugate (f : ArithmeticFunction ℂ) (s : ℂ) :
    LSeries (selbergArithmeticFunctionConjugate f) s = star (LSeries f (star s)) := by
  unfold LSeries
  rw [tsum_star]
  apply tsum_congr
  intro n
  exact lseries_term_conjugate f s n

/-- Absolute convergence of a Dirichlet series is stable under coefficientwise conjugation. -/
theorem lSeriesSummable_conjugate {f : ArithmeticFunction ℂ} {s : ℂ}
    (h : LSeriesSummable f (star s)) :
    LSeriesSummable (selbergArithmeticFunctionConjugate f) s := by
  change Summable (LSeries.term f (star s)) at h
  change Summable (LSeries.term (selbergArithmeticFunctionConjugate f) s)
  have hterm : LSeries.term (selbergArithmeticFunctionConjugate f) s =
      fun n ↦ star (LSeries.term f (star s) n) := by
    funext n
    exact lseries_term_conjugate f s n
  rw [hterm]
  exact h.star

/-- Pole-safe continuation data transported by complex conjugation. -/
def SelbergAnalyticContinuation.conjugate
    (A : SelbergAnalyticContinuation) : SelbergAnalyticContinuation where
  poleOrder := A.poleOrder
  regularized := A.regularized.conjugate

@[simp]
theorem SelbergAnalyticContinuation.conjugate_value
    (A : SelbergAnalyticContinuation) (s : ℂ) :
    A.conjugate.value s = star (A.value (star s)) := by
  change star (A.regularized (star s)) / (s - 1) ^ A.poleOrder =
    (starRingEnd ℂ) (A.regularized (star s) / (star s - 1) ^ A.poleOrder)
  have hdiv : (starRingEnd ℂ) (A.regularized (star s) /
      (star s - 1) ^ A.poleOrder) =
      star (A.regularized (star s)) /
        star ((star s - 1) ^ A.poleOrder) :=
    map_div₀ (starRingEnd ℂ) (A.regularized (star s))
      ((star s - 1) ^ A.poleOrder)
  calc
    star (A.regularized (star s)) / (s - 1) ^ A.poleOrder =
        star (A.regularized (star s)) /
          star ((star s - 1) ^ A.poleOrder) := by simp
    _ = (starRingEnd ℂ) (A.regularized (star s) /
        (star s - 1) ^ A.poleOrder) := hdiv.symm

private theorem real_cpow_conjugate (x : ℝ) (hx : 0 ≤ x) (s : ℂ) :
    star ((x : ℂ) ^ (star s)) = (x : ℂ) ^ s := by
  symm
  have harg : (x : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg hx]
    exact Real.pi_ne_zero.symm
  simpa using Complex.conj_cpow (x : ℂ) s harg

/-- Conjugate gamma-presentation data.  The positive real parameters remain unchanged. -/
def SelbergGammaData.conjugate (G : SelbergGammaData) : SelbergGammaData where
  Q := G.Q
  Q_pos := G.Q_pos
  rank := G.rank
  lambda := G.lambda
  lambda_pos := G.lambda_pos
  mu := fun j ↦ star (G.mu j)
  mu_re_nonneg := by
    intro j
    simpa using G.mu_re_nonneg j
  rootNumber := star G.rootNumber
  rootNumber_norm := by simpa using G.rootNumber_norm

private theorem gamma_term_conjugate (G : SelbergGammaData) (s : ℂ) (j : Fin G.rank) :
    Complex.Gamma ((G.lambda j : ℂ) * s + star (G.mu j)) =
      star (Complex.Gamma ((G.lambda j : ℂ) * star s + G.mu j)) := by
  convert Complex.Gamma_conj ((G.lambda j : ℂ) * star s + G.mu j) using 1 <;> simp

@[simp]
theorem SelbergGammaData.conjugate_gammaFactor (G : SelbergGammaData) (s : ℂ) :
    G.conjugate.gammaFactor s = star (G.gammaFactor (star s)) := by
  simp only [SelbergGammaData.conjugate, SelbergGammaData.gammaFactor, Pi.mul_apply,
    Finset.prod_apply]
  change (G.Q : ℂ) ^ s * ∏ j : Fin G.rank,
      Complex.Gamma ((G.lambda j : ℂ) * s + star (G.mu j)) =
    star ((G.Q : ℂ) ^ (star s) * ∏ j : Fin G.rank,
      Complex.Gamma ((G.lambda j : ℂ) * star s + G.mu j))
  have hmul : star ((G.Q : ℂ) ^ (star s) * ∏ j : Fin G.rank,
      Complex.Gamma ((G.lambda j : ℂ) * star s + G.mu j)) =
      star ((G.Q : ℂ) ^ (star s)) * ∏ j : Fin G.rank,
        star (Complex.Gamma ((G.lambda j : ℂ) * star s + G.mu j)) := by
    have hprod : star (∏ j : Fin G.rank,
        Complex.Gamma ((G.lambda j : ℂ) * star s + G.mu j)) =
        ∏ j : Fin G.rank, star (Complex.Gamma ((G.lambda j : ℂ) * star s + G.mu j)) :=
      map_prod (starRingEnd ℂ) _ _
    calc
      star ((G.Q : ℂ) ^ (star s) * ∏ j : Fin G.rank,
          Complex.Gamma ((G.lambda j : ℂ) * star s + G.mu j)) =
          star ((G.Q : ℂ) ^ (star s)) * star (∏ j : Fin G.rank,
            Complex.Gamma ((G.lambda j : ℂ) * star s + G.mu j)) :=
        map_mul (starRingEnd ℂ) _ _
      _ = star ((G.Q : ℂ) ^ (star s)) * ∏ j : Fin G.rank,
          star (Complex.Gamma ((G.lambda j : ℂ) * star s + G.mu j)) := by rw [hprod]
  rw [hmul]
  rw [real_cpow_conjugate G.Q G.Q_pos.le s]
  congr 1
  exact Finset.prod_congr rfl fun j _ ↦ gamma_term_conjugate G s j

@[simp]
theorem selbergCompletedValue_conjugate (F : ExtendedSelbergClass) (s : ℂ) :
    selbergCompletedValue F.gammaData.conjugate F.continuation.conjugate s =
      star (selbergCompletedValue F.gammaData F.continuation (star s)) := by
  change F.gammaData.conjugate.gammaFactor s * F.continuation.conjugate.value s =
    star (F.gammaData.gammaFactor (star s) * F.continuation.value (star s))
  have hmul : star (F.gammaData.gammaFactor (star s) * F.continuation.value (star s)) =
      star (F.gammaData.gammaFactor (star s)) * star (F.continuation.value (star s)) :=
    map_mul (starRingEnd ℂ) _ _
  rw [hmul, SelbergGammaData.conjugate_gammaFactor,
    SelbergAnalyticContinuation.conjugate_value]

private theorem tendsto_star_codiscrete :
    Tendsto (star : ℂ → ℂ) (codiscrete ℂ) (codiscrete ℂ) := by
  intro S hS
  change S ∈ codiscreteWithin (Set.univ : Set ℂ) at hS
  change (star : ℂ → ℂ) ⁻¹' S ∈ codiscreteWithin (Set.univ : Set ℂ)
  have hEmbedding : Topology.IsEmbedding (star : ℂ → ℂ) :=
    Complex.conjCLE.toHomeomorph.isEmbedding
  have himage : (star : ℂ → ℂ) '' ((star : ℂ → ℂ) ⁻¹' S) = S := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      simpa only [mem_preimage, star_star] using hw
    · intro hz
      refine ⟨star z, ?_, by simp⟩
      simpa only [mem_preimage, star_star] using hz
  have hrange : Set.range (star : ℂ → ℂ) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro z
    exact ⟨star z, by simp⟩
  apply (hEmbedding.image_mem_codiscreteWithin).mp
  simpa only [himage, Set.image_univ, hrange] using hS

private theorem conjugate_functionalEquation (F : ExtendedSelbergClass) :
    selbergCompletedValue F.gammaData.conjugate F.continuation.conjugate =ᶠ[codiscrete ℂ]
      fun s ↦ star F.gammaData.rootNumber *
        selbergConjugateReflection
          (selbergCompletedValue F.gammaData.conjugate F.continuation.conjugate) s := by
  have hF := F.functionalEquation.comp_tendsto tendsto_star_codiscrete
  filter_upwards [hF] with s hs
  change selbergCompletedValue F.gammaData.conjugate F.continuation.conjugate s =
    star F.gammaData.rootNumber * star
      (selbergCompletedValue F.gammaData.conjugate F.continuation.conjugate (1 - star s))
  rw [selbergCompletedValue_conjugate, selbergCompletedValue_conjugate]
  simpa [selbergConjugateReflection] using congrArg star hs

/-- Coefficientwise complex conjugation preserves the extended Selberg carrier. -/
def ExtendedSelbergClass.conjugate (F : ExtendedSelbergClass) : ExtendedSelbergClass where
  coeff := selbergArithmeticFunctionConjugate F.coeff
  coeff_ne_zero := by
    intro h
    apply F.coeff_ne_zero
    apply ArithmeticFunction.ext
    intro n
    have hn := congrArg (fun g : ArithmeticFunction ℂ ↦ g n) h
    simpa using congrArg star hn
  lSeriesSummable := by
    intro s hs
    apply lSeriesSummable_conjugate
    apply F.lSeriesSummable (star s)
    simpa using hs
  continuation := F.continuation.conjugate
  lSeries_eq_value := by
    intro s hs
    rw [lSeries_conjugate, SelbergAnalyticContinuation.conjugate_value]
    exact congrArg star (F.lSeries_eq_value (star s) (by simpa using hs))
  gammaData := F.gammaData.conjugate
  functionalEquation := conjugate_functionalEquation F

@[simp]
theorem ExtendedSelbergClass.conjugate_coeff (F : ExtendedSelbergClass) (n : ℕ) :
    F.conjugate.coeff n = star (F.coeff n) :=
  rfl

@[simp]
theorem ExtendedSelbergClass.conjugate_continuation (F : ExtendedSelbergClass) (s : ℂ) :
    F.conjugate.continuation.value s = star (F.continuation.value (star s)) :=
  SelbergAnalyticContinuation.conjugate_value F.continuation s

@[simp]
theorem ExtendedSelbergClass.conjugate_gammaFactor (F : ExtendedSelbergClass) (s : ℂ) :
    F.conjugate.gammaData.gammaFactor s = star (F.gammaData.gammaFactor (star s)) :=
  SelbergGammaData.conjugate_gammaFactor F.gammaData s

/-- Coefficientwise complex conjugation preserves every full Selberg-class field. -/
def SelbergClass.conjugate (F : SelbergClass) : SelbergClass where
  toExtendedSelbergClass := F.toExtendedSelbergClass.conjugate
  coeff_one := by
    change star (F.coeff 1) = 1
    simp [F.coeff_one]
  ramanujan := by
    intro ε hε
    obtain ⟨C, hC, hbound⟩ := F.ramanujan ε hε
    refine ⟨C, hC, fun n hn ↦ ?_⟩
    simpa using hbound n hn
  eulerLogCoeff := selbergArithmeticFunctionConjugate F.eulerLogCoeff
  eulerLogCoeff_primePower := by
    intro n hn
    apply F.eulerLogCoeff_primePower
    intro hzero
    apply hn
    change star (F.eulerLogCoeff n) = 0
    simp [hzero]
  eulerTheta := F.eulerTheta
  eulerTheta_lt_half := F.eulerTheta_lt_half
  eulerLogBound := by
    obtain ⟨C, hC, hbound⟩ := F.eulerLogBound
    refine ⟨C, hC, fun n hn ↦ ?_⟩
    simpa using hbound n hn
  eulerLogSummable := by
    intro s hs
    apply lSeriesSummable_conjugate
    apply F.eulerLogSummable (star s)
    simpa using hs
  eulerProduct := by
    intro s hs
    change Complex.exp (LSeries (selbergArithmeticFunctionConjugate F.eulerLogCoeff) s) =
      F.continuation.conjugate.value s
    rw [lSeries_conjugate]
    have hexp : Complex.exp (star (LSeries F.eulerLogCoeff (star s))) =
        star (Complex.exp (LSeries F.eulerLogCoeff (star s))) :=
      Complex.exp_conj _
    rw [hexp, SelbergAnalyticContinuation.conjugate_value]
    exact congrArg star (F.eulerProduct (star s) (by simpa using hs))

@[simp]
theorem SelbergClass.conjugate_coeff (F : SelbergClass) (n : ℕ) :
    F.conjugate.coeff n = star (F.coeff n) :=
  rfl

@[simp]
theorem SelbergClass.conjugate_eulerLogCoeff (F : SelbergClass) (n : ℕ) :
    F.conjugate.eulerLogCoeff n = star (F.eulerLogCoeff n) :=
  rfl

@[simp]
theorem SelbergClass.conjugate_value (F : SelbergClass) (s : ℂ) :
    F.conjugate.continuation.value s = star (F.continuation.value (star s)) :=
  SelbergAnalyticContinuation.conjugate_value F.continuation s

end

end RHTower
