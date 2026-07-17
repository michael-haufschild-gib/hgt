import GaloisForLFunctions.RHTower.VonMangoldtGammaBivariateMoment

/-!
# Mixed Gram positivity for the von Mangoldt--Gamma source

The fixed Taylor-remainder kernel supplies more than a positive Hankel matrix at each depth.
Arbitrary monomials in the source rate and the unit-interval remainder parameter have a positive
Gram matrix.  Thus coordinates from different Gamma-anomaly depths belong to one positive
bivariate moment functional.

This is an unconditional source theorem.  Positivity after inverse tilt and polar critical
completion remains a separate comparison problem; no such transport is assumed here.
-/

open scoped BigOperators
open MeasureTheory Set

namespace RHTower

noncomputable section

/-- The unit-interval remainder moment for one exponential rate. -/
def exponentialRemainderMoment (rate : ℝ) (b : ℕ) : ℝ :=
  ∫ u in (0 : ℝ)..1, u ^ b * Real.exp (-rate * (1 - u))

/-- The mixed monomial Gram matrix contributed by one exponential rate. -/
def exponentialRemainderBivariateGramAtom
    {n : ℕ} (rate : ℝ) (a b : Fin n → ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j ↦ rate ^ (a i + a j) * exponentialRemainderMoment rate (b i + b j)

/-- Every single-rate mixed monomial Gram matrix is positive semidefinite. -/
theorem exponentialRemainderBivariateGramAtom_posSemidef
    {n : ℕ} (rate : ℝ) (a b : Fin n → ℕ) :
    (exponentialRemainderBivariateGramAtom rate a b).PosSemidef := by
  classical
  let B : ℕ := (∑ i : Fin n, b i) + 1
  have hble (i : Fin n) : b i ≤ ∑ j : Fin n, b j := by
    exact Finset.single_le_sum (s := Finset.univ) (f := b)
      (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i)
  let e : Fin n → Fin B := fun i ↦
    ⟨b i, lt_of_le_of_lt (hble i) (Nat.lt_succ_self _)⟩
  let H : Matrix (Fin B) (Fin B) ℝ :=
    Matrix.of fun i j ↦ ∫ u : ℝ, u ^ ((i : ℕ) + (j : ℕ))
      ∂exponentialRemainderMeasure rate
  have hH : H.PosSemidef := by
    dsimp only [H]
    apply HTGeometry.hankelMatrix_posSemidef
      (s := fun k ↦ ∫ u : ℝ, u ^ k ∂exponentialRemainderMeasure rate)
      (fun _ ↦ rfl)
      (integrable_pow_exponentialRemainderMeasure rate)
  have hsub : (H.submatrix e e).PosSemidef := hH.submatrix e
  let D : Matrix (Fin n) (Fin n) ℝ := Matrix.diagonal fun i ↦ rate ^ a i
  have hcong := hsub.conjTranspose_mul_mul_same D
  convert hcong using 1
  ext i j
  simp [D, H, e, exponentialRemainderBivariateGramAtom,
    exponentialRemainderMoment, exponentialRemainderMeasure_moment,
    Matrix.mul_apply, Matrix.diagonal_apply]
  rw [pow_add]
  ring

/-- Gram matrix of arbitrary bivariate monomials against a finite exponential source. -/
def finiteExponentialGammaBivariateGram
    {P : Type*} [Fintype P] {n : ℕ}
    (weight rate : P → ℝ) (x : ℝ) (a b : Fin n → ℕ) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j ↦ finiteExponentialGammaBivariateMoment weight rate x
    (a i + a j) (b i + b j)

theorem finiteExponentialGammaBivariateGram_eq_sum
    {P : Type*} [Fintype P] {n : ℕ}
    (weight rate : P → ℝ) (x : ℝ) (a b : Fin n → ℕ) :
    finiteExponentialGammaBivariateGram weight rate x a b =
      ∑ p : P, (weight p * Real.exp (-x * rate p)) •
        exponentialRemainderBivariateGramAtom (rate p) a b := by
  ext i j
  simp only [finiteExponentialGammaBivariateGram,
    finiteExponentialGammaBivariateMoment, Matrix.sum_apply, Matrix.smul_apply,
    smul_eq_mul]
  apply Finset.sum_congr rfl
  intro p hp
  rw [exponentialRemainderBivariateGramAtom, exponentialRemainderMoment]
  ring

/-- Nonnegative source weights make every mixed bivariate monomial Gram positive semidefinite. -/
theorem finiteExponentialGammaBivariateGram_posSemidef
    {P : Type*} [Fintype P] {n : ℕ}
    (weight rate : P → ℝ) (x : ℝ) (a b : Fin n → ℕ)
    (hweight : ∀ p, 0 ≤ weight p) :
    (finiteExponentialGammaBivariateGram weight rate x a b).PosSemidef := by
  rw [finiteExponentialGammaBivariateGram_eq_sum]
  apply Matrix.posSemidef_sum Finset.univ
  intro p hp
  apply Matrix.PosSemidef.smul
  · exact exponentialRemainderBivariateGramAtom_posSemidef (rate p) a b
  · exact mul_nonneg (hweight p) (Real.exp_pos _).le

/-- The mixed bivariate Gram of the actual finite von Mangoldt source. -/
def finiteVonMangoldtGammaBivariateGram
    (M : ℕ) {n : ℕ} (x : ℝ) (a b : Fin n → ℕ) :
    Matrix (Fin n) (Fin n) ℝ :=
  finiteExponentialGammaBivariateGram
    (fun p : Fin M ↦
      ArithmeticFunction.vonMangoldt ((p : ℕ) + 2) / ((p : ℕ) + 2))
    (fun p : Fin M ↦ Real.log ((p : ℕ) + 2)) x a b

/-- Unconditional mixed Gram positivity for the finite von Mangoldt--Gamma source. -/
theorem finiteVonMangoldtGammaBivariateGram_posSemidef
    (M : ℕ) {n : ℕ} (x : ℝ) (a b : Fin n → ℕ) :
    (finiteVonMangoldtGammaBivariateGram M x a b).PosSemidef := by
  apply finiteExponentialGammaBivariateGram_posSemidef
  intro p
  exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity)

/-- The factorially normalized, reverse-indexed anomaly matrix attached to arbitrary admissible
pairs of Gamma depth and remainder degree. -/
def finiteVonMangoldtGammaAnomalyMixedGram
    (M : ℕ) {n : ℕ} (x : ℝ) (a b : Fin n → ℕ)
    (hadm : ∀ i j, b i + b j < a i + a j) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j ↦
    (((b i + b j).factorial : ℕ) : ℝ) *
      (-1 : ℝ) ^ (a i + a j + 1) *
        (finiteVonMangoldtGammaAnomaly M (x : ℂ) (a i + a j) (fun _ ↦ 1)
          (gammaAnomalyReverseIndex (a i + a j) (b i + b j) (hadm i j))).re

/-- The normalized mixed anomaly matrix is exactly the fixed bivariate source Gram. -/
theorem finiteVonMangoldtGammaAnomalyMixedGram_eq_bivariateGram
    (M : ℕ) {n : ℕ} (x : ℝ) (a b : Fin n → ℕ)
    (hadm : ∀ i j, b i + b j < a i + a j) :
    finiteVonMangoldtGammaAnomalyMixedGram M x a b hadm =
      finiteVonMangoldtGammaBivariateGram M x a b := by
  ext i j
  exact finiteVonMangoldtGammaAnomaly_reverse_eq_bivariateMoment
    M x (a i + a j) (b i + b j) (hadm i j)

/-- Every admissible normalized all-depth Gamma-anomaly matrix is positive semidefinite. -/
theorem finiteVonMangoldtGammaAnomalyMixedGram_posSemidef
    (M : ℕ) {n : ℕ} (x : ℝ) (a b : Fin n → ℕ)
    (hadm : ∀ i j, b i + b j < a i + a j) :
    (finiteVonMangoldtGammaAnomalyMixedGram M x a b hadm).PosSemidef := by
  rw [finiteVonMangoldtGammaAnomalyMixedGram_eq_bivariateGram]
  exact finiteVonMangoldtGammaBivariateGram_posSemidef M x a b

end

end RHTower
