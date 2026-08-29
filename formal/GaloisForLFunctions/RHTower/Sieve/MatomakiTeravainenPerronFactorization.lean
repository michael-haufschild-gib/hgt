import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenRealScaleSupport
import GaloisForLFunctions.RHTower.Sieve.PerronPrimeSumBound
import GaloisForLFunctions.RHTower.Sieve.PerronWindowKernel

/-!
# Perron factorization of Matomäki--Teräväinen pieces

The three piece types in Proposition 2.2 are literal Dirichlet convolutions.  This file proves that
their truncated Perron polynomials factor exactly into the source Dirichlet factors at canonical
natural cutoffs obtained from their real support intervals.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction Complex

noncomputable section

/-- Coercing arithmetic-function multiplication to coefficient functions is `LSeries.convolution`.
-/
theorem arithmeticFunction_mul_eq_lseriesConvolution
    (F G : ArithmeticFunction ℂ) :
    (fun n => (F * G) n) = LSeries.convolution (fun n => F n) (fun n => G n) := by
  funext n
  by_cases hn : n = 0
  · subst n
    simp [LSeries.convolution]
  · rw [LSeries.convolution]
    have hF : toArithmeticFunction (fun n => F n) = F := by
      ext k
      by_cases hk : k = 0
      · subst k; simp [toArithmeticFunction]
      · simp [toArithmeticFunction, hk]
    have hG : toArithmeticFunction (fun n => G n) = G := by
      ext k
      by_cases hk : k = 0
      · subst k; simp [toArithmeticFunction]
      · simp [toArithmeticFunction, hk]
    rw [hF, hG]

/-- A Perron polynomial containing the full support equals the corresponding finite `LSeries`. -/
theorem perronPoly_eq_LSeries_of_support
    {f : ℕ → ℂ} {M : ℕ}
    (hf : ∀ n, f n ≠ 0 → n ∈ Finset.Icc 1 M) (σ t : ℝ) :
    perronPoly f M σ t = LSeries f ((σ : ℂ) + (t : ℝ) * I) := by
  simpa [perronPoly] using sum_mul_cpow_neg_eq_LSeries (s := Finset.Icc 1 M)
    (by simp) hf ((σ : ℂ) + (t : ℝ) * I)

/-- The ceiling of the upper real endpoint contains the support of an interval factor. -/
theorem mtRealIntervalAF_support_nat
    (α : ℕ → ℂ) (L U : ℝ) :
    ∀ n, mtRealIntervalAF α L U n ≠ 0 → n ∈ Finset.Icc 1 ⌈U⌉₊ := by
  intro n hn
  have hs := mtRealIntervalAF_scaleSupported α L U hn
  rw [Finset.mem_Icc]
  refine ⟨hs.1, ?_⟩
  exact_mod_cast (hs.2.2.trans (Nat.le_ceil U))

/-- Exact Perron factorization of two finitely supported arithmetic functions. -/
theorem perronPoly_arithmeticFunction_mul
    (F G : ArithmeticFunction ℂ) {MF MG : ℕ}
    (hF : ∀ n, F n ≠ 0 → n ∈ Finset.Icc 1 MF)
    (hG : ∀ n, G n ≠ 0 → n ∈ Finset.Icc 1 MG)
    (σ t : ℝ) :
    perronPoly (fun n => (F * G) n) (MF * MG) σ t =
      perronPoly (fun n => F n) MF σ t *
        perronPoly (fun n => G n) MG σ t := by
  rw [perronPoly_eq_LSeries_of_support
      (fun n hn => convolution_mem_Icc_of_support_mul hF hG
        (arithmeticFunction_mul_eq_lseriesConvolution F G ▸ hn)),
    perronPoly_eq_LSeries_of_support hF,
    perronPoly_eq_LSeries_of_support hG,
    arithmeticFunction_mul_eq_lseriesConvolution,
    LSeries_convolution' (LSeriesSummable_of_support hF _) (LSeriesSummable_of_support hG _)]

/-- Exact factorization for a Proposition-2.2 Type-I piece. -/
theorem MTTypeIPieceData.perronPoly_factorization
    {X Y δ ε : ℝ} (data : MTTypeIPieceData X Y δ ε) (σ t : ℝ) :
    perronPoly (fun n => data.pieceAF n)
        (⌈2 * data.M₁⌉₊ * ⌈(1 + δ) * data.M₂⌉₊) σ t =
      perronPoly (fun n => mtRealIntervalAF data.α data.M₁ (2 * data.M₁) n)
          ⌈2 * data.M₁⌉₊ σ t *
        perronPoly (fun n => mtRealIntervalAF (fun _ => 1) data.M₂
          ((1 + δ) * data.M₂) n) ⌈(1 + δ) * data.M₂⌉₊ σ t := by
  exact perronPoly_arithmeticFunction_mul
    (mtRealIntervalAF data.α data.M₁ (2 * data.M₁))
    (mtRealIntervalAF (fun _ => 1) data.M₂ ((1 + δ) * data.M₂))
    (mtRealIntervalAF_support_nat _ _ _)
    (mtRealIntervalAF_support_nat _ _ _) σ t

/-- Exact three-factor factorization for a Proposition-2.2 Type-I/II piece. -/
theorem MTTypeI_II_PieceData.perronPoly_factorization
    {X Y δ ε : ℝ} (data : MTTypeI_II_PieceData X Y δ ε) (σ t : ℝ) :
    let C1 := ⌈2 * data.M₁⌉₊
    let C2 := ⌈2 * data.M₂⌉₊
    let C3 := ⌈(1 + δ) * data.M₃⌉₊
    perronPoly (fun n => data.pieceAF n) ((C1 * C2) * C3) σ t =
      perronPoly (fun n => mtRealIntervalAF data.α data.M₁ (2 * data.M₁) n)
          C1 σ t *
        perronPoly (fun n => mtRealIntervalAF data.β data.M₂ (2 * data.M₂) n)
          C2 σ t *
        perronPoly (fun n => mtRealIntervalAF (fun _ => 1) data.M₃
          ((1 + δ) * data.M₃) n) C3 σ t := by
  dsimp only
  let F1 := mtRealIntervalAF data.α data.M₁ (2 * data.M₁)
  let F2 := mtRealIntervalAF data.β data.M₂ (2 * data.M₂)
  let F3 := mtRealIntervalAF (fun _ => 1) data.M₃ ((1 + δ) * data.M₃)
  have hF1 := mtRealIntervalAF_support_nat data.α data.M₁ (2 * data.M₁)
  have hF2 := mtRealIntervalAF_support_nat data.β data.M₂ (2 * data.M₂)
  have hF3 := mtRealIntervalAF_support_nat (fun _ => 1) data.M₃ ((1 + δ) * data.M₃)
  have hF12 : ∀ n, (F1 * F2) n ≠ 0 →
      n ∈ Finset.Icc 1 (⌈2 * data.M₁⌉₊ * ⌈2 * data.M₂⌉₊) := by
    intro n hn
    exact convolution_mem_Icc_of_support_mul hF1 hF2
      (arithmeticFunction_mul_eq_lseriesConvolution F1 F2 ▸ hn)
  rw [show data.pieceAF = (F1 * F2) * F3 from rfl,
    perronPoly_arithmeticFunction_mul (F1 * F2) F3 hF12 hF3 σ t,
    perronPoly_arithmeticFunction_mul F1 F2 hF1 hF2 σ t]

/-- Exact factorization for a Proposition-2.2 Type-II piece. -/
theorem MTTypeIIPieceData.perronPoly_factorization
    {X Y z₀ z δ ε : ℝ}
    (data : MTTypeIIPieceData X Y z₀ z δ ε) (σ t : ℝ) :
    perronPoly (fun n => data.pieceAF n)
        (⌈(1 + δ) ^ data.indices.card * data.M₁⌉₊ * ⌈2 * data.M₂⌉₊) σ t =
      perronPoly (fun n => mtRealIntervalAF
          (mtTypeIIPrimeCoefficient data.indices data.block) data.M₁
          ((1 + δ) ^ data.indices.card * data.M₁) n)
        ⌈(1 + δ) ^ data.indices.card * data.M₁⌉₊ σ t *
      perronPoly (fun n => mtRealIntervalAF data.β data.M₂ (2 * data.M₂) n)
        ⌈2 * data.M₂⌉₊ σ t := by
  exact perronPoly_arithmeticFunction_mul
    (mtRealIntervalAF (mtTypeIIPrimeCoefficient data.indices data.block) data.M₁
      ((1 + δ) ^ data.indices.card * data.M₁))
    (mtRealIntervalAF data.β data.M₂ (2 * data.M₂))
    (mtRealIntervalAF_support_nat _ _ _)
    (mtRealIntervalAF_support_nat _ _ _) σ t

end

end RHTower.Sieve
