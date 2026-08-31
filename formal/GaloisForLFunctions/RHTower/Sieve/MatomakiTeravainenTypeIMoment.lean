import GaloisForLFunctions.HTGeometry.IntervalMeanSquareMoment
import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenLemma35CoveredRange
import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenWattProductMeanSquare

/-!
# Matomäki--Teräväinen Type-I amplified moment

This file formalizes the analytic receiver in Section 5.1 of the source paper.  The amplifier is
inserted pointwise, Cauchy--Schwarz separates the Deshouillers--Iwaniec mixed moment from the
fourth moment of the long coefficient block, and the latter is turned into the ordinary affine
mean square of its literal Dirichlet-convolution square.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction Complex MeasureTheory

noncomputable section

/-- Pointwise amplifier insertion followed by Cauchy--Schwarz on one dyadic height block. -/
theorem integral_normSq_mul_normSq_le_amplified
    {long unit amp : ℝ → ℂ} (hlong : Continuous long)
    (hunit : Continuous unit) (hamp : Continuous amp)
    {T K : ℝ} (hT : 0 ≤ T) (hK : 0 ≤ K)
    (hlarge : ∀ t ∈ Set.Icc (T / 2) T, 1 ≤ K * ‖amp t‖) :
    (∫ t in (T / 2)..T, ‖long t‖ ^ 2 * ‖unit t‖ ^ 2) ≤
      K * Real.sqrt (∫ t in (T / 2)..T,
          ‖unit t‖ ^ 4 * ‖amp t‖ ^ 2) *
        Real.sqrt (∫ t in (T / 2)..T, ‖long t‖ ^ 4) := by
  let A : ℝ → ℂ := fun t => unit t * unit t * amp t
  let B : ℝ → ℂ := fun t => long t * long t
  have hA : Continuous A := (hunit.mul hunit).mul hamp
  have hB : Continuous B := hlong.mul hlong
  have hpoint : ∀ t ∈ Set.Icc (T / 2) T,
      ‖long t‖ ^ 2 * ‖unit t‖ ^ 2 ≤ K * (‖A t‖ * ‖B t‖) := by
    intro t ht
    have hbase : 0 ≤ ‖long t‖ ^ 2 * ‖unit t‖ ^ 2 := by positivity
    have hmul := mul_le_mul_of_nonneg_left (hlarge t ht) hbase
    dsimp only [A, B]
    simp only [norm_mul]
    nlinarith
  have hmono := intervalIntegral.integral_mono_on (μ := volume)
    (f := fun t : ℝ => ‖long t‖ ^ 2 * ‖unit t‖ ^ 2)
    (g := fun t : ℝ => K * (‖A t‖ * ‖B t‖))
    (by linarith : T / 2 ≤ T)
    (((hlong.norm.pow 2).mul (hunit.norm.pow 2)).intervalIntegrable _ _)
    ((continuous_const.mul (hA.norm.mul hB.norm)).intervalIntegrable _ _) hpoint
  rw [intervalIntegral.integral_const_mul] at hmono
  have hcs :=
    GaloisForLFunctions.HTGeometry.integral_norm_mul_norm_le_sqrt_mul_sqrt
      hA hB (by linarith : T / 2 ≤ T)
  have hscaled := mul_le_mul_of_nonneg_left hcs hK
  have hAint : (∫ t in (T / 2)..T, ‖A t‖ ^ 2) =
      ∫ t in (T / 2)..T, ‖unit t‖ ^ 4 * ‖amp t‖ ^ 2 := by
    apply intervalIntegral.integral_congr
    intro t _
    dsimp only [A]
    simp only [norm_mul]
    ring
  have hBint : (∫ t in (T / 2)..T, ‖B t‖ ^ 2) =
      ∫ t in (T / 2)..T, ‖long t‖ ^ 4 := by
    apply intervalIntegral.integral_congr
    intro t _
    dsimp only [B]
    simp only [norm_mul]
    ring
  calc
    (∫ t in (T / 2)..T, ‖long t‖ ^ 2 * ‖unit t‖ ^ 2) ≤
        K * ∫ t in (T / 2)..T, ‖A t‖ * ‖B t‖ := hmono
    _ ≤ K *
        (Real.sqrt (∫ t in (T / 2)..T, ‖A t‖ ^ 2) *
          Real.sqrt (∫ t in (T / 2)..T, ‖B t‖ ^ 2)) := hscaled
    _ = K * Real.sqrt (∫ t in (T / 2)..T,
          ‖unit t‖ ^ 4 * ‖amp t‖ ^ 2) *
        Real.sqrt (∫ t in (T / 2)..T, ‖long t‖ ^ 4) := by
      rw [hAint, hBint]
      ring

/-- Dirichlet-convolution square of one dyadic coefficient block. -/
def mtTypeILongSquareAF (a : ℕ → ℂ) (A : ℕ) : ArithmeticFunction ℂ :=
  mtRealIntervalAF a (A : ℝ) (2 * A : ℝ) *
    mtRealIntervalAF a (A : ℝ) (2 * A : ℝ)

/-- The convolution square has the literal squared support. -/
theorem mtTypeILongSquareAF_support (a : ℕ → ℂ) (A : ℕ) :
    ∀ n, mtTypeILongSquareAF a A n ≠ 0 →
      n ∈ Finset.Icc 1 ((2 * A) * (2 * A)) := by
  let F := mtRealIntervalAF a (A : ℝ) (2 * A : ℝ)
  have hF : ∀ n, F n ≠ 0 → n ∈ Finset.Icc 1 (2 * A) := by
    simpa [F] using mtWattCoefficientBlock_support a A
  intro n hn
  exact convolution_mem_Icc_of_support_mul hF hF
    (arithmeticFunction_mul_eq_lseriesConvolution F F ▸ hn)

/-- The squared coefficient block is exactly the Perron polynomial of its convolution square. -/
theorem perronPoly_mtTypeILongSquareAF
    (a : ℕ → ℂ) (A : ℕ) (t : ℝ) :
    perronPoly (fun n => mtTypeILongSquareAF a A n)
        ((2 * A) * (2 * A)) 1 t =
      mtWattCoefficientBlock a A t * mtWattCoefficientBlock a A t := by
  let F := mtRealIntervalAF a (A : ℝ) (2 * A : ℝ)
  have hF : ∀ n, F n ≠ 0 → n ∈ Finset.Icc 1 (2 * A) := by
    simpa [F] using mtWattCoefficientBlock_support a A
  rw [show mtTypeILongSquareAF a A = F * F by rfl,
    perronPoly_arithmeticFunction_mul F F hF hF]
  rfl

/-- Ordinary affine mean square controls the fourth moment of a coefficient block. -/
theorem integral_mtTypeILongBlock_fourth_le_productAffine
    (a : ℕ → ℂ) (A : ℕ) {T : ℝ} (hT : 1 ≤ T) :
    (∫ t in (T / 2)..T, ‖mtWattCoefficientBlock a A t‖ ^ 4) ≤
      generalMeanSquareConst (fun n => mtTypeILongSquareAF a A n)
          (Finset.Icc 1 ((2 * A) * (2 * A))) 1 +
        generalMeanSquareRate (fun n => mtTypeILongSquareAF a A n)
          (Finset.Icc 1 ((2 * A) * (2 * A))) 1 * T := by
  let c : ℕ → ℂ := fun n => mtTypeILongSquareAF a A n
  let M := (2 * A) * (2 * A)
  let B := generalMeanSquareConst c (Finset.Icc 1 M) 1 +
    generalMeanSquareRate c (Finset.Icc 1 M) 1 * T
  have hsupp : ∀ n, c n ≠ 0 → n ∈ Finset.Icc 1 M :=
    mtTypeILongSquareAF_support a A
  have hpoly : ∀ t : ℝ,
      perronPoly c M 1 t = LSeries c (((1 : ℝ) : ℂ) + (t : ℝ) * I) := by
    intro t
    exact perronPoly_eq_LSeries_of_support hsupp 1 t
  have hfullSet := integral_Icc_normSq_LSeries_le_general_affine
    (a := c) (s := Finset.Icc 1 M) (by simp) hsupp 1 hT
  have hfull : (∫ t in (-T)..T, ‖perronPoly c M 1 t‖ ^ 2) ≤ B := by
    rw [intervalIntegral.integral_of_le (by linarith : -T ≤ T),
      ← MeasureTheory.integral_Icc_eq_integral_Ioc]
    simpa only [hpoly, B] using hfullSet
  have hcont : Continuous (fun t : ℝ => ‖perronPoly c M 1 t‖ ^ 2) :=
    (continuous_perronPoly c M 1).norm.pow 2
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (f := fun t : ℝ => ‖perronPoly c M 1 t‖ ^ 2)
    (μ := volume) (a := -T) (b := T / 2) (c := T)
    (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)
  have hleft : 0 ≤ ∫ t in (-T)..(T / 2), ‖perronPoly c M 1 t‖ ^ 2 :=
    intervalIntegral.integral_nonneg (by linarith) (fun _ _ => sq_nonneg _)
  have hsub : (∫ t in (T / 2)..T, ‖perronPoly c M 1 t‖ ^ 2) ≤ B := by
    linarith [hsplit, hleft, hfull]
  have hpoint : ∀ t : ℝ,
      ‖mtWattCoefficientBlock a A t‖ ^ 4 = ‖perronPoly c M 1 t‖ ^ 2 := by
    intro t
    rw [show perronPoly c M 1 t =
      mtWattCoefficientBlock a A t * mtWattCoefficientBlock a A t by
        simpa only [c, M] using perronPoly_mtTypeILongSquareAF a A t]
    simp only [norm_mul]
    ring
  rw [intervalIntegral.integral_congr (fun t _ => hpoint t)]
  simpa only [B, c, M] using hsub

/-- Source-faithful Type-I amplified moment on every range covered by Lemma 3.5.  The
Deshouillers--Iwaniec constant and both analytic moments are produced internally; the only
remaining input is the pointwise amplifier lower bound used to define the source's large set. -/
theorem exists_integral_mtTypeI_amplified_coveredRange
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (a b : ℕ → ℂ) (A B N N' : ℕ) (K : ℝ),
      1 ≤ A → 1 ≤ B → 1 ≤ N → N < N' → N' ≤ 2 * N →
      ∀ T : ℝ, 2 ≤ T →
      (T ≤ (N : ℝ) ∨
        ((B : ℝ) ≤ T ∧
          ((((2 * B) * (N' * N') : ℕ) : ℝ) ≤
            (B : ℝ) ^ (5 / 4 : ℝ) * T ^ (3 / 4 : ℝ)))) →
      0 ≤ K →
      (∀ t ∈ Set.Icc (T / 2) T,
        1 ≤ K * ‖mtWattCoefficientBlock b B t‖) →
      (∫ t in (T / 2)..T,
          ‖mtWattCoefficientBlock a A t‖ ^ 2 *
            ‖mtWattUnitBlock N N' t‖ ^ 2) ≤
        K * Real.sqrt
          (C * T ^ ε *
            (((T + (B : ℝ) ^ 2 * Real.sqrt T +
                    (B : ℝ) ^ (5 / 4 : ℝ) * T ^ (3 / 4 : ℝ)) /
                  ((N : ℝ) ^ 2 * (B : ℝ)) +
                (T + (B : ℝ)) / (T ^ 4 * (B : ℝ))) *
              (1 / (B : ℝ)) *
              (∑ m ∈ Finset.Ioc B (2 * B), ‖b m‖ ^ 2))) *
          Real.sqrt
            (generalMeanSquareConst (fun n => mtTypeILongSquareAF a A n)
                (Finset.Icc 1 ((2 * A) * (2 * A))) 1 +
              generalMeanSquareRate (fun n => mtTypeILongSquareAF a A n)
                (Finset.Icc 1 ((2 * A) * (2 * A))) 1 * T) := by
  obtain ⟨C, hC, hDI⟩ := exists_integral_mtDI_lemma35_coveredRange hε
  refine ⟨C, hC, ?_⟩
  intro a b A B N N' K hA hB hN hNN' hN' T hT hcovered hK hlarge
  have hcs := integral_normSq_mul_normSq_le_amplified
    (long := mtWattCoefficientBlock a A)
    (unit := mtWattUnitBlock N N')
    (amp := mtWattCoefficientBlock b B)
    (continuous_perronPoly _ _ _)
    (continuous_perronPoly _ _ _)
    (continuous_perronPoly _ _ _)
    (zero_le_two.trans hT) hK hlarge
  have hmixed := hDI b B N N' hB hN hNN' hN' T hT hcovered
  have hfourth := integral_mtTypeILongBlock_fourth_le_productAffine a A
    (one_le_two.trans hT)
  have hsqrtMixed := Real.sqrt_le_sqrt hmixed
  have hsqrtFourth := Real.sqrt_le_sqrt hfourth
  have hproduct := mul_le_mul hsqrtMixed hsqrtFourth
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  exact hcs.trans (by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hproduct hK)

end

end RHTower.Sieve
