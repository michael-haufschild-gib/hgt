import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenTypeIPrimeAmplifierMoment
import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenLemma35ConstructedRange

/-!
# Type-I amplifier on the full constructed Lemma 3.5(ii) range

The corpus's strongest unconditional Deshouillers--Iwaniec-shaped moment is available on a union
of five explicit scale regions.  The older Type-I amplifier receiver used only two of them.  This
module propagates the complete constructed union through restricted Cauchy--Schwarz and the literal
powered-prime amplifier cover.  No analytic estimate, coefficient-energy bound, or amplifier lower
bound remains as an external premise.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction Complex MeasureTheory

noncomputable section

/-- Source-faithful Type-I amplified moment on any measurable subset, throughout the full union
of ranges where the corpus constructs Lemma 3.5(ii). -/
theorem exists_setIntegral_mtTypeI_amplified_constructedRange
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (E : Set ℝ) (a b : ℕ → ℂ) (A B N N' : ℕ) (K : ℝ),
      1 ≤ A → 1 ≤ B → 1 ≤ N → N < N' → N' ≤ 2 * N →
      ∀ T : ℝ, 2 ≤ T →
      (T ≤ (N : ℝ) ∨
        Real.sqrt T ≤ (B : ℝ) ∨
          (((2 * B) * (N' * N') : ℕ) : ℝ) ≤
            T + (B : ℝ) ^ 2 * Real.sqrt T +
              (B : ℝ) ^ (5 / 4 : ℝ) * T ^ (3 / 4 : ℝ) ∨
          (T ≤ (N : ℝ) ^ 3 ∧
            T ^ (5 / 6 : ℝ) ≤ (B : ℝ) ^ 2 ∧
            (N : ℝ) ^ (3 / 2 : ℝ) ≤ (B : ℝ) ^ 2 ∧
            (N : ℝ) ≤ (B : ℝ) * T ^ (1 / 6 : ℝ) ∧
            (N : ℝ) ^ (5 / 2 : ℝ) ≤ (B : ℝ) * T)) →
      0 ≤ K → MeasurableSet E → E ⊆ Set.Icc (T / 2) T →
      (∀ t ∈ E, 1 ≤ K * ‖mtWattCoefficientBlock b B t‖) →
      (∫ t in E,
          ‖mtWattCoefficientBlock a A t‖ ^ 2 *
            ‖mtWattUnitBlock N N' t‖ ^ 2) ≤
        K * Real.sqrt
          (C * T ^ epsilon *
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
  obtain ⟨C, hC, hDI⟩ := exists_integral_mtDI_lemma35_constructedRange hepsilon
  refine ⟨C, hC, ?_⟩
  intro E a b A B N N' K hA hB hN hNN' hN' T hT hroute hK hEmeas hE hlarge
  have hcs := setIntegral_normSq_mul_normSq_le_amplified
    (long := mtWattCoefficientBlock a A)
    (unit := mtWattUnitBlock N N')
    (amp := mtWattCoefficientBlock b B)
    (continuous_perronPoly _ _ _)
    (continuous_perronPoly _ _ _)
    (continuous_perronPoly _ _ _)
    hK hEmeas hE hlarge
  have hmixedSet : (∫ t in E,
      ‖mtWattUnitBlock N N' t‖ ^ 4 * ‖mtWattCoefficientBlock b B t‖ ^ 2) ≤
      ∫ t in (T / 2)..T,
        ‖mtWattUnitBlock N N' t‖ ^ 4 * ‖mtWattCoefficientBlock b B t‖ ^ 2 :=
    setIntegral_le_intervalIntegral_of_subset_Icc
      (((continuous_perronPoly _ _ _).norm.pow 4).mul
        ((continuous_perronPoly _ _ _).norm.pow 2))
      (by linarith) hE (fun t =>
        mul_nonneg (pow_nonneg (norm_nonneg (mtWattUnitBlock N N' t)) 4)
          (sq_nonneg ‖mtWattCoefficientBlock b B t‖))
  have hfourthSet : (∫ t in E, ‖mtWattCoefficientBlock a A t‖ ^ 4) ≤
      ∫ t in (T / 2)..T, ‖mtWattCoefficientBlock a A t‖ ^ 4 :=
    setIntegral_le_intervalIntegral_of_subset_Icc
      ((continuous_perronPoly _ _ _).norm.pow 4)
      (by linarith) hE (fun t =>
        pow_nonneg (norm_nonneg (mtWattCoefficientBlock a A t)) 4)
  have hmixed := hmixedSet.trans (hDI b B N N' hB hN hNN' hN' T hT hroute)
  have hfourth := hfourthSet.trans
    (integral_mtTypeILongBlock_fourth_le_productAffine a A (one_le_two.trans hT))
  have hsqrtMixed := Real.sqrt_le_sqrt hmixed
  have hsqrtFourth := Real.sqrt_le_sqrt hfourth
  have hproduct := mul_le_mul hsqrtMixed hsqrtFourth
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  exact hcs.trans (by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hproduct hK)

/-- Prime-amplifier Type-I receiver on every literal block in the full constructed range of
Lemma 3.5(ii). -/
theorem exists_setIntegral_mtTypeI_primeAmplifier_constructedRange
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (a : ℕ → ℂ) (A P ell N N' : ℕ) (T V : ℝ),
      1 ≤ A → 1 ≤ P → 0 < ell → 1 ≤ N → N < N' → N' ≤ 2 * N →
      2 ≤ T → 0 < V →
      (∀ r : Fin ell,
        let B := mtTypeIPrimeBlockLength P ell r
        T ≤ (N : ℝ) ∨
          Real.sqrt T ≤ (B : ℝ) ∨
            (((2 * B) * (N' * N') : ℕ) : ℝ) ≤
              T + (B : ℝ) ^ 2 * Real.sqrt T +
                (B : ℝ) ^ (5 / 4 : ℝ) * T ^ (3 / 4 : ℝ) ∨
            (T ≤ (N : ℝ) ^ 3 ∧
              T ^ (5 / 6 : ℝ) ≤ (B : ℝ) ^ 2 ∧
              (N : ℝ) ^ (3 / 2 : ℝ) ≤ (B : ℝ) ^ 2 ∧
              (N : ℝ) ≤ (B : ℝ) * T ^ (1 / 6 : ℝ) ∧
              (N : ℝ) ^ (5 / 2 : ℝ) ≤ (B : ℝ) * T)) →
      (∫ t in mtTypeIPrimeAmplifierLargeSet P ell T V,
          ‖mtWattCoefficientBlock a A t‖ ^ 2 *
            ‖mtWattUnitBlock N N' t‖ ^ 2) ≤
        ∑ r : Fin ell,
          mtTypeIPrimeBlockMomentBound C epsilon a A P ell N T V r := by
  obtain ⟨C, hC, hrestricted⟩ :=
    exists_setIntegral_mtTypeI_amplified_constructedRange hepsilon
  refine ⟨C, hC, ?_⟩
  intro a A P ell N N' T V hA hP hell hN hNN' hN' hT hV hroute
  let f : ℝ → ℝ := fun t =>
    ‖mtWattCoefficientBlock a A t‖ ^ 2 * ‖mtWattUnitBlock N N' t‖ ^ 2
  have hunion : (∫ t in mtTypeIPrimeAmplifierLargeSet P ell T V, f t) ≤
      ∑ r : Fin ell,
        ∫ t in mtTypeIPrimeAmplifierBlockLargeSet P ell T V r, f t :=
    setIntegral_mtTypeIPrimeAmplifierLargeSet_le_sum_blocks hell T V
      (((continuous_perronPoly _ _ _).norm.pow 2).mul
        ((continuous_perronPoly _ _ _).norm.pow 2))
      (fun _ => by positivity)
  have hblock : ∀ r : Fin ell,
      (∫ t in mtTypeIPrimeAmplifierBlockLargeSet P ell T V r, f t) ≤
        mtTypeIPrimeBlockMomentBound C epsilon a A P ell N T V r := by
    intro r
    let B := mtTypeIPrimeBlockLength P ell r
    let b := mtTypeIPrimeRaisedCoeff P ell
    let K : ℝ := (ell : ℝ) / V
    have hB : 1 ≤ B := by
      have hBpos : 0 < B := by
        dsimp only [B, mtTypeIPrimeBlockLength]
        positivity
      omega
    have hK : 0 ≤ K := by
      dsimp only [K]
      positivity
    have hlarge : ∀ t ∈ mtTypeIPrimeAmplifierBlockLargeSet P ell T V r,
        1 ≤ K * ‖mtWattCoefficientBlock b B t‖ := by
      intro t ht
      have hscale : (1 : ℝ) = K * (V / (ell : ℝ)) := by
        dsimp only [K]
        have hellR : (0 : ℝ) < ell := by positivity
        field_simp
      rw [hscale]
      exact mul_le_mul_of_nonneg_left ht.2 hK
    have hr := hrestricted
      (mtTypeIPrimeAmplifierBlockLargeSet P ell T V r)
      a b A B N N' K hA hB hN hNN' hN' T hT
      (by simpa only [B] using hroute r) hK
      (measurableSet_mtTypeIPrimeAmplifierBlockLargeSet P ell T V r)
      (mtTypeIPrimeAmplifierBlockLargeSet_subset_Icc P ell T V r) hlarge
    simpa only [f, B, b, K, mtTypeIPrimeBlockMomentBound] using hr
  change (∫ t in mtTypeIPrimeAmplifierLargeSet P ell T V, f t) ≤ _
  exact hunion.trans (Finset.sum_le_sum fun r _ => hblock r)

end

end RHTower.Sieve
