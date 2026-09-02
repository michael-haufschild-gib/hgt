import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenLemma35OneUnit
import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenTypeIPrimeAmplifierMoment

/-!
# Type-I powered-prime receiver from the one-unit derivative moment

The one-unit branch keeps one reciprocal block pointwise and applies an affine mean square to the
other reciprocal block times the powered-prime block.  Unlike the Heath--Brown replacement, its
bound is coefficient-energy faithful and introduces no factorial normalization.  This file inserts
that unconditional mixed moment into the exact powered-amplifier block cover.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction Complex MeasureTheory

noncomputable section

/-- One-unit Type-I bound charged to one fixed powered-prime Watt block. -/
noncomputable def mtTypeIPrimeOneUnitBlockMomentBound
    (C epsilon : ℝ) (a : ℕ → ℂ) (A P ell N N' : ℕ) (T V : ℝ)
    (r : Fin ell) : ℝ :=
  let B := mtTypeIPrimeBlockLength P ell r
  let b := mtTypeIPrimeRaisedCoeff P ell
  ((ell : ℝ) / V) * Real.sqrt
      (C * T ^ epsilon *
        (T + ((((2 * B) * N' : ℕ) : ℝ))) *
        (1 / (B : ℝ) ^ 2) *
        (∑ m ∈ Finset.Ioc B (2 * B), ‖b m‖ ^ 2) *
        (1 / (N : ℝ)) *
        (Real.sqrt T / (N : ℝ) + 1 / Real.sqrt T) ^ 2) *
    Real.sqrt
      (generalMeanSquareConst (fun n => mtTypeILongSquareAF a A n)
          (Finset.Icc 1 ((2 * A) * (2 * A))) 1 +
        generalMeanSquareRate (fun n => mtTypeILongSquareAF a A n)
          (Finset.Icc 1 ((2 * A) * (2 * A))) 1 * T)

/-- Powered-prime Type-I receiver on the complete sub-height range of the one-unit derivative
moment.  Amplifier cover, lower bounds, mixed moment, and long fourth moment are all constructed
internally; only the displayed source scale comparisons remain. -/
theorem exists_setIntegral_mtTypeI_primeAmplifier_oneUnit
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (a : ℕ → ℂ) (A P ell N N' : ℕ) (T V : ℝ),
      1 ≤ A → 1 ≤ P → 0 < ell → 1 ≤ N → N < N' → N' ≤ 2 * N →
      2 ≤ T → 0 < V → (N : ℝ) ≤ T →
      (∀ r : Fin ell, (mtTypeIPrimeBlockLength P ell r : ℝ) ≤ T) →
      (∫ t in mtTypeIPrimeAmplifierLargeSet P ell T V,
          ‖mtWattCoefficientBlock a A t‖ ^ 2 *
            ‖mtWattUnitBlock N N' t‖ ^ 2) ≤
        ∑ r : Fin ell,
          mtTypeIPrimeOneUnitBlockMomentBound
            C epsilon a A P ell N N' T V r := by
  obtain ⟨C, hC, honeUnit⟩ :=
    exists_integral_mtWatt_oneUnit_secondDerivative_height hepsilon
  refine ⟨C, hC, ?_⟩
  intro a A P ell N N' T V hA hP hell hN hNN' hN' hT hV hNT hblockHeight
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
        mtTypeIPrimeOneUnitBlockMomentBound
          C epsilon a A P ell N N' T V r := by
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
    have hcs := setIntegral_normSq_mul_normSq_le_amplified
      (long := mtWattCoefficientBlock a A)
      (unit := mtWattUnitBlock N N')
      (amp := mtWattCoefficientBlock b B)
      (continuous_perronPoly _ _ _)
      (continuous_perronPoly _ _ _)
      (continuous_perronPoly _ _ _)
      hK (measurableSet_mtTypeIPrimeAmplifierBlockLargeSet P ell T V r)
      (mtTypeIPrimeAmplifierBlockLargeSet_subset_Icc P ell T V r) hlarge
    have hmixedSet : (∫ t in mtTypeIPrimeAmplifierBlockLargeSet P ell T V r,
        ‖mtWattUnitBlock N N' t‖ ^ 4 * ‖mtWattCoefficientBlock b B t‖ ^ 2) ≤
        ∫ t in (T / 2)..T,
          ‖mtWattUnitBlock N N' t‖ ^ 4 * ‖mtWattCoefficientBlock b B t‖ ^ 2 :=
      setIntegral_le_intervalIntegral_of_subset_Icc
        (((continuous_perronPoly _ _ _).norm.pow 4).mul
          ((continuous_perronPoly _ _ _).norm.pow 2))
        (by linarith)
        (mtTypeIPrimeAmplifierBlockLargeSet_subset_Icc P ell T V r)
        (fun t => mul_nonneg (pow_nonneg (norm_nonneg _) 4) (sq_nonneg _))
    have hfourthSet :
        (∫ t in mtTypeIPrimeAmplifierBlockLargeSet P ell T V r,
          ‖mtWattCoefficientBlock a A t‖ ^ 4) ≤
        ∫ t in (T / 2)..T, ‖mtWattCoefficientBlock a A t‖ ^ 4 :=
      setIntegral_le_intervalIntegral_of_subset_Icc
        ((continuous_perronPoly _ _ _).norm.pow 4)
        (by linarith)
        (mtTypeIPrimeAmplifierBlockLargeSet_subset_Icc P ell T V r)
        (fun t => pow_nonneg (norm_nonneg _) 4)
    have hmixed := hmixedSet.trans
      (honeUnit b B N N' hB hN hNN' hN' T hT (hblockHeight r) hNT)
    have hfourth := hfourthSet.trans
      (integral_mtTypeILongBlock_fourth_le_productAffine a A (one_le_two.trans hT))
    have hsqrtMixed := Real.sqrt_le_sqrt hmixed
    have hsqrtFourth := Real.sqrt_le_sqrt hfourth
    have hproduct := mul_le_mul hsqrtMixed hsqrtFourth
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    have hfinal := hcs.trans (by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hproduct hK)
    rw [show 2 * (A * (2 * A)) = (2 * A) * (2 * A) by ring] at hfinal
    rw [mtTypeIPrimeOneUnitBlockMomentBound]
    dsimp only [f, B, b, K]
    simpa only [mul_assoc] using hfinal
  change (∫ t in mtTypeIPrimeAmplifierLargeSet P ell T V, f t) ≤ _
  exact hunion.trans (Finset.sum_le_sum fun r _ => hblock r)

end

end RHTower.Sieve
