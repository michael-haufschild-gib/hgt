import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenPrimeAmplifierHeathBrownLayerScalar
import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenTypeIPrimeAmplifierHeathBrownMoment

/-!
# Type-I receiver from the powered-prime Heath--Brown layer moment

The threshold-layer decomposition retains the powered-block denominator lost by the earlier
coefficient-energy collapse.  This receiver inserts its exact scalar root envelopes into the
restricted Type-I Cauchy argument.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction Complex MeasureTheory

noncomputable section

/-- Exact Type-I charge for one powered-prime block after threshold-layer scalar collapse. -/
noncomputable def mtTypeIPrimeHeathBrownLayerBlockMomentBound
    (eta : ℝ) (a : ℕ → ℂ) (A P ell N N' : ℕ) (T V : ℝ)
    (r : Fin ell) : ℝ :=
  let B := mtTypeIPrimeHeathBrownBlockLength P ell r
  ((ell : ℝ) / V) *
    (mtTypeIPrimeRaisedHeathBrownLayerRootBound
        P ell B N' (N * N) T eta +
      mtTypeIPrimeRaisedHeathBrownLayerRootBound
        P ell B N' (2 * (N * N)) T eta) *
    Real.sqrt
      (generalMeanSquareConst (fun n => mtTypeILongSquareAF a A n)
          (Finset.Icc 1 ((2 * A) * (2 * A))) 1 +
        generalMeanSquareRate (fun n => mtTypeILongSquareAF a A n)
          (Finset.Icc 1 ((2 * A) * (2 * A))) 1 * T)

/-- Section 5.1 Type-I receiver with the sharp layer-cake mixed moment. -/
theorem setIntegral_mtTypeI_primeAmplifier_heathBrown_layer
    (a : ℕ → ℂ) (A P ell N N' : ℕ) (T V eta : ℝ)
    (hP : 1 ≤ P) (hell : 0 < ell) (hN : 2 ≤ N)
    (hNN' : N < N') (hN'le : N' ≤ 2 * N)
    (hT : 2 ≤ T) (hV : 0 < V) (heta : 0 < eta)
    (hblockHeight : ∀ r : Fin ell,
      (((2 * mtTypeIPrimeHeathBrownBlockLength P ell r : ℕ) : ℝ)) ≤ T) :
    (∫ t in mtTypeIPrimeAmplifierLargeSet P ell T V,
        ‖mtWattCoefficientBlock a A t‖ ^ 2 *
          ‖mtWattUnitBlock N N' t‖ ^ 2) ≤
      ∑ r : Fin ell,
        mtTypeIPrimeHeathBrownLayerBlockMomentBound
          eta a A P ell N N' T V r := by
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
        mtTypeIPrimeHeathBrownLayerBlockMomentBound
          eta a A P ell N N' T V r := by
    intro r
    let B := mtTypeIPrimeHeathBrownBlockLength P ell r
    let b := mtTypeIPrimeRaisedCoeff P ell
    let K : ℝ := (ell : ℝ) / V
    let T' : Set.Ioi (0 : ℝ) := ⟨T, lt_of_lt_of_le zero_lt_two hT⟩
    have hB : 1 ≤ B := by
      have hBpos : 0 < B := by
        dsimp only [B, mtTypeIPrimeHeathBrownBlockLength]
        exact Nat.mul_pos (Nat.pow_pos (Nat.zero_lt_of_lt hP))
          (Nat.pow_pos (by omega))
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
    have hmixedSet :
        (∫ t in mtTypeIPrimeAmplifierBlockLargeSet P ell T V r,
          ‖mtWattUnitBlock N N' t‖ ^ 4 *
            ‖mtWattCoefficientBlock b B t‖ ^ 2) ≤
          ∫ t in (-T)..T,
            ‖mtWattUnitBlock N N' t‖ ^ 4 *
              ‖mtWattCoefficientBlock b B t‖ ^ 2 :=
      setIntegral_le_intervalIntegral_of_subset_Icc
        (((continuous_perronPoly _ _ _).norm.pow 4).mul
          ((continuous_perronPoly _ _ _).norm.pow 2))
        (by linarith)
        (fun t ht => by
          have hinterval :=
            mtTypeIPrimeAmplifierBlockLargeSet_subset_Icc P ell T V r ht
          exact ⟨by linarith [hinterval.1], by linarith [hinterval.2]⟩)
        (fun t => mul_nonneg (pow_nonneg (norm_nonneg _) 4) (sq_nonneg _))
    have hmixedFull :
        (∫ t in (-T)..T,
          ‖mtWattUnitBlock N N' t‖ ^ 4 *
            ‖mtWattCoefficientBlock b B t‖ ^ 2) ≤
        (mtTypeIPrimeRaisedHeathBrownLayerRootBound
            P ell B N' (N * N) T eta +
          mtTypeIPrimeRaisedHeathBrownLayerRootBound
            P ell B N' (2 * (N * N)) T eta) ^ 2 := by
      rw [intervalIntegral.integral_of_le (by linarith),
        ← MeasureTheory.integral_Icc_eq_integral_Ioc]
      have hshape :
          (∫ t in Set.Icc (-T) T,
            ‖mtWattUnitBlock N N' t‖ ^ 4 *
              ‖mtWattCoefficientBlock b B t‖ ^ 2) =
          ∫ t in Set.Icc (-T) T,
            ‖mtWattCoefficientBlock b B t *
              (mtWattUnitBlock N N' t) ^ 2‖ ^ 2 := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards with t
        simp only [norm_mul, norm_pow]
        ring
      rw [hshape]
      exact
        integral_Icc_normSq_mtTypeIPrimeRaised_mul_mtWattUnitBlock_sq_le_layerRootBounds_sq
          P ell hB hN (by omega : 1 ≤ N') hN'le T'
            (by simpa only [T', B] using hblockHeight r) heta
    have hfourthSet :
        (∫ t in mtTypeIPrimeAmplifierBlockLargeSet P ell T V r,
          ‖mtWattCoefficientBlock a A t‖ ^ 4) ≤
        ∫ t in (T / 2)..T, ‖mtWattCoefficientBlock a A t‖ ^ 4 :=
      setIntegral_le_intervalIntegral_of_subset_Icc
        ((continuous_perronPoly _ _ _).norm.pow 4)
        (by linarith)
        (mtTypeIPrimeAmplifierBlockLargeSet_subset_Icc P ell T V r)
        (fun t => pow_nonneg (norm_nonneg _) 4)
    have hmixed := hmixedSet.trans hmixedFull
    have hfourth := hfourthSet.trans
      (integral_mtTypeILongBlock_fourth_le_productAffine a A (one_le_two.trans hT))
    have hroot0 : 0 ≤
        mtTypeIPrimeRaisedHeathBrownLayerRootBound
            P ell B N' (N * N) T eta +
          mtTypeIPrimeRaisedHeathBrownLayerRootBound
            P ell B N' (2 * (N * N)) T eta :=
      add_nonneg
        (mtTypeIPrimeRaisedHeathBrownLayerRootBound_nonneg
          P ell B N' (N * N) T heta)
        (mtTypeIPrimeRaisedHeathBrownLayerRootBound_nonneg
          P ell B N' (2 * (N * N)) T heta)
    have hsqrtMixed := Real.sqrt_le_sqrt hmixed
    rw [Real.sqrt_sq hroot0] at hsqrtMixed
    have hsqrtFourth := Real.sqrt_le_sqrt hfourth
    have hproduct := mul_le_mul hsqrtMixed hsqrtFourth
      (Real.sqrt_nonneg _) hroot0
    have hfinal := hcs.trans (by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hproduct hK)
    rw [show 2 * (A * (2 * A)) = (2 * A) * (2 * A) by ring] at hfinal
    rw [← mul_assoc] at hfinal
    simpa only [f, B, b, K, T', mtTypeIPrimeHeathBrownLayerBlockMomentBound]
      using hfinal
  change (∫ t in mtTypeIPrimeAmplifierLargeSet P ell T V, f t) ≤ _
  exact hunion.trans (Finset.sum_le_sum fun r _ => hblock r)

/-- Source-facing layer receiver with all block heights reduced to complete support. -/
theorem setIntegral_mtTypeI_primeAmplifier_heathBrown_layer_of_fullSupport_le
    (a : ℕ → ℂ) (A P ell N N' : ℕ) (T V eta : ℝ)
    (hP : 1 ≤ P) (hell : 0 < ell) (hN : 2 ≤ N)
    (hNN' : N < N') (hN'le : N' ≤ 2 * N)
    (hT : 2 ≤ T) (hV : 0 < V) (heta : 0 < eta)
    (hfull : ((((2 * P) ^ ell : ℕ) : ℝ)) ≤ T) :
    (∫ t in mtTypeIPrimeAmplifierLargeSet P ell T V,
        ‖mtWattCoefficientBlock a A t‖ ^ 2 *
          ‖mtWattUnitBlock N N' t‖ ^ 2) ≤
      ∑ r : Fin ell,
        mtTypeIPrimeHeathBrownLayerBlockMomentBound
          eta a A P ell N N' T V r := by
  apply setIntegral_mtTypeI_primeAmplifier_heathBrown_layer
    a A P ell N N' T V eta hP hell hN hNN' hN'le hT hV heta
  intro r
  have hblock :
      ((2 * mtTypeIPrimeHeathBrownBlockLength P ell r : ℕ) : ℝ) ≤
        (((2 * P) ^ ell : ℕ) : ℝ) := by
    exact_mod_cast two_mul_mtTypeIPrimeHeathBrownBlockLength_le r
  exact hblock.trans hfull

end

end RHTower.Sieve
