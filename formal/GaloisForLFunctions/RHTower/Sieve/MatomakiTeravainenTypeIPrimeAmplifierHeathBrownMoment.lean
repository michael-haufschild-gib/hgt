import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenPrimeAmplifierHeathBrownEnergyMoment

/-!
# Type-I receiver from the powered-prime Heath--Brown moment

This closes the restricted Type-I Cauchy receiver for the literal powered prime amplifier without
an abstract Lemma 3.5 premise.  The exact amplifier block cover, amplifier lower bounds, mixed
moment, and long-factor fourth moment are all constructed internally.  The remaining scale clause
is the literal Heath--Brown height requirement for each fixed block.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction Complex MeasureTheory

noncomputable section

/-- Length of a literal fixed Watt block, named independently of the DI receiver. -/
def mtTypeIPrimeHeathBrownBlockLength (P ell : ℕ) (r : Fin ell) : ℕ :=
  P ^ ell * 2 ^ (r : ℕ)

/-- Every fixed Watt block ends below the complete powered-prime support length. -/
theorem two_mul_mtTypeIPrimeHeathBrownBlockLength_le
    {P ell : ℕ} (r : Fin ell) :
    2 * mtTypeIPrimeHeathBrownBlockLength P ell r ≤ (2 * P) ^ ell := by
  calc
    2 * mtTypeIPrimeHeathBrownBlockLength P ell r =
        P ^ ell * 2 ^ ((r : ℕ) + 1) := by
      rw [mtTypeIPrimeHeathBrownBlockLength, pow_succ]
      ring
    _ ≤ P ^ ell * 2 ^ ell := by
      exact Nat.mul_le_mul_left _
        (Nat.pow_le_pow_right (by norm_num) (Nat.succ_le_iff.mpr r.isLt))
    _ = (2 * P) ^ ell := by
      rw [mul_pow]
      ring

/-- Exact Type-I bound charged to one powered-prime block by the Heath--Brown replacement. -/
noncomputable def mtTypeIPrimeHeathBrownBlockMomentBound
    (eta : ℝ) (a : ℕ → ℂ) (A P ell N N' : ℕ) (T V : ℝ)
    (r : Fin ell) : ℝ :=
  let B := mtTypeIPrimeHeathBrownBlockLength P ell r
  ((ell : ℝ) / V) * Real.sqrt
      (mtTypeIPrimeRaisedHeathBrownEnergyMomentCoefficient
          P ell B N N' T eta *
        (∑ m ∈ Finset.Ioc B (2 * B),
          ‖mtTypeIPrimeRaisedCoeff P ell m‖ ^ (2 : ℕ))) *
    Real.sqrt
      (generalMeanSquareConst (fun n => mtTypeILongSquareAF a A n)
          (Finset.Icc 1 ((2 * A) * (2 * A))) 1 +
        generalMeanSquareRate (fun n => mtTypeILongSquareAF a A n)
          (Finset.Icc 1 ((2 * A) * (2 * A))) 1 * T)

/-- Section 5.1 Type-I receiver with every analytic moment and amplifier hypothesis discharged. -/
theorem setIntegral_mtTypeI_primeAmplifier_heathBrown
    (a : ℕ → ℂ) (A P ell N N' : ℕ) (T V eta : ℝ)
    (hP : 1 ≤ P) (hell : 0 < ell) (hN : 2 ≤ N)
    (hNN' : N < N') (hN'le : N' ≤ 2 * N)
    (hT : 2 ≤ T) (hV : 0 < V) (heta : 0 < eta)
    (hblockHeight : ∀ r : Fin ell,
      (((2 * mtTypeIPrimeHeathBrownBlockLength P ell r : ℕ) : ℝ)) ≤ T) :
    (∫ t in mtTypeIPrimeAmplifierLargeSet P ell T V,
        ‖mtWattCoefficientBlock a A t‖ ^ (2 : ℕ) *
          ‖mtWattUnitBlock N N' t‖ ^ (2 : ℕ)) ≤
      ∑ r : Fin ell,
        mtTypeIPrimeHeathBrownBlockMomentBound
          eta a A P ell N N' T V r := by
  let f : ℝ → ℝ := fun t =>
    ‖mtWattCoefficientBlock a A t‖ ^ (2 : ℕ) * ‖mtWattUnitBlock N N' t‖ ^ (2 : ℕ)
  have hunion : (∫ t in mtTypeIPrimeAmplifierLargeSet P ell T V, f t) ≤
      ∑ r : Fin ell,
        ∫ t in mtTypeIPrimeAmplifierBlockLargeSet P ell T V r, f t :=
    setIntegral_mtTypeIPrimeAmplifierLargeSet_le_sum_blocks hell T V
      (((continuous_perronPoly _ _ _).norm.pow 2).mul
        ((continuous_perronPoly _ _ _).norm.pow 2))
      (fun _ => by positivity)
  have hblock : ∀ r : Fin ell,
      (∫ t in mtTypeIPrimeAmplifierBlockLargeSet P ell T V r, f t) ≤
        mtTypeIPrimeHeathBrownBlockMomentBound
          eta a A P ell N N' T V r := by
    intro r
    let B := mtTypeIPrimeHeathBrownBlockLength P ell r
    let b := mtTypeIPrimeRaisedCoeff P ell
    let K : ℝ := (ell : ℝ) / V
    let T' : Set.Ioi (0 : ℝ) := ⟨T, lt_of_lt_of_le zero_lt_two hT⟩
    have hB : 1 ≤ B := by
      have hBpos : 0 < B := by
        dsimp only [B, mtTypeIPrimeHeathBrownBlockLength]
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
        ‖mtWattUnitBlock N N' t‖ ^ (4 : ℕ) * ‖mtWattCoefficientBlock b B t‖ ^ (2 : ℕ)) ≤
        ∫ t in (T / 2)..T,
          ‖mtWattUnitBlock N N' t‖ ^ (4 : ℕ) * ‖mtWattCoefficientBlock b B t‖ ^ (2 : ℕ) :=
      setIntegral_le_intervalIntegral_of_subset_Icc
        (((continuous_perronPoly _ _ _).norm.pow 4).mul
          ((continuous_perronPoly _ _ _).norm.pow 2))
        (by linarith)
        (mtTypeIPrimeAmplifierBlockLargeSet_subset_Icc P ell T V r)
        (fun t => mul_nonneg (pow_nonneg (norm_nonneg _) 4) (sq_nonneg _))
    have hfourthSet :
        (∫ t in mtTypeIPrimeAmplifierBlockLargeSet P ell T V r,
          ‖mtWattCoefficientBlock a A t‖ ^ (4 : ℕ)) ≤
        ∫ t in (T / 2)..T, ‖mtWattCoefficientBlock a A t‖ ^ (4 : ℕ) :=
      setIntegral_le_intervalIntegral_of_subset_Icc
        ((continuous_perronPoly _ _ _).norm.pow 4)
        (by linarith)
        (mtTypeIPrimeAmplifierBlockLargeSet_subset_Icc P ell T V r)
        (fun t => pow_nonneg (norm_nonneg _) 4)
    have hmixed := hmixedSet.trans
      (intervalIntegral_normPow_mtWattUnitBlock_mul_normSq_mtTypeIPrimeRaised_le_energy
        P ell hB hN (by omega : 1 ≤ N') hN'le T'
          (by simpa only [T', B] using hblockHeight r) heta)
    have hfourth := hfourthSet.trans
      (integral_mtTypeILongBlock_fourth_le_productAffine a A (one_le_two.trans hT))
    have hsqrtMixed := Real.sqrt_le_sqrt hmixed
    have hsqrtFourth := Real.sqrt_le_sqrt hfourth
    have hproduct := mul_le_mul hsqrtMixed hsqrtFourth
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    have hfinal := hcs.trans (by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hproduct hK)
    rw [show 2 * (A * (2 * A)) = (2 * A) * (2 * A) by ring] at hfinal
    rw [← mul_assoc] at hfinal
    simpa only [f, B, b, K, T', mtTypeIPrimeHeathBrownBlockMomentBound]
      using hfinal
  change (∫ t in mtTypeIPrimeAmplifierLargeSet P ell T V, f t) ≤ _
  exact hunion.trans (Finset.sum_le_sum fun r _ => hblock r)

/-- Source-facing receiver with all block-height clauses reduced to one complete-support bound. -/
theorem setIntegral_mtTypeI_primeAmplifier_heathBrown_of_fullSupport_le
    (a : ℕ → ℂ) (A P ell N N' : ℕ) (T V eta : ℝ)
    (hP : 1 ≤ P) (hell : 0 < ell) (hN : 2 ≤ N)
    (hNN' : N < N') (hN'le : N' ≤ 2 * N)
    (hT : 2 ≤ T) (hV : 0 < V) (heta : 0 < eta)
    (hfull : ((((2 * P) ^ ell : ℕ) : ℝ)) ≤ T) :
    (∫ t in mtTypeIPrimeAmplifierLargeSet P ell T V,
        ‖mtWattCoefficientBlock a A t‖ ^ (2 : ℕ) *
          ‖mtWattUnitBlock N N' t‖ ^ (2 : ℕ)) ≤
      ∑ r : Fin ell,
        mtTypeIPrimeHeathBrownBlockMomentBound
          eta a A P ell N N' T V r := by
  apply setIntegral_mtTypeI_primeAmplifier_heathBrown
    a A P ell N N' T V eta hP hell hN hNN' hN'le hT hV heta
  intro r
  have hblock :
      ((2 * mtTypeIPrimeHeathBrownBlockLength P ell r : ℕ) : ℝ) ≤
        (((2 * P) ^ ell : ℕ) : ℝ) := by
    exact_mod_cast two_mul_mtTypeIPrimeHeathBrownBlockLength_le r
  exact hblock.trans hfull

end

end RHTower.Sieve
