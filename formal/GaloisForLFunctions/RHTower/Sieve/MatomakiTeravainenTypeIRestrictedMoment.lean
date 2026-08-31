import GaloisForLFunctions.HTGeometry.WeightedHolder
import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenTypeIMoment

/-!
# Matomäki--Teräväinen Type-I moment on its actual large-value set

Section 5.1 inserts the powered prime amplifier only where it is large.  This file supplies the
missing restricted-measure receiver.  Cauchy--Schwarz is applied to `volume.restrict E`; both
resulting moments are then enlarged to the complete dyadic height interval.  The canonical
large-value set is defined from the amplifier itself, so its lower-bound premise is discharged.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction Complex MeasureTheory

noncomputable section

/-- Pointwise amplifier insertion and Cauchy--Schwarz on a measurable subset of one height block. -/
theorem setIntegral_normSq_mul_normSq_le_amplified
    {E : Set ℝ} {long unit amp : ℝ → ℂ} (hlong : Continuous long)
    (hunit : Continuous unit) (hamp : Continuous amp)
    {T K : ℝ} (hK : 0 ≤ K) (hEmeas : MeasurableSet E)
    (hE : E ⊆ Set.Icc (T / 2) T)
    (hlarge : ∀ t ∈ E, 1 ≤ K * ‖amp t‖) :
    (∫ t in E, ‖long t‖ ^ 2 * ‖unit t‖ ^ 2) ≤
      K * Real.sqrt (∫ t in E, ‖unit t‖ ^ 4 * ‖amp t‖ ^ 2) *
        Real.sqrt (∫ t in E, ‖long t‖ ^ 4) := by
  let μ : Measure ℝ := volume.restrict E
  let F : ℝ → ℂ := fun t => unit t * unit t * amp t
  let G : ℝ → ℂ := fun t => long t * long t
  have hF : Continuous F := (hunit.mul hunit).mul hamp
  have hG : Continuous G := hlong.mul hlong
  have hμ : μ ≤ volume.restrict (Set.Icc (T / 2) T) :=
    Measure.restrict_mono hE le_rfl
  have hFfull :=
    (hF.norm.pow 2).integrableOn_Icc (μ := volume) (a := T / 2) (b := T)
  change Integrable (fun t => ‖F t‖ ^ 2)
    (volume.restrict (Set.Icc (T / 2) T)) at hFfull
  have hGfull :=
    (hG.norm.pow 2).integrableOn_Icc (μ := volume) (a := T / 2) (b := T)
  change Integrable (fun t => ‖G t‖ ^ 2)
    (volume.restrict (Set.Icc (T / 2) T)) at hGfull
  have hFint : Integrable (fun t => ‖F t‖ ^ 2) μ := hFfull.mono_measure hμ
  have hGint : Integrable (fun t => ‖G t‖ ^ 2) μ := hGfull.mono_measure hμ
  have hcross :=
    GaloisForLFunctions.HTGeometry.integrable_mul_norm_of_integrable_sq
      (μ := μ) hF.aestronglyMeasurable hG.aestronglyMeasurable hFint hGint
  have hpoint : ∀ᵐ t ∂μ,
      ‖long t‖ ^ 2 * ‖unit t‖ ^ 2 ≤ K * (‖F t‖ * ‖G t‖) := by
    filter_upwards [ae_restrict_mem hEmeas] with t ht
    have hbase : 0 ≤ ‖long t‖ ^ 2 * ‖unit t‖ ^ 2 := by positivity
    have hmul := mul_le_mul_of_nonneg_left (hlarge t ht) hbase
    dsimp only [F, G]
    simp only [norm_mul]
    nlinarith
  have hleftFull :=
    ((hlong.norm.pow 2).mul (hunit.norm.pow 2)).integrableOn_Icc
      (μ := volume) (a := T / 2) (b := T)
  change Integrable (fun t => ‖long t‖ ^ 2 * ‖unit t‖ ^ 2)
    (volume.restrict (Set.Icc (T / 2) T)) at hleftFull
  have hleft : Integrable (fun t => ‖long t‖ ^ 2 * ‖unit t‖ ^ 2) μ :=
    hleftFull.mono_measure hμ
  have hmono : (∫ t, ‖long t‖ ^ 2 * ‖unit t‖ ^ 2 ∂μ) ≤
      ∫ t, K * (‖F t‖ * ‖G t‖) ∂μ :=
    integral_mono_ae hleft (hcross.const_mul K) hpoint
  rw [integral_const_mul] at hmono
  have hcs := GaloisForLFunctions.HTGeometry.integral_mul_le_sqrt_mul_sqrt_measure
    (μ := μ) hF.aestronglyMeasurable hG.aestronglyMeasurable hFint hGint
  have hscaled := mul_le_mul_of_nonneg_left hcs hK
  have hFeq : (∫ t, ‖F t‖ ^ 2 ∂μ) =
      ∫ t in E, ‖unit t‖ ^ 4 * ‖amp t‖ ^ 2 := by
    apply integral_congr_ae
    filter_upwards with t
    dsimp only [F, μ]
    simp only [norm_mul]
    ring
  have hGeq : (∫ t, ‖G t‖ ^ 2 ∂μ) =
      ∫ t in E, ‖long t‖ ^ 4 := by
    apply integral_congr_ae
    filter_upwards with t
    dsimp only [G, μ]
    simp only [norm_mul]
    ring
  change (∫ t, ‖long t‖ ^ 2 * ‖unit t‖ ^ 2 ∂μ) ≤ _
  calc
    (∫ t, ‖long t‖ ^ 2 * ‖unit t‖ ^ 2 ∂μ) ≤
        K * ∫ t, ‖F t‖ * ‖G t‖ ∂μ := hmono
    _ ≤ K * (Real.sqrt (∫ t, ‖F t‖ ^ 2 ∂μ) *
        Real.sqrt (∫ t, ‖G t‖ ^ 2 ∂μ)) := hscaled
    _ = K * Real.sqrt (∫ t in E, ‖unit t‖ ^ 4 * ‖amp t‖ ^ 2) *
        Real.sqrt (∫ t in E, ‖long t‖ ^ 4) := by
      rw [hFeq, hGeq]
      ring

/-- A nonnegative continuous integral over a subset of `[a,b]` is bounded by the interval
integral over `[a,b]`. -/
theorem setIntegral_le_intervalIntegral_of_subset_Icc
    {E : Set ℝ} {f : ℝ → ℝ} (hf : Continuous f) {a b : ℝ} (hab : a ≤ b)
    (hE : E ⊆ Set.Icc a b) (hnn : ∀ t, 0 ≤ f t) :
    (∫ t in E, f t) ≤ ∫ t in a..b, f t := by
  have hfull := hf.integrableOn_Icc (μ := volume) (a := a) (b := b)
  change Integrable f (volume.restrict (Set.Icc a b)) at hfull
  have hmono := integral_mono_measure
    (Measure.restrict_mono hE le_rfl)
    (Filter.Eventually.of_forall hnn) hfull
  rw [intervalIntegral.integral_of_le hab,
    ← MeasureTheory.integral_Icc_eq_integral_Ioc]
  exact hmono

/-- Type-I amplified moment on any measurable large-value subset.  Both analytic moment bounds
are produced internally and are charged only on the full dyadic height block. -/
theorem exists_setIntegral_mtTypeI_amplified_coveredRange
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (E : Set ℝ) (a b : ℕ → ℂ) (A B N N' : ℕ) (K : ℝ),
      1 ≤ A → 1 ≤ B → 1 ≤ N → N < N' → N' ≤ 2 * N →
      ∀ T : ℝ, 2 ≤ T →
      (T ≤ (N : ℝ) ∨
        ((B : ℝ) ≤ T ∧
          ((((2 * B) * (N' * N') : ℕ) : ℝ) ≤
            (B : ℝ) ^ (5 / 4 : ℝ) * T ^ (3 / 4 : ℝ)))) →
      0 ≤ K → MeasurableSet E → E ⊆ Set.Icc (T / 2) T →
      (∀ t ∈ E, 1 ≤ K * ‖mtWattCoefficientBlock b B t‖) →
      (∫ t in E,
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
  intro E a b A B N N' K hA hB hN hNN' hN' T hT hcovered hK hEmeas hE hlarge
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
  have hmixed := hmixedSet.trans (hDI b B N N' hB hN hNN' hN' T hT hcovered)
  have hfourth := hfourthSet.trans
    (integral_mtTypeILongBlock_fourth_le_productAffine a A (one_le_two.trans hT))
  have hsqrtMixed := Real.sqrt_le_sqrt hmixed
  have hsqrtFourth := Real.sqrt_le_sqrt hfourth
  have hproduct := mul_le_mul hsqrtMixed hsqrtFourth
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  exact hcs.trans (by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hproduct hK)

/-- Canonical Type-I large-value set, cut out by its actual amplifier. -/
noncomputable def mtTypeIAmplifierLargeSet
    (b : ℕ → ℂ) (B : ℕ) (T K : ℝ) : Set ℝ :=
  Set.Icc (T / 2) T ∩ {t | 1 ≤ K * ‖mtWattCoefficientBlock b B t‖}

theorem measurableSet_mtTypeIAmplifierLargeSet
    (b : ℕ → ℂ) (B : ℕ) (T K : ℝ) :
    MeasurableSet (mtTypeIAmplifierLargeSet b B T K) := by
  exact (isClosed_Icc.inter
    (isClosed_le continuous_const
      (continuous_const.mul (continuous_perronPoly _ _ _).norm))).measurableSet

theorem mtTypeIAmplifierLargeSet_subset_Icc
    (b : ℕ → ℂ) (B : ℕ) (T K : ℝ) :
    mtTypeIAmplifierLargeSet b B T K ⊆ Set.Icc (T / 2) T :=
  Set.inter_subset_left

theorem one_le_mul_norm_mtWattCoefficientBlock_of_mem_amplifierLargeSet
    {b : ℕ → ℂ} {B : ℕ} {T K t : ℝ} (ht : t ∈ mtTypeIAmplifierLargeSet b B T K) :
    1 ≤ K * ‖mtWattCoefficientBlock b B t‖ :=
  ht.2

/-- The restricted Type-I estimate on its canonical large-value set.  No amplifier lower-bound
hypothesis remains: membership in the set supplies it definitionally. -/
theorem exists_setIntegral_mtTypeI_amplifierLargeSet_coveredRange
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
      (∫ t in mtTypeIAmplifierLargeSet b B T K,
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
  obtain ⟨C, hC, hrestricted⟩ := exists_setIntegral_mtTypeI_amplified_coveredRange hε
  refine ⟨C, hC, ?_⟩
  intro a b A B N N' K hA hB hN hNN' hN' T hT hcovered hK
  exact hrestricted (mtTypeIAmplifierLargeSet b B T K) a b A B N N' K
    hA hB hN hNN' hN' T hT hcovered hK
    (measurableSet_mtTypeIAmplifierLargeSet b B T K)
    (mtTypeIAmplifierLargeSet_subset_Icc b B T K)
    (fun _ ht => one_le_mul_norm_mtWattCoefficientBlock_of_mem_amplifierLargeSet ht)

end

end RHTower.Sieve
