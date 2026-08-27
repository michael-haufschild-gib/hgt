import GaloisForLFunctions.RHTower.ThetaCuspLikelihoodEighthAtomPairTrace

/-!
# Exact eighth-score pair-sector trace

This module identifies the raw Bell grade-two trace with the complete ordered
atom-pair Fock sector.  Product tilting, atom expansion, and the four-sector
partition are all exact; no truncation or positivity estimate enters the
connector.
-/

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace RHTower

noncomputable section

/-- Product exponential tilting is multiplication by the two independent Gibbs densities. -/
theorem integral_thetaCuspHigherLikelihoodTiltedMeasure_prod_eq_spectral_prod
    (A B : ℝ) :
    (∫ z : ℝ × ℝ,
      thetaCuspLikelihoodEighthSourceScore (A * (z.1 + z.2))
        ∂(thetaCuspHigherLikelihoodTiltedMeasure B).prod
          (thetaCuspHigherLikelihoodTiltedMeasure B)) =
      ∫ z : ℝ × ℝ,
        thetaCuspLikelihoodEighthSourceScore (A * (z.1 + z.2)) *
          Real.exp (-(B * z.1)) * Real.exp (-(B * z.2))
        ∂thetaCuspHigherLikelihoodSpectralMeasure.prod
          thetaCuspHigherLikelihoodSpectralMeasure := by
  letI : SFinite thetaCuspHigherLikelihoodSpectralMeasure := by
    dsimp [thetaCuspHigherLikelihoodSpectralMeasure,
      thetaCuspAtomLikelihoodSpectralMeasure]
    infer_instance
  have hdMeas : Measurable (fun t : ℝ =>
      ((thetaCuspHigherLikelihoodTiltDensity B t : NNReal) : ENNReal)) :=
    (measurable_thetaCuspHigherLikelihoodTiltDensity B).coe_nnreal_ennreal
  unfold thetaCuspHigherLikelihoodTiltedMeasure
  rw [MeasureTheory.prod_withDensity hdMeas hdMeas]
  change (∫ z : ℝ × ℝ,
      thetaCuspLikelihoodEighthSourceScore (A * (z.1 + z.2))
        ∂(thetaCuspHigherLikelihoodSpectralMeasure.prod
          thetaCuspHigherLikelihoodSpectralMeasure).withDensity
            (fun z => ((thetaCuspHigherLikelihoodTiltDensity B z.1 *
              thetaCuspHigherLikelihoodTiltDensity B z.2 : NNReal) : ENNReal))) = _
  have hpairMeas : Measurable (fun z : ℝ × ℝ =>
      thetaCuspHigherLikelihoodTiltDensity B z.1 *
        thetaCuspHigherLikelihoodTiltDensity B z.2) :=
    ((measurable_thetaCuspHigherLikelihoodTiltDensity B).comp measurable_fst).mul
      ((measurable_thetaCuspHigherLikelihoodTiltDensity B).comp measurable_snd)
  rw [integral_withDensity_eq_integral_smul hpairMeas]
  apply integral_congr_ae
  filter_upwards with z
  rw [NNReal.smul_def]
  change (thetaCuspHigherLikelihoodTiltDensity B z.1 : ℝ) *
      (thetaCuspHigherLikelihoodTiltDensity B z.2 : ℝ) *
        thetaCuspLikelihoodEighthSourceScore (A * (z.1 + z.2)) = _
  have hd (t : ℝ) : (thetaCuspHigherLikelihoodTiltDensity B t : ℝ) =
      Real.exp (-(B * t)) := by
    unfold thetaCuspHigherLikelihoodTiltDensity
    rw [Real.coe_toNNReal _ (Real.exp_pos _).le]
    congr 1
    ring
  rw [hd z.1, hd z.2]
  ring

private theorem integrable_add_pow_mul_exp_neg_thetaCuspHigherLikelihoodSpectralMeasure_prod
    (q : ℕ) {B : ℝ} (hB : 0 < B) :
    Integrable (fun z : ℝ × ℝ =>
      (z.1 + z.2) ^ q * Real.exp (-(B * z.1)) * Real.exp (-(B * z.2)))
      (thetaCuspHigherLikelihoodSpectralMeasure.prod
        thetaCuspHigherLikelihoodSpectralMeasure) := by
  rw [show (fun z : ℝ × ℝ =>
      (z.1 + z.2) ^ q * Real.exp (-(B * z.1)) * Real.exp (-(B * z.2))) =
      fun z => ∑ i ∈ Finset.range (q + 1),
        (q.choose i : ℝ) *
          (z.1 ^ i * Real.exp (-(B * z.1))) *
          (z.2 ^ (q - i) * Real.exp (-(B * z.2))) by
    funext z
    rw [add_pow, Finset.sum_mul, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    ring]
  apply MeasureTheory.integrable_finsetSum
  intro i hi
  have hp :=
    (integrable_pow_mul_exp_neg_thetaCuspHigherLikelihoodSpectralMeasure i hB).mul_prod
      (integrable_pow_mul_exp_neg_thetaCuspHigherLikelihoodSpectralMeasure (q - i) hB)
  exact (hp.const_mul (q.choose i : ℝ)).congr (ae_of_all _ fun z => by ring)

/-- The globally weighted product score is integrable before countable atom expansion. -/
theorem integrable_thetaCuspLikelihoodEighthSourceScore_mul_exp_neg_spectral_prod
    (A : ℝ) {B : ℝ} (hB : 0 < B) :
    Integrable (fun z : ℝ × ℝ =>
      thetaCuspLikelihoodEighthSourceScore (A * (z.1 + z.2)) *
        Real.exp (-(B * z.1)) * Real.exp (-(B * z.2)))
      (thetaCuspHigherLikelihoodSpectralMeasure.prod
        thetaCuspHigherLikelihoodSpectralMeasure) := by
  have hpow (q : ℕ) :=
    integrable_add_pow_mul_exp_neg_thetaCuspHigherLikelihoodSpectralMeasure_prod q hB
  have h8 := (hpow 8).const_mul (A ^ 8)
  have h7 := (hpow 7).const_mul (28 * A ^ 7)
  have h6 := (hpow 6).const_mul (266 * A ^ 6)
  have h5 := (hpow 5).const_mul (1050 * A ^ 5)
  have h4 := (hpow 4).const_mul (1701 * A ^ 4)
  have h3 := (hpow 3).const_mul (966 * A ^ 3)
  have h2 := (hpow 2).const_mul (127 * A ^ 2)
  have h1 := (hpow 1).const_mul A
  convert (((((((h8.sub h7).add h6).sub h5).add h4).sub h3).add h2).sub h1) using 1
  funext z
  simp only [Pi.add_apply, Pi.sub_apply]
  unfold thetaCuspLikelihoodEighthSourceScore
  ring

/-- The product spectral trace is the absolutely convergent ordered atom-pair score sum. -/
theorem integral_thetaCuspLikelihoodEighthSourceScore_spectral_prod_eq_tsum_atomPair
    (A : ℝ) {B : ℝ} (hB : 0 < B) :
    (∫ z : ℝ × ℝ,
      thetaCuspLikelihoodEighthSourceScore (A * (z.1 + z.2)) *
        Real.exp (-(B * z.1)) * Real.exp (-(B * z.2))
        ∂thetaCuspHigherLikelihoodSpectralMeasure.prod
          thetaCuspHigherLikelihoodSpectralMeasure) =
      ∑' p : ℕ × ℕ,
        thetaCuspLikelihoodAtomPairEighthScoreMass (p.1 + 2) (p.2 + 2) A B := by
  letI : ∀ k : ℕ, SFinite (thetaCuspAtomLikelihoodSpectralMeasure (k + 2)) :=
    fun k => by
      dsimp [thetaCuspAtomLikelihoodSpectralMeasure]
      infer_instance
  let f : ℝ × ℝ → ℝ := fun z =>
    thetaCuspLikelihoodEighthSourceScore (A * (z.1 + z.2)) *
      Real.exp (-(B * z.1)) * Real.exp (-(B * z.2))
  have hf := integrable_thetaCuspLikelihoodEighthSourceScore_mul_exp_neg_spectral_prod A hB
  rw [thetaCuspHigherLikelihoodSpectralMeasure, Measure.prod_sum] at hf ⊢
  rw [integral_sum_measure hf]
  apply tsum_congr
  intro p
  symm
  simpa only [f] using
    thetaCuspLikelihoodAtomPairEighthScoreMass_eq_integral
      (n := p.1 + 2) (m := p.2 + 2) (by omega) (by omega) A hB

/-- Full raw algebraic pair trace is the complete ordered atom-pair sector. -/
theorem thetaCuspLikelihoodEighthAlgebraicPairTrace_eq_tsum_atomPair
    {x : ℝ} (hx : 0 ≤ x) :
    thetaCuspLikelihoodEighthAlgebraicPairTrace x =
      ∑' p : ℕ × ℕ,
        thetaCuspLikelihoodAtomPairEighthScoreMass (p.1 + 2) (p.2 + 2)
          (thetaCuspSingleAtomReflectionScale 1 x) (thetaCuspLikelihoodCoordinate x) := by
  let A := thetaCuspSingleAtomReflectionScale 1 x
  let B := thetaCuspLikelihoodCoordinate x
  have hB : 0 < B := by simpa only [B] using thetaCuspLikelihoodCoordinate_pos hx
  calc
    thetaCuspLikelihoodEighthAlgebraicPairTrace x =
        ∫ z : ℝ × ℝ, thetaCuspLikelihoodEighthSourceScore (A * (z.1 + z.2))
          ∂(thetaCuspHigherLikelihoodTiltedMeasure B).prod
            (thetaCuspHigherLikelihoodTiltedMeasure B) := by
      simpa only [A, B] using thetaCuspLikelihoodEighthAlgebraicPairTrace_eq_integral hx
    _ = ∫ z : ℝ × ℝ,
        thetaCuspLikelihoodEighthSourceScore (A * (z.1 + z.2)) *
          Real.exp (-(B * z.1)) * Real.exp (-(B * z.2))
          ∂thetaCuspHigherLikelihoodSpectralMeasure.prod
            thetaCuspHigherLikelihoodSpectralMeasure :=
      integral_thetaCuspHigherLikelihoodTiltedMeasure_prod_eq_spectral_prod A B
    _ = ∑' p : ℕ × ℕ,
        thetaCuspLikelihoodAtomPairEighthScoreMass (p.1 + 2) (p.2 + 2) A B :=
      integral_thetaCuspLikelihoodEighthSourceScore_spectral_prod_eq_tsum_atomPair A hB

/-- The complete ordered atom-pair score family is absolutely summable on the physical seam. -/
theorem summable_thetaCuspLikelihoodAllAtomPairEighthScoreMass
    {A B : ℝ} (hA : Real.pi ≤ A) (hBA : B = A - 3 / 2) :
    Summable (fun p : ℕ × ℕ =>
      thetaCuspLikelihoodAtomPairEighthScoreMass (p.1 + 2) (p.2 + 2) A B) := by
  have hB : 0 < B := by rw [hBA]; nlinarith [Real.pi_gt_three]
  let f : ℝ × ℝ → ℝ := fun z =>
    thetaCuspLikelihoodEighthSourceScore (A * (z.1 + z.2)) *
      Real.exp (-(B * z.1)) * Real.exp (-(B * z.2))
  letI : ∀ k : ℕ, SFinite (thetaCuspAtomLikelihoodSpectralMeasure (k + 2)) :=
    fun k => by
      dsimp [thetaCuspAtomLikelihoodSpectralMeasure]
      infer_instance
  have hf := integrable_thetaCuspLikelihoodEighthSourceScore_mul_exp_neg_spectral_prod A hB
  rw [thetaCuspHigherLikelihoodSpectralMeasure, Measure.prod_sum] at hf
  have hs := (hasSum_integral_measure hf).summable
  apply hs.congr
  intro p
  simpa only [f] using
    (thetaCuspLikelihoodAtomPairEighthScoreMass_eq_integral
      (n := p.1 + 2) (m := p.2 + 2) (by omega) (by omega) A hB).symm

/-- The double ordered atom sum is exactly the pair-sector ledger used by the Fock bound. -/
theorem tsum_thetaCuspLikelihoodAtomPairEighthScoreMass_eq_pairSectorMass
    {A B : ℝ} (hA : Real.pi ≤ A) (hBA : B = A - 3 / 2) :
    (∑' p : ℕ × ℕ,
      thetaCuspLikelihoodAtomPairEighthScoreMass (p.1 + 2) (p.2 + 2) A B) =
      thetaCuspLikelihoodEighthPairSectorMass A B := by
  let F : ℕ × ℕ → ℝ := fun p =>
    thetaCuspLikelihoodAtomPairEighthScoreMass (p.1 + 2) (p.2 + 2) A B
  let R : ℕ → ℝ := fun k => ∑' l : ℕ, F (k, l)
  have hs : Summable F := by
    simpa only [F] using summable_thetaCuspLikelihoodAllAtomPairEighthScoreMass hA hBA
  have hnonneg : 0 ≤ F := by
    intro p
    by_cases hk : p.1 = 0
    · by_cases hl : p.2 = 0
      · have hAseam : (157 / 50 : ℝ) ≤ A := by nlinarith [Real.pi_gt_d2]
        have hcore := thetaCuspLikelihoodEighthDominantPairCore_pos hAseam
        have hmass : 0 < thetaCuspLikelihoodEighthDominantPairMass A := by
          unfold thetaCuspLikelihoodEighthDominantPairMass
          exact mul_pos (Real.exp_pos _) hcore
        dsimp only [F]
        rw [hk, hl]
        norm_num
        rw [thetaCuspLikelihoodAtomPairEighthScoreMass_two_two_eq hAseam hBA]
        exact hmass.le
      · dsimp only [F]
        exact thetaCuspLikelihoodAtomPairEighthScoreMass_nonneg
          (by omega) (by omega) (Or.inr (by omega)) hA hBA
    · dsimp only [F]
      exact thetaCuspLikelihoodAtomPairEighthScoreMass_nonneg
        (by omega) (by omega) (Or.inl (by omega)) hA hBA
  have hprod := (summable_prod_of_nonneg hnonneg).mp hs
  have hrows : ∀ k : ℕ, Summable (fun l : ℕ => F (k, l)) := hprod.1
  have houter : Summable R := by simpa only [R] using hprod.2
  have hrowSplit (k : ℕ) :
      R k = F (k, 0) + ∑' l : ℕ, F (k, l + 1) := by
    have h := (hrows k).sum_add_tsum_nat_add 1
    norm_num [Finset.sum_range_succ] at h
    simpa only [R] using h.symm
  have houterSplit :
      (∑' k : ℕ, R k) = R 0 + ∑' k : ℕ, R (k + 1) := by
    have h := houter.sum_add_tsum_nat_add 1
    norm_num [Finset.sum_range_succ] at h
    exact h.symm
  have hsG : Summable (fun k : ℕ => F (k + 1, 0)) := by
    have hmixed := summable_thetaCuspLikelihoodDominantStablePairEighthScoreMass hA hBA
    apply hmixed.congr
    intro k
    dsimp only [F]
    rw [thetaCuspLikelihoodAtomPairEighthScoreMass_comm]
  have hsRtail : Summable (fun k : ℕ => R (k + 1)) := by
    exact houter.comp_injective (fun a b h => by omega)
  have hsH : Summable (fun k : ℕ => ∑' l : ℕ, F (k + 1, l + 1)) := by
    have hsub := hsRtail.sub hsG
    apply hsub.congr
    intro k
    rw [hrowSplit (k + 1)]
    ring
  have htailSplit :
      (∑' k : ℕ, R (k + 1)) =
        (∑' k : ℕ, F (k + 1, 0)) +
          ∑' k : ℕ, ∑' l : ℕ, F (k + 1, l + 1) := by
    calc
      (∑' k : ℕ, R (k + 1)) =
          ∑' k : ℕ, (F (k + 1, 0) + ∑' l : ℕ, F (k + 1, l + 1)) := by
        apply tsum_congr
        intro k
        exact hrowSplit (k + 1)
      _ = (∑' k : ℕ, F (k + 1, 0)) +
          ∑' k : ℕ, ∑' l : ℕ, F (k + 1, l + 1) :=
        Summable.tsum_add hsG hsH
  have hrowZero :
      R 0 = thetaCuspLikelihoodAtomPairEighthScoreMass 2 2 A B +
        thetaCuspLikelihoodDominantStablePairEighthTail A B := by
    rw [hrowSplit 0]
    unfold thetaCuspLikelihoodDominantStablePairEighthTail
    dsimp only [F]
  have hG :
      (∑' k : ℕ, F (k + 1, 0)) =
        thetaCuspLikelihoodDominantStablePairEighthTail A B := by
    unfold thetaCuspLikelihoodDominantStablePairEighthTail
    apply tsum_congr
    intro k
    dsimp only [F]
    rw [thetaCuspLikelihoodAtomPairEighthScoreMass_comm]
  have hH :
      (∑' k : ℕ, ∑' l : ℕ, F (k + 1, l + 1)) =
        thetaCuspLikelihoodStableStablePairEighthTail A B := by
    have hstable :=
      summable_thetaCuspLikelihoodStableStablePairEighthScoreMass hA hBA
    unfold thetaCuspLikelihoodStableStablePairEighthTail
    rw [hstable.tsum_prod]
  calc
    (∑' p : ℕ × ℕ,
        thetaCuspLikelihoodAtomPairEighthScoreMass (p.1 + 2) (p.2 + 2) A B) =
        ∑' p : ℕ × ℕ, F p := by rfl
    _ = ∑' k : ℕ, R k := by simpa only [R] using hs.tsum_prod
    _ = R 0 + ∑' k : ℕ, R (k + 1) := houterSplit
    _ = (thetaCuspLikelihoodAtomPairEighthScoreMass 2 2 A B +
          thetaCuspLikelihoodDominantStablePairEighthTail A B) +
        (thetaCuspLikelihoodDominantStablePairEighthTail A B +
          thetaCuspLikelihoodStableStablePairEighthTail A B) := by
      rw [hrowZero, htailSplit, hG, hH]
    _ = thetaCuspLikelihoodEighthPairSectorMass A B := by
      unfold thetaCuspLikelihoodEighthPairSectorMass
        thetaCuspLikelihoodNonDominantPairEighthTail
      ring

/-- Exact connector: Bell algebraic pair trace equals the already absorbed pair sector. -/
theorem thetaCuspLikelihoodEighthAlgebraicPairTrace_eq_pairSectorMass
    {x : ℝ} (hx : 0 ≤ x) :
    thetaCuspLikelihoodEighthAlgebraicPairTrace x =
      thetaCuspLikelihoodEighthPairSectorMass
        (thetaCuspSingleAtomReflectionScale 1 x) (thetaCuspLikelihoodCoordinate x) := by
  let A := thetaCuspSingleAtomReflectionScale 1 x
  let B := thetaCuspLikelihoodCoordinate x
  have hA : Real.pi ≤ A := by
    have he : 1 ≤ Real.exp (2 * x) := Real.one_le_exp (by linarith)
    dsimp only [A, thetaCuspSingleAtomReflectionScale]
    norm_num
    exact le_mul_of_one_le_right Real.pi_pos.le he
  have hBA : B = A - 3 / 2 := by
    dsimp only [A, B, thetaCuspLikelihoodCoordinate, thetaCuspSingleAtomReflectionScale]
    rw [show Real.exp x ^ 2 = Real.exp (2 * x) by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring]
    ring
  rw [thetaCuspLikelihoodEighthAlgebraicPairTrace_eq_tsum_atomPair hx]
  simpa only [A, B] using
    tsum_thetaCuspLikelihoodAtomPairEighthScoreMass_eq_pairSectorMass hA hBA

end

end RHTower
