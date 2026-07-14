import GaloisForLFunctions.RHTower.XiCTaylorThetaTailArithmeticPhaseSeam
import GaloisForLFunctions.RHTower.XiCTaylorThetaTailDensityMonotonicity

/-!
# Recombination of the critical logarithmic translate packet

The nested Abel blocks in the theta-tail arithmetic phase seam are not independent.  This file
recombines the complete finite translate packet, at both value and spectral-derivative level, as
one Fourier--Laplace transform.  Its profile is a positive strictly decreasing finite sum of exact
translates of the first canonical density atom.  Thus all Hermitian cross currents internal to one
translate packet remain inside one value--derivative pair.
-/

open Complex Real MeasureTheory Set Filter Topology Polynomial

namespace RHTower

noncomputable section

/-- The source profile obtained after the critical coefficient cancels the phase of a logarithmic
translate. -/
def criticalLogPhaseTranslatedDensityProfile
    (L : ℝ) (N : ℕ) (t : ℝ) : ℝ :=
  ∑ j ∈ Finset.range N,
    Real.exp (-((j : ℝ) * L) / 2) *
      thetaCuspTailSecondDensityAtom 1 (t + (j : ℝ) * L)

/-- A nonempty translated density packet is strictly positive on the positive half-line. -/
theorem criticalLogPhaseTranslatedDensityProfile_pos
    {L : ℝ} (hL : 0 ≤ L) {N : ℕ} (hN : 0 < N)
    {t : ℝ} (ht : 0 ≤ t) :
    0 < criticalLogPhaseTranslatedDensityProfile L N t := by
  unfold criticalLogPhaseTranslatedDensityProfile
  apply Finset.sum_pos'
  · intro j _hj
    exact mul_nonneg (Real.exp_pos _).le
      (thetaCuspTailSecondDensityAtom_pos Nat.zero_lt_one
        (add_nonneg ht (mul_nonneg (Nat.cast_nonneg j) hL))).le
  · refine ⟨0, Finset.mem_range.mpr hN, ?_⟩
    simp only [Nat.cast_zero, zero_mul, neg_zero, zero_div, Real.exp_zero,
      add_zero, one_mul]
    exact thetaCuspTailSecondDensityAtom_pos Nat.zero_lt_one ht

/-- Every nonempty critical translated packet inherits strict decrease from the exact density. -/
theorem strictAntiOn_criticalLogPhaseTranslatedDensityProfile
    {L : ℝ} (hL : 0 ≤ L) {N : ℕ} (hN : 0 < N) :
    StrictAntiOn (criticalLogPhaseTranslatedDensityProfile L N) (Ici 0) := by
  intro x hx y hy hxy
  unfold criticalLogPhaseTranslatedDensityProfile
  apply Finset.sum_lt_sum
  · intro j _hj
    have hshift :
        thetaCuspTailSecondDensityAtom 1 (y + (j : ℝ) * L) <
          thetaCuspTailSecondDensityAtom 1 (x + (j : ℝ) * L) :=
      strictAntiOn_thetaCuspTailSecondDensityAtom Nat.zero_lt_one
        (by exact add_nonneg hx (mul_nonneg (Nat.cast_nonneg j) hL))
        (by exact add_nonneg hy (mul_nonneg (Nat.cast_nonneg j) hL))
        (by linarith)
    exact (mul_lt_mul_of_pos_left hshift (Real.exp_pos _)).le
  · refine ⟨0, Finset.mem_range.mpr hN, ?_⟩
    simp only [Nat.cast_zero, zero_mul, neg_zero, zero_div, Real.exp_zero,
      add_zero, one_mul]
    exact strictAntiOn_thetaCuspTailSecondDensityAtom Nat.zero_lt_one hx hy hxy

/-- Additivity of the untruncated spectral translation character. -/
lemma spectralTranslationPhase_add (u a : ℝ) (z : ℂ) :
    spectralTranslationPhase (u + a) z =
      spectralTranslationPhase u z * spectralTranslationPhase a z := by
  unfold spectralTranslationPhase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private theorem integrableOn_shiftedDensityAtomOne_mul_phase
    {L : ℝ} (hL : 0 ≤ L) (j : ℕ) {z : ℂ} (hz : 0 ≤ z.im) :
    IntegrableOn (fun t : ℝ =>
      ((Real.exp (-((j : ℝ) * L) / 2) *
        thetaCuspTailSecondDensityAtom 1 (t + (j : ℝ) * L) : ℝ) : ℂ) *
          spectralTranslationPhase t z) (Ioi 0) := by
  have hbase := integrableOn_thetaCuspTailSecondDensityAtom_one_mul_phase hz
  apply Integrable.mono hbase
  · have hdensity : Continuous (thetaCuspTailSecondDensityAtom 1) :=
      continuous_iff_continuousAt.mpr fun x =>
        (hasDerivAt_thetaCuspTailSecondDensityAtom 1 x).continuousAt
    have hreal : Continuous (fun t : ℝ =>
        Real.exp (-((j : ℝ) * L) / 2) *
          thetaCuspTailSecondDensityAtom 1 (t + (j : ℝ) * L)) :=
      continuous_const.mul (hdensity.comp (continuous_id.add continuous_const))
    have hphase : Continuous (fun t : ℝ => spectralTranslationPhase t z) := by
      unfold spectralTranslationPhase
      fun_prop
    exact ((Complex.continuous_ofReal.comp hreal).mul hphase).aestronglyMeasurable.restrict
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 ≤ t := ht.le
    have ha : 0 ≤ (j : ℝ) * L := mul_nonneg (Nat.cast_nonneg j) hL
    have hmono :
        thetaCuspTailSecondDensityAtom 1 (t + (j : ℝ) * L) ≤
          thetaCuspTailSecondDensityAtom 1 t := by
      exact (strictAntiOn_thetaCuspTailSecondDensityAtom Nat.zero_lt_one).antitoneOn
        (by simpa using ht0) (by exact add_nonneg ht0 ha) (le_add_of_nonneg_right ha)
    have hshiftNonneg : 0 ≤ thetaCuspTailSecondDensityAtom 1
        (t + (j : ℝ) * L) :=
      (thetaCuspTailSecondDensityAtom_pos Nat.zero_lt_one (add_nonneg ht0 ha)).le
    have hbaseNonneg : 0 ≤ thetaCuspTailSecondDensityAtom 1 t :=
      (thetaCuspTailSecondDensityAtom_pos Nat.zero_lt_one ht0).le
    have hweight : Real.exp (-((j : ℝ) * L) / 2) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      nlinarith
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_pos (Real.exp_pos _), abs_of_nonneg hshiftNonneg,
      abs_of_nonneg hbaseNonneg]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    calc
      Real.exp (-((j : ℝ) * L) / 2) *
          thetaCuspTailSecondDensityAtom 1 (t + (j : ℝ) * L) ≤
          1 * thetaCuspTailSecondDensityAtom 1 (t + (j : ℝ) * L) :=
        mul_le_mul_of_nonneg_right hweight hshiftNonneg
      _ ≤ thetaCuspTailSecondDensityAtom 1 t := by simpa using hmono

private lemma criticalLogPhase_translation_cancel
    (a t : ℝ) (z : ℂ) :
    spectralTranslationPhase (-a) z *
        spectralTranslationPhase (t + a) z =
      spectralTranslationPhase t z := by
  unfold spectralTranslationPhase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private theorem integrableOn_shiftedDensityAtomOne_mul_phaseDerivative
    {L : ℝ} (hL : 0 ≤ L) (j : ℕ) {z : ℂ} (hz : 0 ≤ z.im) :
    IntegrableOn (fun t : ℝ =>
      ((Real.exp (-((j : ℝ) * L) / 2) *
        thetaCuspTailSecondDensityAtom 1 (t + (j : ℝ) * L) : ℝ) : ℂ) *
          ((t : ℂ) * I * spectralTranslationPhase t z)) (Ioi 0) := by
  have hbase := integrableOn_thetaCuspTailSecondDensityAtom_one_mul_phaseDerivative hz
  apply Integrable.mono hbase
  · have hdensity : Continuous (thetaCuspTailSecondDensityAtom 1) :=
      continuous_iff_continuousAt.mpr fun x =>
        (hasDerivAt_thetaCuspTailSecondDensityAtom 1 x).continuousAt
    have hreal : Continuous (fun t : ℝ =>
        Real.exp (-((j : ℝ) * L) / 2) *
          thetaCuspTailSecondDensityAtom 1 (t + (j : ℝ) * L)) :=
      continuous_const.mul (hdensity.comp (continuous_id.add continuous_const))
    have hphase : Continuous (fun t : ℝ =>
        (t : ℂ) * I * spectralTranslationPhase t z) := by
      unfold spectralTranslationPhase
      fun_prop
    exact ((Complex.continuous_ofReal.comp hreal).mul hphase).aestronglyMeasurable.restrict
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 ≤ t := ht.le
    have ha : 0 ≤ (j : ℝ) * L := mul_nonneg (Nat.cast_nonneg j) hL
    have hmono :
        thetaCuspTailSecondDensityAtom 1 (t + (j : ℝ) * L) ≤
          thetaCuspTailSecondDensityAtom 1 t :=
      (strictAntiOn_thetaCuspTailSecondDensityAtom Nat.zero_lt_one).antitoneOn
        (by simpa using ht0) (by exact add_nonneg ht0 ha) (le_add_of_nonneg_right ha)
    have hshiftNonneg : 0 ≤ thetaCuspTailSecondDensityAtom 1
        (t + (j : ℝ) * L) :=
      (thetaCuspTailSecondDensityAtom_pos Nat.zero_lt_one (add_nonneg ht0 ha)).le
    have hbaseNonneg : 0 ≤ thetaCuspTailSecondDensityAtom 1 t :=
      (thetaCuspTailSecondDensityAtom_pos Nat.zero_lt_one ht0).le
    have hweight : Real.exp (-((j : ℝ) * L) / 2) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      nlinarith
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_pos (Real.exp_pos _), abs_of_nonneg hshiftNonneg,
      abs_of_nonneg hbaseNonneg]
    have hfactor :
        0 ≤ |t| * ‖I‖ * ‖spectralTranslationPhase t z‖ :=
      mul_nonneg (mul_nonneg (abs_nonneg _) (norm_nonneg _)) (norm_nonneg _)
    apply mul_le_mul_of_nonneg_right _ hfactor
    calc
      Real.exp (-((j : ℝ) * L) / 2) *
          thetaCuspTailSecondDensityAtom 1 (t + (j : ℝ) * L) ≤
          1 * thetaCuspTailSecondDensityAtom 1 (t + (j : ℝ) * L) :=
        mul_le_mul_of_nonneg_right hweight hshiftNonneg
      _ ≤ thetaCuspTailSecondDensityAtom 1 t := by simpa using hmono

private theorem criticalLogPhase_tail_pair_eq_shiftedProfileDerivative
    {L : ℝ} (hL : 0 ≤ L) (j : ℕ) {z : ℂ} (hz : 0 ≤ z.im) :
    criticalLogPhaseCoefficient L j z *
          thetaCuspTailSecondDensityAtomOnePhaseTailDerivative (j * L) z +
        criticalLogPhaseCoefficientDerivative L j z *
          thetaCuspTailSecondDensityAtomOnePhaseTail (j * L) z =
      ∫ t : ℝ in Ioi 0,
        ((Real.exp (-((j : ℝ) * L) / 2) *
          thetaCuspTailSecondDensityAtom 1 (t + (j : ℝ) * L) : ℝ) : ℂ) *
            ((t : ℂ) * I * spectralTranslationPhase t z) := by
  let a : ℝ := (j : ℝ) * L
  have ha : 0 ≤ a := mul_nonneg (Nat.cast_nonneg j) hL
  have hvalue : IntegrableOn (fun u : ℝ =>
      (thetaCuspTailSecondDensityAtom 1 u : ℂ) *
        spectralTranslationPhase u z) (Ioi a) :=
    (integrableOn_thetaCuspTailSecondDensityAtom_one_mul_phase hz).mono_set
      (Ioi_subset_Ioi ha)
  have hderivative : IntegrableOn (fun u : ℝ =>
      (thetaCuspTailSecondDensityAtom 1 u : ℂ) *
        ((u : ℂ) * I * spectralTranslationPhase u z)) (Ioi a) :=
    (integrableOn_thetaCuspTailSecondDensityAtom_one_mul_phaseDerivative hz).mono_set
      (Ioi_subset_Ioi ha)
  unfold criticalLogPhaseCoefficientDerivative criticalLogPhaseCoefficient
    thetaCuspTailSecondDensityAtomOnePhaseTailDerivative
    thetaCuspTailSecondDensityAtomOnePhaseTail
  change
    ((Real.exp (-a / 2) : ℂ) * spectralTranslationPhase (-a) z) *
          (∫ u : ℝ in Ioi a,
            (thetaCuspTailSecondDensityAtom 1 u : ℂ) *
              ((u : ℂ) * I * spectralTranslationPhase u z)) +
        (-(((j : ℝ) : ℂ) * (L : ℂ)) * I) *
            ((Real.exp (-a / 2) : ℂ) * spectralTranslationPhase (-a) z) *
          (∫ u : ℝ in Ioi a,
            (thetaCuspTailSecondDensityAtom 1 u : ℂ) *
              spectralTranslationPhase u z) = _
  have hcast : ((j : ℝ) : ℂ) * (L : ℂ) = (a : ℂ) := by
    dsimp only [a]
    push_cast
    rfl
  rw [hcast]
  rw [← MeasureTheory.integral_const_mul,
    ← MeasureTheory.integral_const_mul]
  rw [← MeasureTheory.integral_add]
  · have htranslate := integral_Ioi_comp_add_eq_integral_Ioi
      (fun u : ℝ =>
        ((Real.exp (-a / 2) : ℂ) * spectralTranslationPhase (-a) z) *
            ((thetaCuspTailSecondDensityAtom 1 u : ℂ) *
              ((u : ℂ) * I * spectralTranslationPhase u z)) +
          ((-((a : ℂ)) * I) *
            ((Real.exp (-a / 2) : ℂ) * spectralTranslationPhase (-a) z)) *
              ((thetaCuspTailSecondDensityAtom 1 u : ℂ) *
                spectralTranslationPhase u z)) a
    rw [← htranslate]
    apply MeasureTheory.integral_congr_ae
    filter_upwards [] with t
    calc
      _ = ((Real.exp (-a / 2) : ℂ) *
              (thetaCuspTailSecondDensityAtom 1 (t + a) : ℂ)) *
            ((t : ℂ) * I) *
              (spectralTranslationPhase (-a) z *
                spectralTranslationPhase (t + a) z) := by
          push_cast
          ring
      _ = ((Real.exp (-a / 2) : ℂ) *
              (thetaCuspTailSecondDensityAtom 1 (t + a) : ℂ)) *
            ((t : ℂ) * I) * spectralTranslationPhase t z := by
          rw [criticalLogPhase_translation_cancel]
      _ = _ := by
          dsimp only [a]
          push_cast
          ring
  · exact hderivative.const_mul _
  · exact hvalue.const_mul _

/-- The complete finite translate packet is one Fourier--Laplace transform of its recombined
positive source profile. -/
theorem criticalLogPhase_tail_packet_eq_translatedProfile
    {L : ℝ} (hL : 0 ≤ L) {z : ℂ} (hz : 0 ≤ z.im) (N : ℕ) :
    (∑ j ∈ Finset.range N,
      criticalLogPhaseCoefficient L j z *
        thetaCuspTailSecondDensityAtomOnePhaseTail (j * L) z) =
      ∫ t : ℝ in Ioi 0,
        (criticalLogPhaseTranslatedDensityProfile L N t : ℂ) *
          spectralTranslationPhase t z := by
  rw [show (fun t : ℝ =>
      (criticalLogPhaseTranslatedDensityProfile L N t : ℂ) *
        spectralTranslationPhase t z) =
      fun t : ℝ => ∑ j ∈ Finset.range N,
        ((Real.exp (-((j : ℝ) * L) / 2) *
          thetaCuspTailSecondDensityAtom 1 (t + (j : ℝ) * L) : ℝ) : ℂ) *
            spectralTranslationPhase t z by
    funext t
    unfold criticalLogPhaseTranslatedDensityProfile
    push_cast
    rw [Finset.sum_mul]]
  rw [MeasureTheory.integral_finsetSum _ fun j _hj =>
    integrableOn_shiftedDensityAtomOne_mul_phase hL j hz]
  apply Finset.sum_congr rfl
  intro j _hj
  unfold criticalLogPhaseCoefficient
    thetaCuspTailSecondDensityAtomOnePhaseTail
  have htranslate := integral_Ioi_comp_add_eq_integral_Ioi
    (fun u : ℝ => (thetaCuspTailSecondDensityAtom 1 u : ℂ) *
      spectralTranslationPhase u z) ((j : ℝ) * L)
  rw [← htranslate, ← MeasureTheory.integral_const_mul]
  apply MeasureTheory.integral_congr_ae
  filter_upwards [] with t
  rw [show
      ((Real.exp (-((j : ℝ) * L) / 2) : ℂ) *
          spectralTranslationPhase (-((j : ℝ) * L)) z) *
          ((thetaCuspTailSecondDensityAtom 1 (t + (j : ℝ) * L) : ℂ) *
            spectralTranslationPhase (t + (j : ℝ) * L) z) =
        ((Real.exp (-((j : ℝ) * L) / 2) : ℂ) *
          (thetaCuspTailSecondDensityAtom 1 (t + (j : ℝ) * L) : ℂ)) *
          (spectralTranslationPhase (-((j : ℝ) * L)) z *
            spectralTranslationPhase (t + (j : ℝ) * L) z) by ring]
  rw [criticalLogPhase_translation_cancel]
  push_cast
  ring

/-- Exact derivative companion: differentiating the critical coefficient cancels the translated
source coordinate, so the whole packet carries the original `t` moment of the recombined profile. -/
theorem criticalLogPhase_tail_packetDerivative_eq_translatedProfile
    {L : ℝ} (hL : 0 ≤ L) {z : ℂ} (hz : 0 ≤ z.im) (N : ℕ) :
    (∑ j ∈ Finset.range N,
      (criticalLogPhaseCoefficient L j z *
          thetaCuspTailSecondDensityAtomOnePhaseTailDerivative (j * L) z +
        criticalLogPhaseCoefficientDerivative L j z *
          thetaCuspTailSecondDensityAtomOnePhaseTail (j * L) z)) =
      ∫ t : ℝ in Ioi 0,
        (criticalLogPhaseTranslatedDensityProfile L N t : ℂ) *
          ((t : ℂ) * I * spectralTranslationPhase t z) := by
  rw [show (fun t : ℝ =>
      (criticalLogPhaseTranslatedDensityProfile L N t : ℂ) *
        ((t : ℂ) * I * spectralTranslationPhase t z)) =
      fun t : ℝ => ∑ j ∈ Finset.range N,
        ((Real.exp (-((j : ℝ) * L) / 2) *
          thetaCuspTailSecondDensityAtom 1 (t + (j : ℝ) * L) : ℝ) : ℂ) *
            ((t : ℂ) * I * spectralTranslationPhase t z) by
    funext t
    unfold criticalLogPhaseTranslatedDensityProfile
    push_cast
    rw [Finset.sum_mul]]
  rw [MeasureTheory.integral_finsetSum _ fun j _hj =>
    integrableOn_shiftedDensityAtomOne_mul_phaseDerivative hL j hz]
  apply Finset.sum_congr rfl
  intro j _hj
  exact criticalLogPhase_tail_pair_eq_shiftedProfileDerivative hL j hz

/-- Current-level recombination.  In particular, every off-diagonal Hermitian cross term created
by expanding the Abel blocks is already part of the current of one transformed decreasing
profile; no separate cross-term estimate is required inside a fixed translate packet. -/
theorem criticalLogPhase_tail_packetCurrent_eq_translatedProfile
    {L : ℝ} (hL : 0 ≤ L) {z : ℂ} (hz : 0 ≤ z.im) (N : ℕ) :
    (((∑ j ∈ Finset.range N,
        (criticalLogPhaseCoefficient L j z *
            thetaCuspTailSecondDensityAtomOnePhaseTailDerivative (j * L) z +
          criticalLogPhaseCoefficientDerivative L j z *
            thetaCuspTailSecondDensityAtomOnePhaseTail (j * L) z))) *
      (starRingEnd ℂ)
        (∑ j ∈ Finset.range N,
          criticalLogPhaseCoefficient L j z *
            thetaCuspTailSecondDensityAtomOnePhaseTail (j * L) z)).im =
      (((∫ t : ℝ in Ioi 0,
          (criticalLogPhaseTranslatedDensityProfile L N t : ℂ) *
            ((t : ℂ) * I * spectralTranslationPhase t z))) *
        (starRingEnd ℂ)
          (∫ t : ℝ in Ioi 0,
            (criticalLogPhaseTranslatedDensityProfile L N t : ℂ) *
              spectralTranslationPhase t z)).im := by
  rw [criticalLogPhase_tail_packetDerivative_eq_translatedProfile hL hz N,
    criticalLogPhase_tail_packet_eq_translatedProfile hL hz N]

end

end RHTower
