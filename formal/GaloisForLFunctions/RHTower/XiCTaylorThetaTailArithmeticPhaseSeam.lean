import GaloisForLFunctions.RHTower.XiCTaylorThetaTailProductFiberCurrent
import GaloisForLFunctions.HTGeometry.UnitCircleRootRadialOrientation

open Complex Real MeasureTheory Set Filter Topology Polynomial
namespace RHTower
noncomputable section

/-- Positive-half-line phase transform of the first density atom. -/
def thetaCuspTailSecondDensityAtomOnePhaseTail (a : ℝ) (z : ℂ) : ℂ :=
  ∫ u : ℝ in Ioi a,
    (thetaCuspTailSecondDensityAtom 1 u : ℂ) * spectralTranslationPhase u z

/-- Spectral derivative of the positive-half-line phase transform of the first atom. -/
def thetaCuspTailSecondDensityAtomOnePhaseTailDerivative (a : ℝ) (z : ℂ) : ℂ :=
  ∫ u : ℝ in Ioi a,
    (thetaCuspTailSecondDensityAtom 1 u : ℂ) *
      ((u : ℂ) * I * spectralTranslationPhase u z)

/-- Phase transform of one arithmetic density atom on the original positive half-line. -/
def thetaCuspTailSecondDensityAtomPhase (n : ℕ) (z : ℂ) : ℂ :=
  ∫ x : ℝ in Ioi 0,
    (thetaCuspTailSecondDensityAtom n x : ℂ) * spectralTranslationPhase x z

/-- Spectral derivative companion of one arithmetic density-atom phase transform. -/
def thetaCuspTailSecondDensityAtomPhaseDerivative (n : ℕ) (z : ℂ) : ℂ :=
  ∫ x : ℝ in Ioi 0,
    (thetaCuspTailSecondDensityAtom n x : ℂ) *
      ((x : ℂ) * I * spectralTranslationPhase x z)

lemma spectralTranslationPhase_sub (u a : ℝ) (z : ℂ) :
    spectralTranslationPhase (u-a) z =
      spectralTranslationPhase (-a) z * spectralTranslationPhase u z := by
  unfold spectralTranslationPhase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma norm_spectralTranslationPhase_le_one
    {u : ℝ} (hu : 0 ≤ u) {z : ℂ} (hz : 0 ≤ z.im) :
    ‖spectralTranslationPhase u z‖ ≤ 1 := by
  unfold spectralTranslationPhase
  rw [Complex.norm_exp]
  have hre : (((u : ℂ) * I) * z).re = -u * z.im := by
    simp [Complex.mul_re]
  rw [hre, ← Real.exp_zero]
  exact Real.exp_le_exp.mpr (by nlinarith)

theorem integrableOn_thetaCuspTailSecondDensityAtom_one_mul_phase
    {z : ℂ} (hz : 0 ≤ z.im) :
    IntegrableOn (fun u : ℝ =>
      (thetaCuspTailSecondDensityAtom 1 u : ℂ) *
        spectralTranslationPhase u z) (Ioi 0) := by
  have hbase : IntegrableOn (fun u : ℝ =>
      (thetaCuspTailSecondDensityAtom 1 u : ℂ) * (u : ℂ) ^ 0) (Ioi 0) :=
    integrableOn_thetaCuspTailSecondDensityAtom_mul_complexPower 0 0
  change Integrable (fun u : ℝ =>
    (thetaCuspTailSecondDensityAtom 1 u : ℂ) * (u : ℂ) ^ 0)
      (volume.restrict (Ioi 0)) at hbase
  change Integrable (fun u : ℝ =>
    (thetaCuspTailSecondDensityAtom 1 u : ℂ) *
      spectralTranslationPhase u z) (volume.restrict (Ioi 0))
  apply hbase.mono
  · have hphase : Continuous (fun u : ℝ => spectralTranslationPhase u z) := by
      unfold spectralTranslationPhase
      fun_prop
    convert hbase.aestronglyMeasurable.mul hphase.aestronglyMeasurable.restrict using 1
    funext u
    simp
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hp := norm_spectralTranslationPhase_le_one hu.le hz
    simpa only [pow_zero, mul_one, norm_mul, norm_one, mul_one] using
      mul_le_mul_of_nonneg_left hp (norm_nonneg
        (thetaCuspTailSecondDensityAtom 1 u : ℂ))

theorem integrableOn_thetaCuspTailSecondDensityAtom_one_mul_phaseDerivative
    {z : ℂ} (hz : 0 ≤ z.im) :
    IntegrableOn (fun u : ℝ =>
      (thetaCuspTailSecondDensityAtom 1 u : ℂ) *
        ((u : ℂ) * I * spectralTranslationPhase u z)) (Ioi 0) := by
  have hbase :=
    integrableOn_thetaCuspTailSecondDensityAtom_mul_complexPower 0 1
  change Integrable (fun u : ℝ =>
    (thetaCuspTailSecondDensityAtom 1 u : ℂ) * (u : ℂ) ^ 1)
      (volume.restrict (Ioi 0)) at hbase
  change Integrable (fun u : ℝ =>
    (thetaCuspTailSecondDensityAtom 1 u : ℂ) *
      ((u : ℂ) * I * spectralTranslationPhase u z))
        (volume.restrict (Ioi 0))
  apply hbase.mono
  · have hphase : Continuous (fun u : ℝ => I * spectralTranslationPhase u z) := by
      unfold spectralTranslationPhase
      fun_prop
    convert hbase.aestronglyMeasurable.mul hphase.aestronglyMeasurable.restrict using 1
    funext u
    simp only [pow_one, Pi.mul_apply]
    ring
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hp := norm_spectralTranslationPhase_le_one hu.le hz
    simp only [norm_mul, norm_I, mul_one]
    have hupow : ‖(u : ℂ)‖ * ‖spectralTranslationPhase u z‖ ≤
        ‖(u : ℂ) ^ 1‖ := by
      simpa only [pow_one] using
        mul_le_of_le_one_right (norm_nonneg (u : ℂ)) hp
    exact mul_le_mul_of_nonneg_left
      hupow
      (norm_nonneg (thetaCuspTailSecondDensityAtom 1 u : ℂ))

theorem thetaCuspTailSecondDensityAtomPhase_eq_centeredTail
    {n : ℕ} (hn : 0 < n) (z : ℂ) :
    thetaCuspTailSecondDensityAtomPhase n z =
      ((((n : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) *
        spectralTranslationPhase (-Real.log n) z *
          thetaCuspTailSecondDensityAtomOnePhaseTail (Real.log n) z := by
  unfold thetaCuspTailSecondDensityAtomPhase
  rw [integral_densityAtom_mul_eq_rpow_mul_integral_translate
    (fun x => spectralTranslationPhase x z) hn]
  rw [show (fun u : ℝ =>
      (thetaCuspTailSecondDensityAtom 1 u : ℂ) *
        spectralTranslationPhase (u - Real.log n) z) =
      fun u : ℝ => spectralTranslationPhase (-Real.log n) z *
        ((thetaCuspTailSecondDensityAtom 1 u : ℂ) *
          spectralTranslationPhase u z) by
    funext u
    rw [spectralTranslationPhase_sub]
    ring]
  rw [MeasureTheory.integral_const_mul]
  unfold thetaCuspTailSecondDensityAtomOnePhaseTail
  ring

theorem thetaCuspTailSecondDensityAtomPhaseDerivative_eq_centeredTail
    {n : ℕ} (hn : 0 < n) (z : ℂ) (hz : 0 ≤ z.im) :
    thetaCuspTailSecondDensityAtomPhaseDerivative n z =
      ((((n : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) *
        spectralTranslationPhase (-Real.log n) z *
          (thetaCuspTailSecondDensityAtomOnePhaseTailDerivative (Real.log n) z -
            ((Real.log n : ℂ) * I) *
              thetaCuspTailSecondDensityAtomOnePhaseTail (Real.log n) z) := by
  unfold thetaCuspTailSecondDensityAtomPhaseDerivative
  rw [integral_densityAtom_mul_eq_rpow_mul_integral_translate
    (fun x => (x : ℂ) * I * spectralTranslationPhase x z) hn]
  rw [show (fun u : ℝ =>
      (thetaCuspTailSecondDensityAtom 1 u : ℂ) *
        (((u - Real.log n : ℝ) : ℂ) * I *
          spectralTranslationPhase (u - Real.log n) z)) =
      fun u : ℝ => spectralTranslationPhase (-Real.log n) z *
        ((thetaCuspTailSecondDensityAtom 1 u : ℂ) *
          (((u : ℂ) * I * spectralTranslationPhase u z) -
            ((Real.log n : ℂ) * I) * spectralTranslationPhase u z)) by
    funext u
    rw [spectralTranslationPhase_sub]
    push_cast
    ring]
  rw [MeasureTheory.integral_const_mul]
  rw [show (fun u : ℝ =>
      (thetaCuspTailSecondDensityAtom 1 u : ℂ) *
        (((u : ℂ) * I * spectralTranslationPhase u z) -
          ((Real.log n : ℂ) * I) * spectralTranslationPhase u z)) =
      fun u : ℝ =>
        ((thetaCuspTailSecondDensityAtom 1 u : ℂ) *
          ((u : ℂ) * I * spectralTranslationPhase u z)) -
        ((Real.log n : ℂ) * I) *
          ((thetaCuspTailSecondDensityAtom 1 u : ℂ) *
            spectralTranslationPhase u z) by
    funext u
    ring]
  rw [MeasureTheory.integral_sub]
  · rw [MeasureTheory.integral_const_mul]
    unfold thetaCuspTailSecondDensityAtomOnePhaseTailDerivative
      thetaCuspTailSecondDensityAtomOnePhaseTail
    ring
  · exact (integrableOn_thetaCuspTailSecondDensityAtom_one_mul_phaseDerivative hz).mono_set
      (Ioi_subset_Ioi (Real.log_nonneg (by exact_mod_cast hn)))
  · exact (integrableOn_thetaCuspTailSecondDensityAtom_one_mul_phase hz).mono_set
      (Ioi_subset_Ioi (Real.log_nonneg (by exact_mod_cast hn))) |>.const_mul _

end
end RHTower

namespace RHTower
noncomputable section

/-- Swept-window phase removed when the first atom is translated by a nonnegative amount. -/
def thetaCuspTailSecondDensityAtomOnePhaseWindow (a : ℝ) (z : ℂ) : ℂ :=
  ∫ u : ℝ in (0 : ℝ)..a,
    (thetaCuspTailSecondDensityAtom 1 u : ℂ) * spectralTranslationPhase u z

/-- Spectral derivative of the swept-window phase. -/
def thetaCuspTailSecondDensityAtomOnePhaseWindowDerivative (a : ℝ) (z : ℂ) : ℂ :=
  ∫ u : ℝ in (0 : ℝ)..a,
    (thetaCuspTailSecondDensityAtom 1 u : ℂ) *
      ((u : ℂ) * I * spectralTranslationPhase u z)

theorem thetaCuspTailSecondDensityAtomOnePhaseTail_eq_full_sub_window
    {a : ℝ} (ha : 0 ≤ a) {z : ℂ} (hz : 0 ≤ z.im) :
    thetaCuspTailSecondDensityAtomOnePhaseTail a z =
      thetaCuspTailSecondDensityAtomOnePhaseTail 0 z -
        thetaCuspTailSecondDensityAtomOnePhaseWindow a z := by
  have h0 := integrableOn_thetaCuspTailSecondDensityAtom_one_mul_phase hz
  have haInt := h0.mono_set (Ioi_subset_Ioi ha)
  have hsplit := intervalIntegral.integral_interval_add_Ioi h0 haInt
  unfold thetaCuspTailSecondDensityAtomOnePhaseTail
    thetaCuspTailSecondDensityAtomOnePhaseWindow
  linear_combination hsplit

theorem thetaCuspTailSecondDensityAtomOnePhaseTailDerivative_eq_full_sub_window
    {a : ℝ} (ha : 0 ≤ a) {z : ℂ} (hz : 0 ≤ z.im) :
    thetaCuspTailSecondDensityAtomOnePhaseTailDerivative a z =
      thetaCuspTailSecondDensityAtomOnePhaseTailDerivative 0 z -
        thetaCuspTailSecondDensityAtomOnePhaseWindowDerivative a z := by
  have h0 := integrableOn_thetaCuspTailSecondDensityAtom_one_mul_phaseDerivative hz
  have haInt := h0.mono_set (Ioi_subset_Ioi ha)
  have hsplit := intervalIntegral.integral_interval_add_Ioi h0 haInt
  unfold thetaCuspTailSecondDensityAtomOnePhaseTailDerivative
    thetaCuspTailSecondDensityAtomOnePhaseWindowDerivative
  linear_combination hsplit

theorem thetaCuspTailSecondDensityAtomPhase_eq_full_sub_window
    {n : ℕ} (hn : 0 < n) (z : ℂ) (hz : 0 ≤ z.im) :
    thetaCuspTailSecondDensityAtomPhase n z =
      ((((n : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) *
        spectralTranslationPhase (-Real.log n) z *
          (thetaCuspTailSecondDensityAtomOnePhaseTail 0 z -
            thetaCuspTailSecondDensityAtomOnePhaseWindow (Real.log n) z) := by
  rw [thetaCuspTailSecondDensityAtomPhase_eq_centeredTail hn]
  rw [thetaCuspTailSecondDensityAtomOnePhaseTail_eq_full_sub_window
    (Real.log_nonneg (by exact_mod_cast hn)) hz]

theorem thetaCuspTailSecondDensityAtomPhaseDerivative_eq_full_sub_window
    {n : ℕ} (hn : 0 < n) (z : ℂ) (hz : 0 ≤ z.im) :
    thetaCuspTailSecondDensityAtomPhaseDerivative n z =
      ((((n : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) *
        spectralTranslationPhase (-Real.log n) z *
          ((thetaCuspTailSecondDensityAtomOnePhaseTailDerivative 0 z -
              thetaCuspTailSecondDensityAtomOnePhaseWindowDerivative (Real.log n) z) -
            ((Real.log n : ℂ) * I) *
              (thetaCuspTailSecondDensityAtomOnePhaseTail 0 z -
                thetaCuspTailSecondDensityAtomOnePhaseWindow (Real.log n) z)) := by
  rw [thetaCuspTailSecondDensityAtomPhaseDerivative_eq_centeredTail hn z hz]
  rw [thetaCuspTailSecondDensityAtomOnePhaseTail_eq_full_sub_window
      (Real.log_nonneg (by exact_mod_cast hn)) hz,
    thetaCuspTailSecondDensityAtomOnePhaseTailDerivative_eq_full_sub_window
      (Real.log_nonneg (by exact_mod_cast hn)) hz]

/-- Subtractive form of the boundary-current identity. -/
theorem orientedPhaseCurrent_sub_boundary_identity
    (p F F' W W' : ℂ) (a : ℝ) :
    (p * ((F' - W') + ((a : ℂ) * I) * (F - W)) *
        (starRingEnd ℂ) (p * (F - W))).im =
      Complex.normSq p *
        ((F' * (starRingEnd ℂ) F).im +
          (W' * (starRingEnd ℂ) W).im -
          (F' * (starRingEnd ℂ) W).im -
          (W' * (starRingEnd ℂ) F).im +
          a * Complex.normSq (F - W)) := by
  have h := orientedPhaseCurrent_add_boundary_identity p F F' (-W) (-W') a
  simpa only [sub_eq_add_neg, map_neg, neg_mul, mul_neg, Complex.neg_im, neg_neg] using h

/-- Exact one-atom current decomposition.  Translation contributes the favorable drift
`-log(n)|tail|^2`; all failure of a pure phase sign is confined to the swept-window self-current
and its two mixed currents with the common first-atom phase. -/
theorem thetaCuspTailSecondDensityAtomPhase_current_eq_full_window
    {n : ℕ} (hn : 0 < n) (z : ℂ) (hz : 0 ≤ z.im) :
    (thetaCuspTailSecondDensityAtomPhaseDerivative n z *
        (starRingEnd ℂ) (thetaCuspTailSecondDensityAtomPhase n z)).im =
      Complex.normSq
          (((((n : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) *
            spectralTranslationPhase (-Real.log n) z) *
        ((thetaCuspTailSecondDensityAtomOnePhaseTailDerivative 0 z *
            (starRingEnd ℂ) (thetaCuspTailSecondDensityAtomOnePhaseTail 0 z)).im +
          (thetaCuspTailSecondDensityAtomOnePhaseWindowDerivative (Real.log n) z *
            (starRingEnd ℂ)
              (thetaCuspTailSecondDensityAtomOnePhaseWindow (Real.log n) z)).im -
          (thetaCuspTailSecondDensityAtomOnePhaseTailDerivative 0 z *
            (starRingEnd ℂ)
              (thetaCuspTailSecondDensityAtomOnePhaseWindow (Real.log n) z)).im -
          (thetaCuspTailSecondDensityAtomOnePhaseWindowDerivative (Real.log n) z *
            (starRingEnd ℂ) (thetaCuspTailSecondDensityAtomOnePhaseTail 0 z)).im -
          Real.log n * Complex.normSq
            (thetaCuspTailSecondDensityAtomOnePhaseTail 0 z -
              thetaCuspTailSecondDensityAtomOnePhaseWindow (Real.log n) z)) := by
  rw [thetaCuspTailSecondDensityAtomPhase_eq_full_sub_window hn z hz,
    thetaCuspTailSecondDensityAtomPhaseDerivative_eq_full_sub_window hn z hz]
  let p : ℂ := ((((n : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) *
    spectralTranslationPhase (-Real.log n) z
  let F := thetaCuspTailSecondDensityAtomOnePhaseTail 0 z
  let F' := thetaCuspTailSecondDensityAtomOnePhaseTailDerivative 0 z
  let W := thetaCuspTailSecondDensityAtomOnePhaseWindow (Real.log n) z
  let W' := thetaCuspTailSecondDensityAtomOnePhaseWindowDerivative (Real.log n) z
  have h := orientedPhaseCurrent_sub_boundary_identity p F F' W W' (-Real.log n)
  dsimp only [p, F, F', W, W'] at h ⊢
  convert h using 1 <;> push_cast <;> ring

end
end RHTower
namespace RHTower
noncomputable section

/-- Algebraic finite Abel identity for a nested tail. -/
theorem finset_sum_mul_tail_eq_prefix_blocks
    {R : Type*} [CommRing R]
    (p T J : ℕ → R)
    (hrec : ∀ r : ℕ, T r = J r + T (r + 1)) :
    ∀ N : ℕ,
      (∑ j ∈ Finset.range N, p j * T j) =
        (∑ r ∈ Finset.range N,
          (∑ j ∈ Finset.range (r + 1), p j) * J r) +
        (∑ j ∈ Finset.range N, p j) * T N := by
  intro N
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ, ih, hrec N]
      simp only [Finset.sum_range_succ]
      ring

/-- Phase transform of one logarithmic block of the first density atom. -/
def thetaCuspTailSecondDensityAtomOnePhaseBlock
    (a b : ℝ) (z : ℂ) : ℂ :=
  ∫ u : ℝ in a..b,
    (thetaCuspTailSecondDensityAtom 1 u : ℂ) * spectralTranslationPhase u z

/-- Spectral derivative companion of one logarithmic block. -/
def thetaCuspTailSecondDensityAtomOnePhaseBlockDerivative
    (a b : ℝ) (z : ℂ) : ℂ :=
  ∫ u : ℝ in a..b,
    (thetaCuspTailSecondDensityAtom 1 u : ℂ) *
      ((u : ℂ) * I * spectralTranslationPhase u z)

theorem thetaCuspTailSecondDensityAtomOnePhaseTail_block_rec
    {L : ℝ} (hL : 0 ≤ L) {z : ℂ} (hz : 0 ≤ z.im) (r : ℕ) :
    thetaCuspTailSecondDensityAtomOnePhaseTail (r * L) z =
      thetaCuspTailSecondDensityAtomOnePhaseBlock
          (r * L) (((r + 1 : ℕ) : ℝ) * L) z +
        thetaCuspTailSecondDensityAtomOnePhaseTail
          (((r + 1 : ℕ) : ℝ) * L) z := by
  have h0 := integrableOn_thetaCuspTailSecondDensityAtom_one_mul_phase hz
  have hr : 0 ≤ (r : ℝ) * L := mul_nonneg (Nat.cast_nonneg r) hL
  have hrs : 0 ≤ ((r + 1 : ℕ) : ℝ) * L :=
    mul_nonneg (Nat.cast_nonneg (r + 1)) hL
  have hrInt := h0.mono_set (Ioi_subset_Ioi hr)
  have hrsInt := h0.mono_set (Ioi_subset_Ioi hrs)
  have hsplit := intervalIntegral.integral_interval_add_Ioi hrInt hrsInt
  simpa only [thetaCuspTailSecondDensityAtomOnePhaseTail,
    thetaCuspTailSecondDensityAtomOnePhaseBlock, Nat.cast_add, Nat.cast_one] using hsplit.symm

theorem thetaCuspTailSecondDensityAtomOnePhaseTailDerivative_block_rec
    {L : ℝ} (hL : 0 ≤ L) {z : ℂ} (hz : 0 ≤ z.im) (r : ℕ) :
    thetaCuspTailSecondDensityAtomOnePhaseTailDerivative (r * L) z =
      thetaCuspTailSecondDensityAtomOnePhaseBlockDerivative
          (r * L) (((r + 1 : ℕ) : ℝ) * L) z +
        thetaCuspTailSecondDensityAtomOnePhaseTailDerivative
          (((r + 1 : ℕ) : ℝ) * L) z := by
  have h0 := integrableOn_thetaCuspTailSecondDensityAtom_one_mul_phaseDerivative hz
  have hr : 0 ≤ (r : ℝ) * L := mul_nonneg (Nat.cast_nonneg r) hL
  have hrs : 0 ≤ ((r + 1 : ℕ) : ℝ) * L :=
    mul_nonneg (Nat.cast_nonneg (r + 1)) hL
  have hrInt := h0.mono_set (Ioi_subset_Ioi hr)
  have hrsInt := h0.mono_set (Ioi_subset_Ioi hrs)
  have hsplit := intervalIntegral.integral_interval_add_Ioi hrInt hrsInt
  simpa only [thetaCuspTailSecondDensityAtomOnePhaseTailDerivative,
    thetaCuspTailSecondDensityAtomOnePhaseBlockDerivative,
    Nat.cast_add, Nat.cast_one] using hsplit.symm

/-- Critical logarithmic coefficient of the `j`th translate. -/
def criticalLogPhaseCoefficient (L : ℝ) (j : ℕ) (z : ℂ) : ℂ :=
  (Real.exp (-((j : ℝ) * L) / 2) : ℂ) *
    spectralTranslationPhase (-((j : ℝ) * L)) z

/-- Spectral derivative of the critical logarithmic coefficient. -/
def criticalLogPhaseCoefficientDerivative (L : ℝ) (j : ℕ) (z : ℂ) : ℂ :=
  (-(((j : ℝ) * L) : ℂ) * I) * criticalLogPhaseCoefficient L j z

/-- Prefix coefficient carried by the first `N` logarithmic translates. -/
def criticalLogPhasePrefix (L : ℝ) (N : ℕ) (z : ℂ) : ℂ :=
  ∑ j ∈ Finset.range N, criticalLogPhaseCoefficient L j z

/-- Derivative companion of the critical logarithmic prefix. -/
def criticalLogPhasePrefixDerivative (L : ℝ) (N : ℕ) (z : ℂ) : ℂ :=
  ∑ j ∈ Finset.range N, criticalLogPhaseCoefficientDerivative L j z

/-- Exact finite layer-cake formula: all nested swept windows are absorbed into geometric
prefixes on disjoint logarithmic blocks, plus one cofinal tail. -/
theorem criticalLogPhase_tail_packet_eq_prefix_blocks
    {L : ℝ} (hL : 0 ≤ L) {z : ℂ} (hz : 0 ≤ z.im) (N : ℕ) :
    (∑ j ∈ Finset.range N,
      criticalLogPhaseCoefficient L j z *
        thetaCuspTailSecondDensityAtomOnePhaseTail (j * L) z) =
      (∑ r ∈ Finset.range N,
        criticalLogPhasePrefix L (r + 1) z *
          thetaCuspTailSecondDensityAtomOnePhaseBlock
            (r * L) (((r + 1 : ℕ) : ℝ) * L) z) +
      criticalLogPhasePrefix L N z *
        thetaCuspTailSecondDensityAtomOnePhaseTail (N * L) z := by
  simpa only [criticalLogPhasePrefix] using
    finset_sum_mul_tail_eq_prefix_blocks
      (fun j => criticalLogPhaseCoefficient L j z)
      (fun j => thetaCuspTailSecondDensityAtomOnePhaseTail (j * L) z)
      (fun j => thetaCuspTailSecondDensityAtomOnePhaseBlock
        (j * L) (((j + 1 : ℕ) : ℝ) * L) z)
      (fun j => by
        simpa only [Nat.cast_add, Nat.cast_one] using
          thetaCuspTailSecondDensityAtomOnePhaseTail_block_rec hL hz j) N

/-- Derivative layer-cake companion.  Each block retains the derivative of its geometric prefix,
so no phase orientation is lost before polarization. -/
theorem criticalLogPhase_tail_packetDerivative_eq_prefix_blocks
    {L : ℝ} (hL : 0 ≤ L) {z : ℂ} (hz : 0 ≤ z.im) (N : ℕ) :
    (∑ j ∈ Finset.range N,
      (criticalLogPhaseCoefficient L j z *
          thetaCuspTailSecondDensityAtomOnePhaseTailDerivative (j * L) z +
        criticalLogPhaseCoefficientDerivative L j z *
          thetaCuspTailSecondDensityAtomOnePhaseTail (j * L) z)) =
      (∑ r ∈ Finset.range N,
        (criticalLogPhasePrefix L (r + 1) z *
            thetaCuspTailSecondDensityAtomOnePhaseBlockDerivative
              (r * L) (((r + 1 : ℕ) : ℝ) * L) z +
          criticalLogPhasePrefixDerivative L (r + 1) z *
            thetaCuspTailSecondDensityAtomOnePhaseBlock
              (r * L) (((r + 1 : ℕ) : ℝ) * L) z)) +
      (criticalLogPhasePrefix L N z *
          thetaCuspTailSecondDensityAtomOnePhaseTailDerivative (N * L) z +
        criticalLogPhasePrefixDerivative L N z *
          thetaCuspTailSecondDensityAtomOnePhaseTail (N * L) z) := by
  have hvalue := finset_sum_mul_tail_eq_prefix_blocks
    (fun j => criticalLogPhaseCoefficient L j z)
    (fun j => thetaCuspTailSecondDensityAtomOnePhaseTailDerivative (j * L) z)
    (fun j => thetaCuspTailSecondDensityAtomOnePhaseBlockDerivative
      (j * L) (((j + 1 : ℕ) : ℝ) * L) z)
    (fun j => by
      simpa only [Nat.cast_add, Nat.cast_one] using
        thetaCuspTailSecondDensityAtomOnePhaseTailDerivative_block_rec hL hz j) N
  have hphase := finset_sum_mul_tail_eq_prefix_blocks
    (fun j => criticalLogPhaseCoefficientDerivative L j z)
    (fun j => thetaCuspTailSecondDensityAtomOnePhaseTail (j * L) z)
    (fun j => thetaCuspTailSecondDensityAtomOnePhaseBlock
      (j * L) (((j + 1 : ℕ) : ℝ) * L) z)
    (fun j => by
      simpa only [Nat.cast_add, Nat.cast_one] using
        thetaCuspTailSecondDensityAtomOnePhaseTail_block_rec hL hz j) N
  simp only [criticalLogPhasePrefix, criticalLogPhasePrefixDerivative]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  linear_combination hvalue + hphase

end
end RHTower

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry

/-! ## Critical dyadic prefix budget -/

theorem criticalLogPhaseCoefficient_eq_reversePhasePow
    (L : ℝ) (j : ℕ) (z : ℂ) :
    criticalLogPhaseCoefficient L j z =
      Complex.exp (I * (L : ℂ) * (-z + I / 2)) ^ j := by
  unfold criticalLogPhaseCoefficient spectralTranslationPhase
  rw [← Complex.exp_nat_mul, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

theorem criticalLogPhasePrefix_eq_reverseCriticalPhase
    (L : ℝ) (N : ℕ) (z : ℂ) :
    criticalLogPhasePrefix L N z =
      reverseCriticalUnitCirclePolynomialPhase (finiteGeometricPolynomial N) L z := by
  unfold criticalLogPhasePrefix reverseCriticalUnitCirclePolynomialPhase
    finiteGeometricPolynomial
  simp only [Polynomial.eval_geom_sum]
  apply Finset.sum_congr rfl
  intro j _hj
  exact criticalLogPhaseCoefficient_eq_reversePhasePow L j z

theorem criticalLogPhasePrefixDerivative_eq_reverseCriticalPhaseDerivative
    (L : ℝ) (N : ℕ) (z : ℂ) :
    criticalLogPhasePrefixDerivative L N z =
      reverseCriticalUnitCirclePolynomialPhaseDerivative
        (finiteGeometricPolynomial N) L z := by
  have hp : HasDerivAt (criticalLogPhasePrefix L N)
      (criticalLogPhasePrefixDerivative L N z) z := by
    unfold criticalLogPhasePrefix criticalLogPhasePrefixDerivative
      criticalLogPhaseCoefficient criticalLogPhaseCoefficientDerivative
    have hsum := HasDerivAt.sum (u := Finset.range N)
      (A := fun j (u : ℂ) =>
        (Real.exp (-((j : ℝ) * L) / 2) : ℂ) *
          spectralTranslationPhase (-((j : ℝ) * L)) u)
      (A' := fun j =>
        (-(((j : ℝ) * L) : ℂ) * I) *
          ((Real.exp (-((j : ℝ) * L) / 2) : ℂ) *
            spectralTranslationPhase (-((j : ℝ) * L)) z))
      (fun j _hj => by
        have hraw :=
          (hasDerivAt_spectralTranslationPhase (-((j : ℝ) * L)) z).const_mul
            (Real.exp (-((j : ℝ) * L) / 2) : ℂ)
        simpa only [Pi.mul_apply] using!
          hraw.congr_deriv (by
            push_cast
            ring))
    apply hsum.congr_of_eventuallyEq
    filter_upwards with u
    simp only [Finset.sum_apply]
  have hr := hasDerivAt_reverseCriticalUnitCirclePolynomialPhase
    (finiteGeometricPolynomial N) L z
  have hfun : criticalLogPhasePrefix L N =
      reverseCriticalUnitCirclePolynomialPhase (finiteGeometricPolynomial N) L := by
    funext u
    exact criticalLogPhasePrefix_eq_reverseCriticalPhase L N u
  rw [hfun] at hp
  exact hp.unique hr

/-- Every critical dyadic prefix has an explicit degree-linear upper current budget on a fixed
left-strip fibre. -/
theorem criticalLogPhasePrefix_current_le
    {L : ℝ} (hL : 0 ≤ L) {N : ℕ} (hN : 0 < N)
    {z : ℂ} (hz : z.im < 1 / 2) :
    (criticalLogPhasePrefixDerivative L N z *
      (starRingEnd ℂ) (criticalLogPhasePrefix L N z)).im ≤
      L * ((N - 1 : ℕ) : ℝ) *
        (Real.exp (-L * (1 / 2 - z.im)) /
          (1 - Real.exp (-L * (1 / 2 - z.im)))) *
        Complex.normSq (criticalLogPhasePrefix L N z) := by
  have hP := finiteGeometricPolynomial_ne_zero N hN
  have hroots : ∀ ζ ∈ (finiteGeometricPolynomial N).roots, ‖ζ‖ = 1 := by
    intro ζ hζ
    exact finiteGeometricPolynomial_root_norm_eq_one N hN
      ((Polynomial.mem_roots hP).1 hζ)
  rw [criticalLogPhasePrefixDerivative_eq_reverseCriticalPhaseDerivative,
    criticalLogPhasePrefix_eq_reverseCriticalPhase]
  have h := reverseCriticalUnitCirclePolynomialPhase_current_le
    (finiteGeometricPolynomial N) hP hroots hL hz
  rw [finiteGeometricPolynomial_natDegree N hN] at h
  exact h


end

end RHTower
