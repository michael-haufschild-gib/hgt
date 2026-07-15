import GaloisForLFunctions.HTGeometry.FiniteGibbsDifferentialBoundary

/-!
# Fidelity detects phase geometry erased by Born observables

For normalized positive weights and unit phases, the weighted overlap is the Loschmidt/fidelity
amplitude of a diagonal phase kick.  Its fidelity deficit is exactly one half of the weighted
pairwise squared phase dispersion.

This supplies a positive residue for phase blindness of Born probabilities and their Fisher
variance: the same coordinate probabilities can remain fixed while the interferometric overlap
detects every relative phase.  With strictly positive weights, zero deficit is equivalent to
agreement of all phases.

The identity is static.  A phase packet labels available relative clock readings; no external
time evolution is required.  In quantum work statistics the Loschmidt amplitude is the
characteristic function of the spectral distribution, while multipath interferometry reads the
same relative phases through visibility.
-/

open scoped BigOperators

namespace HTGeometry

noncomputable section

/-- Weighted overlap amplitude of a finite phase packet. -/
def finitePhaseOverlap {ι : Type*} [Fintype ι]
    (weight : ι → ℝ) (phase : ι → ℂ) : ℂ :=
  ∑ i, (weight i : ℂ) * phase i

/-- Mean squared pairwise separation of a finite phase packet. -/
def finitePhasePairwiseDispersion {ι : Type*} [Fintype ι]
    (weight : ι → ℝ) (phase : ι → ℂ) : ℝ :=
  ∑ i, ∑ j, weight i * weight j * ‖phase i - phase j‖ ^ 2

/-- **Phase-dispersion/fidelity identity.**  Pairwise phase dispersion is twice the fidelity
deficit of the weighted overlap. -/
theorem finitePhasePairwiseDispersion_eq_two_mul_fidelityDeficit
    {ι : Type*} [Fintype ι] (weight : ι → ℝ) (phase : ι → ℂ)
    (hweight : ∑ i, weight i = 1) (hphase : ∀ i, ‖phase i‖ = 1) :
    finitePhasePairwiseDispersion weight phase =
      2 * (1 - ‖finitePhaseOverlap weight phase‖ ^ 2) := by
  have hre := normalizedWeight_pairwiseSqGap_eq_two_mul_variance
    weight (fun i => (phase i).re) hweight
  have him := normalizedWeight_pairwiseSqGap_eq_two_mul_variance
    weight (fun i => (phase i).im) hweight
  have hnorm : ∀ i, (phase i).re ^ 2 + (phase i).im ^ 2 = 1 := by
    intro i
    calc
      (phase i).re ^ 2 + (phase i).im ^ 2 = ‖phase i‖ ^ 2 := by
        rw [Complex.sq_norm, Complex.normSq_apply]
        ring
      _ = 1 := by rw [hphase i]; norm_num
  have hsecond :
      (∑ i, weight i * (phase i).re ^ 2) +
        (∑ i, weight i * (phase i).im ^ 2) = 1 := by
    rw [← Finset.sum_add_distrib]
    calc
      ∑ i, (weight i * (phase i).re ^ 2 +
          weight i * (phase i).im ^ 2) =
          ∑ i, weight i * ((phase i).re ^ 2 + (phase i).im ^ 2) := by
            apply Finset.sum_congr rfl
            intro i hi
            ring
      _ = ∑ i, weight i := by simp_rw [hnorm, mul_one]
      _ = 1 := hweight
  have hoverlapRe : (finitePhaseOverlap weight phase).re =
      ∑ i, weight i * (phase i).re := by
    simp [finitePhaseOverlap]
  have hoverlapIm : (finitePhaseOverlap weight phase).im =
      ∑ i, weight i * (phase i).im := by
    simp [finitePhaseOverlap]
  have hre' := hre
  have him' := him
  have hsecond' := hsecond
  simp only [pow_two] at hre' him'
  simp only [pow_two] at hsecond'
  unfold finitePhasePairwiseDispersion
  simp_rw [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    mul_add, Finset.sum_add_distrib]
  rw [hre', him', hoverlapRe, hoverlapIm]
  nlinarith [hsecond']

/-- Positive weights make the fidelity deficit nonnegative without a separate
Cauchy--Schwarz hypothesis. -/
theorem finitePhase_fidelityDeficit_nonneg
    {ι : Type*} [Fintype ι] (weight : ι → ℝ) (phase : ι → ℂ)
    (hweight : ∑ i, weight i = 1) (hweightNonneg : ∀ i, 0 ≤ weight i)
    (hphase : ∀ i, ‖phase i‖ = 1) :
    0 ≤ 1 - ‖finitePhaseOverlap weight phase‖ ^ 2 := by
  have hdisp : 0 ≤ finitePhasePairwiseDispersion weight phase := by
    unfold finitePhasePairwiseDispersion
    apply Finset.sum_nonneg
    intro i hi
    apply Finset.sum_nonneg
    intro j hj
    exact mul_nonneg (mul_nonneg (hweightNonneg i) (hweightNonneg j))
      (sq_nonneg _)
  rw [finitePhasePairwiseDispersion_eq_two_mul_fidelityDeficit
    weight phase hweight hphase] at hdisp
  linarith

/-- **Faithful relative-phase criterion.**  For strictly positive weights, zero fidelity deficit
is equivalent to agreement of every relative phase. -/
theorem finitePhase_fidelityDeficit_eq_zero_iff
    {ι : Type*} [Fintype ι] (weight : ι → ℝ) (phase : ι → ℂ)
    (hweight : ∑ i, weight i = 1) (hweightPos : ∀ i, 0 < weight i)
    (hphase : ∀ i, ‖phase i‖ = 1) :
    1 - ‖finitePhaseOverlap weight phase‖ ^ 2 = 0 ↔
      ∀ i j, phase i = phase j := by
  constructor
  · intro hzero
    have hdisp : finitePhasePairwiseDispersion weight phase = 0 := by
      rw [finitePhasePairwiseDispersion_eq_two_mul_fidelityDeficit
        weight phase hweight hphase, hzero, mul_zero]
    unfold finitePhasePairwiseDispersion at hdisp
    have houterNonneg : ∀ i ∈ (Finset.univ : Finset ι),
        0 ≤ ∑ j, weight i * weight j * ‖phase i - phase j‖ ^ 2 := by
      intro i hi
      apply Finset.sum_nonneg
      intro j hj
      exact mul_nonneg (mul_nonneg (hweightPos i).le (hweightPos j).le)
        (sq_nonneg _)
    intro i j
    have hi := (Finset.sum_eq_zero_iff_of_nonneg houterNonneg).mp hdisp i
      (Finset.mem_univ i)
    have hinnerNonneg : ∀ j ∈ (Finset.univ : Finset ι),
        0 ≤ weight i * weight j * ‖phase i - phase j‖ ^ 2 := by
      intro k hk
      exact mul_nonneg (mul_nonneg (hweightPos i).le (hweightPos k).le)
        (sq_nonneg _)
    have hij := (Finset.sum_eq_zero_iff_of_nonneg hinnerNonneg).mp hi j
      (Finset.mem_univ j)
    have hcoeff : weight i * weight j ≠ 0 :=
      (mul_pos (hweightPos i) (hweightPos j)).ne'
    have hnormSq : ‖phase i - phase j‖ ^ 2 = 0 :=
      (mul_eq_zero.mp hij).resolve_left hcoeff
    have hnorm : ‖phase i - phase j‖ = 0 := sq_eq_zero_iff.mp hnormSq
    exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)
  · intro hphaseEq
    have hdisp : finitePhasePairwiseDispersion weight phase = 0 := by
      unfold finitePhasePairwiseDispersion
      apply Finset.sum_eq_zero
      intro i hi
      apply Finset.sum_eq_zero
      intro j hj
      rw [hphaseEq i j, sub_self, norm_zero, zero_pow (by norm_num), mul_zero]
    rw [finitePhasePairwiseDispersion_eq_two_mul_fidelityDeficit
      weight phase hweight hphase] at hdisp
    linarith

end

end HTGeometry
