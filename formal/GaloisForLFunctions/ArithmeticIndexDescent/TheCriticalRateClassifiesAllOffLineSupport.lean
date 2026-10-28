import GaloisForLFunctions.ArithmeticIndexDescent.TheQuadraticScaleWorkDetectsEveryException

/-!
# The critical source rate classifies off-line support

On finite off-line support the completed work is an exact finite sum of
arithmetic source fields. The fields keep all exterior zeros and the
archimedean term. Its quadratic scale increment converges to a height-square
source moment. Together with quartet forcing, this separates zero work,
finite exceptional work and divergent work without assuming an upper bound.
-/

noncomputable section

open Filter Finset Set RHTower
open GaloisForLFunctions.ArithmeticElectrostatics
open GaloisForLFunctions.ArithmeticCorrespondencePositivity
open scoped Topology

namespace GaloisForLFunctions.ArithmeticIndexDescent

/-- A finite height-square source moment. Individual source coefficients can have either sign. -/
def quadraticPacketSourceMoment (F : Finset XiZeroCopy) : ℝ :=
  (3 / 2 : ℝ) * ∑ p ∈ F, xiZeroHeight p ^ 2 * xiSignedDepth p * xiSourceField p

/-- Critical copies have zero normal displacement; every noncritical copy remains in the sum. -/
theorem taperedSourceWork_eq_finite_offLine_sum (hfin : offLineSupport.Finite)
    (R : ℝ) (N : ℕ) :
    xiTaperedSourceWork R N =
      ∑ p ∈ (offLineCopies_finite_of_offLineSupport_finite hfin).toFinset,
        xiSignedDepth p * heightDamping R (xiZeroHeight p) *
          heightTaper N (xiZeroHeight p) * xiSourceField p := by
  classical
  let a : XiZeroCopy → ℝ := fun p =>
    xiSignedDepth p * heightDamping R (xiZeroHeight p) *
      heightTaper N (xiZeroHeight p) * xiSourceField p
  have hbox : (∑' p, a p) = xiTaperedSourceWork R N := by
    apply tsum_eq_sum
    intro p hp
    have ht : (N : ℝ) + 1 ≤ |xiZeroHeight p| :=
      (lt_of_not_ge (fun h => hp ((mem_xiWorkHeightBox N p).mpr h))).le
    simp only [a, heightTaper_eq_zero ht, mul_zero, zero_mul]
  rw [← hbox]
  apply tsum_eq_sum
  intro p hp
  have hnot : p ∉ offLineCopies :=
    ((offLineCopies_finite_of_offLineSupport_finite hfin).mem_toFinset).not.mp hp
  have hcritical : (p.1 : ℂ).re = 1 / 2 := by
    simpa only [offLineCopies, Set.mem_setOf_eq, not_not] using hnot
  simp only [a, xiSignedDepth, hcritical, sub_self, zero_mul]

/-- Finite off-line support gives an exact source expansion, retaining each full exterior field. -/
theorem dampedSourceWork_eq_finite_offLine_sum (hfin : offLineSupport.Finite)
    {R : ℝ} (hR : 4 ≤ R) :
    xiDampedSourceWork R =
      ∑ p ∈ (offLineCopies_finite_of_offLineSupport_finite hfin).toFinset,
        xiSignedDepth p * heightDamping R (xiZeroHeight p) * xiSourceField p := by
  classical
  let F := (offLineCopies_finite_of_offLineSupport_finite hfin).toFinset
  have hp (p : XiZeroCopy) :
      Tendsto (fun N : ℕ => xiSignedDepth p * heightDamping R (xiZeroHeight p) *
        heightTaper N (xiZeroHeight p) * xiSourceField p) atTop
        (𝓝 (xiSignedDepth p * heightDamping R (xiZeroHeight p) * xiSourceField p)) := by
    simpa only [mul_one] using
      (tendsto_const_nhds.mul (heightTaper_tendsto (xiZeroHeight p))).mul_const
        (xiSourceField p)
  have hsum := tendsto_finsetSum F (fun p _ => hp p)
  have heq : (fun N : ℕ => xiTaperedSourceWork R N) =
      (fun N : ℕ => ∑ p ∈ F, xiSignedDepth p * heightDamping R (xiZeroHeight p) *
        heightTaper N (xiZeroHeight p) * xiSourceField p) :=
    funext (taperedSourceWork_eq_finite_offLine_sum hfin R)
  apply tendsto_nhds_unique (xiTaperedSourceWork_tendsto hR)
  change Tendsto (fun N : ℕ => xiTaperedSourceWork R N) atTop
    (𝓝 (∑ p ∈ F, xiSignedDepth p * heightDamping R (xiZeroHeight p) * xiSourceField p))
  rw [heq]
  exact hsum

/-- The critical rate is the full finite Laurent-source moment, not an internally truncated energy. -/
theorem quadraticWorkIncrement_tendsto_sourceMoment (hfin : offLineSupport.Finite) :
    Tendsto quadraticWorkIncrement atTop
      (𝓝 (quadraticPacketSourceMoment
        (offLineCopies_finite_of_offLineSupport_finite hfin).toFinset)) := by
  classical
  let F := (offLineCopies_finite_of_offLineSupport_finite hfin).toFinset
  have hp (p : XiZeroCopy) :
      Tendsto (fun R : ℝ => (xiSignedDepth p * xiSourceField p) *
        (R ^ 2 * (heightDamping (2 * R) (xiZeroHeight p) -
          heightDamping R (xiZeroHeight p)))) atTop
        (𝓝 ((xiSignedDepth p * xiSourceField p) * ((3 / 2 : ℝ) * xiZeroHeight p ^ 2))) :=
    tendsto_const_nhds.mul (heightDamping_quadraticGap_tendsto (xiZeroHeight p))
  have hsum := tendsto_finsetSum F (fun p _ => hp p)
  have hvalue : (∑ p ∈ F,
      (xiSignedDepth p * xiSourceField p) * ((3 / 2 : ℝ) * xiZeroHeight p ^ 2)) =
      quadraticPacketSourceMoment F := by
    rw [quadraticPacketSourceMoment, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p _
    ring
  rw [hvalue] at hsum
  apply hsum.congr'
  filter_upwards [eventually_ge_atTop (4 : ℝ)] with R hR
  unfold quadraticWorkIncrement doubledSourceWorkIncrement
  rw [dampedSourceWork_eq_finite_offLine_sum hfin (show 4 ≤ 2 * R by linarith only [hR]),
    dampedSourceWork_eq_finite_offLine_sum hfin hR, ← Finset.sum_sub_distrib,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  ring

/-- A complete finite source moment pays every actual quartet, despite signed individual rows. -/
theorem quartetCharge_le_finiteSourceMoment (hfin : offLineSupport.Finite)
    {j : XiDivisorSupport} (hj : (j : ℂ).re ≠ 1 / 2) :
    3 * (j : ℂ).im ^ 2 * (1 + reflectionDiagonalAngle j) ≤
      quadraticPacketSourceMoment
        (offLineCopies_finite_of_offLineSupport_finite hfin).toFinset := by
  by_contra! hlt
  let M := quadraticPacketSourceMoment
    (offLineCopies_finite_of_offLineSupport_finite hfin).toFinset
  let c := 3 * (j : ℂ).im ^ 2 * (1 + reflectionDiagonalAngle j)
  have hb : (M + c) / 2 < c := by
    change M < c at hlt
    linarith only [hlt]
  have hlow := ge_of_tendsto (quadraticWorkIncrement_tendsto_sourceMoment hfin)
    ((eventually_lt_quadraticIncrement_of_lt_quartetCharge hj hb).mono fun _ h => h.le)
  change (M + c) / 2 ≤ M at hlow
  change M < c at hlt
  linarith only [hlt, hlow]

/-- Nonempty finite exceptions have a strictly positive source moment beyond the closed quantum. -/
theorem finiteSourceMoment_gt_exclusionQuantum (hfin : offLineSupport.Finite)
    (hnot : ¬RiemannHypothesis) :
    quadraticExclusionQuantum < quadraticPacketSourceMoment
      (offLineCopies_finite_of_offLineSupport_finite hfin).toFinset := by
  obtain ⟨j, hj⟩ : ∃ j : XiDivisorSupport, (j : ℂ).re ≠ 1 / 2 := by
    by_contra! hall
    exact hnot (riemannHypothesis_of_forall_re_eq (c := 1 / 2) hall)
  exact (quartetCharge_gt_exclusionQuantum hj).trans_le (quartetCharge_le_finiteSourceMoment hfin hj)

/-- A finite source moment localizes every exception in a strict height-square range. -/
theorem three_heightSquare_lt_finiteSourceMoment (hfin : offLineSupport.Finite)
    {j : XiDivisorSupport} (hj : (j : ℂ).re ≠ 1 / 2) :
    3 * (j : ℂ).im ^ 2 < quadraticPacketSourceMoment
      (offLineCopies_finite_of_offLineSupport_finite hfin).toFinset := by
  have hheight : 4 ≤ |(j : ℂ).im| := four_le_abs_xiZeroHeight (firstZeroCopy j)
  have hsq : 0 < (j : ℂ).im ^ 2 := by
    nlinarith only [hheight, sq_abs (j : ℂ).im, sq_nonneg (|(j : ℂ).im| - 4)]
  have hprod := mul_pos hsq (reflectionDiagonalAngle_pos hj)
  have hcharge := quartetCharge_le_finiteSourceMoment hfin hj
  nlinarith only [hprod, hcharge]

/-- Critical-rate boundedness is exactly finite off-line support. -/
theorem eventually_bounded_quadraticIncrement_iff :
    (∃ B : ℝ, ∀ᶠ R : ℝ in atTop, quadraticWorkIncrement R ≤ B) ↔
      offLineSupport.Finite := by
  constructor
  · rintro ⟨B, hB⟩
    by_contra hinf
    have hhigh := (quadraticWorkIncrement_tendsto_atTop_of_infinite hinf).eventually
      (eventually_gt_atTop B)
    obtain ⟨R, hR, hR'⟩ := (hB.and hhigh).exists
    exact (not_lt_of_ge hR) hR'
  · intro hfin
    let M := quadraticPacketSourceMoment
      (offLineCopies_finite_of_offLineSupport_finite hfin).toFinset
    refine ⟨M + 1, ?_⟩
    exact ((quadraticWorkIncrement_tendsto_sourceMoment hfin).eventually
      (gt_mem_nhds (show M < M + 1 by linarith))).mono fun _ h => h.le

/-- Existence of any finite critical-rate limit is equivalent to finite off-line support. -/
theorem quadraticIncrement_has_finite_limit_iff :
    (∃ L : ℝ, Tendsto quadraticWorkIncrement atTop (𝓝 L)) ↔ offLineSupport.Finite := by
  constructor
  · rintro ⟨L, hL⟩
    apply eventually_bounded_quadraticIncrement_iff.mp
    refine ⟨L + 1, ?_⟩
    exact (hL.eventually (gt_mem_nhds (show L < L + 1 by linarith))).mono fun _ h => h.le
  · intro hfin
    exact ⟨_, quadraticWorkIncrement_tendsto_sourceMoment hfin⟩

/-- The source has three exact rate regimes: no defect, finite exceptional moment, or divergence. -/
theorem quadratic_source_rate_trichotomy :
    (RiemannHypothesis ∧ ∀ R : ℝ, quadraticWorkIncrement R = 0) ∨
    (offLineSupport.Finite ∧ ¬RiemannHypothesis ∧
      ∃ L : ℝ, quadraticExclusionQuantum < L ∧ Tendsto quadraticWorkIncrement atTop (𝓝 L)) ∨
    (offLineSupport.Infinite ∧ Tendsto quadraticWorkIncrement atTop atTop) := by
  by_cases hRH : RiemannHypothesis
  · exact Or.inl ⟨hRH, quadraticWorkIncrement_eq_zero_of_riemannHypothesis hRH⟩
  by_cases hfin : offLineSupport.Finite
  · exact Or.inr (Or.inl ⟨hfin, hRH, _, finiteSourceMoment_gt_exclusionQuantum hfin hRH,
      quadraticWorkIncrement_tendsto_sourceMoment hfin⟩)
  · exact Or.inr (Or.inr ⟨hfin, quadraticWorkIncrement_tendsto_atTop_of_infinite hfin⟩)

end GaloisForLFunctions.ArithmeticIndexDescent

#print axioms GaloisForLFunctions.ArithmeticIndexDescent.dampedSourceWork_eq_finite_offLine_sum
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.quadraticWorkIncrement_tendsto_sourceMoment
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.three_heightSquare_lt_finiteSourceMoment
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.eventually_bounded_quadraticIncrement_iff
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.quadratic_source_rate_trichotomy
