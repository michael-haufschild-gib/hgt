import GaloisForLFunctions.BezoutValuationIncidence.TheRanksOfSubcriticalVaughanLimits
import GaloisForLFunctions.BezoutValuationIncidence.TheOnlyAccumulationOfVaughanAmplitudesIsZero

/-!
The actual subcritical matrix limit family is compact and countably infinite,
with zero as its unique accumulation point. Its amplitude is continuously
recoverable from one diagonal entry; scalar normalization removes damping.
-/

open Finset Filter RHTower
open GaloisForLFunctions.TransHorizonIncidenceMechanics
open scoped BigOperators Topology
noncomputable section
namespace GaloisForLFunctions.BezoutValuationIncidence
set_option autoImplicit false

/-- The arithmetic family of all subcritical normalized Vaughan Gram limits. -/
def pmVaughanSmoothLimitSet (ε : ℝ) : Set (Matrix (Fin 5) (Fin 5) ℝ) :=
  pmVaughanSmoothLimitMatrix ε '' pmVaughanSmoothAmplitudeSet

private theorem smooth_matrix_diagonal (ε a : ℝ) :
    pmVaughanSmoothLimitMatrix ε a 2 2 = subHalfZetaCoeff ε ^ 2 / (1 - 2 * ε) * a := by
  change subHalfZetaCoeff ε ^ 2 / (1 - 2 * ε) * a * (-1) * (-1) = _
  ring

/-- The smooth matrix depends continuously on its scalar amplitude. -/
theorem continuous_pmVaughanSmoothLimitMatrix (ε : ℝ) :
    Continuous (pmVaughanSmoothLimitMatrix ε) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  exact ((continuous_id.const_mul (subHalfZetaCoeff ε ^ 2 / (1 - 2 * ε))).mul_const
    (pmPronicVaughanSmoothSigns i)).mul_const (pmPronicVaughanSmoothSigns j)

/-- The convolution diagonal recovers the amplitude uniquely below half damping. -/
theorem pmVaughanSmoothLimitMatrix_injective {ε : ℝ}
    (hε : 0 < ε) (hε2 : ε < 1 / 2) : Function.Injective (pmVaughanSmoothLimitMatrix ε) := by
  have hk : 0 < subHalfZetaCoeff ε ^ 2 / (1 - 2 * ε) :=
    div_pos (sq_pos_of_ne_zero (subHalfZetaCoeff_ne_zero hε (by linarith only [hε2])))
      (by linarith only [hε2])
  intro a b hab
  have h := congrArg (fun M : Matrix (Fin 5) (Fin 5) ℝ => M 2 2) hab
  rw [smooth_matrix_diagonal, smooth_matrix_diagonal] at h
  exact mul_left_cancel₀ hk.ne' h

/-- The full matrix limit family is compact. -/
theorem isCompact_pmVaughanSmoothLimitSet (ε : ℝ) : IsCompact (pmVaughanSmoothLimitSet ε) :=
  isCompact_pmVaughanSmoothAmplitudeSet.image (continuous_pmVaughanSmoothLimitMatrix ε)

/-- The full matrix limit family is countable. -/
theorem countable_pmVaughanSmoothLimitSet (ε : ℝ) : (pmVaughanSmoothLimitSet ε).Countable :=
  countable_pmVaughanSmoothAmplitudeSet.image _

/-- Infinitely many distinct arithmetic matrices occur below half damping. -/
theorem infinite_pmVaughanSmoothLimitSet {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2) :
    (pmVaughanSmoothLimitSet ε).Infinite :=
  (Set.infinite_image_iff (pmVaughanSmoothLimitMatrix_injective hε hε2).injOn).mpr
    infinite_pmVaughanSmoothAmplitudeSet

/-- Zero is the unique accumulation point of the actual subcritical matrix limit family. -/
theorem accPt_pmVaughanSmoothLimitSet_iff {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2)
    (L : Matrix (Fin 5) (Fin 5) ℝ) :
    AccPt L (𝓟 (pmVaughanSmoothLimitSet ε)) ↔ L = 0 := by
  constructor
  · intro hacc
    have hL : L ∈ pmVaughanSmoothLimitSet ε := by
      by_contra hnot
      obtain ⟨M, hM, _⟩ := accPt_iff_nhds.mp hacc (pmVaughanSmoothLimitSet ε)ᶜ
        ((isCompact_pmVaughanSmoothLimitSet ε).isClosed.isOpen_compl.mem_nhds hnot)
      exact hM.1 hM.2
    obtain ⟨a, ha, rfl⟩ := hL
    by_cases ha0 : a = 0
    · rw [ha0, pmVaughanSmoothLimitMatrix_zero]
    · exfalso
      have hapos : 0 < a := lt_of_le_of_ne (pmVaughanSmoothAmplitudeSet_nonneg ha) (Ne.symm ha0)
      obtain ⟨δ, hδ, hisolated⟩ := isolated_pmVaughanSmoothAmplitude_of_pos hapos
      let k : ℝ := subHalfZetaCoeff ε ^ 2 / (1 - 2 * ε)
      have hk : 0 < k := div_pos
        (sq_pos_of_ne_zero (subHalfZetaCoeff_ne_zero hε (by linarith only [hε2])))
        (by linarith only [hε2])
      let recover : Matrix (Fin 5) (Fin 5) ℝ → ℝ := fun M => M 2 2 / k
      have hrecover (b : ℝ) : recover (pmVaughanSmoothLimitMatrix ε b) = b := by
        dsimp only [recover]
        rw [smooth_matrix_diagonal]
        change k * b / k = b
        field_simp [hk.ne']
      have hcontinuous : Continuous recover := by
        have hrow : Continuous (fun M : Matrix (Fin 5) (Fin 5) ℝ => M 2) := continuous_apply 2
        have hentry : Continuous (fun v : Fin 5 → ℝ => v 2) := continuous_apply 2
        exact (hentry.comp hrow).div_const k
      have hlocal : Tendsto (fun M => |recover M - a|)
          (𝓝 (pmVaughanSmoothLimitMatrix ε a)) (𝓝 0) := by
        simpa only [hrecover, sub_self, abs_zero] using
          ((hcontinuous.tendsto (pmVaughanSmoothLimitMatrix ε a)).sub_const a).abs
      obtain ⟨M, ⟨hnear, hM⟩, hne⟩ := accPt_iff_nhds.mp hacc
        {M | |recover M - a| < δ} (hlocal.eventually (gt_mem_nhds hδ))
      obtain ⟨b, hb, rfl⟩ := hM
      rw [hrecover] at hnear
      exact hne (congrArg (pmVaughanSmoothLimitMatrix ε) (hisolated b hb hnear))
  · rintro rfl
    apply accPt_iff_nhds.mpr
    intro U hU
    have hpre : {a : ℝ | pmVaughanSmoothLimitMatrix ε a ∈ U} ∈ 𝓝 (0 : ℝ) :=
      ((continuous_pmVaughanSmoothLimitMatrix ε).tendsto 0).eventually
        (by simpa only [pmVaughanSmoothLimitMatrix_zero] using hU)
    obtain ⟨a, ⟨hUa, ha⟩, hane⟩ := accPt_iff_nhds.mp
      ((accPt_pmVaughanSmoothAmplitudeSet_iff 0).mpr rfl) _ hpre
    refine ⟨pmVaughanSmoothLimitMatrix ε a, ⟨hUa, ⟨a, ha, rfl⟩⟩, ?_⟩
    intro hzero
    apply hane
    apply pmVaughanSmoothLimitMatrix_injective hε hε2
    simpa only [pmVaughanSmoothLimitMatrix_zero] using hzero

/-- Membership in the compact matrix family is exactly attainment with positive moving cutoffs. -/
theorem mem_pmVaughanSmoothLimitSet_iff {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2)
    (H : ℕ → ℕ) (hH : Tendsto H atTop atTop) (L : Matrix (Fin 5) (Fin 5) ℝ) :
    L ∈ pmVaughanSmoothLimitSet ε ↔
      ∃ U V : ℕ → ℕ, (∀ t, 1 ≤ U t) ∧ (∀ t, 1 ≤ V t) ∧ ∀ i j,
        Tendsto (fun t => pmPronicVaughanCentredGram ε (U t) (V t) (H t) i j /
          (H t : ℝ) ^ (1 - 2 * ε)) atTop (𝓝 (L i j)) := by
  rw [pmPronicVaughanCentredGram_limit_set_eq hε hε2 H hH L]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, ha, fun _ _ => rfl⟩
  · rintro ⟨a, ha, hL⟩
    exact ⟨a, ha, funext fun i => funext fun j => (hL i j).symm⟩

/-- Allowing zero cutoffs leaves exactly the same family of finite matrix limits. -/
theorem mem_pmVaughanSmoothLimitSet_iff_arbitrary_cutoffs
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2)
    (H : ℕ → ℕ) (hH : Tendsto H atTop atTop) (L : Matrix (Fin 5) (Fin 5) ℝ) :
    L ∈ pmVaughanSmoothLimitSet ε ↔
      ∃ U V : ℕ → ℕ, ∀ i j,
        Tendsto (fun t => pmPronicVaughanCentredGram ε (U t) (V t) (H t) i j /
          (H t : ℝ) ^ (1 - 2 * ε)) atTop (𝓝 (L i j)) := by
  constructor
  · intro hL
    obtain ⟨U, V, _hU, _hV, hG⟩ := (mem_pmVaughanSmoothLimitSet_iff hε hε2 H hH L).mp hL
    exact ⟨U, V, hG⟩
  · rintro ⟨U, V, hG⟩
    obtain ⟨a, ha, hL⟩ := exists_pmVaughanSmoothAmplitude_of_centredGram_limit
      hε hε2 H U V hH L hG
    exact ⟨a, ha, funext fun i => funext fun j => (hL i j).symm⟩

/-- Removing the positive damping coefficient makes the complete matrix limit set independent of damping. -/
theorem normalized_pmVaughanSmoothLimitSet_independent {ε κ : ℝ}
    (hε : 0 < ε) (hε2 : ε < 1 / 2) (hκ : 0 < κ) (hκ2 : κ < 1 / 2) :
    (fun L : Matrix (Fin 5) (Fin 5) ℝ => ((1 - 2 * ε) / subHalfZetaCoeff ε ^ 2) • L) ''
        pmVaughanSmoothLimitSet ε =
      (fun L : Matrix (Fin 5) (Fin 5) ℝ => ((1 - 2 * κ) / subHalfZetaCoeff κ ^ 2) • L) ''
        pmVaughanSmoothLimitSet κ := by
  have hnorm {δ : ℝ} (hδ : 0 < δ) (hδ2 : δ < 1 / 2) (a : ℝ) :
      ((1 - 2 * δ) / subHalfZetaCoeff δ ^ 2) • pmVaughanSmoothLimitMatrix δ a =
        fun i j => a * pmPronicVaughanSmoothSigns i * pmPronicVaughanSmoothSigns j := by
    have hc := subHalfZetaCoeff_ne_zero hδ (by linarith only [hδ2])
    have hβ : 1 - 2 * δ ≠ 0 := ne_of_gt (by linarith only [hδ2])
    funext i j
    change ((1 - 2 * δ) / subHalfZetaCoeff δ ^ 2) *
      (subHalfZetaCoeff δ ^ 2 / (1 - 2 * δ) * a *
        pmPronicVaughanSmoothSigns i * pmPronicVaughanSmoothSigns j) = _
    field_simp [hc, hβ] <;> ring
  ext L
  constructor
  · rintro ⟨M, ⟨a, ha, rfl⟩, rfl⟩
    refine ⟨pmVaughanSmoothLimitMatrix κ a, ⟨a, ha, rfl⟩, ?_⟩
    rw [hnorm hκ hκ2, hnorm hε hε2]
  · rintro ⟨M, ⟨a, ha, rfl⟩, rfl⟩
    refine ⟨pmVaughanSmoothLimitMatrix ε a, ⟨a, ha, rfl⟩, ?_⟩
    rw [hnorm hε hε2, hnorm hκ hκ2]

#print axioms continuous_pmVaughanSmoothLimitMatrix
#print axioms pmVaughanSmoothLimitMatrix_injective
#print axioms isCompact_pmVaughanSmoothLimitSet
#print axioms countable_pmVaughanSmoothLimitSet
#print axioms infinite_pmVaughanSmoothLimitSet
#print axioms accPt_pmVaughanSmoothLimitSet_iff
#print axioms mem_pmVaughanSmoothLimitSet_iff
#print axioms mem_pmVaughanSmoothLimitSet_iff_arbitrary_cutoffs
#print axioms normalized_pmVaughanSmoothLimitSet_independent
end GaloisForLFunctions.BezoutValuationIncidence
