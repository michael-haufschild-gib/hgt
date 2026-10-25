import GaloisForLFunctions.BezoutValuationIncidence.VaughanAdmissionAboveHalfDamping
import GaloisForLFunctions.BezoutValuationIncidence.PositiveFloorMajorantsControlPronicEnergy
import GaloisForLFunctions.BezoutValuationIncidence.MovingVaughanRowsConvergeCellByCell
import GaloisForLFunctions.HTGeometry.MovingTruncationsPreserveDominatedLimits

/-!
Above half damping a positive floor majorant controls all Vaughan rows by one
summable square envelope. Independent cutoff and horizon limits therefore
recover the actual infinite Gram and convergence in pronic norm.
-/

open Finset Filter RHTower
open GaloisForLFunctions.TransHorizonIncidenceMechanics
open GaloisForLFunctions.BiScaleUncertainty
open scoped BigOperators Topology
noncomputable section
namespace GaloisForLFunctions.BezoutValuationIncidence
set_option autoImplicit false

/-- A common positive envelope for the five centered rows above half damping. -/
def pmPronicVaughanUpperEnvelope (ε : ℝ) (n : ℕ) : ℝ :=
  4 * |weightCenteredPrefix (pmVaughanFloorMajorant ε)
    (∑' d : ℕ, pmVaughanFloorMajorant ε d / d) n| + 1

/-- The positive floor-majorant envelope has a finite pronic norm independent of the horizon. -/
theorem pronicNorm_pmPronicVaughanUpperEnvelope_le {ε : ℝ} (hε : 1 / 2 < ε) (T : ℕ) :
    pronicNorm (pmPronicVaughanUpperEnvelope ε) T ≤
      4 * ((Real.sqrt 2 + 1) * pmVaughanFloorMass (ε - 1 / 2)) + 1 := by
  let W : ℕ → ℝ := weightCenteredPrefix (pmVaughanFloorMajorant ε)
    (∑' d : ℕ, pmVaughanFloorMajorant ε d / d)
  have hW : pronicNorm W T ≤ (Real.sqrt 2 + 1) * pmVaughanFloorMass (ε - 1 / 2) :=
    pronicNorm_weightCenteredPrefix_le_vaughan_floor_majorant hε
      (fun d => (abs_of_nonneg (pmVaughanFloorMajorant_nonneg ε d)).le) T
  have hnorm : pronicNorm (fun n => |W n|) T = pronicNorm W T := by
    simp only [pronicNorm, sq_abs]
  have h1 : pronicNorm (fun _ : ℕ => (1 : ℝ)) T ≤ 1 :=
    pronicNorm_le_of_abs_le zero_le_one (fun _ => by rw [abs_one]) T
  change pronicNorm (fun n => 4 * |W n| + 1) T ≤ _
  have h := pronicNorm_add_le (fun n => 4 * |W n|) (fun _ => 1) T
  rw [pronicNorm_smul 4 (fun n => |W n|) T,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4), hnorm] at h
  exact h.trans (add_le_add (mul_le_mul_of_nonneg_left hW (by norm_num)) h1)

private theorem upper_dampedSign_majorized {ε : ℝ} (hε : 0 < ε)
    {r : ℕ → ℝ} (hr : ∀ d, |r d| ≤ 1) (d : ℕ) :
    |dampedSignWeight r ε d| ≤ pmVaughanFloorMajorant ε d := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp [dampedSignWeight, pmVaughanFloorMajorant, Real.zero_rpow (neg_ne_zero.mpr hε.ne')]
  · have hc : (1 : ℝ) ≤ d.divisors.card := by
      exact_mod_cast (one_le_card.mpr ⟨1, Nat.mem_divisors.mpr ⟨one_dvd d, hd.ne'⟩⟩)
    have hc2 : (1 : ℝ) ≤ (d.divisors.card : ℝ) ^ 2 := by nlinarith only [hc]
    rw [dampedSignWeight, abs_mul, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg d) _)]
    exact mul_le_mul_of_nonneg_right ((hr d).trans hc2) (Real.rpow_nonneg (Nat.cast_nonneg d) _)

/-- The same positive envelope dominates every centered Vaughan row at every positive cell. -/
theorem abs_pmPronicVaughanCentredPiece_le_upperEnvelope {ε : ℝ} (hε : 1 / 2 < ε)
    (U V : ℕ) {n : ℕ} (hn : 1 ≤ n) (i : Fin 5) :
    |pmPronicVaughanCentredPiece ε U V n i| ≤ pmPronicVaughanUpperEnvelope ε n := by
  have hε0 : 0 < ε := by linarith only [hε]
  let E : ℝ := |weightCenteredPrefix (pmVaughanFloorMajorant ε)
    (∑' d : ℕ, pmVaughanFloorMajorant ε d / d) n|
  let e : Fin 5 → ℝ := fun j => pmPronicVaughanCentredPiece ε U V n j
  have hE : 0 ≤ E := abs_nonneg _
  have hpattern (r : ℕ → ℝ) (hr : ∀ d, |r d| ≤ 1) : |patternPrefix ε r n| ≤ E :=
    abs_weightCenteredPrefix_le_abs_majorant (summable_pmVaughanFloorMajorant_div hε0)
      (upper_dampedSign_majorized hε0 hr) hn
  have h0 : |e 0| ≤ E := by
    have h := hpattern (Sieve.truncatedMoebius U) (fun d => by
      simpa only [Real.norm_eq_abs] using Sieve.norm_truncatedMoebius_le_one U d)
    simpa only [e, pmPronicVaughanCentredPiece,
      pmPronicVaughanPiece_small_sub_mean_eq_patternPrefix hε0] using h
  have h1 : |e 1| ≤ E := by
    change |pmPronicVaughanCentredPiece ε V U n 0| ≤ E
    have h := hpattern (Sieve.truncatedMoebius V) (fun d => by
      simpa only [Real.norm_eq_abs] using Sieve.norm_truncatedMoebius_le_one V d)
    simpa only [pmPronicVaughanCentredPiece,
      pmPronicVaughanPiece_small_sub_mean_eq_patternPrefix hε0] using h
  have h2 : |e 2| ≤ E := by
    dsimp only [e]
    rw [pmPronicVaughanCentredPiece_smallSmall_eq_prefix hε0, abs_neg]
    apply abs_weightCenteredPrefix_le_abs_majorant (summable_pmVaughanFloorMajorant_div hε0) _ hn
    intro d
    rw [dampedSignWeight, abs_mul, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg d) _)]
    exact mul_le_mul_of_nonneg_right (abs_pmPronicVaughanSmallSmallCoeff_le U V d)
      (Real.rpow_nonneg (Nat.cast_nonneg d) _)
  have h4 : |e 4| ≤ 1 / 2 := by
    simpa only [e, pmPronicVaughanCentredPiece] using
      abs_pmPronicVaughanPiece_pole_sub_mean_le hε0.le U V n
  have hI : |pmBezoutInteriorPrefix ε n| ≤ E + 1 / 2 := by
    have hA : |pmPowerDampedCenteredDivisorPrefix ε n| ≤ E := by
      rw [← patternPrefix_moebius_eq_centeredDivisorPrefix hε0]
      exact hpattern moebiusReal abs_moebiusReal_le_one'
    have heq : pmBezoutInteriorPrefix ε n = pmPowerDampedCenteredDivisorPrefix ε n +
        (-addDiff (pmActiveSawtoothComponent ε) n) := by
      rw [pmPowerDampedCenteredDivisorPrefix_eq_bezout_active_pair_add_interior]
      ring
    rw [heq]
    exact (abs_add_le _ _).trans (add_le_add hA (by
      simpa only [abs_neg] using abs_addDiff_pmActiveSawtoothComponent_le_half hε0.le n))
  have h3 : |e 3| ≤ 4 * E + 1 := by
    have hs : (∑ j : Fin 5, e j) = pmBezoutInteriorPrefix ε n := by
      simp only [e, pmPronicVaughanCentredPiece, sum_sub_distrib, ← sum_mul,
        sum_pmPronicVaughanPiece, sum_pmPronicVaughanMean, zero_mul, sub_zero]
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hs
    change e 0 + (e 1 + (e 2 + (e 3 + e 4))) = pmBezoutInteriorPrefix ε n at hs
    have heq : e 3 = pmBezoutInteriorPrefix ε n - (e 0 + (e 1 + (e 2 + e 4))) := by
      linarith only [hs]
    rw [heq]
    calc
      _ ≤ |pmBezoutInteriorPrefix ε n| + |e 0 + (e 1 + (e 2 + e 4))| := by
        simpa only [sub_eq_add_neg, abs_neg] using
          abs_add_le (pmBezoutInteriorPrefix ε n) (-(e 0 + (e 1 + (e 2 + e 4))))
      _ ≤ |pmBezoutInteriorPrefix ε n| + (|e 0| + (|e 1| + (|e 2| + |e 4|))) :=
        add_le_add le_rfl ((abs_add_le _ _).trans (add_le_add le_rfl
          ((abs_add_le _ _).trans (add_le_add le_rfl (abs_add_le _ _)))))
      _ ≤ _ := by linarith only [hI, h0, h1, h2, h4]
  change |e i| ≤ 4 * E + 1
  fin_cases i
  · exact h0.trans (by linarith only [hE])
  · exact h1.trans (by linarith only [hE])
  · exact h2.trans (by linarith only [hE])
  · exact h3
  · exact h4.trans (by linarith only [hE])

/-- One summable square-cell envelope controls all upper-half centered Vaughan rows. -/
theorem exists_summable_pmPronicVaughanCentredPiece_upper_square_envelope
    {ε : ℝ} (hε : 1 / 2 < ε) :
    ∃ g : ℕ → ℝ, Summable g ∧ (∀ n, 0 ≤ g n) ∧ ∀ U V n : ℕ, ∀ i : Fin 5,
      pmPronicVaughanCentredPiece ε U V n i ^ 2 / (pronicSeq n : ℝ) ≤ g n := by
  let g : ℕ → ℝ := fun n => pmPronicVaughanUpperEnvelope ε n ^ 2 / (pronicSeq n : ℝ)
  have hg : Summable g := summable_sq_div_pronicSeq_of_pronicNorm_bound
    ⟨_, pronicNorm_pmPronicVaughanUpperEnvelope_le hε⟩
  refine ⟨g, hg, fun n => by dsimp only [g]; positivity, fun U V n i => ?_⟩
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [g, pronicSeq, Nat.cast_zero, zero_mul, div_zero, le_refl]
  · have hs := pow_le_pow_left₀ (abs_nonneg _)
      (abs_pmPronicVaughanCentredPiece_le_upperEnvelope hε U V hn i) 2
    rw [sq_abs] at hs
    exact div_le_div_of_nonneg_right hs (Nat.cast_nonneg _)

/-- Every upper-half centered pairing has one common absolutely summable envelope. -/
theorem exists_summable_pmPronicVaughanCentredPiece_upper_pair_envelope
    {ε : ℝ} (hε : 1 / 2 < ε) :
    ∃ g : ℕ → ℝ, Summable g ∧ (∀ n, 0 ≤ g n) ∧ ∀ U V n : ℕ, ∀ i j : Fin 5,
      |pmPronicVaughanCentredPiece ε U V n i * pmPronicVaughanCentredPiece ε U V n j /
        (pronicSeq n : ℝ)| ≤ g n := by
  obtain ⟨g, hg, hg0, hbound⟩ := exists_summable_pmPronicVaughanCentredPiece_upper_square_envelope hε
  exact ⟨g, hg, hg0, fun U V n i j =>
    abs_pair_div_le_common_square_bound (Nat.cast_nonneg _) (hbound U V n i) (hbound U V n j)⟩

/-- The actual upper-half limiting frame has absolutely summable pronic pairings. -/
theorem summable_pmPronicVaughanLimitGram_terms_of_half_lt
    {ε : ℝ} (hε : 1 / 2 < ε) (i j : Fin 5) :
    Summable (fun n : ℕ => pmPronicVaughanLimitFrame ε i n *
      pmPronicVaughanLimitFrame ε j n / (pronicSeq n : ℝ)) := by
  obtain ⟨g, hg, _hg0, hbound⟩ := exists_summable_pmPronicVaughanCentredPiece_upper_pair_envelope hε
  apply hg.of_norm_bounded
  intro n
  rw [Real.norm_eq_abs]
  have hε0 : 0 < ε := by linarith only [hε]
  have hp := ((tendsto_pmPronicVaughanCentredPiece_moving_cell hε0 tendsto_id tendsto_id n i).mul
    (tendsto_pmPronicVaughanCentredPiece_moving_cell hε0 tendsto_id tendsto_id n j)).div_const (pronicSeq n : ℝ)
  exact le_of_tendsto' hp.abs (fun t => hbound t t n i j)

/-- Independent divergence of both cutoffs and the horizon gives a unique actual upper-half Gram limit. -/
theorem tendsto_pmPronicVaughanCentredGram_of_half_lt
    {ε : ℝ} (hε : 1 / 2 < ε) {H U V : ℕ → ℕ}
    (hH : Tendsto H atTop atTop) (hU : Tendsto U atTop atTop) (hV : Tendsto V atTop atTop)
    (i j : Fin 5) :
    Tendsto (fun t => pmPronicVaughanCentredGram ε (U t) (V t) (H t) i j)
      atTop (𝓝 (pmPronicVaughanLimitGram ε i j)) := by
  obtain ⟨g, hg, hg0, hbound⟩ := exists_summable_pmPronicVaughanCentredPiece_upper_pair_envelope hε
  apply HTGeometry.tendsto_sum_Icc_at_moving_horizon_of_summable_bound hH hg hg0
    (by simp only [pronicSeq, Nat.cast_zero, zero_mul, div_zero])
    (fun t n => hbound (U t) (V t) n i j)
  intro n
  have hε0 : 0 < ε := by linarith only [hε]
  exact ((tendsto_pmPronicVaughanCentredPiece_moving_cell hε0 hU hV n i).mul
    (tendsto_pmPronicVaughanCentredPiece_moving_cell hε0 hU hV n j)).div_const (pronicSeq n : ℝ)

/-- Above half damping the centered rows converge in the full infinite pronic square norm. -/
theorem tendsto_tsum_pmPronicVaughanCentredPiece_sub_limit_sq_of_half_lt
    {ε : ℝ} (hε : 1 / 2 < ε) {U V : ℕ → ℕ}
    (hU : Tendsto U atTop atTop) (hV : Tendsto V atTop atTop) (i : Fin 5) :
    Tendsto (fun t => ∑' n : ℕ,
      (pmPronicVaughanCentredPiece ε (U t) (V t) n i - pmPronicVaughanLimitFrame ε i n) ^ 2 /
        (pronicSeq n : ℝ)) atTop (𝓝 0) := by
  obtain ⟨g, hg, _hg0, hbound⟩ := exists_summable_pmPronicVaughanCentredPiece_upper_square_envelope hε
  exact tendsto_tsum_pronic_square_sub_of_summable_envelope hg
    (fun n => tendsto_pmPronicVaughanCentredPiece_moving_cell (by linarith only [hε]) hU hV n i)
    (fun t n => hbound (U t) (V t) n i)

/-- The strong upper-half row limit holds at every moving finite horizon, including bounded ones. -/
theorem tendsto_pronicNorm_pmPronicVaughanCentredPiece_sub_limit_of_half_lt
    {ε : ℝ} (hε : 1 / 2 < ε) {U V : ℕ → ℕ}
    (hU : Tendsto U atTop atTop) (hV : Tendsto V atTop atTop) (H : ℕ → ℕ) (i : Fin 5) :
    Tendsto (fun t => pronicNorm (fun n => pmPronicVaughanCentredPiece ε (U t) (V t) n i -
      pmPronicVaughanLimitFrame ε i n) (H t)) atTop (𝓝 0) := by
  obtain ⟨g, hg, _hg0, hbound⟩ := exists_summable_pmPronicVaughanCentredPiece_upper_square_envelope hε
  exact tendsto_pronicNorm_sub_at_moving_horizon_of_summable_envelope hg
    (fun n => tendsto_pmPronicVaughanCentredPiece_moving_cell (by linarith only [hε]) hU hV n i)
    (fun t n => hbound (U t) (V t) n i) H

#print axioms pronicNorm_pmPronicVaughanUpperEnvelope_le
#print axioms abs_pmPronicVaughanCentredPiece_le_upperEnvelope
#print axioms exists_summable_pmPronicVaughanCentredPiece_upper_square_envelope
#print axioms exists_summable_pmPronicVaughanCentredPiece_upper_pair_envelope
#print axioms summable_pmPronicVaughanLimitGram_terms_of_half_lt
#print axioms tendsto_pmPronicVaughanCentredGram_of_half_lt
#print axioms tendsto_tsum_pmPronicVaughanCentredPiece_sub_limit_sq_of_half_lt
#print axioms tendsto_pronicNorm_pmPronicVaughanCentredPiece_sub_limit_of_half_lt
end GaloisForLFunctions.BezoutValuationIncidence
