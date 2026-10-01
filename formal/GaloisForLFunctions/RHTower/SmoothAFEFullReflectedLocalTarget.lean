import GaloisForLFunctions.RHTower.SmoothAFEReflectedWindowLocalTargetEvent
import GaloisForLFunctions.RHTower.SmoothAFEFullReflectedCubicTail
import GaloisForLFunctions.RHTower.SteinhausSquareScaleWindowSeam

open MeasureTheory Filter Finset
open scoped Topology
noncomputable section
namespace RHTower
open SteinhausModel

/-- The full reflected-primal series at finitely many common-height nodes. -/
def steinhausHilbertFullReflectedCarrier {J : ℕ} (d b : Fin J → ℝ)
    (tau : ℝ) (N : ℕ) (ω : Omega) : EuclideanSpace ℂ (Fin J) :=
  WithLp.toLp 2 (fun j => steinhausFullReflectedPrimalCarrier (d j) (tau + b j) N ω)

/-- The full finite-node reflected carrier is uniformly approximated at square smoothing
by the literal cubic-cutoff carrier, pointwise for every phase assignment. -/
theorem eventually_norm_fullReflectedCarrier_sub_cubic_le
    {J : ℕ} (d b : Fin J → ℝ) (hd : ∀ j, 0 < d j) (hdhalf : ∀ j, d j < 1 / 2)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      ∀ tau ∈ Set.Icc ((5 / 4 : ℝ) * (n ^ 2 : ℕ)) ((7 / 4 : ℝ) * (n ^ 2 : ℕ)),
      ∀ ω : Omega,
        ‖steinhausHilbertFullReflectedCarrier d b tau (n ^ 2) ω -
          steinhausHilbertCarrier
            (fun j => smoothAFEZetaRightReflectedPrimalPositiveCoefficient
              (d j) (tau + b j) 1 (n ^ 2)) (n ^ 3) ω‖ ≤ ε := by
  choose C hC htail using fun j =>
    exists_fullReflectedPrimal_cubic_tail_le (hd j) (hdhalf j) (by norm_num : (0 : ℝ) < 1)
  have hε' : 0 < ε / (J + 1 : ℝ) := div_pos hε (by positivity)
  have hsmall : ∀ᶠ n : ℕ in atTop, ∀ j, C j / n ≤ ε / (J + 1 : ℝ) := by
    apply Filter.eventually_all.mpr
    intro j
    have hlim : Tendsto (fun n : ℕ => C j / n) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    exact (hlim.eventually (gt_mem_nhds hε')).mono (fun _ h => h.le)
  have hoffset : ∀ᶠ n : ℕ in atTop, ∀ j, 4 * |b j| ≤ (n : ℝ) := by
    apply Filter.eventually_all.mpr
    intro j
    exact (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).eventually
      (eventually_ge_atTop (4 * |b j|))
  filter_upwards [hsmall, hoffset, eventually_ge_atTop 1] with n hsmalln hbn hn
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn2 : (n : ℝ) ≤ ((n ^ 2 : ℕ) : ℝ) := by
    simp only [Nat.cast_pow]
    nlinarith
  intro tau htau ω
  have hcoord (j : Fin J) :
      ‖steinhausFullReflectedPrimalCarrier (d j) (tau + b j) (n ^ 2) ω -
        ∑ m ∈ Icc 1 (n ^ 3), smoothAFEZetaRightReflectedPrimalPositiveCoefficient
          (d j) (tau + b j) 1 (n ^ 2) m * X m ω‖ ≤ ε / (J + 1 : ℝ) := by
    have ht : ((n ^ 2 : ℕ) : ℝ) ≤ tau + b j := by
      have hb := (hbn j).trans hn2
      linarith [htau.1, neg_abs_le (b j)]
    have h := htail j n (by omega) (tau + b j) ht ω
    rw [Real.rpow_neg_one, ← div_eq_mul_inv] at h
    exact h.trans (hsmalln j)
  have hsq :
      ‖steinhausHilbertFullReflectedCarrier d b tau (n ^ 2) ω -
        steinhausHilbertCarrier
          (fun j => smoothAFEZetaRightReflectedPrimalPositiveCoefficient
            (d j) (tau + b j) 1 (n ^ 2)) (n ^ 3) ω‖ ^ 2 ≤
      (J : ℝ) * (ε / (J + 1 : ℝ)) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    calc
      _ ≤ ∑ _j : Fin J, (ε / (J + 1 : ℝ)) ^ 2 := by
        apply Finset.sum_le_sum
        intro j _
        exact pow_le_pow_left₀ (norm_nonneg _) (hcoord j) 2
      _ = _ := by simp
  have hJ : (0 : ℝ) ≤ J := Nat.cast_nonneg J
  have hbudget : (J : ℝ) * (ε / (J + 1 : ℝ)) ^ 2 ≤ ε ^ 2 := by
    rw [div_pow, ← mul_div_assoc, div_le_iff₀ (by positivity : (0 : ℝ) < (J + 1) ^ 2)]
    have hj : (J : ℝ) ≤ (J + 1 : ℝ) ^ 2 := by nlinarith [sq_nonneg (J : ℝ)]
    nlinarith [mul_le_mul_of_nonneg_left hj (sq_nonneg ε)]
  nlinarith [norm_nonneg (steinhausHilbertFullReflectedCarrier d b tau (n ^ 2) ω -
    steinhausHilbertCarrier
      (fun j => smoothAFEZetaRightReflectedPrimalPositiveCoefficient
        (d j) (tau + b j) 1 (n ^ 2)) (n ^ 3) ω)]

/-- The literal full reflected-primal carrier realizes all bounded finite-node targets
inside every prescribed finite phase cell, with arbitrarily small power loss in smoothing.
This is an original product-measure event, not a deterministic vertical-flow count. -/
theorem exists_fullReflectedCarrier_prescribedPhase_localTarget
    {J : ℕ} (hJ : 0 < J) (d b : Fin J → ℝ)
    (hd : ∀ j, 0 < d j) (hdhalf : ∀ j, d j < 1 / 2)
    (hinj : Function.Injective (fun j => rightDisplacedLinePt (d j) (b j)))
    (P : ℕ) (ω : Omega) {δ M ε ρ : ℝ}
    (hδ : 0 < δ) (hM : 0 ≤ M) (hε : 0 < ε) (hρ : 0 < ρ) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop,
      ∀ tau ∈ Set.Icc ((5 / 4 : ℝ) * (n ^ 2 : ℕ)) ((7 / 4 : ℝ) * (n ^ 2 : ℕ)),
      ∀ t : EuclideanSpace ℂ (Fin J), ‖t‖ ≤ M →
        c * ((n ^ 2 : ℕ) : ℝ) ^ (-ε) ≤ steinhausMeasure.real
          (steinhausCharacterCell P (steinhausLogPhaseShift ω (-tau)) δ ∩
            {η | ‖steinhausHilbertFullReflectedCarrier d b tau (n ^ 2) η - t‖ < ρ}) := by
  obtain ⟨K, D, c, hK, hc, hfinite⟩ :=
    exists_reflectedWindowCarrier_prescribedPhase_localTarget hJ d b hd hdhalf hinj
      P ω hδ hM hε (half_pos hρ)
  have hscale : Tendsto (fun n : ℕ => n ^ 2) atTop atTop :=
    Filter.tendsto_pow_atTop (by decide)
  refine ⟨c, hc, ?_⟩
  filter_upwards [hscale.eventually hfinite,
    eventually_squareScale_cubicCutoff_freeWindow_seam hK P D,
    eventually_norm_fullReflectedCarrier_sub_cubic_le d b hd hdhalf (half_pos hρ)]
    with n hfiniteN hseam htailN
  intro tau htau t ht
  have hLY : n ^ 3 < (n ^ 2 / (2 * K)) * (n ^ 2 / (2 * K)) := by
    simpa only [pow_two] using hseam.2.2.2.2
  refine (hfiniteN (n ^ 3) hseam.2.1 hseam.2.2.1 hLY tau htau t ht).trans
    (measureReal_mono ?_)
  intro η hη
  refine ⟨hη.1, ?_⟩
  have hnorm := norm_add_le
    (steinhausHilbertFullReflectedCarrier d b tau (n ^ 2) η -
      steinhausHilbertCarrier
        (fun j => smoothAFEZetaRightReflectedPrimalPositiveCoefficient
          (d j) (tau + b j) 1 (n ^ 2)) (n ^ 3) η)
    (steinhausHilbertCarrier
        (fun j => smoothAFEZetaRightReflectedPrimalPositiveCoefficient
          (d j) (tau + b j) 1 (n ^ 2)) (n ^ 3) η - t)
  rw [sub_add_sub_cancel] at hnorm
  have htail := htailN tau htau η
  have htarget : ‖steinhausHilbertCarrier
      (fun j => smoothAFEZetaRightReflectedPrimalPositiveCoefficient
        (d j) (tau + b j) 1 (n ^ 2)) (n ^ 3) η - t‖ < ρ / 2 := hη.2
  change ‖steinhausHilbertFullReflectedCarrier d b tau (n ^ 2) η - t‖ < ρ
  linarith

end RHTower
