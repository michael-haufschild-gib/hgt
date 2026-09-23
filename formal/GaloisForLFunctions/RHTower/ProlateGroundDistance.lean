import GaloisForLFunctions.RHTower.ProlateNegativeSectorLadder
import GaloisForLFunctions.RHTower.ConstrainedProlateFullDistanceCCM

/-!
# The exact constrained ground eigenvector of the true prolate family

Over a ladder envelope every structural, membership, summability, nonvanishing, alignment and tail
hypothesis of the full `ℓ²` distance theorem is available, so the exact constrained ground vector of
the true signed prolate family converges in `ℓ²`, up to sign, to the two-mode seed built from its
own first two constraint coordinates.
-/

noncomputable section

open Set Filter Topology

namespace RHTower

section LadderDistance

variable {D : ℝ → ℕ → ℝ} {ℓ : ℝ → ℕ → ℝ}

theorem secularVector_zero_ne_zero {d l : ℕ → ℝ} {μ : ℝ} (hμ : μ ∈ Ioo (d 0) (d 1))
    (h0 : l 0 ≠ 0) : secularVector d l μ 0 ≠ 0 := by
  rw [secularVector]
  refine div_ne_zero h0 ?_
  intro hc
  have := hμ.1
  have h : d 0 = μ := by linarith [sub_eq_zero.mp hc]
  linarith

theorem LadderEnvelope.memℓp_secular (h : LadderEnvelope D)
    (hsum : ∀ᶠ lam in atTop, Summable fun j => ℓ lam j ^ (2 : ℕ))
    (h0 : ∀ᶠ lam in atTop, ℓ lam 0 ≠ 0) (h1 : ∀ᶠ lam in atTop, ℓ lam 1 ≠ 0) :
    ∀ᶠ lam in atTop, Memℓp (secularVector (D lam) (ℓ lam)
      (infiniteSecularRoot (D lam) (ℓ lam))) 2 := by
  filter_upwards [h.first_struct, hsum, h0, h1] with lam hst hsm hl0 hl1
  obtain ⟨⟨_, h01, h12⟩, hd2⟩ := hst
  exact memℓp_secularVector h01 h12 hd2 hsm hl0 hl1

theorem LadderEnvelope.summable_secular_sq (h : LadderEnvelope D)
    (hsum : ∀ᶠ lam in atTop, Summable fun j => ℓ lam j ^ (2 : ℕ))
    (h0 : ∀ᶠ lam in atTop, ℓ lam 0 ≠ 0) (h1 : ∀ᶠ lam in atTop, ℓ lam 1 ≠ 0) :
    ∀ᶠ lam in atTop, Summable fun j =>
      secularVector (D lam) (ℓ lam) (infiniteSecularRoot (D lam) (ℓ lam)) j ^ (2 : ℕ) := by
  filter_upwards [h.first_struct, hsum, h0, h1] with lam hst hsm hl0 hl1
  obtain ⟨⟨_, h01, h12⟩, hd2⟩ := hst
  obtain ⟨hrmem, _, _⟩ := infiniteSecularRoot_spec h01 h12 hd2 hsm hl0 hl1
  have hlt : infiniteSecularRoot (D lam) (ℓ lam) < D lam 2 := by linarith [hrmem.2]
  exact (summable_nat_add_iff
      (f := fun j => secularVector (D lam) (ℓ lam)
        (infiniteSecularRoot (D lam) (ℓ lam)) j ^ (2 : ℕ)) 2).mp
    (summable_secularVector_sq_tail hd2 hsm hlt)

theorem LadderEnvelope.secularVector_zero_ne_zero (h : LadderEnvelope D)
    (hsum : ∀ᶠ lam in atTop, Summable fun j => ℓ lam j ^ (2 : ℕ))
    (h0 : ∀ᶠ lam in atTop, ℓ lam 0 ≠ 0) (h1 : ∀ᶠ lam in atTop, ℓ lam 1 ≠ 0) :
    ∀ᶠ lam in atTop,
      secularVector (D lam) (ℓ lam) (infiniteSecularRoot (D lam) (ℓ lam)) 0 ≠ 0 := by
  filter_upwards [h.first_struct, hsum, h0, h1] with lam hst hsm hl0 hl1
  obtain ⟨⟨_, h01, h12⟩, hd2⟩ := hst
  obtain ⟨hrmem, _, _⟩ := infiniteSecularRoot_spec h01 h12 hd2 hsm hl0 hl1
  exact _root_.RHTower.secularVector_zero_ne_zero hrmem hl0

/-- **The exact constrained ground vector converges to the two-mode seed in `ℓ²`, over any ladder
envelope.** -/
theorem LadderEnvelope.tendsto_min_norm_ground_distance (h : LadderEnvelope D)
    {a0 a1 : ℝ} (ha0 : a0 ≠ 0) (ha1 : a1 ≠ 0)
    (hsum : ∀ᶠ lam in atTop, Summable fun j => ℓ lam j ^ (2 : ℕ))
    (hbessel : ∀ᶠ lam in atTop, (∑' j : ℕ, ℓ lam j ^ (2 : ℕ)) ≤ 2 * lam)
    (hl0 : Tendsto (fun lam => ℓ lam 0) atTop (nhds a0))
    (hl1 : Tendsto (fun lam => ℓ lam 1) atTop (nhds a1)) :
    Tendsto (fun lam => min
        (‖(‖secularLp (D lam) (ℓ lam) (infiniteSecularRoot (D lam) (ℓ lam))‖)⁻¹
            • secularLp (D lam) (ℓ lam) (infiniteSecularRoot (D lam) (ℓ lam))
          - (‖twoModeSeedLp (ℓ lam)‖)⁻¹ • twoModeSeedLp (ℓ lam)‖ ^ (2 : ℕ))
        (‖(‖secularLp (D lam) (ℓ lam) (infiniteSecularRoot (D lam) (ℓ lam))‖)⁻¹
            • secularLp (D lam) (ℓ lam) (infiniteSecularRoot (D lam) (ℓ lam))
          + (‖twoModeSeedLp (ℓ lam)‖)⁻¹ • twoModeSeedLp (ℓ lam)‖ ^ (2 : ℕ)))
      atTop (nhds 0) := by
  have h0 : ∀ᶠ lam in atTop, ℓ lam 0 ≠ 0 := hl0.eventually_ne ha0
  have h1 : ∀ᶠ lam in atTop, ℓ lam 1 ≠ 0 := hl1.eventually_ne ha1
  exact tendsto_min_norm_lp_normalize_sub_twoModeSeed
    (V := fun lam => secularLp (D lam) (ℓ lam) (infiniteSecularRoot (D lam) (ℓ lam)))
    (G := fun lam => twoModeSeedLp (ℓ lam))
    (D := D) (L := ℓ) (M := fun lam => infiniteSecularRoot (D lam) (ℓ lam))
    ((h.memℓp_secular hsum h0 h1).mono fun lam hm => secularLp_coeFn hm)
    (Eventually.of_forall fun lam => twoModeSeedLp_coeFn (ℓ lam))
    (h.summable_secular_sq hsum h0 h1)
    (h.secularVector_zero_ne_zero hsum h0 h1)
    h0
    (secularVector_head_seed_defect_tendsto_zero ha0 ha1 h.first_struct hsum hbessel
      (h.tail_tendsto_zero 0) hl0 hl1)
    (secularVector_tail_fraction_tendsto_zero ha0 ha1 h.first_struct hsum hbessel
      (h.tail_tendsto_zero 0) hl0 hl1)

end LadderDistance

/-- **Equation `(4)`, unconditionally.**  The exact constrained ground eigenvector of the true
signed prolate family converges in `ℓ²`, up to sign, to the normalized two-mode seed built from its
own first two constraint coordinates. -/
theorem constrainedProlateEven_ground_distance_tendsto_zero :
    let D : ℝ → ℕ → ℝ := fun a j => evenProlateSignedLeakage a (2 * j)
    let ℓ : ℝ → ℕ → ℝ := fun lam j => ‖evenProlateConstraintCoord lam (2 * j)‖
    Tendsto (fun lam : ℝ => min
        (‖(‖secularLp (D lam) (ℓ lam) (infiniteSecularRoot (D lam) (ℓ lam))‖)⁻¹
            • secularLp (D lam) (ℓ lam) (infiniteSecularRoot (D lam) (ℓ lam))
          - (‖twoModeSeedLp (ℓ lam)‖)⁻¹ • twoModeSeedLp (ℓ lam)‖ ^ (2 : ℕ))
        (‖(‖secularLp (D lam) (ℓ lam) (infiniteSecularRoot (D lam) (ℓ lam))‖)⁻¹
            • secularLp (D lam) (ℓ lam) (infiniteSecularRoot (D lam) (ℓ lam))
          + (‖twoModeSeedLp (ℓ lam)‖)⁻¹ • twoModeSeedLp (ℓ lam)‖ ^ (2 : ℕ)))
      atTop (nhds 0) := by
  refine ladderEnvelope_evenProlateSignedLeakage.tendsto_min_norm_ground_distance
    (constrainedProlateHermiteCoordinate_ne_zero 0)
    (constrainedProlateHermiteCoordinate_ne_zero 1)
    evenProlateLadder_sum evenProlateLadder_bessel ?_ ?_
  · exact tendsto_norm_evenProlateConstraintCoord_atTop 0
  · exact tendsto_norm_evenProlateConstraintCoord_atTop 1

/-- **The negative-sector ground eigenvector converges to its two-mode seed.**  The same statement
for the odd sublattice, whose Hermite limits are the modes `h_2` and `h_6`. -/
theorem constrainedProlateNegative_ground_distance_tendsto_zero :
    let D : ℝ → ℕ → ℝ := fun a j => evenProlateSignedLeakage a (2 * j + 1)
    let ℓ : ℝ → ℕ → ℝ := fun lam j => ‖evenProlateConstraintCoord lam (2 * j + 1)‖
    Tendsto (fun lam : ℝ => min
        (‖(‖secularLp (D lam) (ℓ lam) (infiniteSecularRoot (D lam) (ℓ lam))‖)⁻¹
            • secularLp (D lam) (ℓ lam) (infiniteSecularRoot (D lam) (ℓ lam))
          - (‖twoModeSeedLp (ℓ lam)‖)⁻¹ • twoModeSeedLp (ℓ lam)‖ ^ (2 : ℕ))
        (‖(‖secularLp (D lam) (ℓ lam) (infiniteSecularRoot (D lam) (ℓ lam))‖)⁻¹
            • secularLp (D lam) (ℓ lam) (infiniteSecularRoot (D lam) (ℓ lam))
          + (‖twoModeSeedLp (ℓ lam)‖)⁻¹ • twoModeSeedLp (ℓ lam)‖ ^ (2 : ℕ)))
      atTop (nhds 0) := by
  have ha0 : constrainedProlateNegativeCoordinate 0 ≠ 0 :=
    (constrainedProlateNegativeCoordinate_pos 0).ne'
  have ha1 : constrainedProlateNegativeCoordinate 1 ≠ 0 :=
    (constrainedProlateNegativeCoordinate_pos 1).ne'
  exact ladderEnvelope_evenProlateSignedLeakage_negative.tendsto_min_norm_ground_distance
    ha0 ha1 negativeSector_sum negativeSector_bessel
    (tendsto_norm_evenProlateConstraintCoord_negative_atTop 0)
    (tendsto_norm_evenProlateConstraintCoord_negative_atTop 1)

end RHTower

end
