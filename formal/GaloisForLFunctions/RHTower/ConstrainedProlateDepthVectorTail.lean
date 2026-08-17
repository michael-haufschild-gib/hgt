import GaloisForLFunctions.RHTower.ConstrainedProlateClockExactEigenpairLaw
import GaloisForLFunctions.RHTower.ConstrainedProlateSecularVector

/-!
# Tail collapse for every fixed constrained-Prolate depth

The ground-vector tail estimate starts at coordinate `2`.  A depth-`k` eigenvector instead has a
finite head through coordinate `k + 1`, so its tail starts at `k + 2`.  This module proves the
offset estimate and composes it with the exact root supplied by a `LadderEnvelope`.

No root-existence or tail hypothesis is added: the clock law supplies the genuine root in the
`k`-th gap, its next-gap separation, and the rate that drives the squared tail to zero.
-/

open Filter Set

noncomputable section

namespace RHTower

variable {d ℓ : ℕ → ℝ} {m : ℕ} {B μ : ℝ}

/-- Squared secular-vector coordinates from an arbitrary offset are summable below a uniform
spectral floor. -/
theorem summable_secularVector_sq_offset_tail
    (hB : ∀ j, B ≤ d (j + m)) (hsum : Summable fun j => ℓ j ^ 2) (hμ : μ < B) :
    Summable fun j : ℕ => secularVector d ℓ μ (j + m) ^ 2 := by
  have hsum' : Summable fun j : ℕ => ℓ (j + m) ^ 2 := (summable_nat_add_iff m).mpr hsum
  refine Summable.of_nonneg_of_le (fun j => sq_nonneg _) (fun j => ?_)
    (hsum'.div_const ((B - μ) ^ 2))
  unfold secularVector
  rw [div_pow]
  exact div_le_div_of_nonneg_left (sq_nonneg _) (pow_pos (by linarith) 2)
    (pow_le_pow_left₀ (by linarith) (by linarith [hB j]) 2)

/-- Uniform squared-tail bound from an arbitrary offset. -/
theorem secularVector_sq_offset_tail_le
    (hB : ∀ j, B ≤ d (j + m)) (hsum : Summable fun j => ℓ j ^ 2) (hμ : μ < B) :
    (∑' j : ℕ, secularVector d ℓ μ (j + m) ^ 2)
      ≤ (∑' j : ℕ, ℓ (j + m) ^ 2) / (B - μ) ^ 2 := by
  have hsum' : Summable fun j : ℕ => ℓ (j + m) ^ 2 := (summable_nat_add_iff m).mpr hsum
  rw [← tsum_div_const]
  refine Summable.tsum_le_tsum (fun j => ?_)
    (summable_secularVector_sq_offset_tail hB hsum hμ) (hsum'.div_const _)
  unfold secularVector
  rw [div_pow]
  exact div_le_div_of_nonneg_left (sq_nonneg _) (pow_pos (by linarith) 2)
    (pow_le_pow_left₀ (by linarith) (by linarith [hB j]) 2)

/-- **Every fixed-depth exact secular eigenvector is asymptotically supported on its first
`k + 2` coordinates.**  The tail is measured relative to the nonzero zeroth coordinate.

All infinite-dimensional inputs are discharged by the ladder envelope and Bessel hypotheses.  The
finite coordinate limits are the same named prolate-to-Hermite input consumed by the exact depth
root law. -/
theorem LadderEnvelope.ccm_depth_secularVector_tail_fraction_tendsto_zero
    {D : ℝ → ℕ → ℝ}
    (h : LadderEnvelope D) (k : ℕ) {ℓ : ℝ → ℕ → ℝ}
    (hsum : ∀ᶠ lam in atTop, Summable fun j => ℓ lam j ^ 2)
    (hbessel : ∀ᶠ lam in atTop, (∑' j : ℕ, ℓ lam j ^ 2) ≤ 2 * lam)
    (hl : ∀ j, j ≤ k + 1 → Tendsto (fun lam => ℓ lam j) atTop
      (nhds (constrainedProlateHermiteCoordinate j))) :
    Tendsto (fun lam =>
      (∑' j : ℕ,
        secularVector (D lam) (ℓ lam) (depthSecularRoot (D lam) (ℓ lam) k)
          (j + (k + 2)) ^ 2)
        / secularVector (D lam) (ℓ lam) (depthSecularRoot (D lam) (ℓ lam) k) 0 ^ 2)
      atTop (nhds 0) := by
  let a0 := constrainedProlateHermiteCoordinate 0
  have ha0 : a0 ≠ 0 := constrainedProlateHermiteCoordinate_ne_zero 0
  have ha0sq : (0 : ℝ) < a0 ^ 2 := sq_pos_of_ne_zero ha0
  have hl0 : Tendsto (fun lam => ℓ lam 0) atTop (nhds a0) := hl 0 (by omega)
  have hℓ0big : ∀ᶠ lam in atTop, a0 ^ 2 / 2 ≤ ℓ lam 0 ^ 2 :=
    ((hl0.pow 2).eventually (eventually_gt_nhds (by linarith))).mono fun _ hx => hx.le
  have hroot := (h.ccm_depth_ratio_and_exactEigenpair_eventually k hsum hbessel hl).2
  have hrate := h.tail_tendsto_zero k
  have hbound : Tendsto (fun lam =>
      4 / a0 ^ 2 *
        (lam * D lam (k + 1) / (D lam (k + 2) - D lam (k + 1))) ^ 2)
      atTop (nhds 0) := by
    have hsq := hrate.mul hrate
    have hsq' : Tendsto (fun lam =>
        (lam * D lam (k + 1) / (D lam (k + 2) - D lam (k + 1))) ^ 2)
        atTop (nhds 0) := by
      simpa [pow_two] using hsq
    simpa using hsq'.const_mul (4 / a0 ^ 2)
  refine squeeze_zero' (Eventually.of_forall fun lam =>
    div_nonneg (tsum_nonneg fun j => sq_nonneg _) (sq_nonneg _)) ?_ hbound
  filter_upwards [h.depth_struct k, hsum, hbessel, hℓ0big, hroot,
      eventually_ge_atTop (1 : ℝ)]
    with lam hstruct hsumLam hbesselLam hℓ0bigLam hrootLam hlam
  obtain ⟨⟨hhead, hk1, h12⟩, hfloor⟩ := hstruct
  have hd0 : 0 ≤ D lam 0 := (hhead 0 (Nat.zero_le k)).1
  have hd0k : D lam 0 ≤ D lam k := (hhead 0 (Nat.zero_le k)).2
  have hrootMem := hrootLam.1
  have hd0root : D lam 0 < depthSecularRoot (D lam) (ℓ lam) k :=
    lt_of_le_of_lt hd0k hrootMem.1
  have hrefPos : 0 < D lam (k + 1) :=
    lt_of_le_of_lt (le_trans hd0 hd0k) hk1
  have hgapPos : 0 < D lam (k + 2) - D lam (k + 1) := sub_pos.mpr h12
  have hnextRoot : depthSecularRoot (D lam) (ℓ lam) k < D lam (k + 2) :=
    lt_trans hrootMem.2 h12
  have htailCoords : (∑' j : ℕ, ℓ lam (j + (k + 2)) ^ 2) ≤ 2 * lam := by
    have hsplit := hsumLam.sum_add_tsum_nat_add (k + 2)
    have hfin : 0 ≤ ∑ i ∈ Finset.range (k + 2), ℓ lam i ^ 2 :=
      Finset.sum_nonneg fun i _ => sq_nonneg _
    linarith
  have htail :
      (∑' j : ℕ,
          secularVector (D lam) (ℓ lam) (depthSecularRoot (D lam) (ℓ lam) k)
            (j + (k + 2)) ^ 2)
        ≤ 2 * lam / (D lam (k + 2) - D lam (k + 1)) ^ 2 := by
    have hbase := secularVector_sq_offset_tail_le hfloor hsumLam hnextRoot
    have hmass :
        (∑' j : ℕ, ℓ lam (j + (k + 2)) ^ 2)
            / (D lam (k + 2) - depthSecularRoot (D lam) (ℓ lam) k) ^ 2
          ≤ (∑' j : ℕ, ℓ lam (j + (k + 2)) ^ 2)
            / (D lam (k + 2) - D lam (k + 1)) ^ 2 :=
      div_le_div_of_nonneg_left (tsum_nonneg fun j => sq_nonneg _)
        (pow_pos hgapPos 2)
        (pow_le_pow_left₀ hgapPos.le (by linarith [hrootMem.2]) 2)
    exact le_trans hbase (le_trans hmass
      (div_le_div_of_le_of_pos htailCoords (pow_pos hgapPos 2)))
  have hheadFloor : a0 ^ 2 / 2 / D lam (k + 1) ^ 2
      ≤ secularVector (D lam) (ℓ lam) (depthSecularRoot (D lam) (ℓ lam) k) 0 ^ 2 := by
    unfold secularVector
    rw [div_pow]
    have hdenPos : 0 < (D lam 0 - depthSecularRoot (D lam) (ℓ lam) k) ^ 2 :=
      sq_pos_of_ne_zero (sub_ne_zero.mpr (ne_of_lt hd0root))
    have hdenLe : (D lam 0 - depthSecularRoot (D lam) (ℓ lam) k) ^ 2
        ≤ D lam (k + 1) ^ 2 := by
      rw [show (D lam 0 - depthSecularRoot (D lam) (ℓ lam) k) ^ 2 =
        (depthSecularRoot (D lam) (ℓ lam) k - D lam 0) ^ 2 by ring]
      exact pow_le_pow_left₀ (sub_nonneg.mpr hd0root.le)
        (by linarith [hrootMem.2, hd0]) 2
    calc
      a0 ^ 2 / 2 / D lam (k + 1) ^ 2
          ≤ ℓ lam 0 ^ 2 / D lam (k + 1) ^ 2 :=
        div_le_div_of_le_of_pos hℓ0bigLam (pow_pos hrefPos 2)
      _ ≤ ℓ lam 0 ^ 2 /
          (D lam 0 - depthSecularRoot (D lam) (ℓ lam) k) ^ 2 :=
        div_le_div_of_nonneg_left (sq_nonneg _) hdenPos hdenLe
  have hheadPos : 0 < secularVector (D lam) (ℓ lam)
      (depthSecularRoot (D lam) (ℓ lam) k) 0 ^ 2 :=
    lt_of_lt_of_le (div_pos (half_pos ha0sq) (pow_pos hrefPos 2)) hheadFloor
  have hupperNonneg : 0 ≤ 2 * lam / (D lam (k + 2) - D lam (k + 1)) ^ 2 :=
    div_nonneg (by linarith) (sq_nonneg _)
  have heq1 :
      (2 * lam / (D lam (k + 2) - D lam (k + 1)) ^ 2)
          / (a0 ^ 2 / 2 / D lam (k + 1) ^ 2)
        = 4 * lam * D lam (k + 1) ^ 2 /
          (a0 ^ 2 * (D lam (k + 2) - D lam (k + 1)) ^ 2) := by
    field_simp
    ring
  have heq2 :
      4 / a0 ^ 2 *
          (lam * D lam (k + 1) / (D lam (k + 2) - D lam (k + 1))) ^ 2
        = 4 * lam ^ 2 * D lam (k + 1) ^ 2 /
          (a0 ^ 2 * (D lam (k + 2) - D lam (k + 1)) ^ 2) := by
    field_simp
  calc
    (∑' j : ℕ,
        secularVector (D lam) (ℓ lam) (depthSecularRoot (D lam) (ℓ lam) k)
          (j + (k + 2)) ^ 2)
        / secularVector (D lam) (ℓ lam) (depthSecularRoot (D lam) (ℓ lam) k) 0 ^ 2
      ≤ (2 * lam / (D lam (k + 2) - D lam (k + 1)) ^ 2)
          / secularVector (D lam) (ℓ lam) (depthSecularRoot (D lam) (ℓ lam) k) 0 ^ 2 :=
        div_le_div_of_le_of_pos htail hheadPos
    _ ≤ (2 * lam / (D lam (k + 2) - D lam (k + 1)) ^ 2)
          / (a0 ^ 2 / 2 / D lam (k + 1) ^ 2) :=
        div_le_div_of_nonneg_left hupperNonneg
          (div_pos (half_pos ha0sq) (pow_pos hrefPos 2)) hheadFloor
    _ = 4 * lam * D lam (k + 1) ^ 2 /
          (a0 ^ 2 * (D lam (k + 2) - D lam (k + 1)) ^ 2) := heq1
    _ ≤ 4 * lam ^ 2 * D lam (k + 1) ^ 2 /
          (a0 ^ 2 * (D lam (k + 2) - D lam (k + 1)) ^ 2) := by
        refine div_le_div_of_le_of_pos ?_ (mul_pos ha0sq (pow_pos hgapPos 2))
        exact mul_le_mul_of_nonneg_right (by nlinarith) (sq_nonneg _)
    _ = 4 / a0 ^ 2 *
          (lam * D lam (k + 1) / (D lam (k + 2) - D lam (k + 1))) ^ 2 := heq2.symm

end RHTower

end
