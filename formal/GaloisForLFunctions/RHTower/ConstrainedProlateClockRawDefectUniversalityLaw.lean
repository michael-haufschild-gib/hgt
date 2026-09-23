import GaloisForLFunctions.RHTower.CcmFuchsScaleRatio
import GaloisForLFunctions.RHTower.ConstrainedProlateClockExactEigenpairLaw

/-!
# Clock-universal depth raw-defect collapse

The CCM raw-defect theorem was stated for the Gaussian Fuchs clock.  Its proof consumes only
lower-scale collapse, positivity of the reference scale, and the universal depth-root ratio.
Every `LadderEnvelope` supplies those inputs.  Thus every earlier raw contrast becomes
asymptotically invisible for the same eventual nonzero exact eigenpair, independently of the
clock profile.
-/

open Filter Set

noncomputable section

namespace RHTower

/-- Every fixed lower leakage is negligible against the depth reference scale in an arbitrary
ladder envelope. -/
theorem LadderEnvelope.lower_ratio_tendsto_zero
    {D : ℝ → ℕ → ℝ}
    (h : LadderEnvelope D) {j k : ℕ} (hjk : j ≤ k) :
    Tendsto (fun lam => D lam j / D lam (k + 1)) atTop (nhds 0) := by
  refine squeeze_zero' (Eventually.of_forall fun lam =>
    div_nonneg (h.nonneg lam j) (h.nonneg lam (k + 1))) ?_ (h.ratio_tendsto_zero k)
  filter_upwards [h.lt_succ k, h.mono] with lam hlt hmono
  have hden : 0 < D lam (k + 1) := lt_of_le_of_lt (h.nonneg lam k) hlt
  exact (div_le_div_iff_of_pos_right hden).2 (hmono j k hjk)

/-- The depth-`k` raw defect collapses for every clock-enveloped CCM family, not only for the
Gaussian Fuchs clock. -/
theorem LadderEnvelope.ccm_tendsto_depth_raw_defect_div_zero
    {D : ℝ → ℕ → ℝ}
    (h : LadderEnvelope D) (k : ℕ) {ℓ : ℝ → ℕ → ℝ}
    (hsum : ∀ᶠ lam in atTop, Summable fun j => ℓ lam j ^ (2 : ℕ))
    (hbessel : ∀ᶠ lam in atTop, (∑' j : ℕ, ℓ lam j ^ (2 : ℕ)) ≤ 2 * lam)
    (hl : ∀ j, j ≤ k + 1 → Tendsto (fun lam => ℓ lam j) atTop
      (nhds (constrainedProlateHermiteCoordinate j)))
    {m : ℕ} (hmk : m ≤ k) :
    Tendsto (fun lam =>
      (secularVector (D lam) (ℓ lam) (depthSecularRoot (D lam) (ℓ lam) k) m * ℓ lam 0
        - secularVector (D lam) (ℓ lam) (depthSecularRoot (D lam) (ℓ lam) k) 0 * ℓ lam m)
        / (secularVector (D lam) (ℓ lam) (depthSecularRoot (D lam) (ℓ lam) k) 0
            * ℓ lam 0)) atTop (nhds 0) := by
  have htheta := constrainedProlateHermiteTheta_mem_Ioo k
  have hthetaNe : constrainedProlateHermiteTheta k ≠ 0 := ne_of_gt htheta.1
  have hBpos : ∀ᶠ lam in atTop, 0 < D lam (k + 1) := by
    filter_upwards [h.lt_succ k] with lam hlt
    exact lt_of_le_of_lt (h.nonneg lam k) hlt
  have hrootRatio := h.ccm_depth_ratio_tendsto k hsum hbessel hl
  have h0ratio := h.lower_ratio_tendsto_zero (Nat.zero_le k)
  have hmratio := h.lower_ratio_tendsto_zero hmk
  have hrootPos : ∀ᶠ lam in atTop, 0 < depthSecularRoot (D lam) (ℓ lam) k :=
    eventually_pos_of_div_tendsto_pos htheta.1 hBpos hrootRatio
  have hne0 : ∀ᶠ lam in atTop,
      D lam 0 - depthSecularRoot (D lam) (ℓ lam) k ≠ 0 :=
    eventually_sub_ne_zero_of_div_tendsto_zero hrootPos
      (tendsto_div_zero_of_div_tendsto hthetaNe h0ratio hrootRatio)
  have hnem : ∀ᶠ lam in atTop,
      D lam m - depthSecularRoot (D lam) (ℓ lam) k ≠ 0 :=
    eventually_sub_ne_zero_of_div_tendsto_zero hrootPos
      (tendsto_div_zero_of_div_tendsto hthetaNe hmratio hrootRatio)
  have hcoord0Ne : ∀ᶠ lam in atTop, ℓ lam 0 ≠ 0 :=
    (hl 0 (by omega)).eventually_ne (constrainedProlateHermiteCoordinate_ne_zero 0)
  have hcoordRatio : Tendsto (fun lam => ℓ lam m / ℓ lam 0) atTop
      (nhds (constrainedProlateHermiteCoordinate m / constrainedProlateHermiteCoordinate 0)) :=
    (hl m (by omega)).div (hl 0 (by omega))
      (constrainedProlateHermiteCoordinate_ne_zero 0)
  exact tendsto_secularVector_raw_defect_div_zero_of_reference hthetaNe
    h0ratio hmratio hrootRatio hne0 hnem hcoord0Ne hcoordRatio

/-- **Clock-universal exact-eigenpair/raw-defect law.**  The same eventual genuine constrained
eigenpair annihilates its full constraint exactly and makes every preceding raw contrast
asymptotically invisible. -/
theorem LadderEnvelope.ccm_depth_exactEigenpair_and_allRawDefects
    {D : ℝ → ℕ → ℝ}
    (h : LadderEnvelope D) (k : ℕ) {ℓ : ℝ → ℕ → ℝ}
    (hsum : ∀ᶠ lam in atTop, Summable fun j => ℓ lam j ^ (2 : ℕ))
    (hbessel : ∀ᶠ lam in atTop, (∑' j : ℕ, ℓ lam j ^ (2 : ℕ)) ≤ 2 * lam)
    (hl : ∀ j, j ≤ k + 1 → Tendsto (fun lam => ℓ lam j) atTop
      (nhds (constrainedProlateHermiteCoordinate j))) :
    (∀ᶠ lam in atTop,
      depthSecularRoot (D lam) (ℓ lam) k ∈ Ioo (D lam k) (D lam (k + 1)) ∧
      depthSecular (D lam) (ℓ lam) k (depthSecularRoot (D lam) (ℓ lam) k) = 0 ∧
      (∑' j : ℕ,
        ℓ lam j * secularVector (D lam) (ℓ lam)
          (depthSecularRoot (D lam) (ℓ lam) k) j) = 0 ∧
      secularVector (D lam) (ℓ lam) (depthSecularRoot (D lam) (ℓ lam) k) ≠ 0) ∧
    ∀ m, m ≤ k →
      Tendsto (fun lam =>
        (secularVector (D lam) (ℓ lam) (depthSecularRoot (D lam) (ℓ lam) k) m * ℓ lam 0
          - secularVector (D lam) (ℓ lam) (depthSecularRoot (D lam) (ℓ lam) k) 0 * ℓ lam m)
          / (secularVector (D lam) (ℓ lam) (depthSecularRoot (D lam) (ℓ lam) k) 0
              * ℓ lam 0)) atTop (nhds 0) := by
  refine ⟨(h.ccm_depth_ratio_and_exactEigenpair_eventually k hsum hbessel hl).2, ?_⟩
  intro m hmk
  exact h.ccm_tendsto_depth_raw_defect_div_zero k hsum hbessel hl hmk

end RHTower

end
