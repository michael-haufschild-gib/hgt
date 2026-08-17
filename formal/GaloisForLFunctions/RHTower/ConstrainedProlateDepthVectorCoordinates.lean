import GaloisForLFunctions.RHTower.ConstrainedProlateClockRawDefectUniversalityLaw
import GaloisForLFunctions.RHTower.TwoModeFuchsLimit

/-!
# Coordinate limits for every fixed constrained-Prolate depth

The normalized raw-defect law determines coordinates `0,...,k`.  The shoulder coordinate
`k + 1` is determined directly by the exact depth-root ratio.  Together they identify every
coordinate in the finite head with the explicit Hermite contrast, relative to coordinate zero.
-/

open Filter Set

noncomputable section

namespace RHTower

variable {d ℓ : ℕ → ℝ} {μ : ℝ}

/-- A normalized raw defect is exactly the difference between two coordinate ratios. -/
theorem secularVector_div_zero_sub_coord_div_zero
    (m : ℕ) (hv0 : secularVector d ℓ μ 0 ≠ 0) (hℓ0 : ℓ 0 ≠ 0) :
    secularVector d ℓ μ m / secularVector d ℓ μ 0 - ℓ m / ℓ 0 =
      (secularVector d ℓ μ m * ℓ 0 - secularVector d ℓ μ 0 * ℓ m) /
        (secularVector d ℓ μ 0 * ℓ 0) := by
  field_simp

/-- The top Hermite-contrast ratio is the shoulder ratio forced by the limiting secular root. -/
theorem constrainedProlateHermiteContrast_top_div_zero (k : ℕ) :
    constrainedProlateHermiteContrast k (k + 1) /
        constrainedProlateHermiteContrast k 0 =
      (constrainedProlateHermiteCoordinate (k + 1) /
          constrainedProlateHermiteCoordinate 0) *
        ((0 - constrainedProlateHermiteTheta k) /
          (1 - constrainedProlateHermiteTheta k)) := by
  have ha0 := constrainedProlateHermiteCoordinate_ne_zero 0
  have hat := constrainedProlateHermiteCoordinate_ne_zero (k + 1)
  have hS := constrainedProlateHermiteSquareSum_pos k
  have htheta := constrainedProlateHermiteTheta_mem_Ioo k
  have hthetaEq : constrainedProlateHermiteTheta k =
      constrainedProlateHermiteSquareSum k /
        (constrainedProlateHermiteSquareSum k +
          constrainedProlateHermiteCoordinate (k + 1) ^ 2) := by
    rw [← constrainedProlateHermiteTheta_eq_square_ratio,
      Real.sq_sqrt hS.le]
  rw [constrainedProlateHermiteContrast_succ,
    constrainedProlateHermiteContrast_of_le (Nat.zero_le k), hthetaEq]
  field_simp
  ring

/-- Every lower head coordinate has the Hermite-contrast ratio. -/
theorem LadderEnvelope.ccm_depth_secularVector_lower_coordinate_ratio_tendsto
    {D : ℝ → ℕ → ℝ}
    (h : LadderEnvelope D) (k : ℕ) {ℓ : ℝ → ℕ → ℝ}
    (hsum : ∀ᶠ lam in atTop, Summable fun j => ℓ lam j ^ 2)
    (hbessel : ∀ᶠ lam in atTop, (∑' j : ℕ, ℓ lam j ^ 2) ≤ 2 * lam)
    (hl : ∀ j, j ≤ k + 1 → Tendsto (fun lam => ℓ lam j) atTop
      (nhds (constrainedProlateHermiteCoordinate j)))
    {m : ℕ} (hmk : m ≤ k) :
    Tendsto (fun lam =>
      secularVector (D lam) (ℓ lam) (depthSecularRoot (D lam) (ℓ lam) k) m /
        secularVector (D lam) (ℓ lam) (depthSecularRoot (D lam) (ℓ lam) k) 0)
      atTop
      (nhds (constrainedProlateHermiteContrast k m /
        constrainedProlateHermiteContrast k 0)) := by
  have ha0 := constrainedProlateHermiteCoordinate_ne_zero 0
  have hl0 := hl 0 (by omega)
  have hcoord : Tendsto (fun lam => ℓ lam m / ℓ lam 0) atTop
      (nhds (constrainedProlateHermiteCoordinate m /
        constrainedProlateHermiteCoordinate 0)) :=
    (hl m (by omega)).div hl0 ha0
  have hraw := h.ccm_tendsto_depth_raw_defect_div_zero k hsum hbessel hl hmk
  have hadd := hraw.add hcoord
  have hadd' : Tendsto (fun lam =>
      (secularVector (D lam) (ℓ lam) (depthSecularRoot (D lam) (ℓ lam) k) m * ℓ lam 0
        - secularVector (D lam) (ℓ lam) (depthSecularRoot (D lam) (ℓ lam) k) 0 * ℓ lam m)
          / (secularVector (D lam) (ℓ lam) (depthSecularRoot (D lam) (ℓ lam) k) 0
            * ℓ lam 0) + ℓ lam m / ℓ lam 0)
      atTop (nhds (constrainedProlateHermiteCoordinate m /
        constrainedProlateHermiteCoordinate 0)) := by
    simpa using hadd
  have hroot := (h.ccm_depth_ratio_and_exactEigenpair_eventually k hsum hbessel hl).2
  have hℓ0 : ∀ᶠ lam in atTop, ℓ lam 0 ≠ 0 := hl0.eventually_ne ha0
  have hv0 : ∀ᶠ lam in atTop,
      secularVector (D lam) (ℓ lam) (depthSecularRoot (D lam) (ℓ lam) k) 0 ≠ 0 := by
    filter_upwards [hroot, hℓ0] with lam hrootLam hℓ0Lam
    unfold secularVector
    exact div_ne_zero hℓ0Lam (sub_ne_zero.mpr
      (ne_of_lt (lt_of_le_of_lt (h.mono lam (Nat.zero_le k)) hrootLam.1.1)))
  have hratio : Tendsto (fun lam =>
      secularVector (D lam) (ℓ lam) (depthSecularRoot (D lam) (ℓ lam) k) m /
        secularVector (D lam) (ℓ lam) (depthSecularRoot (D lam) (ℓ lam) k) 0)
      atTop (nhds (constrainedProlateHermiteCoordinate m /
        constrainedProlateHermiteCoordinate 0)) := by
    refine hadd'.congr' ?_
    filter_upwards [hv0, hℓ0] with lam hv0Lam hℓ0Lam
    have heq := secularVector_div_zero_sub_coord_div_zero m hv0Lam hℓ0Lam
    linarith
  have htarget : constrainedProlateHermiteCoordinate m /
      constrainedProlateHermiteCoordinate 0 =
      constrainedProlateHermiteContrast k m /
        constrainedProlateHermiteContrast k 0 := by
    rw [constrainedProlateHermiteContrast_of_le hmk,
      constrainedProlateHermiteContrast_of_le (Nat.zero_le k)]
    field_simp
  simpa only [htarget] using hratio

/-- The shoulder coordinate `k + 1` has the top Hermite-contrast ratio. -/
theorem LadderEnvelope.ccm_depth_secularVector_top_coordinate_ratio_tendsto
    {D : ℝ → ℕ → ℝ}
    (h : LadderEnvelope D) (k : ℕ) {ℓ : ℝ → ℕ → ℝ}
    (hsum : ∀ᶠ lam in atTop, Summable fun j => ℓ lam j ^ 2)
    (hbessel : ∀ᶠ lam in atTop, (∑' j : ℕ, ℓ lam j ^ 2) ≤ 2 * lam)
    (hl : ∀ j, j ≤ k + 1 → Tendsto (fun lam => ℓ lam j) atTop
      (nhds (constrainedProlateHermiteCoordinate j))) :
    Tendsto (fun lam =>
      secularVector (D lam) (ℓ lam) (depthSecularRoot (D lam) (ℓ lam) k) (k + 1) /
        secularVector (D lam) (ℓ lam) (depthSecularRoot (D lam) (ℓ lam) k) 0)
      atTop
      (nhds (constrainedProlateHermiteContrast k (k + 1) /
        constrainedProlateHermiteContrast k 0)) := by
  let θ := constrainedProlateHermiteTheta k
  have htheta := constrainedProlateHermiteTheta_mem_Ioo k
  have hthetaNe : 1 - θ ≠ 0 := by dsimp [θ]; linarith [htheta.2]
  have ha0 := constrainedProlateHermiteCoordinate_ne_zero 0
  have hl0 := hl 0 (by omega)
  have hlt := hl (k + 1) le_rfl
  have hcoord : Tendsto (fun lam => ℓ lam (k + 1) / ℓ lam 0) atTop
      (nhds (constrainedProlateHermiteCoordinate (k + 1) /
        constrainedProlateHermiteCoordinate 0)) := hlt.div hl0 ha0
  have hrootRatio := h.ccm_depth_ratio_tendsto k hsum hbessel hl
  have hzeroRatio := h.lower_ratio_tendsto_zero (Nat.zero_le k)
  have hscaleRaw := (hzeroRatio.sub hrootRatio).div
    (tendsto_const_nhds.sub hrootRatio) hthetaNe
  have hBpos : ∀ᶠ lam in atTop, 0 < D lam (k + 1) := by
    filter_upwards [h.lt_succ k] with lam hs
    exact lt_of_le_of_lt (h.nonneg lam k) hs
  have hscale : Tendsto (fun lam =>
      (D lam 0 - depthSecularRoot (D lam) (ℓ lam) k) /
        (D lam (k + 1) - depthSecularRoot (D lam) (ℓ lam) k))
      atTop (nhds ((0 - θ) / (1 - θ))) := by
    refine hscaleRaw.congr' ?_
    filter_upwards [hBpos] with lam hBposLam
    change (D lam 0 / D lam (k + 1) -
          depthSecularRoot (D lam) (ℓ lam) k / D lam (k + 1)) /
        (1 - depthSecularRoot (D lam) (ℓ lam) k / D lam (k + 1)) =
      (D lam 0 - depthSecularRoot (D lam) (ℓ lam) k) /
        (D lam (k + 1) - depthSecularRoot (D lam) (ℓ lam) k)
    field_simp
  have hprod := hcoord.mul hscale
  have hroot := (h.ccm_depth_ratio_and_exactEigenpair_eventually k hsum hbessel hl).2
  have hℓ0 : ∀ᶠ lam in atTop, ℓ lam 0 ≠ 0 := hl0.eventually_ne ha0
  have hℓtop : ∀ᶠ lam in atTop, ℓ lam (k + 1) ≠ 0 :=
    hlt.eventually_ne (constrainedProlateHermiteCoordinate_ne_zero (k + 1))
  have hratio : Tendsto (fun lam =>
      secularVector (D lam) (ℓ lam) (depthSecularRoot (D lam) (ℓ lam) k) (k + 1) /
        secularVector (D lam) (ℓ lam) (depthSecularRoot (D lam) (ℓ lam) k) 0)
      atTop (nhds ((constrainedProlateHermiteCoordinate (k + 1) /
          constrainedProlateHermiteCoordinate 0) * ((0 - θ) / (1 - θ)))) := by
    refine hprod.congr' ?_
    filter_upwards [hroot, hℓ0, hℓtop] with lam hrootLam hℓ0Lam hℓtopLam
    unfold secularVector
    have hden0 : D lam 0 - depthSecularRoot (D lam) (ℓ lam) k ≠ 0 :=
      sub_ne_zero.mpr (ne_of_lt
        (lt_of_le_of_lt (h.mono lam (Nat.zero_le k)) hrootLam.1.1))
    have hdenTop : D lam (k + 1) - depthSecularRoot (D lam) (ℓ lam) k ≠ 0 :=
      sub_ne_zero.mpr (ne_of_gt hrootLam.1.2)
    field_simp
  rw [constrainedProlateHermiteContrast_top_div_zero]
  exact hratio

/-- All coordinates in the finite depth head converge to the corresponding Hermite-contrast
ratio. -/
theorem LadderEnvelope.ccm_depth_secularVector_coordinate_ratio_tendsto
    {D : ℝ → ℕ → ℝ}
    (h : LadderEnvelope D) (k : ℕ) {ℓ : ℝ → ℕ → ℝ}
    (hsum : ∀ᶠ lam in atTop, Summable fun j => ℓ lam j ^ 2)
    (hbessel : ∀ᶠ lam in atTop, (∑' j : ℕ, ℓ lam j ^ 2) ≤ 2 * lam)
    (hl : ∀ j, j ≤ k + 1 → Tendsto (fun lam => ℓ lam j) atTop
      (nhds (constrainedProlateHermiteCoordinate j)))
    {m : ℕ} (hm : m < k + 2) :
    Tendsto (fun lam =>
      secularVector (D lam) (ℓ lam) (depthSecularRoot (D lam) (ℓ lam) k) m /
        secularVector (D lam) (ℓ lam) (depthSecularRoot (D lam) (ℓ lam) k) 0)
      atTop
      (nhds (constrainedProlateHermiteContrast k m /
        constrainedProlateHermiteContrast k 0)) := by
  rcases lt_or_eq_of_le (show m ≤ k + 1 by omega) with hmk | rfl
  · exact h.ccm_depth_secularVector_lower_coordinate_ratio_tendsto k hsum hbessel hl (by omega)
  · exact h.ccm_depth_secularVector_top_coordinate_ratio_tendsto k hsum hbessel hl

end RHTower

end
