import GaloisForLFunctions.RHTower.CcmFuchsScaleRatio
import GaloisForLFunctions.RHTower.ConstrainedProlateLadderExactTransfer

/-!
# The depth-`k` raw defect vanishes for the CCM Fuchs family

The exact constrained eigenvector in the `k`-th gap pairs against each preceding raw CCM contrast
by an amount negligible against its own head weight.  Every input is a theorem about the family:
the lower scales are negligible against `d_{k+1}`, the root is comparable to `d_{k+1}` with
proportion `θ_k > 0`, and the coordinates converge.  Positivity of the root and separation of the
root from the lower poles are derived from those limits rather than assumed.
-/

open Filter

noncomputable section

namespace RHTower

/-- The exact constrained root in the `k`-th gap of the CCM Fuchs family. -/
def ccmFuchsDepthRoot (A : ℕ → ℝ) (ℓ : ℝ → ℕ → ℝ) (k : ℕ) (lam : ℝ) : ℝ :=
  depthSecularRoot (ccmFuchsScale A lam) (ℓ lam) k

/-- **The depth-`k` raw defect of the exact eigenvector vanishes.**  For every `m ≤ k` the pairing
of the exact eigenvector against the raw contrast `r_m`, normalized by the head weight, tends to
zero. -/
theorem ccm_tendsto_depth_raw_defect_div_zero
    {A : ℕ → ℝ} (hA : ∀ j, 0 < A j) {C : ℝ} (hC : 1 ≤ C) (k : ℕ)
    (hgrow : ∀ j, A (k + 2) ≤ C ^ j * A (j + (k + 2)))
    {ℓ : ℝ → ℕ → ℝ}
    (hsum : ∀ᶠ lam in atTop, Summable fun j => ℓ lam j ^ 2)
    (hbessel : ∀ᶠ lam in atTop, (∑' j : ℕ, ℓ lam j ^ 2) ≤ 2 * lam)
    (hl : ∀ j, j ≤ k + 1 → Tendsto (fun lam => ℓ lam j) atTop
      (nhds (constrainedProlateHermiteCoordinate j)))
    {m : ℕ} (hmk : m ≤ k) :
    Tendsto (fun lam =>
      (secularVector (ccmFuchsScale A lam) (ℓ lam) (ccmFuchsDepthRoot A ℓ k lam) m * ℓ lam 0
        - secularVector (ccmFuchsScale A lam) (ℓ lam) (ccmFuchsDepthRoot A ℓ k lam) 0 * ℓ lam m)
        / (secularVector (ccmFuchsScale A lam) (ℓ lam) (ccmFuchsDepthRoot A ℓ k lam) 0
            * ℓ lam 0)) atTop (nhds 0) := by
  -- the limiting proportion of the root to the reference scale
  have hθ := constrainedProlateHermiteTheta_mem_Ioo k
  have hθpos : 0 < constrainedProlateHermiteTheta k := hθ.1
  have hθne : constrainedProlateHermiteTheta k ≠ 0 := ne_of_gt hθpos
  -- the reference scale is positive
  have hBpos : ∀ᶠ lam : ℝ in atTop, 0 < ccmFuchsScale A lam (k + 1) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with lam hlam
    exact fuchsRate_pos (hA (k + 1)) _ hlam
  -- the root ratio, from the existing CCM depth law
  have hMB : Tendsto (fun lam => ccmFuchsDepthRoot A ℓ k lam / ccmFuchsScale A lam (k + 1))
      atTop (nhds (constrainedProlateHermiteTheta k)) :=
    ccm_fuchsModel_depthSecularRoot_ratio_tendsto hA hC k hgrow hsum hbessel hl
  -- scale negligibility
  have h0B := ccmFuchsScale_div_tendsto_zero hA (Nat.zero_le k)
  have hmB := ccmFuchsScale_div_tendsto_zero hA hmk
  -- positivity of the root, derived
  have hMpos : ∀ᶠ lam : ℝ in atTop, 0 < ccmFuchsDepthRoot A ℓ k lam :=
    eventually_pos_of_div_tendsto_pos hθpos hBpos hMB
  -- separation of the poles from the root, derived
  have hne0 : ∀ᶠ lam : ℝ in atTop,
      ccmFuchsScale A lam 0 - ccmFuchsDepthRoot A ℓ k lam ≠ 0 :=
    eventually_sub_ne_zero_of_div_tendsto_zero hMpos
      (tendsto_div_zero_of_div_tendsto hθne h0B hMB)
  have hnem : ∀ᶠ lam : ℝ in atTop,
      ccmFuchsScale A lam m - ccmFuchsDepthRoot A ℓ k lam ≠ 0 :=
    eventually_sub_ne_zero_of_div_tendsto_zero hMpos
      (tendsto_div_zero_of_div_tendsto hθne hmB hMB)
  -- the head coordinate is eventually nonzero
  have ha0ne : constrainedProlateHermiteCoordinate 0 ≠ 0 :=
    constrainedProlateHermiteCoordinate_ne_zero 0
  have hl0ne : ∀ᶠ lam : ℝ in atTop, ℓ lam 0 ≠ 0 :=
    (hl 0 (by omega)).eventually_ne ha0ne
  -- the coordinate ratio converges
  have hratio : Tendsto (fun lam => ℓ lam m / ℓ lam 0) atTop
      (nhds (constrainedProlateHermiteCoordinate m / constrainedProlateHermiteCoordinate 0)) :=
    (hl m (by omega)).div (hl 0 (by omega)) ha0ne
  exact tendsto_secularVector_raw_defect_div_zero_of_reference hθne h0B hmB hMB hne0 hnem
    hl0ne hratio

end RHTower

end
