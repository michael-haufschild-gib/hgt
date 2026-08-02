import GaloisForLFunctions.RHTower.ConstrainedProlateDepthVectorCoordinates
import GaloisForLFunctions.RHTower.ConstrainedProlateDepthVectorTail
import GaloisForLFunctions.RHTower.ConstrainedProlateFullDistanceCCM
import GaloisForLFunctions.RHTower.HermiteContrastLp

/-!
# Strong Hermite-contrast limit for every fixed constrained-Prolate depth

The exact secular vector is rescaled by its zeroth coordinate.  Every coordinate in its finite
head then converges to the corresponding Hermite-contrast ratio, while the full squared tail
vanishes.  These two statements assemble into strong convergence in `ℓ²`.
-/

open Filter Set GaloisForLFunctions

noncomputable section

namespace RHTower

/-- The exact depth secular vector is eventually square-summable. -/
theorem ClockEnvelope.ccm_depth_summable_secularVector_sq
    {D : ℝ → ℕ → ℝ} {e : ℕ → ℕ} {E : ℝ → ℝ}
    (h : ClockEnvelope D e E) (k : ℕ) {ℓ : ℝ → ℕ → ℝ}
    (hsum : ∀ᶠ lam in atTop, Summable fun j => ℓ lam j ^ 2)
    (hbessel : ∀ᶠ lam in atTop, (∑' j : ℕ, ℓ lam j ^ 2) ≤ 2 * lam)
    (hl : ∀ j, j ≤ k + 1 → Tendsto (fun lam => ℓ lam j) atTop
      (nhds (constrainedProlateHermiteCoordinate j))) :
    ∀ᶠ lam in atTop, Summable fun j =>
      secularVector (D lam) (ℓ lam) (depthSecularRoot (D lam) (ℓ lam) k) j ^ 2 := by
  have hroot := (h.ccm_depth_ratio_and_exactEigenpair_eventually k hsum hbessel hl).2
  filter_upwards [h.depth_struct k, hsum, hroot] with lam hstruct hsumLam hrootLam
  obtain ⟨hhead, hfloor⟩ := hstruct
  have htail := summable_secularVector_sq_offset_tail hfloor hsumLam
    (lt_trans hrootLam.1.2 hhead.2.2)
  exact (summable_nat_add_iff (k + 2)).mp htail

/-- The exact depth secular vector is eventually an `ℓ²` vector. -/
theorem ClockEnvelope.ccm_depth_memℓp
    {D : ℝ → ℕ → ℝ} {e : ℕ → ℕ} {E : ℝ → ℝ}
    (h : ClockEnvelope D e E) (k : ℕ) {ℓ : ℝ → ℕ → ℝ}
    (hsum : ∀ᶠ lam in atTop, Summable fun j => ℓ lam j ^ 2)
    (hbessel : ∀ᶠ lam in atTop, (∑' j : ℕ, ℓ lam j ^ 2) ≤ 2 * lam)
    (hl : ∀ j, j ≤ k + 1 → Tendsto (fun lam => ℓ lam j) atTop
      (nhds (constrainedProlateHermiteCoordinate j))) :
    ∀ᶠ lam in atTop,
      Memℓp (secularVector (D lam) (ℓ lam) (depthSecularRoot (D lam) (ℓ lam) k)) 2 :=
  (h.ccm_depth_summable_secularVector_sq k hsum hbessel hl).mono
    fun _ hsq => memℓp_two_of_sq_summable hsq

/-- **Strong depth-`k` eigenvector limit.**  After rescaling its zeroth coordinate to one, the
exact infinite-dimensional secular eigenvector converges in `ℓ²` to the similarly rescaled
explicit Hermite contrast. -/
theorem ClockEnvelope.ccm_depth_rescaled_secularLp_tendsto_hermiteContrast
    {D : ℝ → ℕ → ℝ} {e : ℕ → ℕ} {E : ℝ → ℝ}
    (h : ClockEnvelope D e E) (k : ℕ) {ℓ : ℝ → ℕ → ℝ}
    (hsum : ∀ᶠ lam in atTop, Summable fun j => ℓ lam j ^ 2)
    (hbessel : ∀ᶠ lam in atTop, (∑' j : ℕ, ℓ lam j ^ 2) ≤ 2 * lam)
    (hl : ∀ j, j ≤ k + 1 → Tendsto (fun lam => ℓ lam j) atTop
      (nhds (constrainedProlateHermiteCoordinate j))) :
    Tendsto (fun lam =>
      (secularVector (D lam) (ℓ lam) (depthSecularRoot (D lam) (ℓ lam) k) 0)⁻¹ •
        secularLp (D lam) (ℓ lam) (depthSecularRoot (D lam) (ℓ lam) k))
      atTop
      (nhds ((constrainedProlateHermiteContrast k 0)⁻¹ • hermiteContrastLp k)) := by
  let w : ℕ → ℝ := constrainedProlateHermiteContrast k
  let w0 : ℝ := constrainedProlateHermiteContrast k 0
  have hw0 : w0 ≠ 0 := by
    dsimp only [w0]
    rw [constrainedProlateHermiteContrast_of_le (Nat.zero_le k)]
    exact neg_ne_zero.mpr (constrainedProlateHermiteCoordinate_ne_zero 0)
  have hmem := h.ccm_depth_memℓp k hsum hbessel hl
  have hsumV := h.ccm_depth_summable_secularVector_sq k hsum hbessel hl
  have hroot := (h.ccm_depth_ratio_and_exactEigenpair_eventually k hsum hbessel hl).2
  have hl0 := hl 0 (by omega)
  have hℓ0 : ∀ᶠ lam in atTop, ℓ lam 0 ≠ 0 :=
    hl0.eventually_ne (constrainedProlateHermiteCoordinate_ne_zero 0)
  have hv0 : ∀ᶠ lam in atTop,
      secularVector (D lam) (ℓ lam) (depthSecularRoot (D lam) (ℓ lam) k) 0 ≠ 0 := by
    filter_upwards [hroot, hℓ0] with lam hrootLam hℓ0Lam
    unfold secularVector
    exact div_ne_zero hℓ0Lam (sub_ne_zero.mpr
      (ne_of_lt (lt_of_le_of_lt (h.mono lam (Nat.zero_le k)) hrootLam.1.1)))
  have hfinite : Tendsto (fun lam =>
      ∑ j ∈ Finset.range (k + 2),
        (secularVector (D lam) (ℓ lam) (depthSecularRoot (D lam) (ℓ lam) k) j /
            secularVector (D lam) (ℓ lam) (depthSecularRoot (D lam) (ℓ lam) k) 0
          - w j / w0) ^ 2) atTop (nhds 0) := by
    have hterms : ∀ j ∈ Finset.range (k + 2), Tendsto (fun lam =>
        (secularVector (D lam) (ℓ lam) (depthSecularRoot (D lam) (ℓ lam) k) j /
            secularVector (D lam) (ℓ lam) (depthSecularRoot (D lam) (ℓ lam) k) 0
          - w j / w0) ^ 2) atTop (nhds 0) := by
      intro j hj
      have hj' : j < k + 2 := Finset.mem_range.mp hj
      have hratio := h.ccm_depth_secularVector_coordinate_ratio_tendsto
        k hsum hbessel hl hj'
      have hdiff := hratio.sub
        (tendsto_const_nhds : Tendsto (fun _ : ℝ => w j / w0) atTop (nhds (w j / w0)))
      have hsq := hdiff.pow 2
      simpa only [w, w0, sub_self, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using hsq
    simpa using tendsto_finsetSum _ hterms
  have htail := h.ccm_depth_secularVector_tail_fraction_tendsto_zero k hsum hbessel hl
  have htotal : Tendsto (fun lam =>
      (∑ j ∈ Finset.range (k + 2),
        (secularVector (D lam) (ℓ lam) (depthSecularRoot (D lam) (ℓ lam) k) j /
            secularVector (D lam) (ℓ lam) (depthSecularRoot (D lam) (ℓ lam) k) 0
          - w j / w0) ^ 2) +
      (∑' j : ℕ,
        secularVector (D lam) (ℓ lam) (depthSecularRoot (D lam) (ℓ lam) k)
          (j + (k + 2)) ^ 2) /
        secularVector (D lam) (ℓ lam) (depthSecularRoot (D lam) (ℓ lam) k) 0 ^ 2)
      atTop (nhds 0) := by
    simpa using hfinite.add htail
  have hsq : Tendsto (fun lam =>
      ‖(secularVector (D lam) (ℓ lam) (depthSecularRoot (D lam) (ℓ lam) k) 0)⁻¹ •
          secularLp (D lam) (ℓ lam) (depthSecularRoot (D lam) (ℓ lam) k)
        - w0⁻¹ • hermiteContrastLp k‖ ^ 2) atTop (nhds 0) := by
    refine htotal.congr' ?_
    filter_upwards [hmem, hsumV, hv0] with lam hmemLam hsumVLam hv0Lam
    let v0 := secularVector (D lam) (ℓ lam)
      (depthSecularRoot (D lam) (ℓ lam) k) 0
    have hvscaled : Summable fun j =>
        (secularVector (D lam) (ℓ lam) (depthSecularRoot (D lam) (ℓ lam) k) j / v0) ^ 2 := by
      have hs := hsumVLam.div_const (v0 ^ 2)
      refine hs.congr fun j => ?_
      rw [div_pow]
    have hwscaled : Summable fun j => (w j / w0) ^ 2 := by
      have hs := (summable_constrainedProlateHermiteContrast_sq k).div_const (w0 ^ 2)
      refine hs.congr fun j => ?_
      rw [div_pow]
    have herr : Summable fun j =>
        (secularVector (D lam) (ℓ lam) (depthSecularRoot (D lam) (ℓ lam) k) j / v0
          - w j / w0) ^ 2 := by
      refine Summable.of_nonneg_of_le (fun j => sq_nonneg _) (fun j => ?_)
        ((hvscaled.mul_left 2).add (hwscaled.mul_left 2))
      nlinarith [sq_nonneg
        (secularVector (D lam) (ℓ lam) (depthSecularRoot (D lam) (ℓ lam) k) j / v0
          + w j / w0)]
    rw [lp_norm_sq_eq_tsum]
    have hcoord : ∀ j : ℕ,
        (((v0⁻¹ • secularLp (D lam) (ℓ lam)
            (depthSecularRoot (D lam) (ℓ lam) k)
          - w0⁻¹ • hermiteContrastLp k : lp (fun _ : ℕ => ℝ) 2) : ℕ → ℝ) j) ^ 2 =
          (secularVector (D lam) (ℓ lam) (depthSecularRoot (D lam) (ℓ lam) k) j / v0
            - w j / w0) ^ 2 := by
      intro j
      change (v0⁻¹ * (secularLp (D lam) (ℓ lam)
          (depthSecularRoot (D lam) (ℓ lam) k)) j
        - w0⁻¹ * (hermiteContrastLp k) j) ^ 2 = _
      rw [show (secularLp (D lam) (ℓ lam)
          (depthSecularRoot (D lam) (ℓ lam) k)) j =
            secularVector (D lam) (ℓ lam)
              (depthSecularRoot (D lam) (ℓ lam) k) j from
        congrFun (secularLp_coeFn hmemLam) j]
      change (v0⁻¹ * secularVector (D lam) (ℓ lam)
          (depthSecularRoot (D lam) (ℓ lam) k) j - w0⁻¹ * w j) ^ 2 = _
      rw [div_eq_mul_inv, div_eq_mul_inv]
      ring
    rw [tsum_congr hcoord, ← herr.sum_add_tsum_nat_add (k + 2)]
    congr 1
    rw [← tsum_div_const]
    apply tsum_congr
    intro j
    rw [show w (j + (k + 2)) = 0 by
      dsimp only [w]
      exact constrainedProlateHermiteContrast_eq_zero_of_succ_lt (by omega)]
    simp only [zero_div, sub_zero, div_pow]
    rfl
  have hsqrt : Tendsto (fun lam => Real.sqrt
      (‖(secularVector (D lam) (ℓ lam) (depthSecularRoot (D lam) (ℓ lam) k) 0)⁻¹ •
          secularLp (D lam) (ℓ lam) (depthSecularRoot (D lam) (ℓ lam) k)
        - w0⁻¹ • hermiteContrastLp k‖ ^ 2)) atTop (nhds 0) := by
    simpa only [Function.comp_def, Real.sqrt_zero] using
      (Real.continuous_sqrt.tendsto 0).comp hsq
  have hnorm : Tendsto (fun lam =>
      ‖(secularVector (D lam) (ℓ lam) (depthSecularRoot (D lam) (ℓ lam) k) 0)⁻¹ •
          secularLp (D lam) (ℓ lam) (depthSecularRoot (D lam) (ℓ lam) k)
        - w0⁻¹ • hermiteContrastLp k‖) atTop (nhds 0) := by
    simpa only [Real.sqrt_zero, Real.sqrt_sq (norm_nonneg _)] using hsqrt
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simpa only [w0] using hnorm

end RHTower

end
