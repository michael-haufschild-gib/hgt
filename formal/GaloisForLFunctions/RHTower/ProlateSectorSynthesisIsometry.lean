import GaloisForLFunctions.RHTower.ProlateSectorGroundVector
import GaloisForLFunctions.RHTower.ProlateTrueFamilyDistanceRate
import GaloisForLFunctions.RHTower.ProlateSectorConstrainedGround

/-!
# The sector synthesis is an isometry, and the operator form of the ground-vector rate

Synthesising a real `ℓ²` coefficient sequence against the orthonormal phase-normalized prolate
family of a sector preserves distances, so the `ℓ²` statement of the ground-vector convergence rate
is literally a statement about the vectors of the even carrier: the unit constrained ground
eigenvector of the compressed leakage operator on the Fourier-even sector converges to the
normalized two-mode seed at rate `O(lambda^{-7})`.
-/

noncomputable section

open Filter Set Asymptotics
open scoped InnerProduct InnerProductSpace

namespace RHTower

/-- The squared `ℓ²` norm is the series of squared coordinates. -/
theorem lp_two_norm_sq (p : lp (fun _ : ℕ => ℝ) 2) : ‖p‖ ^ (2 : ℕ) = ∑' j : ℕ, p j ^ (2 : ℕ) := by
  have h : (inner ℝ p p : ℝ) = ∑' j : ℕ, p j * p j := lp_inner_eq_tsum_mul p p
  rw [real_inner_self_eq_norm_sq] at h
  rw [h]
  exact tsum_congr fun j => by ring

/-- **The synthesis map preserves differences.** -/
theorem norm_sub_eq_of_hasSum_lp {a : ℝ} (ha : 0 < a) {σ : ℕ → ℕ} (hσ : Function.Injective σ)
    (p q : lp (fun _ : ℕ => ℝ) 2) {f g : evenSubspace}
    (hf : HasSum (fun j : ℕ => ((p j : ℝ) : ℂ) • sectorMode a σ j) f)
    (hg : HasSum (fun j : ℕ => ((q j : ℝ) : ℂ) • sectorMode a σ j) g) :
    ‖f - g‖ = ‖p - q‖ := by
  have h := hasSum_norm_sub_sq_of_hasSum ha hσ hf hg
  have hterm : ∀ j : ℕ, ‖((p j : ℝ) : ℂ) - ((q j : ℝ) : ℂ)‖ ^ (2 : ℕ) = (p - q) j ^ (2 : ℕ) := by
    intro j
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, sq_abs, lp.coeFn_sub]
    rfl
  have hfun : (fun j : ℕ => ‖((p j : ℝ) : ℂ) - ((q j : ℝ) : ℂ)‖ ^ (2 : ℕ))
      = fun j : ℕ => (p - q) j ^ (2 : ℕ) := funext hterm
  rw [hfun] at h
  have h3 : ‖p - q‖ ^ (2 : ℕ) = ‖f - g‖ ^ (2 : ℕ) := by
    rw [lp_two_norm_sq]
    exact h.tsum_eq
  have hnn1 : (0 : ℝ) ≤ ‖f - g‖ := norm_nonneg _
  have hnn2 : (0 : ℝ) ≤ ‖p - q‖ := norm_nonneg _
  nlinarith [h3, hnn1, hnn2]

/-- **The synthesis map preserves sums.** -/
theorem norm_add_eq_of_hasSum_lp {a : ℝ} (ha : 0 < a) {σ : ℕ → ℕ} (hσ : Function.Injective σ)
    (p q : lp (fun _ : ℕ => ℝ) 2) {f g : evenSubspace}
    (hf : HasSum (fun j : ℕ => ((p j : ℝ) : ℂ) • sectorMode a σ j) f)
    (hg : HasSum (fun j : ℕ => ((q j : ℝ) : ℂ) • sectorMode a σ j) g) :
    ‖f + g‖ = ‖p + q‖ := by
  have hgneg : HasSum (fun j : ℕ => (((-q) j : ℝ) : ℂ) • sectorMode a σ j) (-g) := by
    have h := hg.neg
    have hfun : (fun j : ℕ => -(((q j : ℝ) : ℂ) • sectorMode a σ j))
        = fun j : ℕ => (((-q) j : ℝ) : ℂ) • sectorMode a σ j := by
      funext j
      rw [lp.coeFn_neg]
      simp [neg_smul]
    rwa [hfun] at h
  have h := norm_sub_eq_of_hasSum_lp ha hσ p (-q) hf hgneg
  rw [sub_neg_eq_add, sub_neg_eq_add] at h
  exact h

/-- The unit constrained ground coordinates of a sector. -/
def sectorGroundUnit (a : ℝ) (σ : ℕ → ℕ) (j : ℕ) : ℝ :=
  (‖secularLp (sectorLeakage a σ) (sectorCoord a σ)
      (infiniteSecularRoot (sectorLeakage a σ) (sectorCoord a σ))‖)⁻¹
    * sectorGroundCoeff a σ j

/-- The unit two-mode seed coordinates of a sector. -/
def sectorSeedUnit (a : ℝ) (σ : ℕ → ℕ) (j : ℕ) : ℝ :=
  (‖twoModeSeedLp (sectorCoord a σ)‖)⁻¹ * twoModeSeedFun (sectorCoord a σ) j

theorem sectorGroundUnit_eq {a : ℝ} {σ : ℕ → ℕ}
    (hmem : Memℓp (secularVector (sectorLeakage a σ) (sectorCoord a σ)
      (infiniteSecularRoot (sectorLeakage a σ) (sectorCoord a σ))) 2) (j : ℕ) :
    ((‖secularLp (sectorLeakage a σ) (sectorCoord a σ)
        (infiniteSecularRoot (sectorLeakage a σ) (sectorCoord a σ))‖)⁻¹ •
      secularLp (sectorLeakage a σ) (sectorCoord a σ)
        (infiniteSecularRoot (sectorLeakage a σ) (sectorCoord a σ))) j
      = sectorGroundUnit a σ j := by
  rw [lp.coeFn_smul, Pi.smul_apply, secularLp_coeFn hmem, smul_eq_mul]
  rfl

theorem sectorSeedUnit_eq {a : ℝ} {σ : ℕ → ℕ} (j : ℕ) :
    ((‖twoModeSeedLp (sectorCoord a σ)‖)⁻¹ • twoModeSeedLp (sectorCoord a σ)) j
      = sectorSeedUnit a σ j := by
  rw [lp.coeFn_smul, Pi.smul_apply, twoModeSeedLp_coeFn, smul_eq_mul]
  rfl

theorem sectorLeakage_positive_eq (a : ℝ) :
    sectorLeakage a positiveSectorIndex = fun j : ℕ => evenProlateSignedLeakage a (2 * j) := rfl

theorem sectorCoord_positive_eq (a : ℝ) :
    sectorCoord a positiveSectorIndex
      = fun j : ℕ => ‖evenProlateConstraintCoord a (2 * j)‖ := rfl

/-- **Equation `(4)` in the operator's own terms.**  The unit constrained ground eigenvector of the
compressed leakage operator on the Fourier-even sector converges, up to sign, to the normalized
two-mode seed at rate `O(lambda^{-7})`. -/
theorem constrainedProlateEven_operator_ground_distance_isBigO :
    ∃ C : ℝ, ∀ᶠ lam : ℝ in atTop,
      ∀ f g : evenSubspace,
        HasSum (fun j : ℕ => ((sectorGroundUnit lam positiveSectorIndex j : ℝ) : ℂ)
          • sectorMode lam positiveSectorIndex j) f →
        HasSum (fun j : ℕ => ((sectorSeedUnit lam positiveSectorIndex j : ℝ) : ℂ)
          • sectorMode lam positiveSectorIndex j) g →
        min ‖f - g‖ ‖f + g‖ ≤ C * (lam ^ (7 : ℕ))⁻¹ := by
  obtain ⟨K, hK, hO⟩ := constrainedProlateEven_ground_distance_isBigO
  obtain ⟨C, hC⟩ := hO.bound
  refine ⟨C, ?_⟩
  have hne0 : constrainedProlateHermiteCoordinate 0 ≠ 0 := by
    rw [constrainedProlateHermiteCoordinate_zero_eq]
    positivity
  have hne1 : constrainedProlateHermiteCoordinate 1 ≠ 0 := by
    rw [constrainedProlateHermiteCoordinate_one_eq]
    positivity
  filter_upwards [hC, ladderEnvelope_evenProlateSignedLeakage.first_struct,
    (tendsto_norm_evenProlateConstraintCoord_atTop 0).eventually_ne hne0,
    (tendsto_norm_evenProlateConstraintCoord_atTop 1).eventually_ne hne1,
    eventually_gt_atTop (0 : ℝ)] with lam hbd hs h0 h1 hlam f g hf hg
  have hσ : Function.Injective positiveSectorIndex := positiveSectorIndex_injective
  have hsumL : Summable fun j : ℕ => sectorCoord lam positiveSectorIndex j ^ (2 : ℕ) := summable_sectorCoord_sq lam hσ
  have hmem : Memℓp (secularVector (sectorLeakage lam positiveSectorIndex) (sectorCoord lam positiveSectorIndex)
      (infiniteSecularRoot (sectorLeakage lam positiveSectorIndex) (sectorCoord lam positiveSectorIndex))) 2 :=
    memℓp_secularVector hs.1.2.1 hs.1.2.2 hs.2 hsumL h0 h1
  set P : lp (fun _ : ℕ => ℝ) 2 :=
    (‖secularLp (sectorLeakage lam positiveSectorIndex) (sectorCoord lam positiveSectorIndex)
        (infiniteSecularRoot (sectorLeakage lam positiveSectorIndex) (sectorCoord lam positiveSectorIndex))‖)⁻¹ •
      secularLp (sectorLeakage lam positiveSectorIndex) (sectorCoord lam positiveSectorIndex)
        (infiniteSecularRoot (sectorLeakage lam positiveSectorIndex) (sectorCoord lam positiveSectorIndex)) with hPdef
  set Q : lp (fun _ : ℕ => ℝ) 2 :=
    (‖twoModeSeedLp (sectorCoord lam positiveSectorIndex)‖)⁻¹ • twoModeSeedLp (sectorCoord lam positiveSectorIndex) with hQdef
  have hPfun : (fun j : ℕ => ((sectorGroundUnit lam positiveSectorIndex j : ℝ) : ℂ) • sectorMode lam positiveSectorIndex j)
      = fun j : ℕ => ((P j : ℝ) : ℂ) • sectorMode lam positiveSectorIndex j := by
    funext j
    rw [hPdef, sectorGroundUnit_eq hmem j]
  have hQfun : (fun j : ℕ => ((sectorSeedUnit lam positiveSectorIndex j : ℝ) : ℂ) • sectorMode lam positiveSectorIndex j)
      = fun j : ℕ => ((Q j : ℝ) : ℂ) • sectorMode lam positiveSectorIndex j := by
    funext j
    rw [hQdef, sectorSeedUnit_eq j]
  rw [hPfun] at hf
  rw [hQfun] at hg
  have hsub : ‖f - g‖ = ‖P - Q‖ := norm_sub_eq_of_hasSum_lp hlam hσ P Q hf hg
  have hadd : ‖f + g‖ = ‖P + Q‖ := norm_add_eq_of_hasSum_lp hlam hσ P Q hf hg
  have hbd' : min ‖P - Q‖ ‖P + Q‖ ≤ C * (lam ^ (7 : ℕ))⁻¹ := by
    have hmin : (0 : ℝ) ≤ min ‖P - Q‖ ‖P + Q‖ := le_min (norm_nonneg _) (norm_nonneg _)
    have hpow : (0 : ℝ) < (lam ^ (7 : ℕ))⁻¹ := by positivity
    have hb : ‖min ‖P - Q‖ ‖P + Q‖‖ ≤ C * ‖(lam ^ (7 : ℕ))⁻¹‖ := hbd
    rwa [Real.norm_eq_abs, abs_of_nonneg hmin, Real.norm_eq_abs, abs_of_pos hpow] at hb
  rw [hsub, hadd]
  exact hbd'

end RHTower

end
