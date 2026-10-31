import GaloisForLFunctions.ConjugateDiagonalGeometry.FiniteThetaProductCurrents
import GaloisForLFunctions.ConjugateDiagonalGeometry.HorizontalCollisionGaussian
import GaloisForLFunctions.ConjugateDiagonalGeometry.FiniteThetaReadingsRecoverCompactCurrents

/-!
# Integer theta prefixes read the horizontal collision charge

A compact Gaussian pair test is evaluated against two finite theta curvature
currents. The prefix stage dominates the separate Laplacian norms, so the
product-current error tends to zero even as the test sharpens.

The reading uses no divisor locations. Its error is bounded by
`εₙ(2Qₖ(χ)+εₙ)+M² exp(-δ²n²)` once `n≥ceil(1/δ)`, where `δ` is the least
relevant nonzero coordinate or endpoint separation in the finite divisor.
The reading converges to the actual multiplicity-weighted collision charge;
rounding eventually recovers that integer exactly.
-/

open Complex MeasureTheory Filter Set Metric Laplacian InnerProductSpace
open scoped Laplacian Topology Classical
namespace GaloisForLFunctions.ConjugateDiagonalGeometry
noncomputable section

def finiteThetaPairSourceReading (F : ℂ → ℂ → ℝ) (n : ℕ) : ℝ :=
  finiteThetaSourceReading (fun z => finiteThetaSourceReading (F z) n) n

private theorem cutoff_mul_eq_self_of_ball_support {φ : ℂ → ℝ} {r : ℝ} {k : ℕ}
    (hr : r ≤ (k : ℝ) + 1) (hs : ∀ z, z ∉ closedBall (0 : ℂ) r → φ z = 0) :
    (fun z => sourceCutoff k z * φ z) = φ := by
  funext z
  by_cases hz : z ∈ closedBall (0 : ℂ) r
  · have hk : sourceCutoff k z = 1 := by
      apply (sourceCutoff k).one_of_mem_closedBall
      rw [mem_closedBall] at hz ⊢
      exact hz.trans hr
    rw [hk, one_mul]
  · rw [hs z hz, mul_zero]

/-- The product-current error uses only separate second derivatives and an actual source mass. -/
theorem exists_finiteTheta_pair_current_error :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ R : ℕ, ∀ F : ℂ → ℂ → ℝ,
      ContDiff ℝ 2 (Function.uncurry F) → (∀ z w, |F z w| ≤ 1) →
      (∀ z w, z ∉ closedBall (0 : ℂ) ((R : ℝ) + 2) ∨
        w ∉ closedBall (0 : ℂ) ((R : ℝ) + 2) → F z w = 0) →
      ∀ k : ℕ, R + 3 ≤ k →
      let B := pairTestDifferentialBound F R
      let ε := K * B * Real.exp (-((k : ℝ)^4) + 56*(k : ℝ)^2 + 62)
      let S := (RHTower.xi_zeros_closedBall_finite 0 ((R : ℝ) + 3)).toFinset
      |finiteThetaPairSourceReading F k -
        ∑ z ∈ S, (HTGeometry.zeroMult RHTower.xi z : ℝ) *
          (∑ w ∈ S, (HTGeometry.zeroMult RHTower.xi w : ℝ) * F z w)| ≤
        ε * (2 * finiteThetaSourceReading (sourceCutoff (R + 1)) k + ε) := by
  obtain ⟨K, hK, hscalar⟩ := exists_uniform_finiteTheta_compact_current_error
  refine ⟨K, hK, fun R F hF hbound hzero k hk => ?_⟩
  dsimp only
  let B := pairTestDifferentialBound F R
  let ε := K * B * Real.exp (-((k : ℝ)^4) + 56*(k : ℝ)^2 + 62)
  let S := (RHTower.xi_zeros_closedBall_finite 0 ((R : ℝ) + 3)).toFinset
  let m : ℂ → ℝ := fun z => HTGeometry.zeroMult RHTower.xi z
  let χ : ℂ → ℝ := sourceCutoff (R + 1)
  have hB : 0 ≤ B := zero_le_one.trans (one_le_pairTestDifferentialBound F R)
  have hε : 0 ≤ ε := by dsimp only [ε]; positivity
  have hk1 : 1 ≤ k := by omega
  have hkR : (R : ℝ) + 3 ≤ (k : ℝ) + 1 := by exact_mod_cast (show R + 3 ≤ k + 1 by omega)
  have hread (φ : ℂ → ℝ) (hp : ContDiff ℝ 2 φ)
      (hs : ∀ z, z ∉ closedBall (0 : ℂ) ((R : ℝ) + 3) → φ z = 0)
      (C : ℝ) (hC : 0 ≤ C) (hΔ : ∀ z, |Δ φ z| ≤ C) :
      |finiteThetaSourceReading φ k - ∑ z ∈ S, m z * φ z| ≤
        K * C * Real.exp (-((k : ℝ)^4) + 56*(k : ℝ)^2 + 62) := by
    have hc := HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) ((R : ℝ) + 3)) hs
    have he := hscalar k hk1 φ hp hc C hC
      (cutoff_mul_eq_self_of_ball_support hkR hs) hΔ
    rwa [zetaSourceTrace_eq_sum_on_ball _ φ hs] at he
  have hsmall {z : ℂ} (hz : z ∉ closedBall (0 : ℂ) ((R : ℝ) + 3)) :
      z ∉ closedBall (0 : ℂ) ((R : ℝ) + 2) := by
    intro h
    apply hz
    rw [mem_closedBall] at h ⊢
    linarith only [h]
  have hrow (z : ℂ) : ContDiff ℝ 2 (F z) := hF.comp (contDiff_const.prodMk contDiff_id)
  have hcol (w : ℂ) : ContDiff ℝ 2 (fun z => F z w) := hF.comp (contDiff_id.prodMk contDiff_const)
  have hrowerr (z : ℂ) : |finiteThetaSourceReading (F z) k - ∑ w ∈ S, m w * F z w| ≤ ε * χ z := by
    exact (hread (F z) (hrow z) (fun w hw => hzero z w (Or.inr (hsmall hw)))
      (B * χ z) (mul_nonneg hB (sourceCutoff (R + 1)).nonneg)
      (fun w => pairTestDifferentialBound_row_global hF R hzero z w)).trans_eq
        (by dsimp only [ε]; ring)
  have hswap : ContDiff ℝ 2 (Function.uncurry (fun z w => F w z)) :=
    hF.comp (contDiff_snd.prodMk contDiff_fst)
  have hcolerr (w : ℂ) :
      |finiteThetaSourceReading (fun z => F z w) k - ∑ z ∈ S, m z * F z w| ≤ ε * χ w := by
    have hΔ (z : ℂ) : |Δ (fun u => F u w) z| ≤ B * χ w := by
      simpa only [pairTestDifferentialBound_swap] using
        pairTestDifferentialBound_row_global hswap R
          (fun u v h => hzero v u h.symm) w z
    exact (hread (fun z => F z w) (hcol w) (fun z hz => hzero z w (Or.inl (hsmall hz)))
      (B * χ w) (mul_nonneg hB (sourceCutoff (R + 1)).nonneg) hΔ).trans_eq
        (by dsimp only [ε]; ring)
  have hχsupp (z : ℂ) (hz : z ∉ closedBall (0 : ℂ) ((R : ℝ) + 3)) : χ z = 0 := by
    apply (sourceCutoff (R + 1)).zero_of_le_dist
    change (((R + 1 : ℕ) : ℝ) + 2) ≤ dist z 0
    rw [mem_closedBall] at hz
    push_cast
    linarith only [lt_of_not_ge hz]
  have hχΔ (z : ℂ) : |Δ χ z| ≤ B :=
    (abs_sourceCutoffLaplacian_le (R + 1) z).trans (by
      dsimp only [B, pairTestDifferentialBound]
      exact le_add_of_nonneg_left (by positivity))
  have hmass : |finiteThetaSourceReading χ k - ∑ z ∈ S, m z * χ z| ≤ ε :=
    hread χ (sourceCutoff (R + 1)).contDiff hχsupp B hB hχΔ
  have hmass' : (∑ z ∈ S, m z * χ z) ≤ finiteThetaSourceReading χ k + ε := by
    have h := (abs_le.mp hmass).1
    linarith only [h]
  have hprod := abs_finiteThetaProductSourceReading_sub_finitePair_le
    (fun z => (hrow z).continuous) (fun w => (hcol w).continuous) hbound S m
    (fun z _ => Nat.cast_nonneg _) (sourceCutoff (R + 1)).continuous k hrowerr hcolerr
  have hsum : finiteThetaSourceReading χ k + (∑ z ∈ S, m z * χ z) ≤
      2 * finiteThetaSourceReading χ k + ε := by linarith only [hmass']
  exact hprod.trans (mul_le_mul_of_nonneg_left hsum hε)

#print axioms exists_finiteTheta_pair_current_error

/-- The differential cost is computed from the compact Gaussian test, without divisor data. -/
def thetaCollisionDifferentialCost (T : ℝ) (n : ℕ) : ℝ :=
  pairTestDifferentialBound (collisionWindowPairTest T (collisionWindowRadius T) n)
    (collisionWindowRadius T)

def thetaCollisionStage (T : ℝ) (n : ℕ) : ℕ :=
  thetaTestStage (collisionWindowRadius T) n (thetaCollisionDifferentialCost T n)

/-- A finite integer theta-prefix reading of the horizontal collision kernel. -/
def finiteThetaCollisionReading (T : ℝ) (n : ℕ) : ℝ :=
  finiteThetaPairSourceReading (collisionWindowPairTest T (collisionWindowRadius T) n)
    (thetaCollisionStage T n)

def thetaCollisionCurrentError (K T : ℝ) (n : ℕ) : ℝ :=
  K * thetaCollisionDifferentialCost T n * Real.exp
    (-((thetaCollisionStage T n : ℝ)^4) + 56*(thetaCollisionStage T n : ℝ)^2 + 62)

theorem tendsto_thetaCollisionStage (T : ℝ) : Tendsto (thetaCollisionStage T) atTop atTop :=
  tendsto_atTop_mono (fun n => le_thetaTestStage _ n _) tendsto_id

theorem tendsto_thetaCollisionCurrentError {K : ℝ} (hK : 0 ≤ K) (T : ℝ) :
    Tendsto (thetaCollisionCurrentError K T) atTop (𝓝 0) :=
  tendsto_thetaTestStage_error (collisionWindowRadius T)
    (fun _n => zero_le_one.trans (one_le_pairTestDifferentialBound _ _)) hK

/-- The literal collision pair reading has a universal source-current error. -/
theorem exists_thetaCollision_pair_error :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (T : ℝ) (n : ℕ),
      let R := collisionWindowRadius T
      let S := (RHTower.xi_zeros_closedBall_finite 0 ((R : ℝ) + 3)).toFinset
      |finiteThetaCollisionReading T n -
        ∑ z ∈ S, (HTGeometry.zeroMult RHTower.xi z : ℝ) *
          (∑ w ∈ S, (HTGeometry.zeroMult RHTower.xi w : ℝ) *
            collisionWindowPairTest T R n z w)| ≤
        thetaCollisionCurrentError K T n *
          (2 * finiteThetaSourceReading (sourceCutoff (R + 1)) (thetaCollisionStage T n) +
            thetaCollisionCurrentError K T n) := by
  obtain ⟨K, hK, hpair⟩ := exists_finiteTheta_pair_current_error
  refine ⟨K, hK, fun T n => ?_⟩
  exact hpair (collisionWindowRadius T)
    (collisionWindowPairTest T (collisionWindowRadius T) n)
    (contDiff_collisionWindowPairTest T _ n) (abs_collisionWindowPairTest_le_one T _ n)
    (collisionWindowPairTest_eq_zero_outside T _ n) (thetaCollisionStage T n)
    (by unfold thetaCollisionStage thetaTestStage; omega)

theorem tendsto_thetaCollisionProductError {K : ℝ} (hK : 0 ≤ K) (T : ℝ) :
    Tendsto (fun n : ℕ => thetaCollisionCurrentError K T n *
      (2 * finiteThetaSourceReading (sourceCutoff (collisionWindowRadius T + 1))
        (thetaCollisionStage T n) + thetaCollisionCurrentError K T n)) atTop (𝓝 0) := by
  have he := tendsto_thetaCollisionCurrentError hK T
  have hm := (tendsto_finiteThetaSourceReading_compact
    (sourceCutoff (collisionWindowRadius T + 1))
    (sourceCutoff (collisionWindowRadius T + 1)).contDiff
    (sourceCutoff (collisionWindowRadius T + 1)).hasCompactSupport).comp
      (tendsto_thetaCollisionStage T)
  simpa only [Function.comp_apply, zero_mul, add_zero] using he.mul ((hm.const_mul 2).add he)

#print axioms exists_thetaCollision_pair_error
#print axioms tendsto_thetaCollisionProductError

/-- Endpoint marks make the height collars quantitative on the entire compact divisor. -/
def collisionWindowSeparationSet (T : ℝ) : Finset ℂ :=
  insert 0 (insert (⟨0, T⟩ : ℂ)
    (RHTower.xi_zeros_closedBall_finite 0 ((collisionWindowRadius T : ℝ) + 3)).toFinset)

/-- The minimum nonzero pair-coordinate or window-endpoint separation. -/
def collisionWindowGap (T : ℝ) : ℝ :=
  min (finiteCollisionGap (RHTower.stripZeros_finite T).toFinset)
    (finiteCoordinateGap (collisionWindowSeparationSet T) Complex.im)

theorem collisionWindowGap_pos (T : ℝ) : 0 < collisionWindowGap T :=
  lt_min (finiteCollisionGap_pos _) (finiteCoordinateGap_pos _ _)

def collisionWindowThreshold (T : ℝ) : ℕ := Nat.ceil (1 / collisionWindowGap T)

private theorem collisionWindowCutoff_eq_window_of_gap (T : ℝ) (n : ℕ) {z : ℂ}
    (hz : z ∈ (RHTower.xi_zeros_closedBall_finite 0
      ((collisionWindowRadius T : ℝ) + 3)).toFinset)
    (hn : 1 ≤ (n : ℝ) * collisionWindowGap T) :
    collisionWindowCutoff T (collisionWindowRadius T) n z =
      if z ∈ RHTower.stripZeros T then 1 else 0 := by
  have hzS : z ∈ collisionWindowSeparationSet T :=
    Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hz)
  have hzero : (0 : ℂ) ∈ collisionWindowSeparationSet T := Finset.mem_insert_self _ _
  have htop : (⟨0, T⟩ : ℂ) ∈ collisionWindowSeparationSet T :=
    Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have hgap0 (h : z.im ≠ 0) : collisionWindowGap T ≤ |z.im| := by
    have he := (min_le_right
      (finiteCollisionGap (RHTower.stripZeros_finite T).toFinset)
      (finiteCoordinateGap (collisionWindowSeparationSet T) Complex.im)).trans
        (finiteCoordinateGap_le _ Complex.im hzS hzero (by simpa only [zero_im] using h))
    simpa only [collisionWindowGap, zero_im, sub_zero] using he
  have hgapT (h : z.im ≠ T) : collisionWindowGap T ≤ |T - z.im| :=
    (min_le_right _ _).trans (finiteCoordinateGap_le _ Complex.im htop hzS h.symm)
  have hh : collisionHeightCutoff T n z.im = if 0 ≤ z.im ∧ z.im < T then 1 else 0 := by
    by_cases hy : 0 ≤ z.im
    · by_cases hT : z.im < T
      · have hg : collisionWindowGap T ≤ T - z.im := by
          simpa only [abs_of_pos (sub_pos.mpr hT)] using hgapT hT.ne
        have hprod : 1 ≤ (n : ℝ) * (T - z.im) :=
          hn.trans (mul_le_mul_of_nonneg_left hg (Nat.cast_nonneg _))
        rw [if_pos ⟨hy, hT⟩, collisionHeightCutoff,
          Real.smoothTransition.one_of_one_le (by
            nlinarith only [mul_nonneg (Nat.cast_nonneg n) hy]),
          Real.smoothTransition.one_of_one_le hprod, mul_one]
      · rw [if_neg (fun h => hT h.2), collisionHeightCutoff,
          Real.smoothTransition.zero_of_nonpos
            (mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg n)
              (sub_nonpos.mpr (le_of_not_gt hT))), mul_zero]
    · have hy0 : z.im < 0 := lt_of_not_ge hy
      have hg : collisionWindowGap T ≤ -z.im := by
        simpa only [abs_of_neg hy0] using hgap0 hy0.ne
      have hprod := hn.trans (mul_le_mul_of_nonneg_left hg (Nat.cast_nonneg n))
      rw [if_neg (fun h => hy h.1), collisionHeightCutoff,
        Real.smoothTransition.zero_of_nonpos (by nlinarith only [hprod]), zero_mul]
  rw [collisionWindowCutoff, hh]
  by_cases hw : z ∈ RHTower.stripZeros T
  · rw [if_pos hw, if_pos ⟨hw.1.2.2.1, hw.1.2.2.2⟩,
      sourceCutoff_collisionWindowRadius_eq_one hw.1, mul_one]
  · have hh' : ¬ (0 ≤ z.im ∧ z.im < T) := by
      intro hi
      have hs := RHTower.xi_zero_re_mem_open_unit
        ((RHTower.xi_zeros_closedBall_finite 0
          ((collisionWindowRadius T : ℝ) + 3)).mem_toFinset.mp hz).2
      exact hw ⟨⟨hs.1, hs.2, hi.1, hi.2⟩,
        ((RHTower.xi_zeros_closedBall_finite 0
          ((collisionWindowRadius T : ℝ) + 3)).mem_toFinset.mp hz).2⟩
    rw [if_neg hw, if_neg hh', mul_zero]

private theorem collisionPairSum_eq_window_of_gap (T : ℝ) (n : ℕ)
    (hgap : 1 ≤ (n : ℝ) * collisionWindowGap T) :
    let R := collisionWindowRadius T
    let S := (RHTower.xi_zeros_closedBall_finite 0 ((R : ℝ) + 3)).toFinset
    (∑ z ∈ S, (HTGeometry.zeroMult RHTower.xi z : ℝ) *
        (∑ w ∈ S, (HTGeometry.zeroMult RHTower.xi w : ℝ) *
          collisionWindowPairTest T R n z w)) = xiWindowGaussianPairSum T ((n : ℝ)^2) := by
  classical
  let R := collisionWindowRadius T
  let S := (RHTower.xi_zeros_closedBall_finite 0 ((R : ℝ) + 3)).toFinset
  let W := (RHTower.stripZeros_finite T).toFinset
  let m : ℂ → ℝ := fun z => HTGeometry.zeroMult RHTower.xi z
  have hsub : W ⊆ S := by
    intro z hz
    have hwin := (RHTower.stripZeros_finite T).mem_toFinset.mp hz
    have hχ := sourceCutoff_collisionWindowRadius_eq_one hwin.1
    have hs : z ∈ Function.support (sourceCutoff R : ℂ → ℝ) := by
      change sourceCutoff R z ≠ 0
      rw [hχ]
      exact one_ne_zero
    rw [(sourceCutoff R).support_eq] at hs
    change dist z 0 < (R : ℝ) + 2 at hs
    apply (RHTower.xi_zeros_closedBall_finite 0 ((R : ℝ) + 3)).mem_toFinset.mpr
    refine ⟨?_, hwin.2⟩
    rw [mem_closedBall]
    linarith only [hs]
  have hn (z : ℂ) (hz : z ∈ S) :
      collisionWindowCutoff T R n z = if z ∈ RHTower.stripZeros T then 1 else 0 :=
    collisionWindowCutoff_eq_window_of_gap T n hz hgap
  have hcutone (z : ℂ) (hz : z ∈ W) : collisionWindowCutoff T R n z = 1 := by
    simpa only [if_pos ((RHTower.stripZeros_finite T).mem_toFinset.mp hz)] using hn z (hsub hz)
  have hcutzero (z : ℂ) (hz : z ∈ S) (hw : z ∉ W) : collisionWindowCutoff T R n z = 0 := by
    have hnot : z ∉ RHTower.stripZeros T := fun h =>
      hw ((RHTower.stripZeros_finite T).mem_toFinset.mpr h)
    simpa only [if_neg hnot] using hn z hz
  change (∑ z ∈ S, m z * (∑ w ∈ S, m w * collisionWindowPairTest T R n z w)) = _
  calc
    _ = ∑ z ∈ W, m z * (∑ w ∈ S, m w * collisionWindowPairTest T R n z w) := by
      symm
      apply Finset.sum_subset hsub
      intro z hz hw
      simp only [collisionWindowPairTest, hcutzero z hz hw, zero_mul,
        mul_zero, Finset.sum_const_zero]
    _ = xiWindowGaussianPairSum T ((n : ℝ)^2) := by
      apply Finset.sum_congr rfl
      intro z hz
      have hi : (∑ w ∈ S, m w * collisionWindowPairTest T R n z w) =
          ∑ w ∈ W, m w * collisionWindowPairTest T R n z w := by
        symm
        apply Finset.sum_subset hsub
        intro w hw hnot
        simp only [collisionWindowPairTest, hcutzero w hw hnot, mul_zero, zero_mul]
      rw [hi, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro w hw
      rw [collisionWindowPairTest, hcutone z hz, hcutone w hw, one_mul, one_mul]
      ring

private theorem xiWindowGaussianPairSum_error_at_gap (T q : ℝ) (hq : 0 ≤ q) :
    |xiWindowGaussianPairSum T q - (RHTower.xiHorizontalCollisionCharge T : ℝ)| ≤
      (RHTower.xiStripWindowTotalOrder T : ℝ)^2 * Real.exp (-q * (collisionWindowGap T)^2) := by
  let S := (RHTower.stripZeros_finite T).toFinset
  let m := HTGeometry.zeroMult RHTower.xi
  have hd : collisionWindowGap T ≤ finiteCollisionGap S := min_le_left _ _
  have hcharge : (RHTower.xiHorizontalCollisionCharge T : ℝ) =
      ∑ z ∈ S, ∑ w ∈ S, (m z : ℝ) * (m w : ℝ) *
        (if z.im = w.im ∧ z ≠ w then 1 else 0) := by
    rw [RHTower.xiHorizontalCollisionCharge_eq_sum_pairs,
      RHTower.xiHorizontalCollisionPairs, Finset.sum_filter, Finset.sum_product]
    push_cast
    simp only [S, m, HTGeometry.zeroMult, mul_ite, mul_one, mul_zero]
  have h := abs_horizontalCollisionGaussian_pair_error S m (collisionWindowGap_pos T).le
    (fun _ hz _ hw h => hd.trans ((min_le_left _ _).trans (finiteCoordinateGap_le S _ hz hw h)))
    (fun _ hz _ hw h => hd.trans ((min_le_right _ _).trans (finiteCoordinateGap_le S _ hz hw h))) q hq
  rw [← hcharge] at h
  simpa only [xiWindowGaussianPairSum, RHTower.xiStripWindowTotalOrder,
    Nat.cast_sum, m, HTGeometry.zeroMult] using h

/-- The explicit separation threshold pays both collars and the Gaussian pair error. -/
theorem finiteThetaCollisionReading_error :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (T : ℝ) (n : ℕ), collisionWindowThreshold T ≤ n →
      |finiteThetaCollisionReading T n - (RHTower.xiHorizontalCollisionCharge T : ℝ)| ≤
        thetaCollisionCurrentError K T n *
          (2 * finiteThetaSourceReading (sourceCutoff (collisionWindowRadius T + 1))
            (thetaCollisionStage T n) + thetaCollisionCurrentError K T n) +
        (RHTower.xiStripWindowTotalOrder T : ℝ)^2 *
          Real.exp (-((n : ℝ)^2) * (collisionWindowGap T)^2) := by
  obtain ⟨K, hK, hpair⟩ := exists_thetaCollision_pair_error
  refine ⟨K, hK, fun T n hn => ?_⟩
  have hn' : Nat.ceil (1 / collisionWindowGap T) ≤ n := hn
  have hgap : 1 ≤ (n : ℝ) * collisionWindowGap T :=
    (div_le_iff₀ (collisionWindowGap_pos T)).mp
      ((Nat.le_ceil _).trans (by exact_mod_cast hn'))
  have hp := hpair T n
  dsimp only at hp
  rw [collisionPairSum_eq_window_of_gap T n hgap] at hp
  have htriangle := dist_triangle (finiteThetaCollisionReading T n)
    (xiWindowGaussianPairSum T ((n : ℝ)^2)) (RHTower.xiHorizontalCollisionCharge T : ℝ)
  simp only [Real.dist_eq] at htriangle
  exact htriangle.trans (add_le_add hp
    (xiWindowGaussianPairSum_error_at_gap T _ (sq_nonneg (n : ℝ))))

theorem exists_finiteThetaCollisionReading_error :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ T : ℝ, ∃ δ > 0, ∀ᶠ n : ℕ in atTop,
      |finiteThetaCollisionReading T n - (RHTower.xiHorizontalCollisionCharge T : ℝ)| ≤
        thetaCollisionCurrentError K T n *
          (2 * finiteThetaSourceReading (sourceCutoff (collisionWindowRadius T + 1))
            (thetaCollisionStage T n) + thetaCollisionCurrentError K T n) +
        (RHTower.xiStripWindowTotalOrder T : ℝ)^2 * Real.exp (-((n : ℝ)^2) * δ^2) := by
  obtain ⟨K, hK, he⟩ := finiteThetaCollisionReading_error
  refine ⟨K, hK, fun T => ⟨collisionWindowGap T, collisionWindowGap_pos T, ?_⟩⟩
  filter_upwards [eventually_ge_atTop (collisionWindowThreshold T)] with n hn
  exact he T n hn

#print axioms finiteThetaCollisionReading_error
#print axioms exists_finiteThetaCollisionReading_error

theorem finiteThetaCollisionReading_nonneg (T : ℝ) (n : ℕ) :
    0 ≤ finiteThetaCollisionReading T n := by
  apply finiteThetaSourceReading_nonneg
  intro z
  apply finiteThetaSourceReading_nonneg
  intro w
  exact mul_nonneg (mul_nonneg
    (collisionWindowCutoff_nonneg T _ n z) (collisionWindowCutoff_nonneg T _ n w))
    (horizontalCollisionGaussian_nonneg (sq_nonneg (n : ℝ)) z w)

/-- Finite integer theta prefixes recover the actual horizontal collision charge. -/
theorem tendsto_finiteThetaCollisionReading (T : ℝ) :
    Tendsto (finiteThetaCollisionReading T) atTop
      (𝓝 (RHTower.xiHorizontalCollisionCharge T : ℝ)) := by
  obtain ⟨K, hK, he⟩ := exists_finiteThetaCollisionReading_error
  obtain ⟨δ, hδ, herr⟩ := he T
  have hlim := (tendsto_thetaCollisionProductError hK T).add
    (tendsto_collisionGaussian_error hδ (RHTower.xiStripWindowTotalOrder T : ℝ))
  simp only [add_zero] at hlim
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (herr.and (hlim.eventually_lt_const hε))
  exact ⟨N, fun n hn => by
    simpa only [Real.dist_eq] using (hN n hn).1.trans_lt (hN n hn).2⟩

/-- Rounding eventually reads the exact integer charge, including its multiplicities. -/
theorem eventually_floor_finiteThetaCollisionReading (T : ℝ) :
    ∀ᶠ n : ℕ in atTop, Nat.floor (finiteThetaCollisionReading T n + 1 / 2) =
      RHTower.xiHorizontalCollisionCharge T := by
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (tendsto_finiteThetaCollisionReading T)
    (1 / 4) (by norm_num)
  filter_upwards [eventually_ge_atTop N] with n hn
  have h : |finiteThetaCollisionReading T n -
      (RHTower.xiHorizontalCollisionCharge T : ℝ)| < 1 / 4 := by
    simpa only [Real.dist_eq] using hN n hn
  apply (Nat.floor_eq_iff (add_nonneg (finiteThetaCollisionReading_nonneg T n)
    (by norm_num))).mpr
  constructor <;> linarith only [(abs_lt.mp h).1, (abs_lt.mp h).2]

#print axioms tendsto_finiteThetaCollisionReading
#print axioms eventually_floor_finiteThetaCollisionReading

end
end GaloisForLFunctions.ConjugateDiagonalGeometry
