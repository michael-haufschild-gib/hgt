import GaloisForLFunctions.RenormalizedIntersectionTheory.GaussMayerRawNegativeUnitDeterminants
import GaloisForLFunctions.RenormalizedIntersectionTheory.GaussMayerDeterminantPerturbation
import GaloisForLFunctions.RenormalizedIntersectionTheory.GaussMayerComplementaryDeterminant

/-!
# Exact finite part of finite-branch Mayer determinants

Double centering removes the constant input and output from each actual
Gauss branch and improves its decay to `n^(-Re w-2)`. The complementary
Cauchy matrix identifies the coefficient of the scalar rank-one mode.
A dimension-independent determinant perturbation estimate then proves
`E_N-a_N B → A` throughout `Re w>0`, where `D=A+ζ B` is the actual
source determinant and `E_N` is the genuine finite-branch determinant.

Away from `w=1`, subtracting `N^(1-w)B/(1-w)` gives limit `D`.
In the critical strip, raw determinants converge exactly when `B=0`;
otherwise their norms have the sharp growth coefficient `‖B‖/‖1-w‖`.
-/

open Complex Metric Set Filter Topology
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.RenormalizedIntersectionTheory.MayerCutoff
open GaloisForLFunctions.RenormalizedIntersectionTheory.MayerNuclear
open GaloisForLFunctions.RenormalizedIntersectionTheory.MayerFredholm
open GaloisForLFunctions.RenormalizedIntersectionTheory.MayerParameter
open GaloisForLFunctions.RenormalizedIntersectionTheory.MayerRaw
set_option autoImplicit false
noncomputable section
namespace GaloisForLFunctions.RenormalizedIntersectionTheory.MayerFinitePart

/-- Remove the value at zero from a disc-algebra function. -/
def centering : DiscSpace →L[ℂ] DiscSpace :=
  ContinuousLinearMap.id ℂ DiscSpace-constantProjection

theorem centering_apply (f : DiscSpace) (z : Disc) :
    (centering f).1 z = f.1 z-f.1 zeroPoint := rfl

/-- Compress away the constant output and the evaluation input. -/
def compressed (T : DiscSpace →L[ℂ] DiscSpace) : DiscSpace →L[ℂ] DiscSpace :=
  centering ∘L T ∘L centering

theorem compressed_sub (T U : DiscSpace →L[ℂ] DiscSpace) :
    compressed (T-U) = compressed T-compressed U := by
  apply ContinuousLinearMap.ext
  intro f
  simp only [compressed, ContinuousLinearMap.comp_apply, _root_.sub_apply, map_sub]

theorem compressed_smul (a : ℂ) (T : DiscSpace →L[ℂ] DiscSpace) :
    compressed (a • T) = a • compressed T := by
  apply ContinuousLinearMap.ext
  intro f
  simp only [compressed, ContinuousLinearMap.comp_apply, _root_.smul_apply, map_smul]

theorem compressed_projection : compressed constantProjection = 0 := by
  apply ContinuousLinearMap.ext
  intro f
  apply Subtype.ext
  ext z
  change (f.1 zeroPoint-f.1 zeroPoint)-(f.1 zeroPoint-f.1 zeroPoint) = 0
  ring

theorem compressed_branchRemainder {w : ℂ} (hw : 0 < w.re) {n : ℕ} (hn : 1 ≤ n) :
    compressed (branchRemainder w hw n hn) = compressed (branch w hw n hn) := by
  rw [branchRemainder, compressed_sub, compressed_smul, compressed_projection, smul_zero, sub_zero]

private theorem plane_centering (f : DiscSpace) {z : ℂ} (hz : z ∈ outer) :
    plane (centering f) z = plane f z-f.1 zeroPoint := by
  rw [plane_eq (centering f) ⟨z,hz⟩, centering_apply, plane_eq f ⟨z,hz⟩]

/-- Double centering creates two differences, each carrying an additional branch denominator. -/
theorem compressed_branch_apply {w : ℂ} (hw : 0 < w.re) {n : ℕ} (hn : 1 ≤ n)
    (f : DiscSpace) (z : Disc) :
    (compressed (branch w hw n hn) f).1 z =
      ((n : ℂ)+z.1)^(-w) *
        (plane f (((n : ℂ)+z.1)⁻¹)-plane f ((n : ℂ)⁻¹)) +
      (((n : ℂ)+z.1)^(-w)-(n : ℂ)^(-w)) *
        (plane f ((n : ℂ)⁻¹)-f.1 zeroPoint) := by
  have hu : ((n : ℂ)+z.1)⁻¹ ∈ outer :=
    closedBall_subset_closedBall (by norm_num : (1 : ℝ) ≤ 3/2)
      (inverse_branch_inner hn z.property)
  have hu0 : (n : ℂ)⁻¹ ∈ outer := by
    have h := closedBall_subset_closedBall (by norm_num : (1 : ℝ) ≤ 3/2)
      (inverse_branch_inner hn zeroPoint.property)
    simpa only [zeroPoint, add_zero] using h
  change (centering (branch w hw n hn (centering f))).1 z = _
  rw [centering_apply, branch_apply, branch_apply]
  change ((n : ℂ)+z.1)^(-w)*plane (centering f) (((n : ℂ)+z.1)⁻¹) -
    ((n : ℂ)+0)^(-w)*plane (centering f) (((n : ℂ)+0)⁻¹) = _
  rw [add_zero, plane_centering f hu, plane_centering f hu0]
  ring

/-- Inverse branches gain two powers when their base point is subtracted. -/
theorem inverse_branch_difference_bound {n : ℕ} (hn : 1 ≤ n) {z : ℂ} (hz : z ∈ outer) :
    ‖((n : ℂ)+z)⁻¹-(n : ℂ)⁻¹‖ ≤ 5/(n : ℝ)^2 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnc : (n : ℂ) ≠ 0 := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn).ne'
  have hz' : ‖z-1‖ ≤ (3/2 : ℝ) := by simpa only [mem_closedBall, dist_eq_norm] using hz
  have hzn : ‖z‖ ≤ (5/2 : ℝ) := by
    have h := norm_add_le (z-1) (1 : ℂ)
    rw [sub_add_cancel, norm_one] at h
    linarith only [h,hz']
  have ha : (n : ℂ)+z ≠ 0 := by
    have hlow := (neg_le_abs (z-1).re).trans ((Complex.abs_re_le_norm _).trans hz')
    simp only [Complex.sub_re, Complex.one_re] at hlow
    intro he
    have hre := congrArg Complex.re he
    simp only [Complex.add_re, Complex.natCast_re, Complex.zero_re] at hre
    linarith only [hn1,hlow,hre]
  have he : ((n : ℂ)+z)⁻¹-(n : ℂ)⁻¹ = -z*((n : ℂ)+z)⁻¹*(n : ℂ)⁻¹ := by
    field_simp [ha,hnc]
    ring
  rw [he, norm_mul, norm_mul, norm_neg, norm_inv (n : ℂ), Complex.norm_natCast]
  calc
    _ ≤ (5/2 : ℝ)*(2/(n : ℝ))*(n : ℝ)⁻¹ :=
      mul_le_mul_of_nonneg_right (mul_le_mul hzn (inverse_branch_norm_le hn hz)
        (norm_nonneg _) (by norm_num)) (inv_nonneg.mpr hn0.le)
    _ = _ := by ring

/-- The complementary branch has two powers of decay and only linear growth in monomial degree. -/
theorem norm_compressed_branch_monomial {w : ℂ} (hw : 0 < w.re)
    {n : ℕ} (hn : 1 ≤ n) (k : ℕ) :
    ‖compressed (branch w hw n hn) (monomial k)‖ ≤
      (k : ℝ)*(5*powerBound w+(5/2 : ℝ)*‖w‖*powerBound (w+1)) *
        (n : ℝ)^(-w.re-2) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hp := (powerBound_pos w).le
  have hq := (powerBound_pos (w+1)).le
  have hkin : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
  change ‖(compressed (branch w hw n hn) (monomial k)).1‖ ≤ _
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro z
  have hu := inverse_branch_inner hn z.property
  have hu0 : (n : ℂ)⁻¹ ∈ closedBall (1 : ℂ) 1 := by
    simpa only [zeroPoint, add_zero] using inverse_branch_inner hn zeroPoint.property
  have hu' : ‖((n : ℂ)+z.1)⁻¹-1‖ ≤ 1 := by
    simpa only [mem_closedBall, dist_eq_norm] using hu
  have hu0' : ‖(n : ℂ)⁻¹-1‖ ≤ 1 := by
    simpa only [mem_closedBall, dist_eq_norm] using hu0
  have hdiff : ‖(((n : ℂ)+z.1)⁻¹-1)^k-((n : ℂ)⁻¹-1)^k‖ ≤
      (k : ℝ)*(5/(n : ℝ)^2) := by
    have h := norm_pow_sub_pow_le_of_norm_le hu' hu0' k
    simp only [one_pow, mul_one] at h
    rw [show (((n : ℂ)+z.1)⁻¹-1)-((n : ℂ)⁻¹-1) =
      ((n : ℂ)+z.1)⁻¹-(n : ℂ)⁻¹ by ring] at h
    exact h.trans (mul_le_mul_of_nonneg_left (inverse_branch_difference_bound hn z.property) hkin)
  have hbase : ‖((n : ℂ)⁻¹-1)^k-(-1 : ℂ)^k‖ ≤ (k : ℝ)*(n : ℝ)⁻¹ := by
    have h := norm_pow_sub_pow_le_of_norm_le hu0'
      (by norm_num : ‖(-1 : ℂ)‖ ≤ (1 : ℝ)) k
    simpa only [one_pow, mul_one, sub_neg_eq_add, sub_add_cancel,
      norm_inv, Complex.norm_natCast] using h
  have huD := closedBall_subset_closedBall (by norm_num : (1 : ℝ) ≤ 3/2) hu
  have hu0D := closedBall_subset_closedBall (by norm_num : (1 : ℝ) ≤ 3/2) hu0
  have he : (compressed (branch w hw n hn) (monomial k)).1 z =
      ((n : ℂ)+z.1)^(-w) * ((((n : ℂ)+z.1)⁻¹-1)^k-((n : ℂ)⁻¹-1)^k) +
      (((n : ℂ)+z.1)^(-w)-(n : ℂ)^(-w)) * (((n : ℂ)⁻¹-1)^k-(-1)^k) := by
    rw [compressed_branch_apply, plane_eq (monomial k) ⟨_,huD⟩,
      plane_eq (monomial k) ⟨_,hu0D⟩]
    change _ + _ * (_-(0-1 : ℂ)^k) = _
    rw [zero_sub]
    rfl
  rw [he]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul]
  have hfirst := mul_le_mul (norm_branch_weight_le hw hn z.property) hdiff
    (norm_nonneg _) (by positivity : 0 ≤ powerBound w*(n : ℝ)^(-w.re))
  have hsecond := mul_le_mul (norm_branch_weight_sub_le hw hn z.property) hbase
    (norm_nonneg _) (by positivity : 0 ≤ ((5/2 : ℝ)*‖w‖*powerBound (w+1))*(n : ℝ)^(-w.re-1))
  refine (add_le_add hfirst hsecond).trans_eq ?_
  rw [Real.rpow_sub hn0, Real.rpow_sub hn0, Real.rpow_one, Real.rpow_two]
  ring

/-- The actual complementary branches sum to the compressed holomorphic remainder. -/
theorem hasSum_compressed_branch {w : ℂ} (hw : 0 < w.re) (f : DiscSpace) :
    HasSum (fun n : ℕ => compressed (branch w hw (n+1) (Nat.succ_pos n)) f)
      (compressed (remainder w) f) := by
  have hs := centering.hasSum ((ContinuousLinearMap.apply ℂ DiscSpace (centering f)).hasSum
    (remainder_locallyUniform.summable hw).hasSum)
  change HasSum (fun n : ℕ => compressed (entireRemainder n w) f)
    (compressed (remainder w) f) at hs
  simpa only [entireRemainder_eq hw, compressed_branchRemainder hw] using hs

/-- Finite complementary branches are exactly the compression of the genuine cutoff remainder. -/
theorem compressed_finiteRemainder {w : ℂ} (hw : 0 < w.re) (N : ℕ) (f : DiscSpace) :
    compressed (finiteRemainder w N) f =
      ∑ n ∈ Finset.range N, compressed (branch w hw (n+1) (Nat.succ_pos n)) f := by
  change centering ((∑ n ∈ Finset.range N, entireRemainder n w) (centering f)) = _
  rw [_root_.sum_apply, map_sum]
  apply Finset.sum_congr rfl
  intro n hn
  change compressed (entireRemainder n w) f = _
  rw [entireRemainder_eq hw, compressed_branchRemainder hw]

/-- Scalar tail for the doubly centered branch decay. -/
def doubleTail (w : ℂ) (N : ℕ) : ℝ :=
  ∑' k : ℕ, ((k+N+1 : ℕ) : ℝ)^(-w.re-2)

private theorem summable_succ_rpow {s : ℝ} (hs : 1 < s) :
    Summable (fun n : ℕ => ((n+1 : ℕ) : ℝ)^(-s)) :=
  (summable_nat_add_iff (f := fun n : ℕ => (n : ℝ)^(-s)) 1).mpr
    (RHTower.Sieve.summable_nat_rpow_neg hs)

private theorem double_decay_summable {w : ℂ} (hw : 0 < w.re) :
    Summable (fun n : ℕ => ((n+1 : ℕ) : ℝ)^(-w.re-2)) := by
  simpa only [neg_add, sub_eq_add_neg] using summable_succ_rpow (by linarith only [hw] : 1 < w.re+2)

private theorem single_decay_summable {w : ℂ} (hw : 0 < w.re) :
    Summable (fun n : ℕ => ((n+1 : ℕ) : ℝ)^(-w.re-1)) := by
  simpa only [neg_add, sub_eq_add_neg] using summable_succ_rpow (by linarith only [hw] : 1 < w.re+1)

private theorem tendsto_shifted_tsum_zero {a : ℕ → ℝ} (ha : Summable a) :
    Tendsto (fun N : ℕ => ∑' k, a (k+N)) atTop (𝓝 0) := by
  have he (N : ℕ) : (∑' k, a (k+N)) = (∑' k, a k)-∑ k ∈ Finset.range N, a k := by
    have h := ha.sum_add_tsum_nat_add N
    linarith only [h]
  simp_rw [he]
  simpa only [sub_self] using
    (tendsto_const_nhds (x := ∑' k, a k)).sub ha.hasSum.tendsto_sum_nat

theorem doubleTail_nonneg (w : ℂ) (N : ℕ) : 0 ≤ doubleTail w N :=
  tsum_nonneg fun _ => Real.rpow_nonneg (Nat.cast_nonneg _) _

/-- The first moment of the complementary branch tail vanishes. -/
theorem tendsto_mul_doubleTail {w : ℂ} (hw : 0 < w.re) :
    Tendsto (fun N : ℕ => (N : ℝ)*doubleTail w N) atTop (𝓝 0) := by
  have hd := double_decay_summable hw
  have hs := single_decay_summable hw
  have hb (N : ℕ) : (N : ℝ)*doubleTail w N ≤
      ∑' k : ℕ, ((k+N+1 : ℕ) : ℝ)^(-w.re-1) := by
    have hdN : Summable (fun k : ℕ => ((k+N+1 : ℕ) : ℝ)^(-w.re-2)) :=
      (summable_nat_add_iff N).mpr hd
    have hsN : Summable (fun k : ℕ => ((k+N+1 : ℕ) : ℝ)^(-w.re-1)) :=
      (summable_nat_add_iff N).mpr hs
    rw [doubleTail, ← tsum_mul_left]
    apply (hdN.mul_left (N : ℝ)).tsum_le_tsum _ hsN
    intro k
    have hx : (0 : ℝ) < (k+N+1 : ℕ) := by positivity
    have hn : (N : ℝ) ≤ (k+N+1 : ℕ) := by exact_mod_cast (show N ≤ k+N+1 by omega)
    calc
      _ ≤ ((k+N+1 : ℕ) : ℝ)*((k+N+1 : ℕ) : ℝ)^(-w.re-2) :=
        mul_le_mul_of_nonneg_right hn (Real.rpow_nonneg hx.le _)
      _ = _ := by
        calc
          _ = ((k+N+1 : ℕ) : ℝ)^(1 : ℝ)*((k+N+1 : ℕ) : ℝ)^(-w.re-2) := by
            rw [Real.rpow_one]
          _ = ((k+N+1 : ℕ) : ℝ)^(1+(-w.re-2)) := (Real.rpow_add hx _ _).symm
          _ = _ := by congr 1; ring
  exact squeeze_zero (fun N => mul_nonneg (Nat.cast_nonneg _) (doubleTail_nonneg w N)) hb
    (tendsto_shifted_tsum_zero hs)

/-- Source constant in the doubly centered monomial estimate. -/
def doubleBound (w : ℂ) : ℝ := 5*powerBound w+(5/2 : ℝ)*‖w‖*powerBound (w+1)

theorem doubleBound_nonneg (w : ℂ) : 0 ≤ doubleBound w := by
  have := (powerBound_pos w).le
  have := (powerBound_pos (w+1)).le
  unfold doubleBound
  positivity

private theorem summable_norm_compressed_monomial {w : ℂ} (hw : 0 < w.re) (j : ℕ) :
    Summable (fun n : ℕ =>
      ‖compressed (branch w hw (n+1) (Nat.succ_pos n)) (monomial j)‖) := by
  have hbound (n : ℕ) :
      ‖compressed (branch w hw (n+1) (Nat.succ_pos n)) (monomial j)‖ ≤
        ((j : ℝ)*doubleBound w)*((n+1 : ℕ) : ℝ)^(-w.re-2) :=
    norm_compressed_branch_monomial hw (Nat.succ_pos n) j
  exact ((double_decay_summable hw).mul_left ((j : ℝ)*doubleBound w)).of_nonneg_of_le
    (fun _ => norm_nonneg _) hbound

private theorem compressed_monomial_tail_eq {w : ℂ} (hw : 0 < w.re) (N j : ℕ) :
    compressed (remainder w) (monomial j)-compressed (finiteRemainder w N) (monomial j) =
      ∑' k : ℕ, compressed (branch w hw (k+N+1) (Nat.succ_pos (k+N))) (monomial j) := by
  have hs := hasSum_compressed_branch hw (monomial j)
  have ht := hs.summable.sum_add_tsum_nat_add N
  rw [compressed_finiteRemainder hw]
  exact sub_eq_iff_eq_add.mpr (hs.tsum_eq.symm.trans (ht.symm.trans (add_comm _ _)))

/-- Summing the actual centered branch bounds controls the complementary operator tail. -/
theorem norm_compressed_monomial_tail {w : ℂ} (hw : 0 < w.re) (N j : ℕ) :
    ‖compressed (remainder w) (monomial j)-compressed (finiteRemainder w N) (monomial j)‖ ≤
      (j : ℝ)*doubleBound w*doubleTail w N := by
  rw [compressed_monomial_tail_eq hw]
  have hn := summable_norm_compressed_monomial hw j
  have hnN : Summable (fun k : ℕ =>
      ‖compressed (branch w hw (k+N+1) (Nat.succ_pos (k+N))) (monomial j)‖) :=
    (summable_nat_add_iff (f := fun k : ℕ =>
      ‖compressed (branch w hw (k+1) (Nat.succ_pos k)) (monomial j)‖) N).mpr hn
  have hdN : Summable (fun k : ℕ => ((k+N+1 : ℕ) : ℝ)^(-w.re-2)) :=
    (summable_nat_add_iff (f := fun k : ℕ => ((k+1 : ℕ) : ℝ)^(-w.re-2)) N).mpr
      (double_decay_summable hw)
  calc
    _ ≤ ∑' k : ℕ, ‖compressed (branch w hw (k+N+1) (Nat.succ_pos (k+N))) (monomial j)‖ :=
      norm_tsum_le_tsum_norm hnN
    _ ≤ ∑' k : ℕ, ((j : ℝ)*doubleBound w)*((k+N+1 : ℕ) : ℝ)^(-w.re-2) :=
      hnN.tsum_le_tsum (fun k => norm_compressed_branch_monomial hw (Nat.succ_pos (k+N)) j)
        (hdN.mul_left ((j : ℝ)*doubleBound w))
    _ = _ := by rw [tsum_mul_left]; rfl

/-- Geometric constant for the actual compressed branch tail. -/
def tailConstant (w : ℂ) (N : ℕ) : ℝ := doubleBound w*degreeBound*doubleTail w N

theorem tailConstant_nonneg (w : ℂ) (N : ℕ) : 0 ≤ tailConstant w N :=
  mul_nonneg (mul_nonneg (doubleBound_nonneg w) degreeBound_nonneg) (doubleTail_nonneg w N)

private theorem scaled_compressed_tail_bound {w : ℂ} (hw : 0 < w.re) (N j : ℕ) :
    ‖((balanceRadius : ℂ)^j)⁻¹ •
      (compressed (remainder w) (monomial j)-compressed (finiteRemainder w N) (monomial j))‖ ≤
        tailConstant w N*rate^j := by
  have hb : 0 ≤ balanceRadius⁻¹^j := pow_nonneg (inv_nonneg.mpr balanceRadius_pos.le) _
  have hH := doubleBound_nonneg w
  have ht := doubleTail_nonneg w N
  rw [norm_smul, norm_inv, norm_pow, Complex.norm_real,
    Real.norm_of_nonneg balanceRadius_pos.le, ← inv_pow]
  calc
    _ ≤ balanceRadius⁻¹^j*((j : ℝ)*doubleBound w*doubleTail w N) :=
      mul_le_mul_of_nonneg_left (norm_compressed_monomial_tail hw N j) hb
    _ = (doubleBound w*doubleTail w N)*((j : ℝ)*balanceRadius⁻¹^j) := by ring
    _ ≤ (doubleBound w*doubleTail w N)*(((j : ℝ)+1)*balanceRadius⁻¹^j) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (by linarith : (j : ℝ) ≤ j+1) hb)
        (mul_nonneg hH ht)
    _ ≤ (doubleBound w*doubleTail w N)*(degreeBound*rate^j) :=
      mul_le_mul_of_nonneg_left (degree_bound j) (mul_nonneg hH ht)
    _ = _ := by unfold tailConstant; ring

/-- Actual Cauchy coordinates inherit the doubly centered branch-tail bound. -/
theorem compressed_matrix_tail_bound {w : ℂ} (hw : 0 < w.re) (N i j : ℕ) :
    ‖MayerPole.operatorMatrix (compressed (remainder w)) i j-
      MayerPole.operatorMatrix (compressed (finiteRemainder w N)) i j‖ ≤
        tailConstant w N*rate^i*rate^j := by
  have he : MayerPole.operatorMatrix (compressed (remainder w)) i j-
      MayerPole.operatorMatrix (compressed (finiteRemainder w N)) i j =
      functional i (((balanceRadius : ℂ)^j)⁻¹ •
        (compressed (remainder w) (monomial j)-compressed (finiteRemainder w N) (monomial j))) := by
    rw [smul_sub,map_sub]
    rfl
  rw [he]
  refine ((functional i).le_opNorm _).trans ?_
  exact (mul_le_mul (norm_functional_le i) (scaled_compressed_tail_bound hw N j)
    (norm_nonneg _) (pow_nonneg rate_bounds.1 i)).trans_eq (by ring)

private theorem doubleTail_le_zero {w : ℂ} (hw : 0 < w.re) (N : ℕ) :
    doubleTail w N ≤ doubleTail w 0 := by
  have h := (double_decay_summable hw).sum_add_tsum_nat_add N
  have hp : 0 ≤ ∑ k ∈ Finset.range N, ((k+1 : ℕ) : ℝ)^(-w.re-2) :=
    Finset.sum_nonneg fun _ _ => Real.rpow_nonneg (Nat.cast_nonneg _) _
  change (∑' k : ℕ, ((k+N+1 : ℕ) : ℝ)^(-w.re-2)) ≤
    ∑' k : ℕ, ((k+0+1 : ℕ) : ℝ)^(-w.re-2)
  simp only [Nat.add_zero]
  linarith only [h,hp]

private theorem tailConstant_le_zero {w : ℂ} (hw : 0 < w.re) (N : ℕ) :
    tailConstant w N ≤ tailConstant w 0 :=
  mul_le_mul_of_nonneg_left (doubleTail_le_zero hw N)
    (mul_nonneg (doubleBound_nonneg w) degreeBound_nonneg)

/-- Multiplication by the raw scalar growth still leaves a vanishing geometric tail. -/
theorem tendsto_mul_tailConstant {w : ℂ} (hw : 0 < w.re) :
    Tendsto (fun N : ℕ => (N : ℝ)*tailConstant w N) atTop (𝓝 0) := by
  have h := (tendsto_mul_doubleTail hw).const_mul (doubleBound w*degreeBound)
  have he : (fun N : ℕ => (N : ℝ)*tailConstant w N) =
      fun N : ℕ => (doubleBound w*degreeBound)*((N : ℝ)*doubleTail w N) := by
    funext N
    unfold tailConstant
    ring
  rw [he]
  simpa only [mul_zero] using h

private theorem compressed_zero : compressed (0 : DiscSpace →L[ℂ] DiscSpace) = 0 := by
  apply ContinuousLinearMap.ext
  intro f
  simp only [compressed, ContinuousLinearMap.comp_apply, zero_apply, map_zero]

/-- The limiting compressed operator has a geometric matrix bound supplied by actual branches. -/
theorem compressed_remainder_geometric {w : ℂ} (hw : 0 < w.re) :
    GeomFredholm.GeomDecay (MayerPole.operatorMatrix (compressed (remainder w)))
      (tailConstant w 0) rate := by
  refine ⟨tailConstant_nonneg w 0,rate_bounds.1,rate_bounds.2,fun i j => ?_⟩
  have h := compressed_matrix_tail_bound hw 0 i j
  have hzero : finiteRemainder w 0 = 0 := by simp only [finiteRemainder, Finset.range_zero, Finset.sum_empty]
  simpa only [hzero,compressed_zero,MayerPole.operatorMatrix,zero_apply,
    smul_zero,map_zero,sub_zero] using h

/-- Finite and limiting complementary operators have one common geometric bound. -/
theorem compressed_finite_geometric {w : ℂ} (hw : 0 < w.re) (N : ℕ) :
    GeomFredholm.GeomDecay (MayerPole.operatorMatrix (compressed (finiteRemainder w N)))
      (2*tailConstant w 0) rate := by
  have hR := compressed_remainder_geometric hw
  refine ⟨mul_nonneg (by norm_num) (tailConstant_nonneg w 0),rate_bounds.1,rate_bounds.2,fun i j => ?_⟩
  have hd := compressed_matrix_tail_bound hw N i j
  have ht := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (tailConstant_le_zero hw N) (pow_nonneg rate_bounds.1 i))
    (pow_nonneg rate_bounds.1 j)
  have htri := norm_add_le
    (MayerPole.operatorMatrix (compressed (remainder w)) i j)
    (MayerPole.operatorMatrix (compressed (finiteRemainder w N)) i j-
      MayerPole.operatorMatrix (compressed (remainder w)) i j)
  rw [← add_sub_assoc,add_sub_cancel_left,norm_sub_rev] at htri
  exact htri.trans ((add_le_add (hR.bound i j) (hd.trans ht)).trans_eq (by ring))

open GeomFredholm

private theorem rowProjection_evaluationWeight :
    MayerCompression.rowProjection MayerCancellation.evaluationWeight = MayerPole.projectionMatrix := by
  funext i j
  rw [MayerPole.projectionMatrix_eq]
  rfl

private theorem evaluationWeight_zero : MayerCancellation.evaluationWeight 0 = 1 := by
  simp only [MayerCancellation.evaluationWeight, pow_zero, inv_one, one_mul]

private theorem evaluationWeight_bound (j : ℕ) : ‖MayerCancellation.evaluationWeight j‖ ≤ rate^j := by
  have h := MayerPole.geomDecay_projection.bound 0 j
  rw [MayerPole.projectionMatrix_eq] at h
  simpa only [if_true, pow_zero, one_mul, MayerCancellation.evaluationWeight] using h

/-- Complementary block of the actual operator's rescaled Cauchy matrix. -/
def complementaryMatrix (T : DiscSpace →L[ℂ] DiscSpace) : ℕ → ℕ → ℂ :=
  MayerCompression.complement (MayerPole.operatorMatrix T) MayerCancellation.evaluationWeight

/-- Fredholm determinant of the actual finite remainder. -/
def finiteRegularPart (w : ℂ) (N : ℕ) (lam : ℂ) : ℂ :=
  fdet (MayerPole.operatorMatrix (finiteRemainder w N)) lam

/-- Coefficient of the finite scalar constant mode. -/
def finitePolePart (w : ℂ) (N : ℕ) (lam : ℂ) : ℂ :=
  -lam*fdet (complementaryMatrix (finiteRemainder w N)) lam

/-- The genuine finite-branch determinant at an arbitrary spectral parameter. -/
def rawSpectralDeterminant (w : ℂ) (hw : 0 < w.re) (N : ℕ) (lam : ℂ) : ℂ :=
  fdet (rawMatrix w hw N) lam

private theorem fdet_remainder_eq_regularPart (w lam : ℂ) :
    fdet (MayerPole.remainderMatrix w) lam = MayerPole.regularPart w lam := by
  have he : MayerPole.perturbedMatrix w 0 = MayerPole.remainderMatrix w := by
    funext i j
    simp only [MayerPole.perturbedMatrix, zero_mul, add_zero]
  change _ = fdet (MayerPole.perturbedMatrix w 0) lam
  rw [he]

/-- The actual finite remainder determinants converge at every spectral parameter. -/
theorem finiteRegularPart_tendsto {w : ℂ} (hw : 0 < w.re) (lam : ℂ) :
    Tendsto (fun N => finiteRegularPart w N lam) atTop (𝓝 (MayerPole.regularPart w lam)) := by
  have h := tendsto_fdet_of_uniform_geometric
    (Eventually.of_forall (finiteRemainder_geometric hw))
    (operatorMatrix_tendsto (finiteRemainder_tendsto hw)) lam
  change Tendsto (fun N => finiteRegularPart w N lam) atTop
    (𝓝 (fdet (MayerPole.remainderMatrix w) lam)) at h
  rwa [fdet_remainder_eq_regularPart] at h

/-- The source pole coefficient is the actual complementary determinant. -/
theorem polePart_eq_complement {w : ℂ} (hw : 0 < w.re) (lam : ℂ) :
    MayerPole.polePart w lam = -lam*fdet (complementaryMatrix (remainder w)) lam := by
  obtain ⟨r,C,hr,hhalf,hC⟩ := MayerPole.remainderMatrix_local_bound hw
  have hM := hC w (mem_closedBall_self hr.le)
  have h := MayerCompression.fdet_projection_affine hM evaluationWeight_zero
    evaluationWeight_bound lam 1
  rw [rowProjection_evaluationWeight] at h
  simp only [one_mul] at h
  have h1 : MayerPole.perturbedMatrix w 1 =
      fun i j => MayerPole.remainderMatrix w i j+MayerPole.projectionMatrix i j := by
    funext i j
    simp only [MayerPole.perturbedMatrix, one_mul]
  have h0 := fdet_remainder_eq_regularPart w lam
  change MayerPole.perturbedDeterminant w 1 lam-MayerPole.regularPart w lam = _
  change fdet (MayerPole.perturbedMatrix w 1) lam-MayerPole.regularPart w lam = _
  rw [h1,h,← h0]
  change fdet (MayerPole.remainderMatrix w) lam-lam*fdet (complementaryMatrix (remainder w)) lam-
    fdet (MayerPole.remainderMatrix w) lam = _
  ring

/-- Exact determinant decomposition retains the actual finite branch sum. -/
theorem rawSpectralDeterminant_decomposition {w : ℂ} (hw : 0 < w.re) (N : ℕ) (lam : ℂ) :
    rawSpectralDeterminant w hw N lam = finiteRegularPart w N lam+
      scalarPart w N*finitePolePart w N lam := by
  have h := MayerCompression.fdet_projection_affine (finiteRemainder_geometric hw N)
    evaluationWeight_zero evaluationWeight_bound lam (scalarPart w N)
  rw [rowProjection_evaluationWeight] at h
  have he : rawMatrix w hw N = fun i j => MayerPole.operatorMatrix (finiteRemainder w N) i j+
      scalarPart w N*MayerPole.projectionMatrix i j := by
    funext i j
    exact rawMatrix_decomposition hw N i j
  change fdet (rawMatrix w hw N) lam = _
  rw [he,h]
  unfold finiteRegularPart finitePolePart complementaryMatrix
  ring

private theorem functional_constant_succ (i : ℕ) (c : ℂ) : functional (i+1) (constant c) = 0 := by
  change (balanceRadius : ℂ)^(i+1) *
    coefficient coefficientRadius coefficientRadius_pos radii.2.2 (i+1) (constant c) = 0
  rw [MayerPole.coefficient_constant, if_neg (Nat.succ_ne_zero i), mul_zero]

private theorem functional_centering_succ (i : ℕ) (f : DiscSpace) :
    functional (i+1) (centering f) = functional (i+1) f := by
  change functional (i+1) (f-constant (f.1 zeroPoint)) = _
  rw [map_sub,functional_constant_succ,sub_zero]

private theorem centering_monomial (j : ℕ) :
    centering (monomial j) = monomial j-(-1 : ℂ)^j • constant 1 := by
  apply Subtype.ext
  ext z
  change (z.1-1)^j-(0-1 : ℂ)^j = (z.1-1)^j-(-1 : ℂ)^j*1
  rw [zero_sub,mul_one]

private theorem operatorMatrix_zero_column (T : DiscSpace →L[ℂ] DiscSpace) (i : ℕ) :
    MayerPole.operatorMatrix T i 0 = functional i (T (constant 1)) := by
  have hm : monomial 0 = constant 1 := by
    apply Subtype.ext
    ext z
    exact pow_zero (z.1-1)
  simp only [MayerPole.operatorMatrix,pow_zero,inv_one,one_smul,hm]

/-- The abstract complementary block is exactly the actual double-centered Cauchy matrix. -/
theorem complementaryMatrix_eq_compressed (T : DiscSpace →L[ℂ] DiscSpace) (i j : ℕ) :
    complementaryMatrix T i j = MayerPole.operatorMatrix (compressed T) (i+1) (j+1) := by
  unfold complementaryMatrix MayerCompression.complement
  rw [operatorMatrix_zero_column]
  change MayerPole.operatorMatrix T (i+1) (j+1)-
      functional (i+1) (T (constant 1))*MayerCancellation.evaluationWeight (j+1) =
    functional (i+1) (((balanceRadius : ℂ)^(j+1))⁻¹ •
      centering (T (centering (monomial (j+1)))))
  rw [map_smul,smul_eq_mul,functional_centering_succ,centering_monomial,
    map_sub,map_smul,map_sub,map_smul]
  simp only [MayerPole.operatorMatrix,MayerCancellation.evaluationWeight,map_smul,smul_eq_mul]
  ring

private theorem geomDecay_shift {M : ℕ → ℕ → ℂ} {C η : ℝ}
    (hM : GeomDecay M C η) : GeomDecay (fun i j => M (i+1) (j+1)) (C*η^2) η := by
  have hC := hM.const_nonneg
  have hη := hM.rate_nonneg
  refine ⟨by positivity,hη,hM.rate_lt_one,fun i j => ?_⟩
  exact (hM.bound (i+1) (j+1)).trans_eq (by rw [pow_succ,pow_succ];ring)

/-- Source and finite complementary matrices have a common geometric majorant. -/
theorem complementaryMatrix_geometric {w : ℂ} (hw : 0 < w.re) (N : ℕ) :
    GeomDecay (complementaryMatrix (finiteRemainder w N))
      ((2*tailConstant w 0)*rate^2) rate := by
  have he : complementaryMatrix (finiteRemainder w N) =
      fun i j => MayerPole.operatorMatrix (compressed (finiteRemainder w N)) (i+1) (j+1) :=
    funext fun i => funext fun j => complementaryMatrix_eq_compressed _ i j
  rw [he]
  exact geomDecay_shift (compressed_finite_geometric hw N)

private theorem complementaryRemainder_common_geometric {w : ℂ} (hw : 0 < w.re) :
    GeomDecay (complementaryMatrix (remainder w))
      ((2*tailConstant w 0)*rate^2) rate := by
  have h := geomDecay_shift (compressed_remainder_geometric hw)
  have hc := tailConstant_nonneg w 0
  refine ⟨by positivity,rate_bounds.1,rate_bounds.2,fun i j => ?_⟩
  rw [complementaryMatrix_eq_compressed]
  refine (h.bound i j).trans ?_
  have hbase : tailConstant w 0*rate^2 ≤ (2*tailConstant w 0)*rate^2 :=
    mul_le_mul_of_nonneg_right (by linarith only [hc]) (sq_nonneg _)
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hbase (pow_nonneg rate_bounds.1 i)) (pow_nonneg rate_bounds.1 j)

/-- The actual complementary matrices differ by a geometric weighted-tail bound. -/
theorem complementaryMatrix_tail_bound {w : ℂ} (hw : 0 < w.re) (N i j : ℕ) :
    ‖complementaryMatrix (finiteRemainder w N) i j-complementaryMatrix (remainder w) i j‖ ≤
      (tailConstant w N*rate^2)*rate^i*rate^j := by
  rw [complementaryMatrix_eq_compressed,complementaryMatrix_eq_compressed,norm_sub_rev]
  exact (compressed_matrix_tail_bound hw N (i+1) (j+1)).trans_eq
    (by rw [pow_succ,pow_succ];ring)

/-- Fixed spectral constant for the complementary determinant tail. -/
def poleTailFactor (w lam : ℂ) : ℝ := ‖lam‖*rate^2*
  MayerDeterminantBounds.perturbationConstant lam ((2*tailConstant w 0)*rate^2) rate

private theorem poleTailFactor_nonneg (w lam : ℂ) : 0 ≤ poleTailFactor w lam := by
  unfold poleTailFactor MayerDeterminantBounds.perturbationConstant
  positivity

/-- The source pole coefficient is approximated with the actual doubly centered tail. -/
theorem norm_finitePolePart_sub_le {w : ℂ} (hw : 0 < w.re) (N : ℕ) (lam : ℂ) :
    ‖finitePolePart w N lam-MayerPole.polePart w lam‖ ≤ tailConstant w N*poleTailFactor w lam := by
  rw [polePart_eq_complement hw,finitePolePart,← mul_sub,norm_mul,norm_neg]
  have h := MayerDeterminantBounds.norm_fdet_sub_le (complementaryMatrix_geometric hw N)
    (complementaryRemainder_common_geometric hw)
    (mul_nonneg (tailConstant_nonneg w N) (sq_nonneg _))
    (complementaryMatrix_tail_bound hw N) lam
  exact (mul_le_mul_of_nonneg_left h (norm_nonneg lam)).trans_eq
    (by unfold poleTailFactor;ring)

/-- The divergent scalar constant mode times the complementary error still tends to zero. -/
theorem scalarPart_mul_pole_error_tendsto {w : ℂ} (hw : 0 < w.re) (lam : ℂ) :
    Tendsto (fun N => scalarPart w N*(finitePolePart w N lam-MayerPole.polePart w lam))
      atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hlim := (tendsto_mul_tailConstant hw).mul_const (poleTailFactor w lam)
  simp only [zero_mul] at hlim
  apply squeeze_zero (fun N => norm_nonneg _) _ hlim
  intro N
  rw [norm_mul]
  exact (mul_le_mul (scalarPart_norm hw N) (norm_finitePolePart_sub_le hw N lam)
    (norm_nonneg _) (Nat.cast_nonneg N)).trans_eq (by ring)

/-- Exact finite part of the genuine branch-cutoff determinants on the whole source half-plane. -/
theorem rawSpectralDeterminant_finitePart_tendsto {w : ℂ} (hw : 0 < w.re) (lam : ℂ) :
    Tendsto (fun N => rawSpectralDeterminant w hw N lam-scalarPart w N*MayerPole.polePart w lam)
      atTop (𝓝 (MayerPole.regularPart w lam)) := by
  have h := (finiteRegularPart_tendsto hw lam).add (scalarPart_mul_pole_error_tendsto hw lam)
  simp only [add_zero] at h
  have he : (fun N => rawSpectralDeterminant w hw N lam-scalarPart w N*MayerPole.polePart w lam) =
      fun N => finiteRegularPart w N lam+
        scalarPart w N*(finitePolePart w N lam-MayerPole.polePart w lam) := by
    funext N
    rw [rawSpectralDeterminant_decomposition hw]
    ring
  rw [he]
  exact h

private def constantCoordinate : (DiscSpace →L[ℂ] DiscSpace) →L[ℂ] ℂ :=
  (evaluation zeroPoint).comp (ContinuousLinearMap.apply ℂ DiscSpace (constant 1))

private theorem constantCoordinate_projection : constantCoordinate constantProjection = 1 := rfl

private theorem branch_constant_zero {w : ℂ} (hw : 0 < w.re) {n : ℕ} (hn : 1 ≤ n) :
    (branch w hw n hn (constant 1)).1 zeroPoint = (n : ℂ)^(-w) := by
  have hu : (n : ℂ)⁻¹ ∈ outer := by
    have h := closedBall_subset_closedBall (by norm_num : (1 : ℝ) ≤ 3/2)
      (inverse_branch_inner hn zeroPoint.property)
    simpa only [zeroPoint,add_zero] using h
  rw [branch_apply]
  change ((n : ℂ)+0)^(-w)*plane (constant 1) (((n : ℂ)+0)⁻¹) = _
  rw [add_zero,plane_eq (constant 1) ⟨_,hu⟩]
  exact mul_one _

private theorem constantCoordinate_cutoff {w : ℂ} (hw : 0 < w.re) (N : ℕ) :
    constantCoordinate (cutoff w hw N) = scalarPart w N := by
  change evaluation zeroPoint (cutoff w hw N (constant 1)) = _
  rw [cutoff,_root_.sum_apply,map_sum]
  change (∑ n ∈ Finset.range N, (branch w hw (n+1) (Nat.succ_pos n) (constant 1)).1 zeroPoint) = _
  simp only [branch_constant_zero hw,scalarPart]

private theorem constantCoordinate_finiteRemainder {w : ℂ} (hw : 0 < w.re) (N : ℕ) :
    constantCoordinate (finiteRemainder w N) = 0 := by
  have h := congrArg constantCoordinate (cutoff_eq hw N)
  rw [constantCoordinate_cutoff hw,map_add,map_smul,constantCoordinate_projection,
    smul_eq_mul,mul_one] at h
  linear_combination -h

private theorem constantCoordinate_remainder {w : ℂ} (hw : 0 < w.re) :
    constantCoordinate (remainder w) = 0 := by
  have ht := constantCoordinate.continuous.continuousAt.tendsto.comp (finiteRemainder_tendsto hw)
  have he : (fun N => constantCoordinate (finiteRemainder w N)) = fun _ : ℕ => (0 : ℂ) :=
    funext (constantCoordinate_finiteRemainder hw)
  change Tendsto (fun N => constantCoordinate (finiteRemainder w N)) atTop _ at ht
  rw [he] at ht
  exact tendsto_nhds_unique ht tendsto_const_nhds

private theorem constantCoordinate_regularized {w : ℂ} (hw : 0 < w.re) :
    constantCoordinate (regularized w hw) = riemannZeta w := by
  rw [← source_eq hw,source,map_add,map_smul,constantCoordinate_projection,
    constantCoordinate_remainder hw,smul_eq_mul,mul_one,add_zero]

/-- The finite scalar mode has the same actual zeta finite part as the operator. -/
theorem scalarPart_finitePart_tendsto {w : ℂ} (hw : 0 < w.re) (hw1 : w ≠ 1) :
    Tendsto (fun N => scalarPart w N-counterterm w N) atTop (𝓝 (riemannZeta w)) := by
  have ht := constantCoordinate.continuous.continuousAt.tendsto.comp (tendsto_corrected_cutoff hw hw1)
  change Tendsto (fun N => constantCoordinate (cutoff w hw N-counterterm w N • constantProjection))
    atTop (𝓝 (constantCoordinate (regularized w hw))) at ht
  simpa only [map_sub,map_smul,constantCoordinate_projection,constantCoordinate_cutoff hw,
    constantCoordinate_regularized hw,smul_eq_mul,mul_one] using ht

/-- Exact leading scalar coefficient in the critical strip. -/
theorem scalarPart_scaled_tendsto {w : ℂ} (hw : 0 < w.re) (hwlt : w.re < 1) :
    Tendsto (fun N : ℕ => (N : ℂ)^(w-1)*scalarPart w N) atTop (𝓝 ((1-w)⁻¹)) := by
  have ht := constantCoordinate.continuous.continuousAt.tendsto.comp (tendsto_scaled_cutoff hw hwlt)
  change Tendsto (fun N : ℕ => constantCoordinate ((N : ℂ)^(w-1) • cutoff w hw N))
    atTop (𝓝 (constantCoordinate ((1-w)⁻¹ • constantProjection))) at ht
  simpa only [map_smul,constantCoordinate_projection,constantCoordinate_cutoff hw,
    smul_eq_mul,mul_one] using ht

/-- The counterterm normalization converges to the actual source determinant. -/
theorem rawSpectralDeterminant_counterterm_tendsto {w : ℂ} (hw : 0 < w.re) (hw1 : w ≠ 1)
    (lam : ℂ) :
    Tendsto (fun N => rawSpectralDeterminant w hw N lam-counterterm w N*MayerPole.polePart w lam)
      atTop (𝓝 (sourceDeterminant w lam)) := by
  have ht := (rawSpectralDeterminant_finitePart_tendsto hw lam).add
    ((scalarPart_finitePart_tendsto hw hw1).mul_const (MayerPole.polePart w lam))
  rw [← MayerPole.sourceDeterminant_decomposition hw lam] at ht
  have he : (fun N => rawSpectralDeterminant w hw N lam-counterterm w N*MayerPole.polePart w lam) =
      fun N => (rawSpectralDeterminant w hw N lam-scalarPart w N*MayerPole.polePart w lam)+
        (scalarPart w N-counterterm w N)*MayerPole.polePart w lam := by
    funext N
    ring
  rw [he]
  exact ht

private theorem nat_cpow_tendsto_zero {v : ℂ} (hv : v.re < 0) :
    Tendsto (fun N : ℕ => (N : ℂ)^v) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have h := (_root_.tendsto_rpow_neg_atTop (neg_pos.mpr hv)).comp tendsto_natCast_atTop_atTop
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hn : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
  rw [show (N : ℂ) = ((N : ℝ) : ℂ) by simp,Complex.norm_cpow_eq_rpow_re_of_pos hn,neg_neg]
  rfl

/-- The source pole coefficient is also the exact leading coefficient of raw determinant growth. -/
theorem rawSpectralDeterminant_scaled_tendsto {w : ℂ} (hw : 0 < w.re) (hwlt : w.re < 1)
    (lam : ℂ) :
    Tendsto (fun N : ℕ => (N : ℂ)^(w-1)*rawSpectralDeterminant w hw N lam)
      atTop (𝓝 (MayerPole.polePart w lam/(1-w))) := by
  have hs := nat_cpow_tendsto_zero (v := w-1)
    (by simpa only [Complex.sub_re,Complex.one_re] using sub_neg.mpr hwlt)
  have ht := (hs.mul (rawSpectralDeterminant_finitePart_tendsto hw lam)).add
    ((scalarPart_scaled_tendsto hw hwlt).mul_const (MayerPole.polePart w lam))
  simp only [zero_mul,zero_add] at ht
  have hlim : (1-w)⁻¹*MayerPole.polePart w lam = MayerPole.polePart w lam/(1-w) := by
    rw [div_eq_mul_inv,mul_comm]
  rw [hlim] at ht
  have he : (fun N : ℕ => (N : ℂ)^(w-1)*rawSpectralDeterminant w hw N lam) =
      fun N : ℕ => (N : ℂ)^(w-1)*(rawSpectralDeterminant w hw N lam-
        scalarPart w N*MayerPole.polePart w lam)+
        ((N : ℂ)^(w-1)*scalarPart w N)*MayerPole.polePart w lam := by
    funext N
    ring
  rw [he]
  exact ht

/-- Sharp norm asymptotic of the genuine finite-branch determinant in the critical strip. -/
theorem rawSpectralDeterminant_norm_ratio {w : ℂ} (hw : 0 < w.re) (hwlt : w.re < 1)
    (lam : ℂ) :
    Tendsto (fun N : ℕ => ‖rawSpectralDeterminant w hw N lam‖/(N : ℝ)^(1-w.re))
      atTop (𝓝 (‖MayerPole.polePart w lam‖/‖1-w‖)) := by
  have ht := (rawSpectralDeterminant_scaled_tendsto hw hwlt lam).norm
  rw [norm_div] at ht
  refine ht.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hn : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
  rw [norm_mul,show (N : ℂ) = ((N : ℝ) : ℂ) by simp,
    Complex.norm_cpow_eq_rpow_re_of_pos hn,Complex.sub_re,Complex.one_re,
    show w.re-1 = -(1-w.re) by ring,Real.rpow_neg hn.le]
  ring

private theorem one_sub_ne_zero {w : ℂ} (hwlt : w.re < 1) : (1 : ℂ)-w ≠ 0 := by
  intro he
  have h := congrArg Complex.re he
  simp only [Complex.sub_re,Complex.one_re,Complex.zero_re] at h
  linarith only [hwlt,h]

/-- Outside the pole-coefficient zero set, the raw determinant norm diverges. -/
theorem rawSpectralDeterminant_norm_atTop {w : ℂ} (hw : 0 < w.re) (hwlt : w.re < 1)
    (lam : ℂ) (hB : MayerPole.polePart w lam ≠ 0) :
    Tendsto (fun N => ‖rawSpectralDeterminant w hw N lam‖) atTop atTop := by
  have hp : Tendsto (fun N : ℕ => (N : ℝ)^(1-w.re)) atTop atTop :=
    (_root_.tendsto_rpow_atTop (sub_pos.mpr hwlt)).comp tendsto_natCast_atTop_atTop
  have ht := Tendsto.pos_mul_atTop
    (div_pos (norm_pos_iff.mpr hB) (norm_pos_iff.mpr (one_sub_ne_zero hwlt)))
    (rawSpectralDeterminant_norm_ratio hw hwlt lam) hp
  refine ht.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hn : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
  exact div_mul_cancel₀ _ (Real.rpow_pos_of_pos hn _).ne'

private theorem polePart_zero_of_raw_tendsto {w : ℂ} (hw : 0 < w.re) (hwlt : w.re < 1)
    {lam z : ℂ} (hE : Tendsto (fun N => rawSpectralDeterminant w hw N lam) atTop (𝓝 z)) :
    MayerPole.polePart w lam = 0 := by
  have hs := nat_cpow_tendsto_zero (v := w-1)
    (by simpa only [Complex.sub_re,Complex.one_re] using sub_neg.mpr hwlt)
  have ht := hs.mul hE
  simp only [zero_mul] at ht
  have he := tendsto_nhds_unique (rawSpectralDeterminant_scaled_tendsto hw hwlt lam) ht
  have h := congrArg (fun u : ℂ => u*(1-w)) he
  rw [div_mul_cancel₀ _ (one_sub_ne_zero hwlt),zero_mul] at h
  exact h

/-- Raw determinants converge exactly at the zeros of the source pole coefficient. -/
theorem rawSpectralDeterminant_tendsto_iff {w : ℂ} (hw : 0 < w.re) (hwlt : w.re < 1)
    (lam : ℂ) :
    Tendsto (fun N => rawSpectralDeterminant w hw N lam) atTop (𝓝 (sourceDeterminant w lam)) ↔
      MayerPole.polePart w lam = 0 := by
  constructor
  · exact polePart_zero_of_raw_tendsto hw hwlt
  · intro hB
    have ht := rawSpectralDeterminant_finitePart_tendsto hw lam
    simpa only [MayerPole.sourceDeterminant_decomposition hw lam,hB,mul_zero,sub_zero,add_zero] using ht

/-- No alternative finite limit exists away from the exact exceptional set. -/
theorem rawSpectralDeterminant_has_limit_iff {w : ℂ} (hw : 0 < w.re) (hwlt : w.re < 1)
    (lam : ℂ) :
    (∃ z : ℂ, Tendsto (fun N => rawSpectralDeterminant w hw N lam) atTop (𝓝 z)) ↔
      MayerPole.polePart w lam = 0 := by
  constructor
  · rintro ⟨z,hz⟩
    exact polePart_zero_of_raw_tendsto hw hwlt hz
  · intro hB
    exact ⟨sourceDeterminant w lam,(rawSpectralDeterminant_tendsto_iff hw hwlt lam).mpr hB⟩

#print axioms compressed_branch_apply
#print axioms inverse_branch_difference_bound
#print axioms norm_compressed_branch_monomial
#print axioms hasSum_compressed_branch
#print axioms compressed_finiteRemainder
#print axioms tendsto_mul_doubleTail
#print axioms norm_compressed_monomial_tail
#print axioms compressed_matrix_tail_bound
#print axioms complementaryMatrix_eq_compressed
#print axioms polePart_eq_complement
#print axioms rawSpectralDeterminant_decomposition
#print axioms rawSpectralDeterminant_finitePart_tendsto
#print axioms rawSpectralDeterminant_counterterm_tendsto
#print axioms rawSpectralDeterminant_scaled_tendsto
#print axioms rawSpectralDeterminant_norm_ratio
#print axioms rawSpectralDeterminant_norm_atTop
#print axioms rawSpectralDeterminant_tendsto_iff
#print axioms rawSpectralDeterminant_has_limit_iff

end GaloisForLFunctions.RenormalizedIntersectionTheory.MayerFinitePart
