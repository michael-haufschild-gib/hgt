import GaloisForLFunctions.RHTower.RiemannGaussian.GaussianZetaGeometry
import GaloisForLFunctions.RHTower.Sieve.ZetaTruncated
import GaloisForLFunctions.RHTower.Sieve.DirichletTruncationError
import GaloisForLFunctions.HTGeometry.HolomorphicCompactOpenDomain
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Gauss–Mayer cutoff renormalization

On the Banach disc algebra of `|z - 1| ≤ 3/2`, write `w = 2s` for the Mayer
exponent. For `Re w > 0` and `w ≠ 1`, subtracting `N^(1-w)/(1-w)` times
evaluation at zero makes the first `N` branch operators converge in norm,
with an explicit `O(N^(-Re w))` error.
The corrected operator agrees with the ordinary branch sum on `Re w > 1`.

For `0 < Re w < 1`, the normalized raw operators converge to
`(1-w)⁻¹` times the same norm-one projection. This gives their exact growth,
classifies every possible leading subtraction, and proves divergence at all
nontrivial zeta scattering parameters, including critical zeros. No nuclearity,
Fredholm determinant identity, or resonance exclusion is asserted here.
-/

open Complex Metric Set Filter Topology
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace GaloisForLFunctions.RenormalizedIntersectionTheory.MayerCutoff

/-- The closed Mayer disc, centered at one with radius three halves. -/
abbrev outer : Set ℂ := closedBall 1 (3 / 2)
/-- Interior of the Mayer disc. -/
abbrev inner : Set ℂ := ball 1 (3 / 2)
/-- Points of the closed Mayer disc. -/
abbrev Disc := ↥outer

/-- The origin, viewed as an interior point of the Mayer disc. -/
def zeroPoint : Disc := ⟨0, by norm_num [mem_closedBall, dist_eq_norm]⟩
instance : Nonempty Disc := ⟨zeroPoint⟩

private def inclusion : C(↥inner, Disc) :=
  ⟨fun z => ⟨z.1, ball_subset_closedBall z.2⟩,
    continuous_subtype_val.subtype_mk _⟩

private def restriction : C(Disc, ℂ) →L[ℂ] C(↥inner, ℂ) :=
  ContinuousMap.compCLM ℂ ℂ inclusion

/-- Continuous functions on the closed disc that are holomorphic in its interior. -/
def discSubmodule : Submodule ℂ C(Disc, ℂ) :=
  (holoCompactOpenSubmodule inner).comap restriction.toLinearMap

/-- The Banach disc algebra, with the uniform norm on the closed disc. -/
def DiscSpace : Type := ↥discSubmodule

instance : NormedAddCommGroup DiscSpace :=
  inferInstanceAs (NormedAddCommGroup ↥discSubmodule)

instance : NormedSpace ℂ DiscSpace :=
  inferInstanceAs (NormedSpace ℂ ↥discSubmodule)

private theorem closed_discSubmodule : IsClosed (discSubmodule : Set C(Disc, ℂ)) :=
  (isClosed_holoCompactOpen (Ω := inner) isOpen_ball).preimage restriction.continuous

instance : CompleteSpace DiscSpace := by
  haveI : IsClosed (discSubmodule : Set C(Disc, ℂ)) := closed_discSubmodule
  exact IsClosed.completeSpace_coe (s := (discSubmodule : Set C(Disc, ℂ)))

/-- Extend a disc-algebra function by zero outside the closed disc. -/
def plane (f : DiscSpace) : ℂ → ℂ := holoExtend outer (f.1 : Disc → ℂ)

theorem plane_eq (f : DiscSpace) (z : Disc) : plane f z = f.1 z :=
  holoExtend_coe _ _

theorem differentiableOn_plane (f : DiscSpace) : DifferentiableOn ℂ (plane f) inner := by
  have hf : DifferentiableOn ℂ (holoExtend inner (restriction f.1)) inner := f.2
  apply hf.congr
  intro z hz
  rw [plane, holoExtend_of_mem _ (ball_subset_closedBall hz), holoExtend_of_mem _ hz]
  rfl

theorem norm_plane_le (f : DiscSpace) {z : ℂ} (hz : z ∈ outer) :
    ‖plane f z‖ ≤ ‖f‖ := by
  rw [show plane f z = f.1 ⟨z, hz⟩ from plane_eq f ⟨z, hz⟩]
  exact ContinuousMap.norm_coe_le_norm f.1 ⟨z, hz⟩

/-- Constant functions in the disc algebra. -/
def constant (c : ℂ) : DiscSpace :=
  ⟨ContinuousMap.const Disc c, by
    change DifferentiableOn ℂ (holoExtend inner (fun _ => c)) inner
    apply (differentiableOn_const c).congr
    intro z hz
    exact holoExtend_of_mem _ hz⟩

theorem norm_constant (c : ℂ) : ‖constant c‖ = ‖c‖ := by
  change ‖ContinuousMap.const Disc c‖ = ‖c‖
  exact le_antisymm ((ContinuousMap.norm_le _ (norm_nonneg c)).mpr (fun _ => le_rfl))
    (ContinuousMap.norm_coe_le_norm (ContinuousMap.const Disc c) zeroPoint)

/-- Evaluation at zero followed by constant extension. -/
def constantProjection : DiscSpace →L[ℂ] DiscSpace :=
  LinearMap.mkContinuous
    { toFun := fun f => constant (f.1 zeroPoint)
      map_add' := fun f g => by apply Subtype.ext; ext z; rfl
      map_smul' := fun c f => by apply Subtype.ext; ext z; rfl }
    1 (fun f => by
      change ‖constant (f.1 zeroPoint)‖ ≤ 1 * ‖f‖
      rw [norm_constant, one_mul]
      exact ContinuousMap.norm_coe_le_norm f.1 zeroPoint)

/-- The evaluation projection has norm exactly one. -/
theorem norm_constantProjection : ‖constantProjection‖ = 1 := by
  apply le_antisymm
  · exact ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun f => by
      change ‖constant (f.1 zeroPoint)‖ ≤ 1 * ‖f‖
      rw [norm_constant, one_mul]
      exact ContinuousMap.norm_coe_le_norm f.1 zeroPoint
  · have h := constantProjection.le_opNorm (constant 1)
    simpa only [show constantProjection (constant 1) = constant 1 from rfl,
      norm_constant, norm_one, mul_one] using h

private theorem innerClosed_subset : closedBall (1 : ℂ) 1 ⊆ inner :=
  closedBall_subset_ball (by norm_num)

private theorem re_lower {z : ℂ} (hz : z ∈ outer) : -(1 / 2 : ℝ) ≤ z.re := by
  have h := Complex.abs_re_le_norm (z - 1)
  have hn : ‖z - 1‖ ≤ (3 / 2 : ℝ) := by simpa only [mem_closedBall, dist_eq_norm] using hz
  have hr := (neg_le_abs (z - 1).re).trans (h.trans hn)
  simp only [Complex.sub_re, Complex.one_re] at hr
  linarith only [hr]

/-- Every Gauss inverse branch lies in the same strictly smaller disc. -/
theorem inverse_branch_inner {n : ℕ} (hn : 1 ≤ n) {z : ℂ} (hz : z ∈ outer) :
    ((n : ℂ) + z)⁻¹ ∈ closedBall (1 : ℂ) 1 := by
  let a := (n : ℂ) + z
  have hre : 1 / 2 ≤ a.re := by
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hz' := re_lower hz
    simp only [a, Complex.add_re, Complex.natCast_re]
    linarith only [hn', hz']
  have ha : a ≠ 0 := by intro h; rw [h, Complex.zero_re] at hre; norm_num at hre
  have hs : ‖1 - a‖ ^ 2 ≤ ‖a‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.one_re,
      Complex.sub_im, Complex.one_im]
    nlinarith only [hre]
  have hnorm : ‖1 - a‖ ≤ ‖a‖ := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hs
  have he : a⁻¹ - 1 = (1 - a) / a := by field_simp [ha]
  rw [mem_closedBall, dist_eq_norm]
  change ‖a⁻¹ - 1‖ ≤ 1
  rw [he, norm_div]
  exact (div_le_one (norm_pos_iff.mpr ha)).mpr hnorm

theorem inverse_branch_norm_le {n : ℕ} (hn : 1 ≤ n) {z : ℂ} (hz : z ∈ outer) :
    ‖((n : ℂ) + z)⁻¹‖ ≤ 2 / (n : ℝ) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hz' := re_lower hz
  have hre := Complex.re_le_norm ((n : ℂ) + z)
  simp only [Complex.add_re, Complex.natCast_re] at hre
  have hhalf : (n : ℝ) / 2 ≤ ‖(n : ℂ) + z‖ := by linarith only [hn', hz', hre]
  have hnp : 0 < (n : ℝ) / 2 := by linarith only [hn']
  rw [norm_inv]
  calc ‖(n : ℂ) + z‖⁻¹ ≤ ((n : ℝ) / 2)⁻¹ :=
         (inv_le_inv₀ (hnp.trans_le hhalf) hnp).mpr hhalf
       _ = 2 / (n : ℝ) := by rw [inv_div]

/-- Cauchy's estimate on a fixed interior margin. -/
private theorem deriv_plane_bound (f : DiscSpace) {z : ℂ} (hz : z ∈ closedBall (1 : ℂ) 1) :
    ‖deriv (plane f) z‖ ≤ 4 * ‖f‖ := by
  have hsub : closedBall z (1 / 4) ⊆ inner := by
    intro w hw
    have hz' : ‖z - 1‖ ≤ 1 := by simpa only [mem_closedBall, dist_eq_norm] using hz
    have hw' : ‖w - z‖ ≤ (1 / 4 : ℝ) := by simpa only [mem_closedBall, dist_eq_norm] using hw
    have he : w - 1 = (w - z) + (z - 1) := by ring
    change w ∈ ball (1 : ℂ) (3 / 2)
    rw [mem_ball, dist_eq_norm]
    rw [he]
    exact (norm_add_le _ _).trans_lt (by linarith only [hz', hw'])
  have h := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by norm_num : (0 : ℝ) < 1 / 4)
    ((differentiableOn_plane f).diffContOnCl_ball hsub)
    (fun w hw => norm_plane_le f (ball_subset_closedBall (hsub (sphere_subset_closedBall hw))))
  convert h using 1; ring

private theorem plane_sub_zero_bound (f : DiscSpace) {z : ℂ} (hz : z ∈ closedBall (1 : ℂ) 1) :
    ‖plane f z - plane f 0‖ ≤ 4 * ‖f‖ * ‖z‖ := by
  have h := (convex_closedBall (1 : ℂ) (1 : ℝ)).norm_image_sub_le_of_norm_deriv_le
    (fun w hw => (differentiableOn_plane f).differentiableAt
      (isOpen_ball.mem_nhds (innerClosed_subset hw)))
    (fun w hw => deriv_plane_bound f hw)
    (by norm_num [mem_closedBall, dist_eq_norm] : (0 : ℂ) ∈ closedBall (1 : ℂ) 1) hz
  simpa only [sub_zero] using h

/-- Uniform principal-power bound for the shifted Gauss branches. -/
def powerBound (w : ℂ) : ℝ :=
  (2 : ℝ) ^ w.re * Real.exp (Real.pi * |w.im|)

theorem powerBound_pos (w : ℂ) : 0 < powerBound w := by
  unfold powerBound
  positivity

private theorem nat_add_re_lower {n : ℕ} (hn : 1 ≤ n) {z : ℂ} (hz : z ∈ outer) :
    (n : ℝ) / 2 ≤ ((n : ℂ) + z).re := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hz' := re_lower hz
  simp only [Complex.add_re, Complex.natCast_re]
  linarith only [hn', hz']

private theorem nat_add_slit {n : ℕ} (hn : 1 ≤ n) {z : ℂ} (hz : z ∈ outer) :
    (n : ℂ) + z ∈ Complex.slitPlane := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  exact Complex.mem_slitPlane_iff.mpr (Or.inl ((half_pos hn').trans_le (nat_add_re_lower hn hz)))

private theorem norm_cpow_neg_bound {a : ℂ} (ha : a ≠ 0) (w : ℂ) :
    ‖a ^ (-w)‖ ≤ ‖a‖ ^ (-w.re) * Real.exp (Real.pi * |w.im|) := by
  rw [Complex.norm_cpow_of_ne_zero ha, Complex.neg_re, Complex.neg_im,
    mul_neg, Real.exp_neg, div_inv_eq_mul]
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (norm_nonneg _) _)
  apply Real.exp_le_exp.mpr
  calc a.arg * w.im ≤ |a.arg * w.im| := le_abs_self _
       _ = |a.arg| * |w.im| := abs_mul _ _
       _ ≤ Real.pi * |w.im| := mul_le_mul_of_nonneg_right
         (abs_le.mpr ⟨(Complex.neg_pi_lt_arg a).le, Complex.arg_le_pi a⟩) (abs_nonneg _)

theorem norm_branch_weight_le {w : ℂ} (hw : 0 < w.re)
    {n : ℕ} (hn : 1 ≤ n) {z : ℂ} (hz : z ∈ outer) :
    ‖((n : ℂ) + z) ^ (-w)‖ ≤ powerBound w * (n : ℝ) ^ (-w.re) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hnorm : (n : ℝ) / 2 ≤ ‖(n : ℂ) + z‖ :=
    (nat_add_re_lower hn hz).trans (Complex.re_le_norm _)
  have ha : (n : ℂ) + z ≠ 0 := norm_pos_iff.mp ((half_pos hn').trans_le hnorm)
  refine (norm_cpow_neg_bound ha w).trans ?_
  have hp := Real.rpow_le_rpow_of_nonpos (half_pos hn') hnorm (neg_nonpos.mpr hw.le)
  calc ‖(n : ℂ) + z‖ ^ (-w.re) * Real.exp (Real.pi * |w.im|)
      ≤ ((n : ℝ) / 2) ^ (-w.re) * Real.exp (Real.pi * |w.im|) :=
        mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le
       _ = powerBound w * (n : ℝ) ^ (-w.re) := by
         rw [Real.div_rpow hn'.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
           div_inv_eq_mul]
         unfold powerBound
         ring

private theorem hasDerivAt_branch_weight (w : ℂ) {n : ℕ} (hn : 1 ≤ n)
    {z : ℂ} (hz : z ∈ outer) :
    HasDerivAt (fun u : ℂ => ((n : ℂ) + u) ^ (-w))
      (-w * ((n : ℂ) + z) ^ (-(w + 1))) z := by
  have h := ((hasDerivAt_id z).const_add (n : ℂ)).cpow_const (c := -w) (nat_add_slit hn hz)
  simpa only [id_eq, mul_one, show -w - 1 = -(w + 1) by ring] using h

private theorem norm_branch_weight_deriv_le {w : ℂ} (hw : 0 < w.re)
    {n : ℕ} (hn : 1 ≤ n) {z : ℂ} (hz : z ∈ outer) :
    ‖deriv (fun u : ℂ => ((n : ℂ) + u) ^ (-w)) z‖ ≤
      ‖w‖ * powerBound (w + 1) * (n : ℝ) ^ (-w.re - 1) := by
  rw [(hasDerivAt_branch_weight w hn hz).deriv, norm_mul, norm_neg]
  have hw' : 0 < (w + 1).re := by simp only [Complex.add_re, Complex.one_re]; linarith only [hw]
  have h := mul_le_mul_of_nonneg_left (norm_branch_weight_le hw' hn hz) (norm_nonneg w)
  simpa only [Complex.add_re, Complex.one_re, neg_add, sub_eq_add_neg, mul_assoc] using h

theorem norm_branch_weight_sub_le {w : ℂ} (hw : 0 < w.re)
    {n : ℕ} (hn : 1 ≤ n) {z : ℂ} (hz : z ∈ outer) :
    ‖((n : ℂ) + z) ^ (-w) - (n : ℂ) ^ (-w)‖ ≤
      ((5 / 2 : ℝ) * ‖w‖ * powerBound (w + 1)) * (n : ℝ) ^ (-w.re - 1) := by
  have h := (convex_closedBall (1 : ℂ) (3 / 2 : ℝ)).norm_image_sub_le_of_norm_deriv_le
    (fun u hu => (hasDerivAt_branch_weight w hn hu).differentiableAt)
    (fun u hu => norm_branch_weight_deriv_le hw hn hu)
    (by norm_num [mem_closedBall, dist_eq_norm] : (0 : ℂ) ∈ outer) hz
  simp only [add_zero, sub_zero] at h
  have hzn : ‖z‖ ≤ (5 / 2 : ℝ) := by
    have hz' : ‖z - 1‖ ≤ (3 / 2 : ℝ) := by simpa only [mem_closedBall, dist_eq_norm] using hz
    have ht := norm_add_le (z - 1) (1 : ℂ)
    rw [sub_add_cancel, norm_one] at ht
    linarith only [ht, hz']
  refine h.trans ?_
  calc (‖w‖ * powerBound (w + 1) * (n : ℝ) ^ (-w.re - 1)) * ‖z‖
      ≤ (‖w‖ * powerBound (w + 1) * (n : ℝ) ^ (-w.re - 1)) * (5 / 2) :=
        mul_le_mul_of_nonneg_left hzn (mul_nonneg (mul_nonneg (norm_nonneg _) (powerBound_pos _).le) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
       _ = _ := by ring

private theorem nat_add_ne_zero {n : ℕ} (hn : 1 ≤ n) {z : ℂ} (hz : z ∈ outer) :
    (n : ℂ) + z ≠ 0 := by
  have h := nat_add_re_lower hn hz
  have hn' : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  intro he
  rw [he, Complex.zero_re] at h
  linarith only [h, hn']

private def branchMap (n : ℕ) (hn : 1 ≤ n) : C(Disc, Disc) :=
  ⟨fun z => ⟨((n : ℂ) + z.1)⁻¹,
      ball_subset_closedBall (innerClosed_subset (inverse_branch_inner hn z.2))⟩,
    ((continuous_const.add continuous_subtype_val).inv₀
      (fun z => nat_add_ne_zero hn z.2)).subtype_mk _⟩

private def weightMap (w : ℂ) (n : ℕ) (hn : 1 ≤ n) : C(Disc, ℂ) :=
  ⟨fun z => ((n : ℂ) + z.1) ^ (-w), by
    apply continuous_iff_continuousAt.mpr
    intro z
    exact (hasDerivAt_branch_weight w hn z.2).continuousAt.comp continuous_subtype_val.continuousAt⟩

/-- One weighted inverse branch preserves the disc algebra. -/
private def branchValue (w : ℂ) (n : ℕ) (hn : 1 ≤ n) (f : DiscSpace) : DiscSpace :=
  ⟨weightMap w n hn * f.1.comp (branchMap n hn), by
    change DifferentiableOn ℂ
      (holoExtend inner (restriction (weightMap w n hn * f.1.comp (branchMap n hn)))) inner
    have hd : DifferentiableOn ℂ
        (fun z => ((n : ℂ) + z) ^ (-w) * plane f (((n : ℂ) + z)⁻¹)) inner := by
      intro z hz
      have hzD := ball_subset_closedBall hz
      have hf := (differentiableOn_plane f).differentiableAt
        (isOpen_ball.mem_nhds (innerClosed_subset (inverse_branch_inner hn hzD)))
      exact ((hasDerivAt_branch_weight w hn hzD).differentiableAt.mul
        (hf.comp z (((differentiableAt_id.const_add (n : ℂ)).inv
          (nat_add_ne_zero hn hzD))))).differentiableWithinAt
    apply hd.congr
    intro z hz
    rw [holoExtend_of_mem _ hz]
    change ((n : ℂ) + z) ^ (-w) * f.1 (branchMap n hn (inclusion ⟨z, hz⟩)) = _
    exact congrArg (fun v => ((n : ℂ) + z) ^ (-w) * v)
      (plane_eq f (branchMap n hn (inclusion ⟨z, hz⟩))).symm⟩

private theorem branchValue_apply (w : ℂ) (n : ℕ) (hn : 1 ≤ n)
    (f : DiscSpace) (z : Disc) :
    (branchValue w n hn f).1 z =
      ((n : ℂ) + z.1) ^ (-w) * plane f (((n : ℂ) + z.1)⁻¹) := by
  change _ * f.1 (branchMap n hn z) = _
  exact congrArg (fun v => ((n : ℂ) + z.1) ^ (-w) * v)
    (plane_eq f (branchMap n hn z)).symm

private theorem norm_branchValue_le {w : ℂ} (hw : 0 < w.re)
    {n : ℕ} (hn : 1 ≤ n) (f : DiscSpace) :
    ‖branchValue w n hn f‖ ≤ (powerBound w * (n : ℝ) ^ (-w.re)) * ‖f‖ := by
  have hp := (powerBound_pos w).le
  change ‖(branchValue w n hn f).1‖ ≤ _
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro z
  rw [branchValue_apply, norm_mul]
  exact mul_le_mul (norm_branch_weight_le hw hn z.2)
    (norm_plane_le f (branchMap n hn z).2) (norm_nonneg _) (by positivity)

/-- The weighted Gauss inverse branch with exponent `w = 2s`. -/
def branch (w : ℂ) (hw : 0 < w.re) (n : ℕ) (hn : 1 ≤ n) :
    DiscSpace →L[ℂ] DiscSpace :=
  LinearMap.mkContinuous
    { toFun := branchValue w n hn
      map_add' := fun f g => by apply Subtype.ext; ext z; exact mul_add _ _ _
      map_smul' := fun c f => by apply Subtype.ext; ext z; exact mul_left_comm _ _ _ }
    (powerBound w * (n : ℝ) ^ (-w.re)) (norm_branchValue_le hw hn)

/-- The branch operator is the actual weighted continued-fraction inverse branch. -/
theorem branch_apply (w : ℂ) (hw : 0 < w.re) (n : ℕ) (hn : 1 ≤ n)
    (f : DiscSpace) (z : Disc) :
    (branch w hw n hn f).1 z =
      ((n : ℂ) + z.1) ^ (-w) * plane f (((n : ℂ) + z.1)⁻¹) :=
  branchValue_apply w n hn f z

/-- Remove the scalar constant-input term from one branch. -/
def branchRemainder (w : ℂ) (hw : 0 < w.re) (n : ℕ) (hn : 1 ≤ n) :
    DiscSpace →L[ℂ] DiscSpace := branch w hw n hn - (n : ℂ) ^ (-w) • constantProjection

/-- Explicit coefficient in the summable branch-remainder estimate. -/
def remainderBound (w : ℂ) : ℝ :=
  8 * powerBound w + (5 / 2 : ℝ) * ‖w‖ * powerBound (w + 1)

private theorem remainderBound_nonneg (w : ℂ) : 0 ≤ remainderBound w := by
  have h := (powerBound_pos w).le
  have h' := (powerBound_pos (w + 1)).le
  unfold remainderBound
  positivity

private theorem norm_branchRemainder_apply_le {w : ℂ} (hw : 0 < w.re)
    {n : ℕ} (hn : 1 ≤ n) (f : DiscSpace) (z : Disc) :
    ‖(branchRemainder w hw n hn f).1 z‖ ≤
      remainderBound w * (n : ℝ) ^ (-w.re - 1) * ‖f‖ := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hdiff := (plane_sub_zero_bound f (inverse_branch_inner hn z.2)).trans
    (mul_le_mul_of_nonneg_left (inverse_branch_norm_le hn z.2) (by positivity))
  have hzero : plane f 0 = f.1 zeroPoint := plane_eq f zeroPoint
  rw [hzero] at hdiff
  have h0 : ‖f.1 zeroPoint‖ ≤ ‖f‖ := ContinuousMap.norm_coe_le_norm f.1 zeroPoint
  have hp := (powerBound_pos w).le
  have hp' := (powerBound_pos (w + 1)).le
  have he : (branchRemainder w hw n hn f).1 z =
      ((n : ℂ) + z.1) ^ (-w) * (plane f (((n : ℂ) + z.1)⁻¹) - f.1 zeroPoint) +
      (((n : ℂ) + z.1) ^ (-w) - (n : ℂ) ^ (-w)) * f.1 zeroPoint := by
    change (branchValue w n hn f).1 z - (n : ℂ) ^ (-w) * f.1 zeroPoint = _
    rw [branchValue_apply]
    ring
  rw [he]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul]
  have hfirst := mul_le_mul (norm_branch_weight_le hw hn z.2) hdiff
    (norm_nonneg _) (by positivity : 0 ≤ powerBound w * (n : ℝ) ^ (-w.re))
  have hsecond := mul_le_mul (norm_branch_weight_sub_le hw hn z.2) h0
    (norm_nonneg _) (by positivity : 0 ≤ ((5 / 2 : ℝ) * ‖w‖ * powerBound (w + 1)) * (n : ℝ) ^ (-w.re - 1))
  refine (add_le_add hfirst hsecond).trans_eq ?_
  rw [Real.rpow_sub hn', Real.rpow_one]
  unfold remainderBound
  ring

/-- Subtraction improves branch decay by one power of the branch index. -/
theorem norm_branchRemainder_le {w : ℂ} (hw : 0 < w.re)
    {n : ℕ} (hn : 1 ≤ n) :
    ‖branchRemainder w hw n hn‖ ≤ remainderBound w * (n : ℝ) ^ (-w.re - 1) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (remainderBound_nonneg w)
    (Real.rpow_nonneg (Nat.cast_nonneg n) _))
  intro f
  have hB := remainderBound_nonneg w
  change ‖(branchRemainder w hw n hn f).1‖ ≤ _
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  exact norm_branchRemainder_apply_le hw hn f

private def remainderSequence (w : ℂ) (hw : 0 < w.re) (j : ℕ) :
    DiscSpace →L[ℂ] DiscSpace := branchRemainder w hw (j + 1) (Nat.succ_le_succ (Nat.zero_le _))

private theorem summable_norm_remainderSequence (w : ℂ) (hw : 0 < w.re) :
    Summable (fun j => ‖remainderSequence w hw j‖) := by
  have hp : Summable (fun j : ℕ => ((j + 1 : ℕ) : ℝ) ^ (-(w.re + 1))) :=
    (summable_nat_add_iff (f := fun n : ℕ => (n : ℝ) ^ (-(w.re + 1))) 1).mpr
      (RHTower.Sieve.summable_nat_rpow_neg (by linarith only [hw]))
  apply (hp.mul_left (remainderBound w)).of_nonneg_of_le (fun j => norm_nonneg _)
  intro j
  simpa only [remainderSequence, Nat.succ_eq_add_one, neg_add, sub_eq_add_neg] using
    norm_branchRemainder_le hw (Nat.succ_le_succ (Nat.zero_le j))

/-- The absolutely convergent branch correction in operator norm. -/
private def remainderSum (w : ℂ) (hw : 0 < w.re) : DiscSpace →L[ℂ] DiscSpace :=
  ∑' j, remainderSequence w hw j

/-- Sum the first `N` genuine Gauss branches. -/
def cutoff (w : ℂ) (hw : 0 < w.re) (N : ℕ) : DiscSpace →L[ℂ] DiscSpace :=
  ∑ j ∈ Finset.range N, branch w hw (j + 1) (Nat.succ_le_succ (Nat.zero_le _))

private def scalarCutoff (w : ℂ) (N : ℕ) : ℂ :=
  ∑ j ∈ Finset.range N, ((j + 1 : ℕ) : ℂ) ^ (-w)

/-- Zeta finite part plus the absolutely convergent operator remainders. -/
def regularized (w : ℂ) (hw : 0 < w.re) : DiscSpace →L[ℂ] DiscSpace :=
  riemannZeta w • constantProjection + remainderSum w hw

private theorem cutoff_decomposition (w : ℂ) (hw : 0 < w.re) (N : ℕ) :
    cutoff w hw N = scalarCutoff w N • constantProjection +
      ∑ j ∈ Finset.range N, remainderSequence w hw j := by
  unfold cutoff scalarCutoff remainderSequence branchRemainder
  rw [Finset.sum_sub_distrib, Finset.sum_smul]
  abel

private theorem norm_remainder_tail_le (w : ℂ) (hw : 0 < w.re) {N : ℕ} (hN : 1 ≤ N) :
    ‖remainderSum w hw - ∑ j ∈ Finset.range N, remainderSequence w hw j‖ ≤
      remainderBound w / w.re * (N : ℝ) ^ (-w.re) := by
  have hs := summable_norm_remainderSequence w hw
  have ht := hs.of_norm.sum_add_tsum_nat_add N
  have he : remainderSum w hw - ∑ j ∈ Finset.range N, remainderSequence w hw j =
      ∑' j, remainderSequence w hw (j + N) := by
    rw [remainderSum, ← ht, add_sub_cancel_left]
  rw [he]
  have hshift : Summable (fun j => ‖remainderSequence w hw (j + N)‖) :=
    (summable_nat_add_iff N).mpr hs
  have hp : Summable (fun j : ℕ => ((j + (N + 1) : ℕ) : ℝ) ^ (-(w.re + 1))) :=
    (summable_nat_add_iff (f := fun n : ℕ => (n : ℝ) ^ (-(w.re + 1))) (N + 1)).mpr
      (RHTower.Sieve.summable_nat_rpow_neg (by linarith only [hw]))
  refine (norm_tsum_le_tsum_norm hshift).trans ?_
  have hb := hshift.tsum_le_tsum (g := fun j : ℕ =>
      remainderBound w * ((j + (N + 1) : ℕ) : ℝ) ^ (-(w.re + 1))) (fun j => by
        simpa only [remainderSequence, Nat.succ_eq_add_one, Nat.add_assoc, neg_add, sub_eq_add_neg] using
          norm_branchRemainder_le hw (Nat.succ_le_succ (Nat.zero_le (j + N))))
    (hp.mul_left (remainderBound w))
  refine hb.trans ?_
  rw [tsum_mul_left]
  have htail := RHTower.Sieve.tsum_tail_rpow_neg_le (by linarith only [hw] : 1 < w.re + 1) hN
  have htail' : (∑' j : ℕ, ((j + (N + 1) : ℕ) : ℝ) ^ (-(w.re + 1))) ≤
      (N : ℝ) ^ (-w.re) / w.re := by
    simpa only [Nat.add_assoc, show 1 - (w.re + 1) = -w.re by ring,
      add_sub_cancel_right] using htail
  exact (mul_le_mul_of_nonneg_left htail' (remainderBound_nonneg w)).trans_eq (by ring)

private theorem scalarCutoff_eq_Icc (w : ℂ) (N : ℕ) :
    scalarCutoff w N = ∑ k ∈ Finset.Icc 1 N, ((k : ℝ) : ℂ) ^ (-w) := by
  unfold scalarCutoff
  refine Finset.sum_bij (fun j _ => j + 1) ?_ ?_ ?_ ?_
  · intro j hj
    simp only [Finset.mem_range] at hj
    simp only [Finset.mem_Icc]
    omega
  · intro a ha b hb hab
    omega
  · intro k hk
    simp only [Finset.mem_Icc] at hk
    refine ⟨k - 1, Finset.mem_range.mpr (by omega), by omega⟩
  · intro j hj
    simp only [Complex.ofReal_natCast]

/-- Elementary coefficient of the divergent constant mode. -/
def counterterm (w : ℂ) (N : ℕ) : ℂ := (N : ℂ) ^ (1 - w) / (1 - w)

private theorem norm_scalar_error_le {w : ℂ} (hw : 0 < w.re) (hw1 : w ≠ 1)
    {N : ℕ} (hN : 1 ≤ N) :
    ‖scalarCutoff w N - counterterm w N - riemannZeta w‖ ≤
      ‖w‖ / w.re * (N : ℝ) ^ (-w.re) := by
  have he := RHTower.Sieve.riemannZeta_eq_sum_add_tail hw hw1 hN
  rw [scalarCutoff_eq_Icc, counterterm, he]
  have hneg : (N : ℂ) ^ (1 - w) / (1 - w) = -((N : ℂ) ^ (1 - w) / (w - 1)) := by
    rw [← neg_sub w 1, div_neg]
  simp only [Complex.ofReal_natCast] at *
  rw [hneg]
  have halg : ∀ a b c : ℂ, a - -b - (a + b - c) = c := by intros; ring
  rw [halg, norm_mul]
  exact (mul_le_mul_of_nonneg_left
    (RHTower.Sieve.norm_integral_Ioi_fract_cpow_le hw hN) (norm_nonneg w)).trans_eq (by ring)

/-- Quantitative operator-norm convergence after subtracting the constant mode. -/
theorem norm_corrected_cutoff_le {w : ℂ} (hw : 0 < w.re) (hw1 : w ≠ 1)
    {N : ℕ} (hN : 1 ≤ N) :
    ‖cutoff w hw N - counterterm w N • constantProjection - regularized w hw‖ ≤
      ((‖w‖ + remainderBound w) / w.re) * (N : ℝ) ^ (-w.re) := by
  have he : cutoff w hw N - counterterm w N • constantProjection - regularized w hw =
      (scalarCutoff w N - counterterm w N - riemannZeta w) • constantProjection -
      (remainderSum w hw - ∑ j ∈ Finset.range N, remainderSequence w hw j) := by
    rw [cutoff_decomposition, regularized, sub_smul, sub_smul]
    abel
  rw [he]
  refine (norm_sub_le _ _).trans ?_
  rw [norm_smul, norm_constantProjection, mul_one]
  exact (add_le_add (norm_scalar_error_le hw hw1 hN)
    (norm_remainder_tail_le w hw hN)).trans_eq (by ring)

private theorem tendsto_nat_rpow_neg {σ : ℝ} (hσ : 0 < σ) :
    Tendsto (fun N : ℕ => (N : ℝ) ^ (-σ)) atTop (𝓝 0) :=
  (tendsto_rpow_neg_atTop hσ).comp tendsto_natCast_atTop_atTop

private theorem tendsto_nat_cpow_of_re_neg {v : ℂ} (hv : v.re < 0) :
    Tendsto (fun N : ℕ => (N : ℂ) ^ v) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hr := tendsto_nat_rpow_neg (neg_pos.mpr hv)
  refine hr.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN' : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
  rw [show (N : ℂ) = ((N : ℝ) : ℂ) from by simp,
    Complex.norm_cpow_eq_rpow_re_of_pos hN', neg_neg]

/-- Corrected cutoffs converge throughout `Re w > 0`, away from `w = 1`. -/
theorem tendsto_corrected_cutoff {w : ℂ} (hw : 0 < w.re) (hw1 : w ≠ 1) :
    Tendsto (fun N : ℕ => cutoff w hw N - counterterm w N • constantProjection)
      atTop (𝓝 (regularized w hw)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have ht := (tendsto_nat_rpow_neg hw).const_mul ((‖w‖ + remainderBound w) / w.re)
  simp only [mul_zero] at ht
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) ?_ ht
  filter_upwards [eventually_ge_atTop 1] with N hN
  exact norm_corrected_cutoff_le hw hw1 hN

private theorem scaled_counterterm {w : ℂ} (N : ℕ) (hN : 1 ≤ N) :
    (N : ℂ) ^ (w - 1) * counterterm w N = (1 - w)⁻¹ := by
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hN))
  unfold counterterm
  rw [← mul_div_assoc, ← Complex.cpow_add _ _ hN0,
    show w - 1 + (1 - w) = 0 by ring, Complex.cpow_zero, one_div]

/-- The entire divergent part has one-dimensional range. -/
theorem tendsto_scaled_cutoff {w : ℂ} (hw : 0 < w.re) (hwlt : w.re < 1) :
    Tendsto (fun N : ℕ => (N : ℂ) ^ (w - 1) • cutoff w hw N)
      atTop (𝓝 ((1 - w)⁻¹ • constantProjection)) := by
  have hw1 : w ≠ 1 := by intro h; rw [h, Complex.one_re] at hwlt; exact lt_irrefl _ hwlt
  have hs : Tendsto (fun N : ℕ => (N : ℂ) ^ (w - 1)) atTop (𝓝 0) :=
    tendsto_nat_cpow_of_re_neg (by simpa only [Complex.sub_re, Complex.one_re] using sub_neg.mpr hwlt)
  have ht := (hs.smul (tendsto_corrected_cutoff hw hw1)).add_const
    ((1 - w)⁻¹ • constantProjection)
  simp only [zero_smul, zero_add] at ht
  refine ht.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  rw [smul_sub, smul_smul, scaled_counterterm N hN]
  abel

/-- Exact growth of the uncorrected finite-alphabet operator. -/
theorem tendsto_cutoff_norm_ratio {w : ℂ} (hw : 0 < w.re) (hwlt : w.re < 1) :
    Tendsto (fun N : ℕ => ‖cutoff w hw N‖ / (N : ℝ) ^ (1 - w.re))
      atTop (𝓝 (1 / ‖1 - w‖)) := by
  have ht := (tendsto_scaled_cutoff hw hwlt).norm
  rw [norm_smul, norm_inv, norm_constantProjection, mul_one, ← one_div] at ht
  refine ht.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN' : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
  rw [norm_smul, show (N : ℂ) = ((N : ℝ) : ℂ) from by simp,
    Complex.norm_cpow_eq_rpow_re_of_pos hN', Complex.sub_re, Complex.one_re,
    show w.re - 1 = -(1 - w.re) by ring, Real.rpow_neg hN'.le]
  ring

private theorem counterterm_tendsto_zero {w : ℂ} (hw : 1 < w.re) :
    Tendsto (counterterm w) atTop (𝓝 0) := by
  have h : (1 - w).re < 0 := by simp only [Complex.sub_re, Complex.one_re]; linarith only [hw]
  change Tendsto (fun N : ℕ => (N : ℂ) ^ (1 - w) / (1 - w)) atTop (𝓝 0)
  simpa only [zero_div] using (tendsto_nat_cpow_of_re_neg h).div_const (1 - w)

/-- On the original half-plane the correction tends to zero. -/
private theorem tendsto_cutoff_of_one_lt_re {w : ℂ} (hw : 1 < w.re) :
    Tendsto (cutoff w (zero_lt_one.trans hw)) atTop
      (𝓝 (regularized w (zero_lt_one.trans hw))) := by
  have hw1 : w ≠ 1 := by intro h; rw [h, Complex.one_re] at hw; exact lt_irrefl _ hw
  have ht := (tendsto_corrected_cutoff (zero_lt_one.trans hw) hw1).add
    ((counterterm_tendsto_zero hw).smul_const constantProjection)
  simpa only [sub_add_cancel, zero_smul, add_zero] using ht

/-- Raw cutoffs diverge in norm in the open strip `0 < Re w < 1`. -/
theorem tendsto_cutoff_norm_atTop {w : ℂ} (hw : 0 < w.re) (hwlt : w.re < 1) :
    Tendsto (fun N : ℕ => ‖cutoff w hw N‖) atTop atTop := by
  have hw1 : (1 : ℂ) - w ≠ 0 := by
    intro h
    have he := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.one_re, Complex.zero_re] at he
    linarith only [hwlt, he]
  have hp : Tendsto (fun N : ℕ => (N : ℝ) ^ (1 - w.re)) atTop atTop :=
    (tendsto_rpow_atTop (sub_pos.mpr hwlt)).comp tendsto_natCast_atTop_atTop
  have ht := Tendsto.pos_mul_atTop (one_div_pos.mpr (norm_pos_iff.mpr hw1))
    (tendsto_cutoff_norm_ratio hw hwlt) hp
  refine ht.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN' : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
  exact div_mul_cancel₀ _ (ne_of_gt (Real.rpow_pos_of_pos hN' _))

/-- Any convergent elementary subtraction must remove exactly the evaluation mode. -/
private theorem leadingCoefficient_unique {w : ℂ} (hw : 0 < w.re) (hwlt : w.re < 1)
    {B A : DiscSpace →L[ℂ] DiscSpace}
    (hA : Tendsto (fun N : ℕ => cutoff w hw N - (N : ℂ) ^ (1 - w) • B) atTop (𝓝 A)) :
    B = (1 - w)⁻¹ • constantProjection := by
  have hs : Tendsto (fun N : ℕ => (N : ℂ) ^ (w - 1)) atTop (𝓝 0) :=
    tendsto_nat_cpow_of_re_neg (by simpa only [Complex.sub_re, Complex.one_re] using sub_neg.mpr hwlt)
  have ht : Tendsto (fun N : ℕ => (N : ℂ) ^ (w - 1) • cutoff w hw N - B)
      atTop (𝓝 0) := by
    have h := hs.smul hA
    simp only [zero_smul] at h
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hN))
    rw [smul_sub, smul_smul, ← Complex.cpow_add _ _ hN0,
      show w - 1 + (1 - w) = 0 by ring, Complex.cpow_zero, one_smul]
  have he := tendsto_nhds_unique ((tendsto_scaled_cutoff hw hwlt).sub_const B) ht
  exact (sub_eq_zero.mp he).symm

/-- A convergent leading subtraction exists exactly for the evaluation-mode coefficient. -/
theorem corrected_cutoff_converges_iff {w : ℂ} (hw : 0 < w.re) (hwlt : w.re < 1)
    (B : DiscSpace →L[ℂ] DiscSpace) :
    (∃ A, Tendsto (fun N : ℕ => cutoff w hw N - (N : ℂ) ^ (1 - w) • B) atTop (𝓝 A)) ↔
      B = (1 - w)⁻¹ • constantProjection := by
  constructor
  · rintro ⟨A, hA⟩
    exact leadingCoefficient_unique hw hwlt hA
  · rintro rfl
    have hw1 : w ≠ 1 := by intro h; rw [h, Complex.one_re] at hwlt; exact lt_irrefl _ hwlt
    refine ⟨regularized w hw, ?_⟩
    simpa only [counterterm, div_eq_mul_inv, smul_smul] using tendsto_corrected_cutoff hw hw1

/-- Every actual zeta scattering parameter has divergent raw branch cutoffs. -/
theorem tendsto_nontrivialZero_cutoff_norm_atTop (ρ : RiemannGaussian.NontrivialZetaZero) :
    Tendsto (fun N : ℕ => ‖cutoff ρ.1 ρ.zero_lt_re N‖) atTop atTop :=
  tendsto_cutoff_norm_atTop ρ.zero_lt_re ρ.re_lt_one

/-- Exact leading operator at every actual scattering parameter `s = ρ/2`. -/
theorem nontrivialZero_cutoff_leading_coefficient (ρ : RiemannGaussian.NontrivialZetaZero) :
    Tendsto (fun N : ℕ => (N : ℂ) ^ (ρ.1 - 1) • cutoff ρ.1 ρ.zero_lt_re N)
      atTop (𝓝 ((1 - ρ.1)⁻¹ • constantProjection)) :=
  tendsto_scaled_cutoff ρ.zero_lt_re ρ.re_lt_one

/-- Pointwise formula identifying cutoffs with the actual Gauss–Mayer sums. -/
theorem cutoff_apply (w : ℂ) (hw : 0 < w.re) (N : ℕ)
    (f : DiscSpace) (z : Disc) :
    (cutoff w hw N f).1 z =
      ∑ j ∈ Finset.range N, (((j + 1 : ℕ) : ℂ) + z.1) ^ (-w) *
        plane f ((((j + 1 : ℕ) : ℂ) + z.1)⁻¹) := by
  induction N with
  | zero => simp only [cutoff, Finset.range_zero, Finset.sum_empty, zero_apply]; rfl
  | succ N ih =>
      have he : cutoff w hw (N + 1) = cutoff w hw N +
          branch w hw (N + 1) (Nat.succ_le_succ (Nat.zero_le _)) := by
        exact Finset.sum_range_succ _ N
      rw [he, add_apply, Finset.sum_range_succ]
      change (cutoff w hw N f).1 z + (branchValue w (N + 1) _ f).1 z = _
      rw [ih, branchValue_apply]

/-- The projection returns the constant value `f(0)`. -/
theorem constantProjection_apply (f : DiscSpace) (z : Disc) :
    (constantProjection f).1 z = f.1 zeroPoint := rfl

/-- Uniform norm bound for a single weighted branch. -/
theorem norm_branch_le {w : ℂ} (hw : 0 < w.re) {n : ℕ} (hn : 1 ≤ n) :
    ‖branch w hw n hn‖ ≤ powerBound w * (n : ℝ) ^ (-w.re) := by
  apply ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg (powerBound_pos w).le (Real.rpow_nonneg (Nat.cast_nonneg n) _))
  exact norm_branchValue_le hw hn

/-- Ordinary branch operators converge absolutely when `Re w > 1`. -/
theorem summable_norm_branch {w : ℂ} (hw : 1 < w.re) :
    Summable (fun j => ‖branch w (zero_lt_one.trans hw) (j + 1)
      (Nat.succ_le_succ (Nat.zero_le _))‖) := by
  have hp : Summable (fun j : ℕ => ((j + 1 : ℕ) : ℝ) ^ (-w.re)) :=
    (summable_nat_add_iff (f := fun n : ℕ => (n : ℝ) ^ (-w.re)) 1).mpr
      (RHTower.Sieve.summable_nat_rpow_neg hw)
  apply (hp.mul_left (powerBound w)).of_nonneg_of_le (fun j => norm_nonneg _)
  intro j
  exact norm_branch_le (zero_lt_one.trans hw) (Nat.succ_le_succ (Nat.zero_le j))

/-- The regularized operator agrees with the original transfer operator on `Re w > 1`. -/
theorem regularized_eq_tsum_branch {w : ℂ} (hw : 1 < w.re) :
    regularized w (zero_lt_one.trans hw) =
      ∑' j, branch w (zero_lt_one.trans hw) (j + 1) (Nat.succ_le_succ (Nat.zero_le _)) := by
  have hs := (summable_norm_branch hw).of_norm
  exact tendsto_nhds_unique (tendsto_cutoff_of_one_lt_re hw) hs.hasSum.tendsto_sum_nat

end GaloisForLFunctions.RenormalizedIntersectionTheory.MayerCutoff

#print axioms GaloisForLFunctions.RenormalizedIntersectionTheory.MayerCutoff.norm_corrected_cutoff_le
#print axioms GaloisForLFunctions.RenormalizedIntersectionTheory.MayerCutoff.tendsto_scaled_cutoff
#print axioms GaloisForLFunctions.RenormalizedIntersectionTheory.MayerCutoff.tendsto_cutoff_norm_ratio
#print axioms GaloisForLFunctions.RenormalizedIntersectionTheory.MayerCutoff.corrected_cutoff_converges_iff
#print axioms GaloisForLFunctions.RenormalizedIntersectionTheory.MayerCutoff.tendsto_nontrivialZero_cutoff_norm_atTop
#print axioms GaloisForLFunctions.RenormalizedIntersectionTheory.MayerCutoff.regularized_eq_tsum_branch
