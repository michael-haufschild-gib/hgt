import GaloisForLFunctions.RenormalizedIntersectionTheory.GaussMayerCutoffRenormalization
import GaloisForLFunctions.HTGeometry.DiscCoefficientExpansion
import GaloisForLFunctions.RHTower.Deninger.DeningerNuclearOperator

/-!
# Order-zero nuclearity of the regularized Gauss–Mayer operator

The actual operator on the Banach disc algebra `|z - 1| ≤ 3/2` is controlled by
suprema on any smaller disc of radius greater than one. Cauchy coefficients
therefore give a rank-one expansion with geometrically decaying norm products.
Its first `N` terms have rank at most `N`, with an explicit operator-norm error;
the same decomposition is summable to every positive real power.

The analytic interpretation is on `Re w > 0`, away from the scalar pole `w = 1`.
Pointwise statements also apply to the totalized value of `regularized` there.
-/

open Complex Metric Set Filter Topology
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.RenormalizedIntersectionTheory.MayerCutoff

noncomputable section

namespace GaloisForLFunctions.RenormalizedIntersectionTheory.MayerNuclear

private theorem plane_add (f g : DiscSpace) : plane (f + g) = plane f + plane g :=
  holoExtend_add _ _

private theorem plane_smul (c : ℂ) (f : DiscSpace) : plane (c • f) = c • plane f :=
  holoExtend_smul c _

private theorem plane_on_smaller_closed (f : DiscSpace) {R : ℝ} (hR : R < 3 / 2) :
    DifferentiableOn ℂ (plane f) (closedBall (1 : ℂ) R) :=
  (differentiableOn_plane f).mono (closedBall_subset_ball hR)

/-- The centered monomial `z ↦ (z - 1)^k` in the Banach disc algebra. -/
def monomial (k : ℕ) : DiscSpace :=
  ⟨⟨fun z => (z.1 - 1) ^ k, (continuous_subtype_val.sub continuous_const).pow k⟩, by
    change DifferentiableOn ℂ
      (holoExtend MayerCutoff.inner (fun z : ↥MayerCutoff.inner => (z.1 - 1) ^ k)) MayerCutoff.inner
    apply ((differentiableOn_id.sub_const 1).pow k).congr
    intro z hz
    exact holoExtend_of_mem _ hz⟩

private theorem plane_monomial (k : ℕ) {z : ℂ} (hz : z ∈ outer) :
    plane (monomial k) z = (z - 1) ^ k :=
  plane_eq (monomial k) ⟨z, hz⟩

private theorem cauchy_integrable (f : DiscSpace) {R : ℝ} (hR : 0 < R)
    (hRouter : R < 3 / 2) (k : ℕ) :
    CircleIntegrable (fun z => ((z - 1) ^ (k + 1))⁻¹ * plane f z) 1 R := by
  apply ContinuousOn.circleIntegrable hR.le
  apply ContinuousOn.mul _ ((plane_on_smaller_closed f hRouter).continuousOn.mono sphere_subset_closedBall)
  apply ContinuousOn.inv₀ ((continuousOn_id.sub continuousOn_const).pow (k + 1))
  intro z hz
  apply pow_ne_zero
  intro he
  have hn := DiscCoefficients.norm_sub_eq_of_mem_sphere hz
  change z - 1 = 0 at he
  rw [he, norm_zero] at hn
  exact hR.ne' hn.symm

private theorem coefficient_bound (R : ℝ) (hR : 0 < R) (hRouter : R < 3 / 2)
    (k : ℕ) (f : DiscSpace) :
    ‖DiscCoefficients.cauchyCoeff 1 R k (plane f)‖ ≤ R⁻¹ ^ k * ‖f‖ := by
  have h := DiscCoefficients.norm_cauchyCoeff_le hR
    (fun z hz => norm_plane_le f (ball_subset_closedBall
      (closedBall_subset_ball hRouter (sphere_subset_closedBall hz)))) k
  simpa only [div_eq_mul_inv, inv_pow, mul_comm] using h

/-- The bounded Cauchy coefficient functional on an interior circle. -/
def coefficient (R : ℝ) (hR : 0 < R) (hRouter : R < 3 / 2) (k : ℕ) :
    DiscSpace →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun f => DiscCoefficients.cauchyCoeff 1 R k (plane f)
      map_add' := fun f g => by
        rw [plane_add]
        unfold DiscCoefficients.cauchyCoeff
        simp only [Pi.add_apply, mul_add]
        rw [circleIntegral.integral_add (cauchy_integrable f hR hRouter k)
          (cauchy_integrable g hR hRouter k), mul_add]
      map_smul' := fun c f => by
        rw [plane_smul]
        exact DiscCoefficients.cauchyCoeff_const_mul 1 R k c (plane f) }
    (R⁻¹ ^ k) (coefficient_bound R hR hRouter k)

/-- Cauchy's estimate bounds the coefficient functional by `R⁻ᵏ`. -/
theorem norm_coefficient_le (R : ℝ) (hR : 0 < R) (hRouter : R < 3 / 2) (k : ℕ) :
    ‖coefficient R hR hRouter k‖ ≤ R⁻¹ ^ k := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro f
  change ‖DiscCoefficients.cauchyCoeff 1 R k (plane f)‖ ≤ R⁻¹ ^ k * ‖f‖
  exact coefficient_bound R hR hRouter k f

private theorem deriv_plane_local_bound (f : DiscSpace) {r A : ℝ}
    (hr : 1 < r) (hrouter : r < 3 / 2)
    (hf : ∀ z ∈ closedBall (1 : ℂ) r, ‖plane f z‖ ≤ A)
    {z : ℂ} (hz : z ∈ closedBall (1 : ℂ) 1) :
    ‖deriv (plane f) z‖ ≤ A / (r - 1) := by
  have hlocal : closedBall z (r - 1) ⊆ closedBall (1 : ℂ) r := by
    intro v hv
    have hz' : ‖z - 1‖ ≤ 1 := by simpa only [mem_closedBall, dist_eq_norm] using hz
    have hv' : ‖v - z‖ ≤ r - 1 := by simpa only [mem_closedBall, dist_eq_norm] using hv
    rw [mem_closedBall, dist_eq_norm,
      show v - 1 = (v - z) + (z - 1) by ring]
    exact (norm_add_le _ _).trans (by linarith only [hz', hv'])
  have hsub : closedBall z (r - 1) ⊆ inner :=
    hlocal.trans (closedBall_subset_ball hrouter)
  exact Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (sub_pos.mpr hr)
    ((differentiableOn_plane f).diffContOnCl_ball hsub)
    (fun v hv => hf v (hlocal (sphere_subset_closedBall hv)))

private theorem plane_sub_zero_local_bound (f : DiscSpace) {r A : ℝ}
    (hr : 1 < r) (hrouter : r < 3 / 2)
    (hf : ∀ z ∈ closedBall (1 : ℂ) r, ‖plane f z‖ ≤ A)
    {z : ℂ} (hz : z ∈ closedBall (1 : ℂ) 1) :
    ‖plane f z - plane f 0‖ ≤ A / (r - 1) * ‖z‖ := by
  have h := (convex_closedBall (1 : ℂ) (1 : ℝ)).norm_image_sub_le_of_norm_deriv_le
    (fun v hv => (differentiableOn_plane f).differentiableAt
      (isOpen_ball.mem_nhds (closedBall_subset_ball (by norm_num : (1 : ℝ) < 3 / 2) hv)))
    (fun v hv => deriv_plane_local_bound f hr hrouter hf hv)
    (by norm_num [mem_closedBall, dist_eq_norm] : (0 : ℂ) ∈ closedBall (1 : ℂ) 1) hz
  simpa only [sub_zero] using h

/-- Local branch-remainder constant from the Cauchy derivative and principal-power bounds. -/
def localRemainderBound (w : ℂ) (r : ℝ) : ℝ :=
  2 / (r - 1) * powerBound w + (5 / 2 : ℝ) * ‖w‖ * powerBound (w + 1)

private theorem localRemainderBound_nonneg (w : ℂ) {r : ℝ} (hr : 1 < r) :
    0 ≤ localRemainderBound w r := by
  have hp := (powerBound_pos w).le
  have hp' := (powerBound_pos (w + 1)).le
  have hδ := (sub_pos.mpr hr).le
  unfold localRemainderBound
  positivity

private theorem norm_branchRemainder_apply_local {w : ℂ} (hw : 0 < w.re)
    {n : ℕ} (hn : 1 ≤ n) (f : DiscSpace) {r A : ℝ}
    (hr : 1 < r) (hrouter : r < 3 / 2)
    (hf : ∀ z ∈ closedBall (1 : ℂ) r, ‖plane f z‖ ≤ A) (z : Disc) :
    ‖(branchRemainder w hw n hn f).1 z‖ ≤
      localRemainderBound w r * (n : ℝ) ^ (-w.re - 1) * A := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hp := (powerBound_pos w).le
  have hp' := (powerBound_pos (w + 1)).le
  have hz0 : (0 : ℂ) ∈ closedBall (1 : ℂ) r := by
    simpa only [mem_closedBall, dist_zero_left, norm_one] using hr.le
  have hA : 0 ≤ A := (norm_nonneg (plane f 0)).trans (hf 0 hz0)
  have hδ : 0 < r - 1 := sub_pos.mpr hr
  -- Subtract the constant mode before estimating each inverse branch.
  have hdiff := (plane_sub_zero_local_bound f hr hrouter hf (inverse_branch_inner hn z.2)).trans
    (mul_le_mul_of_nonneg_left (inverse_branch_norm_le hn z.2) (div_nonneg hA hδ.le))
  have hzero : plane f 0 = f.1 zeroPoint := plane_eq f zeroPoint
  rw [hzero] at hdiff
  have h0 : ‖f.1 zeroPoint‖ ≤ A := by rw [← hzero]; exact hf 0 hz0
  have he : (branchRemainder w hw n hn f).1 z =
      ((n : ℂ) + z.1) ^ (-w) * (plane f (((n : ℂ) + z.1)⁻¹) - f.1 zeroPoint) +
      (((n : ℂ) + z.1) ^ (-w) - (n : ℂ) ^ (-w)) * f.1 zeroPoint := by
    change (branch w hw n hn f).1 z - (n : ℂ) ^ (-w) * f.1 zeroPoint = _
    rw [branch_apply]
    ring
  rw [he]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul]
  have hfirst := mul_le_mul (norm_branch_weight_le hw hn z.2) hdiff
    (norm_nonneg _) (mul_nonneg (powerBound_pos w).le (Real.rpow_nonneg (Nat.cast_nonneg _) _))
  have hsecond := mul_le_mul (norm_branch_weight_sub_le hw hn z.2) h0
    (norm_nonneg _) (by positivity : 0 ≤ ((5 / 2 : ℝ) * ‖w‖ * powerBound (w + 1)) * (n : ℝ) ^ (-w.re - 1))
  refine (add_le_add hfirst hsecond).trans_eq ?_
  rw [Real.rpow_sub hn', Real.rpow_one]
  unfold localRemainderBound
  ring

private theorem norm_branchRemainder_local {w : ℂ} (hw : 0 < w.re)
    {n : ℕ} (hn : 1 ≤ n) (f : DiscSpace) {r A : ℝ}
    (hr : 1 < r) (hrouter : r < 3 / 2)
    (hf : ∀ z ∈ closedBall (1 : ℂ) r, ‖plane f z‖ ≤ A) :
    ‖branchRemainder w hw n hn f‖ ≤
      localRemainderBound w r * (n : ℝ) ^ (-w.re - 1) * A := by
  have hz0 : (0 : ℂ) ∈ closedBall (1 : ℂ) r := by
    simpa only [mem_closedBall, dist_zero_left, norm_one] using hr.le
  have hA : 0 ≤ A := (norm_nonneg (plane f 0)).trans (hf 0 hz0)
  have hB := localRemainderBound_nonneg w hr
  change ‖(branchRemainder w hw n hn f).1‖ ≤ _
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  exact norm_branchRemainder_apply_local hw hn f hr hrouter hf

private def decay (w : ℂ) (j : ℕ) : ℝ := ((j + 1 : ℕ) : ℝ) ^ (-w.re - 1)

private theorem decay_nonneg (w : ℂ) (j : ℕ) : 0 ≤ decay w j :=
  Real.rpow_nonneg (Nat.cast_nonneg _) _

private theorem decay_summable {w : ℂ} (hw : 0 < w.re) : Summable (decay w) := by
  have h := (summable_nat_add_iff (f := fun n : ℕ => (n : ℝ) ^ (-(w.re + 1))) 1).mpr
    (RHTower.Sieve.summable_nat_rpow_neg (by linarith only [hw]))
  change Summable (fun j : ℕ => ((j + 1 : ℕ) : ℝ) ^ (-w.re - 1))
  rw [show -w.re - 1 = -(w.re + 1) by ring]
  exact h

/-- Local operator constant: `|ζ(w)|` plus the summable branch-remainder majorant. -/
def localBound (w : ℂ) (r : ℝ) : ℝ :=
  ‖riemannZeta w‖ + localRemainderBound w r * ∑' j, decay w j

private theorem localBound_nonneg (w : ℂ) {r : ℝ} (hr : 1 < r) :
    0 ≤ localBound w r :=
  add_nonneg (norm_nonneg _) (mul_nonneg (localRemainderBound_nonneg w hr)
    (tsum_nonneg (decay_nonneg w)))

private theorem remainder_norm_summable {w : ℂ} (hw : 0 < w.re) :
    Summable (fun j : ℕ => ‖branchRemainder w hw (j + 1) (Nat.succ_le_succ (Nat.zero_le j))‖) := by
  apply ((decay_summable hw).mul_left (remainderBound w)).of_nonneg_of_le (fun _ => norm_nonneg _)
  exact fun j => norm_branchRemainder_le hw (Nat.succ_le_succ (Nat.zero_le j))

private theorem regularized_apply_eq {w : ℂ} (hw : 0 < w.re) (f : DiscSpace) :
    regularized w hw f = riemannZeta w • constant (f.1 zeroPoint) +
      ∑' j : ℕ, branchRemainder w hw (j + 1) (Nat.succ_le_succ (Nat.zero_le j)) f := by
  change (riemannZeta w • constantProjection +
    ∑' j : ℕ, branchRemainder w hw (j + 1) (Nat.succ_le_succ (Nat.zero_le j))) f = _
  have htsum := (ContinuousLinearMap.apply ℂ DiscSpace f).map_tsum
    (remainder_norm_summable hw).of_norm
  change (∑' j : ℕ, branchRemainder w hw (j + 1)
    (Nat.succ_le_succ (Nat.zero_le j))) f =
      ∑' j : ℕ, branchRemainder w hw (j + 1) (Nat.succ_le_succ (Nat.zero_le j)) f at htsum
  rw [_root_.add_apply, _root_.smul_apply, htsum]
  rfl

/-- A supremum on any concentric disc of radius greater than one controls the full operator norm. -/
theorem regularized_local_bound {w : ℂ} (hw : 0 < w.re)
    (f : DiscSpace) {r A : ℝ} (hr : 1 < r) (hrouter : r < 3 / 2)
    (hf : ∀ z ∈ closedBall (1 : ℂ) r, ‖plane f z‖ ≤ A) :
    ‖regularized w hw f‖ ≤ localBound w r * A := by
  have hz0 : (0 : ℂ) ∈ closedBall (1 : ℂ) r := by
    simpa only [mem_closedBall, dist_zero_left, norm_one] using hr.le
  have hA : 0 ≤ A := (norm_nonneg (plane f 0)).trans (hf 0 hz0)
  have hzero : ‖f.1 zeroPoint‖ ≤ A := by rw [← plane_eq f zeroPoint]; exact hf 0 hz0
  let F : ℕ → DiscSpace := fun j =>
    branchRemainder w hw (j + 1) (Nat.succ_le_succ (Nat.zero_le j)) f
  have hsum : Summable (fun j => ‖F j‖) :=
    ((remainder_norm_summable hw).mul_right ‖f‖).of_nonneg_of_le
      (fun _ => norm_nonneg _) (fun j => ContinuousLinearMap.le_opNorm _ f)
  have hmajor : Summable (fun j => localRemainderBound w r * decay w j * A) :=
    ((decay_summable hw).mul_left _).mul_right _
  have ht : ‖∑' j, F j‖ ≤ (localRemainderBound w r * ∑' j, decay w j) * A := by
    refine (norm_tsum_le_tsum_norm hsum).trans ?_
    calc ∑' j, ‖F j‖ ≤ ∑' j, localRemainderBound w r * decay w j * A :=
           hsum.tsum_le_tsum (fun j => norm_branchRemainder_local hw
             (Nat.succ_le_succ (Nat.zero_le j)) f hr hrouter hf) hmajor
         _ = _ := by rw [tsum_mul_right, tsum_mul_left]
  rw [regularized_apply_eq hw f]
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, norm_constant]
  calc ‖riemannZeta w‖ * ‖f.1 zeroPoint‖ + ‖∑' j, F j‖
      ≤ ‖riemannZeta w‖ * A + (localRemainderBound w r * ∑' j, decay w j) * A :=
        add_le_add (mul_le_mul_of_nonneg_left hzero (norm_nonneg _)) ht
       _ = localBound w r * A := by unfold localBound; ring

/-- The image of the `k`th monomial is bounded by the local constant times `r^k`. -/
theorem regularized_monomial_bound {w : ℂ} (hw : 0 < w.re)
    {r : ℝ} (hr : 1 < r) (hrouter : r < 3 / 2) (k : ℕ) :
    ‖regularized w hw (monomial k)‖ ≤ localBound w r * r ^ k := by
  apply regularized_local_bound hw (monomial k) hr hrouter
  intro z hz
  rw [plane_monomial k (ball_subset_closedBall (closedBall_subset_ball hrouter hz)), norm_pow]
  apply pow_le_pow_left₀ (norm_nonneg _)
  simpa only [mem_closedBall, dist_eq_norm] using hz

/-- Cauchy coefficient norms times monomial-image norms decay geometrically. -/
theorem nuclear_term_bound {w : ℂ} (hw : 0 < w.re) {r R : ℝ}
    (hr : 1 < r) (hrR : r < R) (hRouter : R < 3 / 2) (k : ℕ) :
    ‖coefficient R (zero_lt_one.trans (hr.trans hrR)) hRouter k‖ *
      ‖regularized w hw (monomial k)‖ ≤ localBound w r * (r / R) ^ k := by
  have hR : 0 < R := zero_lt_one.trans (hr.trans hrR)
  refine (mul_le_mul (norm_coefficient_le R hR hRouter k)
    (regularized_monomial_bound hw hr (hrR.trans hRouter) k)
    (norm_nonneg _) (by positivity)).trans_eq ?_
  rw [div_pow, div_eq_mul_inv, inv_pow]
  ring

private def planeLinear : DiscSpace →ₗ[ℂ] (ℂ → ℂ) where
  toFun := plane
  map_add' := plane_add
  map_smul' := plane_smul

private def taylorPartial (R : ℝ) (hR : 0 < R) (hRouter : R < 3 / 2)
    (N : ℕ) (f : DiscSpace) : DiscSpace :=
  ∑ k ∈ Finset.range N, coefficient R hR hRouter k f • monomial k

private theorem plane_taylorPartial (R : ℝ) (hR : 0 < R) (hRouter : R < 3 / 2)
    (N : ℕ) (f : DiscSpace) {z : ℂ} (hz : z ∈ outer) :
    plane (taylorPartial R hR hRouter N f) z =
      ∑ k ∈ Finset.range N, coefficient R hR hRouter k f * (z - 1) ^ k := by
  change planeLinear (∑ k ∈ Finset.range N,
    coefficient R hR hRouter k f • monomial k) z = _
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro k hk
  change coefficient R hR hRouter k f * plane (monomial k) z = _
  rw [plane_monomial k hz]

private theorem hasSum_taylor (R : ℝ) (hR : 0 < R) (hRouter : R < 3 / 2)
    (f : DiscSpace) {z : ℂ} (hz : z ∈ ball (1 : ℂ) R) :
    HasSum (fun k => coefficient R hR hRouter k f * (z - 1) ^ k) (plane f z) := by
  change HasSum (fun k => DiscCoefficients.cauchyCoeff 1 R k (plane f) * (z - 1) ^ k)
    (plane f z)
  simpa only [DiscCoefficients.coeff, Complex.ofReal_one, one_pow, one_mul, div_one]
    using DiscCoefficients.hasSum_coeff hR zero_lt_one (plane_on_smaller_closed f hRouter) hz

private theorem taylor_term_bound (R : ℝ) (hR : 0 < R) (hRouter : R < 3 / 2)
    (f : DiscSpace) {r : ℝ} (_hr : 0 ≤ r) {z : ℂ} (hz : z ∈ closedBall (1 : ℂ) r)
    (k : ℕ) :
    ‖coefficient R hR hRouter k f * (z - 1) ^ k‖ ≤ ‖f‖ * (r / R) ^ k := by
  rw [norm_mul, norm_pow]
  have hz' : ‖z - 1‖ ≤ r := by simpa only [mem_closedBall, dist_eq_norm] using hz
  refine (mul_le_mul (coefficient_bound R hR hRouter k f)
    (pow_le_pow_left₀ (norm_nonneg _) hz' k) (by positivity) (by positivity)).trans_eq ?_
  rw [div_pow, div_eq_mul_inv, inv_pow]
  ring

/-- Only the smaller disc is used; no boundary convergence of Taylor sums is assumed. -/
private theorem taylor_local_remainder (R : ℝ) (hR : 0 < R) (hRouter : R < 3 / 2)
    (N : ℕ) (f : DiscSpace) {r : ℝ} (hr : 0 ≤ r) (hrR : r < R)
    {z : ℂ} (hz : z ∈ closedBall (1 : ℂ) r) :
    ‖plane (taylorPartial R hR hRouter N f - f) z‖ ≤
      ‖f‖ * (r / R) ^ N / (1 - r / R) := by
  have he : plane (taylorPartial R hR hRouter N f - f) z =
      plane (taylorPartial R hR hRouter N f) z - plane f z :=
    congrFun (map_sub planeLinear _ _) z
  rw [he, plane_taylorPartial R hR hRouter N f
    (ball_subset_closedBall (closedBall_subset_ball (hrR.trans hRouter) hz))]
  exact norm_sub_le_of_geometric_bound_of_hasSum ((div_lt_one hR).mpr hrR)
    (taylor_term_bound R hR hRouter f hr hz)
    (hasSum_taylor R hR hRouter f (closedBall_subset_ball hrR hz)) N

/-- The `k`th rank-one term of the actual Mayer operator's Cauchy expansion. -/
def rankTerm (w : ℂ) (hw : 0 < w.re) (R : ℝ) (hR : 0 < R)
    (hRouter : R < 3 / 2) (k : ℕ) : DiscSpace →L[ℂ] DiscSpace :=
  (coefficient R hR hRouter k).smulRight (regularized w hw (monomial k))

/-- The first `N` terms of the rank-one Cauchy expansion. -/
def approximation (w : ℂ) (hw : 0 < w.re) (R : ℝ) (hR : 0 < R)
    (hRouter : R < 3 / 2) (N : ℕ) : DiscSpace →L[ℂ] DiscSpace :=
  ∑ k ∈ Finset.range N, rankTerm w hw R hR hRouter k

private theorem approximation_apply (w : ℂ) (hw : 0 < w.re) (R : ℝ) (hR : 0 < R)
    (hRouter : R < 3 / 2) (N : ℕ) (f : DiscSpace) :
    approximation w hw R hR hRouter N f = regularized w hw (taylorPartial R hR hRouter N f) := by
  simp only [approximation, rankTerm, taylorPartial, _root_.sum_apply,
    ContinuousLinearMap.smulRight_apply, map_sum, map_smul]

/-- The Taylor truncation has range in a space of dimension at most `N`. -/
theorem approximation_finiteRank (w : ℂ) (hw : 0 < w.re)
    (R : ℝ) (hR : 0 < R) (hRouter : R < 3 / 2) (N : ℕ) :
    ∃ V : Submodule ℂ DiscSpace, FiniteDimensional ℂ V ∧
      Module.finrank ℂ V ≤ N ∧ ∀ f, approximation w hw R hR hRouter N f ∈ V := by
  classical
  refine ⟨Submodule.span ℂ
      ((((Finset.range N).image (fun k => regularized w hw (monomial k)) :
        Finset DiscSpace) : Set DiscSpace)),
    FiniteDimensional.span_of_finite ℂ (Finset.finite_toSet _), ?_, ?_⟩
  · exact (finrank_span_finset_le_card _).trans
      (Finset.card_image_le.trans (by simp))
  · intro f
    simp only [approximation, _root_.sum_apply]
    refine Submodule.sum_mem _ fun k hk => ?_
    change coefficient R hR hRouter k f • regularized w hw (monomial k) ∈ _
    exact Submodule.smul_mem _ _
      (Submodule.subset_span (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hk)))

/-- The Taylor truncation approximates the actual operator with an explicit geometric error. -/
theorem approximation_error {w : ℂ} (hw : 0 < w.re) {r R : ℝ}
    (hr : 1 < r) (hrR : r < R) (hRouter : R < 3 / 2) (N : ℕ) :
    ‖approximation w hw R (zero_lt_one.trans (hr.trans hrR)) hRouter N - regularized w hw‖ ≤
      localBound w r * (r / R) ^ N / (1 - r / R) := by
  have hR : 0 < R := zero_lt_one.trans (hr.trans hrR)
  have hq0 : 0 ≤ r / R := div_nonneg (zero_lt_one.trans hr).le hR.le
  have hq1 : r / R < 1 := (div_lt_one hR).mpr hrR
  apply ContinuousLinearMap.opNorm_le_bound _
    (div_nonneg (mul_nonneg (localBound_nonneg w hr) (pow_nonneg hq0 _)) (sub_pos.mpr hq1).le)
  intro f
  change ‖approximation w hw R hR hRouter N f - regularized w hw f‖ ≤ _
  rw [approximation_apply, ← map_sub]
  have h := regularized_local_bound hw (taylorPartial R hR hRouter N f - f)
    hr (hrR.trans hRouter) (fun z hz => taylor_local_remainder R hR hRouter N f
      (zero_lt_one.trans hr).le hrR hz)
  exact h.trans_eq (by ring)

private theorem norm_rankTerm_bound {w : ℂ} (hw : 0 < w.re) {r R : ℝ}
    (hr : 1 < r) (hrR : r < R) (hRouter : R < 3 / 2) (k : ℕ) :
    ‖rankTerm w hw R (zero_lt_one.trans (hr.trans hrR)) hRouter k‖ ≤
      localBound w r * (r / R) ^ k := by
  rw [rankTerm, ContinuousLinearMap.norm_smulRight_apply]
  exact nuclear_term_bound hw hr hrR hRouter k

/-- The rank-one expansion is absolutely summable in operator norm. -/
theorem rankTerm_norm_summable {w : ℂ} (hw : 0 < w.re) {r R : ℝ}
    (hr : 1 < r) (hrR : r < R) (hRouter : R < 3 / 2) :
    Summable (fun k => ‖rankTerm w hw R (zero_lt_one.trans (hr.trans hrR)) hRouter k‖) := by
  have hR : 0 < R := zero_lt_one.trans (hr.trans hrR)
  exact ((summable_geometric_of_lt_one (div_nonneg (zero_lt_one.trans hr).le hR.le)
    ((div_lt_one hR).mpr hrR)).mul_left (localBound w r)).of_nonneg_of_le
      (fun _ => norm_nonneg _) (norm_rankTerm_bound hw hr hrR hRouter)

/-- The rank-one series sums to the actual regularized operator in operator norm. -/
theorem hasSum_rankTerm {w : ℂ} (hw : 0 < w.re) {r R : ℝ}
    (hr : 1 < r) (hrR : r < R) (hRouter : R < 3 / 2) :
    HasSum (rankTerm w hw R (zero_lt_one.trans (hr.trans hrR)) hRouter) (regularized w hw) := by
  have hR : 0 < R := zero_lt_one.trans (hr.trans hrR)
  have hq0 : 0 ≤ r / R := div_nonneg (zero_lt_one.trans hr).le hR.le
  have hq1 : r / R < 1 := (div_lt_one hR).mpr hrR
  have hs := (rankTerm_norm_summable hw hr hrR hRouter).of_norm.hasSum
  have hl : Tendsto (fun N => approximation w hw R hR hRouter N) atTop (𝓝 (regularized w hw)) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    apply squeeze_zero (fun _ => norm_nonneg _) (approximation_error hw hr hrR hRouter)
    have hpow := tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1
    simpa only [mul_zero, zero_div] using
      (tendsto_const_nhds.mul hpow).div_const (1 - r / R)
  have heq := tendsto_nhds_unique hs.tendsto_sum_nat hl
  exact heq ▸ hs

/-- The same Cauchy decomposition has summable norm products to every positive real power. -/
theorem nuclear_products_summable_rpow {w : ℂ} (hw : 0 < w.re) {r R : ℝ}
    (hr : 1 < r) (hrR : r < R) (hRouter : R < 3 / 2) {p : ℝ} (hp : 0 < p) :
    Summable (fun k =>
      (‖coefficient R (zero_lt_one.trans (hr.trans hrR)) hRouter k‖ *
        ‖regularized w hw (monomial k)‖) ^ p) := by
  have hR : 0 < R := zero_lt_one.trans (hr.trans hrR)
  have hq0 : 0 ≤ r / R := div_nonneg (zero_lt_one.trans hr).le hR.le
  have hq1 : r / R < 1 := (div_lt_one hR).mpr hrR
  have he : ∀ k : ℕ, ((r / R) ^ k) ^ p = ((r / R) ^ p) ^ k := by
    intro k
    induction k with
    | zero => simp only [pow_zero, Real.one_rpow]
    | succ k ih =>
        rw [pow_succ, Real.mul_rpow (pow_nonneg hq0 _) hq0, ih, pow_succ]
  apply ((summable_geometric_of_lt_one (Real.rpow_nonneg hq0 p)
    (Real.rpow_lt_one hq0 hq1 hp)).mul_left ((localBound w r) ^ p)).of_nonneg_of_le
    (fun _ => Real.rpow_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)) p)
  intro k
  calc
    _ ≤ (localBound w r * (r / R) ^ k) ^ p :=
      Real.rpow_le_rpow (mul_nonneg (norm_nonneg _) (norm_nonneg _))
        (nuclear_term_bound hw hr hrR hRouter k) hp.le
    _ = _ := by rw [Real.mul_rpow (localBound_nonneg w hr) (pow_nonneg hq0 _), he]

/-- A single rank-one expansion of the actual regularized operator works for every positive order. -/
theorem nuclear_order_zero {w : ℂ} (hw : 0 < w.re) :
    ∃ (φ : ℕ → (DiscSpace →L[ℂ] ℂ)) (y : ℕ → DiscSpace),
      (∀ p : ℝ, 0 < p → Summable (fun k => (‖φ k‖ * ‖y k‖) ^ p)) ∧
      HasSum (fun k => (φ k).smulRight (y k)) (regularized w hw) := by
  let r : ℝ := 9 / 8
  let R : ℝ := 5 / 4
  have hr : 1 < r := by norm_num [r]
  have hrR : r < R := by norm_num [r, R]
  have hRouter : R < 3 / 2 := by norm_num [R]
  have hR : 0 < R := zero_lt_one.trans (hr.trans hrR)
  refine ⟨coefficient R hR hRouter, fun k => regularized w hw (monomial k), ?_, ?_⟩
  · exact fun _ hp => nuclear_products_summable_rpow hw hr hrR hRouter hp
  · exact hasSum_rankTerm hw hr hrR hRouter

/-- The regularized Mayer operator satisfies the existing Banach nuclearity interface. -/
theorem nuclear_regularized {w : ℂ} (hw : 0 < w.re) :
    RHTower.DeningerIsNuclear (regularized w hw) := by
  let r : ℝ := 9 / 8
  let R : ℝ := 5 / 4
  have hr : 1 < r := by norm_num [r]
  have hrR : r < R := by norm_num [r, R]
  have hRouter : R < 3 / 2 := by norm_num [R]
  have hR : 0 < R := zero_lt_one.trans (hr.trans hrR)
  refine ⟨ℕ, coefficient R hR hRouter, fun k => regularized w hw (monomial k), ?_, ?_⟩
  · have h := rankTerm_norm_summable hw hr hrR hRouter
    simpa only [rankTerm, ContinuousLinearMap.norm_smulRight_apply] using h
  · intro f
    exact (ContinuousLinearMap.apply ℂ DiscSpace f).hasSum (hasSum_rankTerm hw hr hrR hRouter)

/-- The actual regularized Mayer operator is compact. -/
theorem compact_regularized {w : ℂ} (hw : 0 < w.re) :
    IsCompactOperator (regularized w hw) :=
  (nuclear_regularized hw).isCompactOperator

#print axioms regularized_local_bound
#print axioms approximation_error
#print axioms hasSum_rankTerm
#print axioms nuclear_regularized
#print axioms approximation_finiteRank
#print axioms nuclear_products_summable_rpow
#print axioms compact_regularized
#print axioms nuclear_order_zero

end GaloisForLFunctions.RenormalizedIntersectionTheory.MayerNuclear
