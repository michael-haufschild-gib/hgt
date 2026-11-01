import GaloisForLFunctions.RenormalizedIntersectionTheory.GaussMayerFredholmDeterminant
import GaloisForLFunctions.HTGeometry.WeightedCompositionTrace
import GaloisForLFunctions.HTGeometry.NevanlinnaFullRankPhaseGdelta
import Mathlib.Analysis.Complex.SummableUniformlyOn
import Mathlib.Topology.Algebra.InfiniteSum.TsumUniformlyOn

/-!
# Fixed-point trace of the actual regularized Gauss–Mayer operator

The Cauchy diagonal in the source Fredholm determinant equals the sum of the
Gauss fixed-point contributions after subtraction of the constant mode.
A polynomial-geometric monomial bound justifies the countable interchange.
The corrected scalar summands have explicit two-power decay and converge
normally on `Re w > -1`, continuing the actual first trace beyond the
operator's initial half-plane.
-/

open Complex Metric Set Filter Topology
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.RenormalizedIntersectionTheory.MayerCutoff
open GaloisForLFunctions.RenormalizedIntersectionTheory.MayerNuclear
open GaloisForLFunctions.RenormalizedIntersectionTheory.MayerFredholm

noncomputable section
namespace GaloisForLFunctions.RenormalizedIntersectionTheory.MayerTrace

/-- Positive reciprocal of the fixed point of the `n`th Gauss branch. -/
def multiplier (n : ℕ) : ℝ := ((n : ℝ) + Real.sqrt ((n : ℝ)^2 + 4)) / 2

private theorem multiplier_equation (n : ℕ) :
    multiplier n ^ 2 - n * multiplier n = 1 := by
  have hs := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (n : ℝ)^2 + 4)
  unfold multiplier
  nlinarith only [hs]

theorem nat_lt_multiplier (n : ℕ) : (n : ℝ) < multiplier n := by
  have hs := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (n : ℝ)^2 + 4)
  have hp := Real.sqrt_nonneg ((n : ℝ)^2 + 4)
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have he : (n : ℝ) < Real.sqrt ((n : ℝ)^2 + 4) := by nlinarith only [hs, hp, hn]
  unfold multiplier
  linarith only [he]

theorem multiplier_pos (n : ℕ) : 0 < multiplier n :=
  lt_of_le_of_lt (Nat.cast_nonneg n) (nat_lt_multiplier n)

theorem multiplier_sub_nat (n : ℕ) : multiplier n - n = (multiplier n)⁻¹ := by
  rw [← one_div]
  apply (eq_div_iff (multiplier_pos n).ne').mpr
  rw [sub_mul]
  simpa only [pow_two, one_div] using multiplier_equation n

theorem multiplier_eq_nat_add_inv (n : ℕ) :
    multiplier n = n + (multiplier n)⁻¹ := by
  have h := multiplier_sub_nat n
  linarith only [h]

theorem multiplier_le_nat_add_inv {n : ℕ} (hn : 1 ≤ n) :
    multiplier n ≤ n + (n : ℝ)⁻¹ := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  rw [multiplier_eq_nat_add_inv n]
  exact add_le_add le_rfl ((inv_le_inv₀ (multiplier_pos n) hn0).mpr (nat_lt_multiplier n).le)

/-- Cauchy coefficient on the fixed circle of radius `32/25`. -/
def traceCoefficient (k : ℕ) : DiscSpace →L[ℂ] ℂ :=
  coefficient coefficientRadius coefficientRadius_pos radii.2.2 k

/-- The diagonal does not depend on the rescaling used in the Hilbert factorization. -/
theorem matrix_diagonal {w : ℂ} (hw : 0 < w.re) (k : ℕ) :
    matrix w hw k k = traceCoefficient k (regularized w hw (monomial k)) := by
  have hs : (balanceRadius : ℂ)^k ≠ 0 :=
    pow_ne_zero _ (Complex.ofReal_ne_zero.mpr balanceRadius_pos.ne')
  change (balanceRadius : ℂ)^k * traceCoefficient k
    (((balanceRadius : ℂ)^k)⁻¹ • regularized w hw (monomial k)) = _
  rw [map_smul, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hs, one_mul]

private theorem plane_monomial (k : ℕ) {z : ℂ} (hz : z ∈ outer) :
    plane (monomial k) z = (z - 1)^k := plane_eq (monomial k) ⟨z, hz⟩

/-- The regularized branch on a monomial grows at most linearly in its degree. -/
theorem norm_remainder_monomial {w : ℂ} (hw : 0 < w.re)
    {n : ℕ} (hn : 1 ≤ n) (k : ℕ) :
    ‖branchRemainder w hw n hn (monomial k)‖ ≤
      (2 * k * powerBound w + (5 / 2 : ℝ) * ‖w‖ * powerBound (w + 1)) *
        (n : ℝ)^(-w.re - 1) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hp := (powerBound_pos w).le
  have hq := (powerBound_pos (w + 1)).le
  change ‖(branchRemainder w hw n hn (monomial k)).1‖ ≤ _
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro z
  have hu := inverse_branch_inner hn z.2
  have hu' : ‖((n : ℂ) + z.1)⁻¹ - 1‖ ≤ 1 := by
    simpa only [mem_closedBall, dist_eq_norm] using hu
  have hdiff := norm_pow_sub_pow_le_of_norm_le hu'
    (by norm_num : ‖(-1 : ℂ)‖ ≤ (1 : ℝ)) k
  simp only [one_pow, mul_one, sub_neg_eq_add, sub_add_cancel] at hdiff
  have hdiff' := hdiff.trans (mul_le_mul_of_nonneg_left
    (inverse_branch_norm_le hn z.2) (Nat.cast_nonneg k))
  have hzero : ‖(-1 : ℂ)^k‖ = 1 := by simp
  have he : (branchRemainder w hw n hn (monomial k)).1 z =
      ((n : ℂ) + z.1)^(-w) * ((((n : ℂ) + z.1)⁻¹ - 1)^k - (-1)^k) +
      (((n : ℂ) + z.1)^(-w) - (n : ℂ)^(-w)) * (-1)^k := by
    change (branch w hw n hn (monomial k)).1 z - (n : ℂ)^(-w) * (0 - 1)^k = _
    rw [zero_sub, branch_apply, plane_monomial k
      (closedBall_subset_closedBall (by norm_num : (1 : ℝ) ≤ 3/2) hu)]
    ring
  rw [he]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul, hzero, mul_one]
  have hfirst := mul_le_mul (norm_branch_weight_le hw hn z.2) hdiff'
    (norm_nonneg _) (mul_nonneg hp (Real.rpow_nonneg (Nat.cast_nonneg _) _))
  refine (add_le_add hfirst (norm_branch_weight_sub_le hw hn z.2)).trans_eq ?_
  rw [Real.rpow_sub hn0, Real.rpow_one]
  ring

private theorem branch_decay_summable {w : ℂ} (hw : 0 < w.re) :
    Summable (fun j : ℕ => ((j + 1 : ℕ) : ℝ)^(-w.re - 1)) := by
  rw [show -w.re - 1 = -(w.re + 1) by ring]
  exact (summable_nat_add_iff (f := fun n : ℕ => (n : ℝ)^(-(w.re + 1))) 1).mpr
    (RHTower.Sieve.summable_nat_rpow_neg (by linarith only [hw]))

private theorem coefficient_degree_summable (w : ℂ) :
    Summable (fun k : ℕ => coefficientRadius⁻¹ ^ k *
      (2 * k * powerBound w + (5 / 2 : ℝ) * ‖w‖ * powerBound (w + 1))) := by
  have hr : ‖coefficientRadius⁻¹‖ < 1 := by norm_num [coefficientRadius]
  have h1 := (summable_pow_mul_geometric_of_norm_lt_one 1 hr).mul_left (2 * powerBound w)
  have h0 := (summable_geometric_of_norm_lt_one hr).mul_left
    ((5 / 2 : ℝ) * ‖w‖ * powerBound (w + 1))
  have heq : (fun k : ℕ => coefficientRadius⁻¹ ^ k *
      (2 * k * powerBound w + (5 / 2 : ℝ) * ‖w‖ * powerBound (w + 1))) =
      (fun k : ℕ => 2 * powerBound w * ((k : ℝ)^1 * coefficientRadius⁻¹ ^ k) +
        (5 / 2 : ℝ) * ‖w‖ * powerBound (w + 1) * coefficientRadius⁻¹ ^ k) := by
    funext k
    ring
  rw [heq]
  exact h1.add h0


private theorem nat_add_slit {n : ℕ} (hn : 1 ≤ n) {z : ℂ} (hz : z ∈ outer) :
    (n : ℂ) + z ∈ Complex.slitPlane := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hz' : ‖z - 1‖ ≤ (3 / 2 : ℝ) := by
    simpa only [mem_closedBall, dist_eq_norm] using hz
  have hlow := (neg_le_abs (z - 1).re).trans ((Complex.abs_re_le_norm _).trans hz')
  simp only [Complex.sub_re, Complex.one_re] at hlow
  apply Complex.mem_slitPlane_iff.mpr
  left
  simp only [Complex.add_re, Complex.natCast_re]
  linarith only [hn', hlow]

private theorem nat_add_ne_zero {n : ℕ} (hn : 1 ≤ n) {z : ℂ} (hz : z ∈ outer) :
    (n : ℂ) + z ≠ 0 := by
  intro he
  have h := Complex.mem_slitPlane_iff.mp (nat_add_slit hn hz)
  rw [he] at h
  norm_num at h

private theorem fixedPoint_mem {n : ℕ} (hn : 1 ≤ n) :
    ((multiplier n)⁻¹ : ℂ) ∈ ball 1 coefficientRadius := by
  have ha := multiplier_pos n
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h1 : 1 < multiplier n := hn'.trans_lt (nat_lt_multiplier n)
  have hi : 0 < (multiplier n)⁻¹ := inv_pos.mpr ha
  have hi1 : (multiplier n)⁻¹ < 1 := (inv_lt_one₀ ha).mpr h1
  rw [mem_ball, dist_eq_norm, ← Complex.ofReal_inv, ← Complex.ofReal_one, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs, abs_of_neg (by linarith only [hi1])]
  norm_num [coefficientRadius]
  linarith only [hi]

private theorem fixedPoint_add (n : ℕ) :
    (n : ℂ) + ((multiplier n)⁻¹ : ℂ) = (multiplier n : ℂ) := by
  exact_mod_cast (multiplier_eq_nat_add_inv n).symm

private theorem fixedPoint_eq (n : ℕ) :
    ((n : ℂ) + ((multiplier n)⁻¹ : ℂ))⁻¹ = ((multiplier n)⁻¹ : ℂ) := by
  rw [fixedPoint_add]

/-- The fixed-point contribution of a single Gauss branch. -/
def branchTrace (w : ℂ) (n : ℕ) : ℂ :=
  (multiplier n : ℂ)^(-w) / (1 + ((multiplier n : ℂ)⁻¹)^2)

/-- The actual branch diagonal sums to its fixed-point contribution. -/
theorem hasSum_branch_diagonal {w : ℂ} (hw : 0 < w.re)
    {n : ℕ} (hn : 1 ≤ n) :
    HasSum (fun k => traceCoefficient k (branch w hw n hn (monomial k))) (branchTrace w n) := by
  have hsub : closedBall (1 : ℂ) coefficientRadius ⊆ outer :=
    closedBall_subset_closedBall radii.2.2.le
  have hphi : DifferentiableOn ℂ (fun z : ℂ => ((n : ℂ) + z)⁻¹)
      (closedBall 1 coefficientRadius) := by
    intro z hz
    exact ((differentiableAt_id.const_add (n : ℂ)).inv
      (nat_add_ne_zero hn (hsub hz))).differentiableWithinAt
  have hweight : DifferentiableOn ℂ (fun z : ℂ => ((n : ℂ) + z)^(-w))
      (closedBall 1 coefficientRadius) := by
    intro z hz
    exact (((hasDerivAt_id z).const_add (n : ℂ)).cpow_const
      (c := -w) (nat_add_slit hn (hsub hz))).differentiableAt.differentiableWithinAt
  have hmap : MapsTo (fun z : ℂ => ((n : ℂ) + z)⁻¹)
      (closedBall 1 coefficientRadius) (closedBall 1 ((25/32 : ℝ) * coefficientRadius)) := by
    norm_num [coefficientRadius]
    intro z hz
    exact inverse_branch_inner hn (hsub hz)
  have h := DiscCoefficients.hasSum_coeff_diag coefficientRadius_pos
    (by norm_num : (0 : ℝ) < 1) (by norm_num : (0 : ℝ) ≤ 25/32)
    (by norm_num : (25/32 : ℝ) < 1) hphi hmap hweight
    (fixedPoint_mem hn) (fixedPoint_eq n)
  have hd := (((hasDerivAt_id (((multiplier n)⁻¹ : ℂ))).const_add (n : ℂ)).inv
    (nat_add_ne_zero hn (ball_subset_closedBall
      (closedBall_subset_ball radii.2.2 (ball_subset_closedBall (fixedPoint_mem hn)))))).deriv
  simp only [id_eq, fixedPoint_add] at hd
  change deriv (fun z : ℂ => ((n : ℂ) + z)⁻¹) ((multiplier n : ℂ)⁻¹) =
    -1 / (multiplier n : ℂ)^2 at hd
  have hresult : (((n : ℂ) + ((multiplier n)⁻¹ : ℂ))^(-w)) /
      (1 - deriv (fun z : ℂ => ((n : ℂ) + z)⁻¹) ((multiplier n)⁻¹ : ℂ)) =
        branchTrace w n := by
    rw [hd, fixedPoint_add]
    unfold branchTrace
    congr 1
    simp only [inv_pow]
    ring
  rw [hresult] at h
  simp only [DiscCoefficients.coeff, Complex.ofReal_one, one_pow, one_mul, div_one] at h
  have heq : (fun k : ℕ => DiscCoefficients.cauchyCoeff 1 coefficientRadius k
      (fun z => ((n : ℂ) + z)^(-w) * (((n : ℂ) + z)⁻¹ - 1)^k)) =
      (fun k : ℕ => traceCoefficient k (branch w hw n hn (monomial k))) := by
    funext k
    unfold DiscCoefficients.cauchyCoeff
    congr 1
    apply circleIntegral.integral_congr coefficientRadius_pos.le
    intro z hz
    dsimp only
    have hzD := hsub (sphere_subset_closedBall hz)
    rw [show plane (branch w hw n hn (monomial k)) z =
        (branch w hw n hn (monomial k)).1 ⟨z, hzD⟩ from plane_eq _ ⟨z, hzD⟩,
      branch_apply, plane_monomial k
        (closedBall_subset_closedBall (by norm_num : (1 : ℝ) ≤ 3/2)
          (inverse_branch_inner hn hzD))]
  rw [heq] at h
  exact h

private theorem projection_diagonal_hasSum :
    HasSum (fun k => traceCoefficient k (constantProjection (monomial k))) 1 := by
  have hmap : MapsTo (fun _ : ℂ => (0 : ℂ)) (closedBall 1 coefficientRadius)
      (closedBall 1 ((25/32 : ℝ) * coefficientRadius)) := by
    intro z hz
    norm_num [coefficientRadius, mem_closedBall, dist_eq_norm]
  have h := DiscCoefficients.hasSum_coeff_diag coefficientRadius_pos
    (by norm_num : (0 : ℝ) < 1) (by norm_num : (0 : ℝ) ≤ 25/32)
    (by norm_num : (25/32 : ℝ) < 1) (differentiableOn_const 0) hmap
    (differentiableOn_const 1)
    (by norm_num [mem_ball, dist_eq_norm, coefficientRadius] :
      (0 : ℂ) ∈ ball 1 coefficientRadius) rfl
  simp only [deriv_const, sub_zero, div_one, Complex.ofReal_one, zero_sub,
    one_mul, DiscCoefficients.coeff, one_pow] at h
  have heq : (fun k : ℕ => DiscCoefficients.cauchyCoeff 1 coefficientRadius k
      (fun _ => (-1 : ℂ)^k)) =
      (fun k : ℕ => traceCoefficient k (constantProjection (monomial k))) := by
    funext k
    unfold DiscCoefficients.cauchyCoeff
    congr 1
    apply circleIntegral.integral_congr coefficientRadius_pos.le
    intro z hz
    dsimp only
    have hzD : z ∈ outer := closedBall_subset_closedBall radii.2.2.le
      (sphere_subset_closedBall hz)
    rw [show plane (constantProjection (monomial k)) z =
      (constantProjection (monomial k)).1 ⟨z, hzD⟩ from plane_eq _ ⟨z, hzD⟩]
    change _ * (-1 : ℂ)^k = _ * (0 - 1)^k
    rw [zero_sub]
  rw [heq] at h
  exact h

/-- Cauchy diagonal of a single branch after its constant-mode subtraction. -/
def remainderDiagonal (w : ℂ) (hw : 0 < w.re) (k j : ℕ) : ℂ :=
  traceCoefficient k (branchRemainder w hw (j + 1) (Nat.succ_le_succ (Nat.zero_le j)) (monomial k))

/-- Absolute summability in both indices justifies the trace/branch interchange. -/
theorem summable_norm_remainderDiagonal {w : ℂ} (hw : 0 < w.re) :
    Summable (fun p : ℕ × ℕ => ‖remainderDiagonal w hw p.1 p.2‖) := by
  have hmajor : Summable (fun p : ℕ × ℕ =>
      (coefficientRadius⁻¹ ^ p.1 * (2 * p.1 * powerBound w +
        (5 / 2 : ℝ) * ‖w‖ * powerBound (w + 1))) *
        ((p.2 + 1 : ℕ) : ℝ)^(-w.re - 1)) :=
    summable_mul_of_summable_norm (coefficient_degree_summable w).norm
      (branch_decay_summable hw).norm
  apply hmajor.of_nonneg_of_le (fun _ => norm_nonneg _)
  intro p
  calc
    _ ≤ ‖traceCoefficient p.1‖ * ‖branchRemainder w hw (p.2 + 1)
        (Nat.succ_le_succ (Nat.zero_le p.2)) (monomial p.1)‖ :=
      (traceCoefficient p.1).le_opNorm _
    _ ≤ coefficientRadius⁻¹ ^ p.1 *
        ((2 * p.1 * powerBound w + (5 / 2 : ℝ) * ‖w‖ * powerBound (w + 1)) *
          ((p.2 + 1 : ℕ) : ℝ)^(-w.re - 1)) :=
      mul_le_mul (norm_coefficient_le _ _ _ p.1)
        (norm_remainder_monomial hw (Nat.succ_le_succ (Nat.zero_le p.2)) p.1)
        (norm_nonneg _) (pow_nonneg (inv_nonneg.mpr coefficientRadius_pos.le) _)
    _ = _ := by ring

private theorem remainder_diagonal_hasSum {w : ℂ} (hw : 0 < w.re)
    {n : ℕ} (hn : 1 ≤ n) :
    HasSum (fun k => traceCoefficient k (branchRemainder w hw n hn (monomial k)))
      (branchTrace w n - (n : ℂ)^(-w)) := by
  have h := (hasSum_branch_diagonal hw hn).sub
    (projection_diagonal_hasSum.mul_left ((n : ℂ)^(-w)))
  simpa only [mul_one, branchRemainder, _root_.sub_apply, _root_.smul_apply,
    map_sub, map_smul, smul_eq_mul] using h

private theorem regularized_diagonal {w : ℂ} (hw : 0 < w.re) (k : ℕ) :
    matrix w hw k k = riemannZeta w * traceCoefficient k (constantProjection (monomial k)) +
      ∑' j, remainderDiagonal w hw k j := by
  rw [matrix_diagonal]
  have hrem : Summable (fun j : ℕ =>
      branchRemainder w hw (j + 1) (Nat.succ_le_succ (Nat.zero_le j))) := by
    apply Summable.of_norm
    apply ((branch_decay_summable hw).mul_left (remainderBound w)).of_nonneg_of_le
      (fun _ => norm_nonneg _)
    exact fun j => norm_branchRemainder_le hw (Nat.succ_le_succ (Nat.zero_le j))
  let ev : (DiscSpace →L[ℂ] DiscSpace) →L[ℂ] ℂ :=
    (traceCoefficient k).comp (ContinuousLinearMap.apply ℂ DiscSpace (monomial k))
  have he := ev.map_tsum hrem
  change traceCoefficient k ((∑' j : ℕ, branchRemainder w hw (j + 1)
    (Nat.succ_le_succ (Nat.zero_le j))) (monomial k)) =
      ∑' j, remainderDiagonal w hw k j at he
  change traceCoefficient k ((riemannZeta w • constantProjection +
    ∑' j : ℕ, branchRemainder w hw (j + 1) (Nat.succ_le_succ (Nat.zero_le j)))
      (monomial k)) = _
  rw [_root_.add_apply, _root_.smul_apply, map_add, map_smul, smul_eq_mul, he]

private theorem sum_remainder_diagonal {w : ℂ} (hw : 0 < w.re) :
    (∑' k, ∑' j, remainderDiagonal w hw k j) =
      ∑' j : ℕ, (branchTrace w (j + 1) - ((j + 1 : ℕ) : ℂ)^(-w)) := by
  have hs : Summable (Function.uncurry (remainderDiagonal w hw)) :=
    (summable_norm_remainderDiagonal hw).of_norm
  calc
    _ = ∑' j, ∑' k, remainderDiagonal w hw k j := hs.tsum_comm.symm
    _ = _ := by
      apply tsum_congr
      intro j
      exact (remainder_diagonal_hasSum hw (Nat.succ_le_succ (Nat.zero_le j))).tsum_eq

/-- The actual regularized trace is the normally corrected fixed-point series. -/
theorem diagonalTrace_eq {w : ℂ} (hw : 0 < w.re) :
    diagonalTrace w hw = riemannZeta w +
      ∑' j : ℕ, (branchTrace w (j + 1) - ((j + 1 : ℕ) : ℂ)^(-w)) := by
  have hs : Summable (Function.uncurry (remainderDiagonal w hw)) :=
    (summable_norm_remainderDiagonal hw).of_norm
  have hproj := projection_diagonal_hasSum.mul_left (riemannZeta w)
  have heq : (fun k : ℕ => matrix w hw k k) =
      (fun k : ℕ => riemannZeta w * traceCoefficient k (constantProjection (monomial k)) +
        ∑' j, remainderDiagonal w hw k j) := funext (regularized_diagonal hw)
  have hsOuter : Summable (fun k : ℕ => ∑' j, remainderDiagonal w hw k j) := hs.prod
  rw [diagonalTrace, heq, hproj.summable.tsum_add hsOuter, hproj.tsum_eq,
    mul_one, sum_remainder_diagonal hw]


private theorem norm_positive_cpow_sub {r : ℂ} {x y : ℝ}
    (hx : 0 < x) (hxy : x ≤ y) (hr : r.re ≤ 1) :
    ‖(y : ℂ)^r - (x : ℂ)^r‖ ≤ ‖r‖ * x^(r.re - 1) * (y - x) := by
  have hd (t : ℝ) (ht : t ∈ Icc x y) :
      HasDerivWithinAt (fun u : ℝ => (u : ℂ)^r)
        (r * (t : ℂ)^(r - 1)) (Icc x y) t := by
    by_cases hr0 : r = 0
    · subst r
      simpa using (hasDerivAt_const (x := t) (c := (1 : ℂ))).hasDerivWithinAt
    · exact (hasDerivAt_ofReal_cpow_const (ne_of_gt (hx.trans_le ht.1)) hr0).hasDerivWithinAt
  have hb (t : ℝ) (ht : t ∈ Ico x y) :
      ‖r * (t : ℂ)^(r - 1)‖ ≤ ‖r‖ * x^(r.re - 1) := by
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (hx.trans_le ht.1)]
    simp only [Complex.sub_re, Complex.one_re]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos hx ht.1 (sub_nonpos.mpr hr)) (norm_nonneg r)
  exact norm_image_sub_le_of_norm_deriv_le_segment' hd hb y (right_mem_Icc.mpr hxy)

/-- Removing the constant mode gives two powers of decay in the scalar branch trace. -/
theorem norm_branchTrace_sub_le {w : ℂ} (hw : -1 < w.re) {n : ℕ} (hn : 1 ≤ n) :
    ‖branchTrace w n - (n : ℂ)^(-w)‖ ≤
      (‖w‖ + 1) * (n : ℝ)^(-w.re - 2) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have ha := multiplier_pos n
  have hna := (nat_lt_multiplier n).le
  have hdiff := norm_positive_cpow_sub (r := -w) hn0 hna
    (by simp only [Complex.neg_re]; linarith only [hw])
  simp only [norm_neg, Complex.neg_re] at hdiff
  have hdiff' : ‖(multiplier n : ℂ)^(-w) - (n : ℂ)^(-w)‖ ≤
      ‖w‖ * (n : ℝ)^(-w.re - 2) := by
    refine hdiff.trans ?_
    have hi : multiplier n - n ≤ (n : ℝ)⁻¹ := by
      have h := multiplier_le_nat_add_inv hn
      linarith only [h]
    calc
      _ ≤ ‖w‖ * (n : ℝ)^(-w.re - 1) * (n : ℝ)⁻¹ :=
        mul_le_mul_of_nonneg_left hi (by positivity)
      _ = _ := by
        conv_rhs => rw [show -w.re - 2 = (-w.re - 1) - 1 by ring,
          Real.rpow_sub hn0, Real.rpow_one]
        ring
  have hdenR : 0 < 1 + ((multiplier n)⁻¹)^2 := by positivity
  have hden : (1 : ℂ) + ((multiplier n : ℂ)⁻¹)^2 ≠ 0 := by
    exact_mod_cast hdenR.ne'
  have halg : branchTrace w n - (multiplier n : ℂ)^(-w) =
      -((multiplier n : ℂ)^(-w) * ((multiplier n : ℂ)⁻¹)^2) /
        (1 + ((multiplier n : ℂ)⁻¹)^2) := by
    apply (eq_div_iff hden).mpr
    unfold branchTrace
    rw [sub_mul, div_mul_cancel₀ _ hden]
    ring
  have hcorr : ‖branchTrace w n - (multiplier n : ℂ)^(-w)‖ ≤
      (n : ℝ)^(-w.re - 2) := by
    rw [halg, norm_div, norm_neg, norm_mul, norm_pow, norm_inv,
      Complex.norm_real, Real.norm_of_nonneg ha.le,
      Complex.norm_cpow_eq_rpow_re_of_pos ha, Complex.neg_re]
    have hd : ‖(1 : ℂ) + ((multiplier n : ℂ)⁻¹)^2‖ = 1 + ((multiplier n)⁻¹)^2 := by
      rw [← Complex.ofReal_inv, ← Complex.ofReal_pow, ← Complex.ofReal_one,
        ← Complex.ofReal_add, Complex.norm_real, Real.norm_of_nonneg hdenR.le]
    rw [hd]
    calc
      _ ≤ (multiplier n)^(-w.re) * ((multiplier n)⁻¹)^2 :=
        div_le_self (by positivity) (by nlinarith only [sq_nonneg ((multiplier n)⁻¹)])
      _ = (multiplier n)^(-w.re - 2) := by
        rw [Real.rpow_sub ha, Real.rpow_two, inv_pow]
        ring
      _ ≤ (n : ℝ)^(-w.re - 2) :=
        Real.rpow_le_rpow_of_nonpos hn0 hna (by linarith only [hw])
  calc
    _ ≤ ‖branchTrace w n - (multiplier n : ℂ)^(-w)‖ +
        ‖(multiplier n : ℂ)^(-w) - (n : ℂ)^(-w)‖ := by
      have he : branchTrace w n - (n : ℂ)^(-w) =
          (branchTrace w n - (multiplier n : ℂ)^(-w)) +
            ((multiplier n : ℂ)^(-w) - (n : ℂ)^(-w)) := by ring
      rw [he]
      exact norm_add_le _ _
    _ ≤ (n : ℝ)^(-w.re - 2) + ‖w‖ * (n : ℝ)^(-w.re - 2) := add_le_add hcorr hdiff'
    _ = _ := by ring

/-- The corrected fixed-point series converges beyond the operator's initial half-plane. -/
theorem correctedTrace_summable {w : ℂ} (hw : -1 < w.re) :
    Summable (fun j : ℕ => branchTrace w (j + 1) - ((j + 1 : ℕ) : ℂ)^(-w)) := by
  have hs : Summable (fun j : ℕ => ((j + 1 : ℕ) : ℝ)^(-w.re - 2)) := by
    rw [show -w.re - 2 = -(w.re + 2) by ring]
    exact (summable_nat_add_iff (f := fun n : ℕ => (n : ℝ)^(-(w.re + 2))) 1).mpr
      (RHTower.Sieve.summable_nat_rpow_neg (by linarith only [hw]))
  exact (((hs.mul_left (‖w‖ + 1)).of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun j => norm_branchTrace_sub_le hw (Nat.succ_le_succ (Nat.zero_le j))))).of_norm

/-- The trace after subtraction of its zeta term. -/
def traceCorrection (w : ℂ) : ℂ :=
  ∑' j : ℕ, (branchTrace w (j + 1) - ((j + 1 : ℕ) : ℂ)^(-w))

/-- The fixed-point correction converges normally on `Re w > -1`. -/
theorem correctedTrace_locallyUniform :
    SummableLocallyUniformlyOn
      (fun j : ℕ => fun w : ℂ => branchTrace w (j + 1) - ((j + 1 : ℕ) : ℂ)^(-w))
      {w : ℂ | -1 < w.re} := by
  apply SummableLocallyUniformlyOn_of_locally_bounded
    (isOpen_lt continuous_const Complex.continuous_re)
  intro K hK hKc
  by_cases hKn : K.Nonempty
  · obtain ⟨a, haK, hamin⟩ := hKc.exists_isMinOn hKn Complex.continuous_re.continuousOn
    obtain ⟨C, hC⟩ := hKc.bddAbove_image continuous_norm.continuousOn
    have ha : -1 < a.re := hK haK
    have hC0 : 0 ≤ C := (norm_nonneg a).trans (hC ⟨a, haK, rfl⟩)
    have hs : Summable (fun j : ℕ => ((j + 1 : ℕ) : ℝ)^(-a.re - 2)) := by
      rw [show -a.re - 2 = -(a.re + 2) by ring]
      exact (summable_nat_add_iff (f := fun n : ℕ => (n : ℝ)^(-(a.re + 2))) 1).mpr
        (RHTower.Sieve.summable_nat_rpow_neg (by linarith only [ha]))
    refine ⟨fun j : ℕ => (C + 1) * ((j + 1 : ℕ) : ℝ)^(-a.re - 2), hs.mul_left _, ?_⟩
    intro j w hwK
    have hw : -1 < w.re := hK hwK
    have hRe : a.re ≤ w.re := hamin hwK
    have hn : (1 : ℝ) ≤ (j + 1 : ℕ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le j)
    refine (norm_branchTrace_sub_le hw (Nat.succ_le_succ (Nat.zero_le j))).trans ?_
    exact mul_le_mul (add_le_add (hC ⟨w, hwK, rfl⟩) le_rfl)
      (Real.rpow_le_rpow_of_exponent_le hn (by linarith only [hRe]))
      (Real.rpow_nonneg (by positivity) _) (by linarith only [hC0])
  · refine ⟨fun _ : ℕ => 0, summable_zero, ?_⟩
    intro j w hwK
    exact False.elim (hKn ⟨w, hwK⟩)

/-- Holomorphy of the correction follows from normal convergence of entire summands. -/
theorem differentiableOn_traceCorrection :
    DifferentiableOn ℂ traceCorrection {w : ℂ | -1 < w.re} := by
  apply SummableLocallyUniformlyOn.differentiableOn
    (isOpen_lt continuous_const Complex.continuous_re) correctedTrace_locallyUniform
  intro j w hw
  have ha : (multiplier (j + 1) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (multiplier_pos _).ne'
  have hn : ((j + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero j)
  simp only [branchTrace, Complex.cpow_def_of_ne_zero ha, Complex.cpow_def_of_ne_zero hn]
  fun_prop

/-- The fixed-point continuation of the actual first Fredholm trace. -/
def continuedTrace (w : ℂ) : ℂ := riemannZeta w + traceCorrection w

/-- The continuation agrees with the trace of the original regularized Banach operator. -/
theorem continuedTrace_eq_diagonalTrace {w : ℂ} (hw : 0 < w.re) :
    continuedTrace w = diagonalTrace w hw := (diagonalTrace_eq hw).symm

/-- The actual first trace continues holomorphically to `Re w > -1`, away from `w = 1`. -/
theorem differentiableOn_continuedTrace :
    DifferentiableOn ℂ continuedTrace {w : ℂ | -1 < w.re ∧ w ≠ 1} := by
  intro w hw
  exact ((differentiableAt_riemannZeta hw.2).add
    (differentiableOn_traceCorrection.differentiableAt
      ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hw.1))).differentiableWithinAt


end GaloisForLFunctions.RenormalizedIntersectionTheory.MayerTrace

#print axioms GaloisForLFunctions.RenormalizedIntersectionTheory.MayerTrace.norm_remainder_monomial
#print axioms GaloisForLFunctions.RenormalizedIntersectionTheory.MayerTrace.hasSum_branch_diagonal
#print axioms GaloisForLFunctions.RenormalizedIntersectionTheory.MayerTrace.summable_norm_remainderDiagonal
#print axioms GaloisForLFunctions.RenormalizedIntersectionTheory.MayerTrace.diagonalTrace_eq
#print axioms GaloisForLFunctions.RenormalizedIntersectionTheory.MayerTrace.norm_branchTrace_sub_le
#print axioms GaloisForLFunctions.RenormalizedIntersectionTheory.MayerTrace.correctedTrace_locallyUniform
#print axioms GaloisForLFunctions.RenormalizedIntersectionTheory.MayerTrace.differentiableOn_continuedTrace
