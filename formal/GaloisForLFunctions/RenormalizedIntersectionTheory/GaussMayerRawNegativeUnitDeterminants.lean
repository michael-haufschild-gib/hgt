import GaloisForLFunctions.RenormalizedIntersectionTheory.GaussMayerNegativeUnitCancellation
import GaloisForLFunctions.RenormalizedIntersectionTheory.GaussMayerFixedPointTrace

/-!
# Convergence of raw negative-unit Mayer determinants

The genuine first-`N` Gauss branches have convergent Fredholm determinants
`det(I+L_N(w))` throughout `Re w>0`, although their operator norms diverge
on `0<Re w<1`. The finite successor response gives an exact rank-one shear
whose trace exponential cancels. The remaining centered tail tends to zero,
and uniform geometric Cauchy bounds justify the determinant limit.

The finite-branch operator and its Hilbert matrix are linked by their actual
Cauchy expansion. Branch truncation and matrix truncation remain distinct.
The limit is the actual source determinant at spectral parameter `-1`,
including its assigned value at the operator's source pole.
-/

open Complex Metric Set Filter Topology
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.RenormalizedIntersectionTheory.MayerCutoff
open GaloisForLFunctions.RenormalizedIntersectionTheory.MayerNuclear
open GaloisForLFunctions.RenormalizedIntersectionTheory.MayerFredholm
open GaloisForLFunctions.RenormalizedIntersectionTheory.MayerParameter
open GaloisForLFunctions.RenormalizedIntersectionTheory.MayerCancellation

set_option autoImplicit false
noncomputable section
namespace GaloisForLFunctions.RenormalizedIntersectionTheory.MayerRaw

/-- Scalar constant mode in the first `N` genuine branches. -/
def scalarPart (w : ℂ) (N : ℕ) : ℂ :=
  ∑ n ∈ Finset.range N, ((n+1 : ℕ) : ℂ)^(-w)

/-- Finite sum of the actual constant-mode branch remainders. -/
def finiteRemainder (w : ℂ) (N : ℕ) : DiscSpace →L[ℂ] DiscSpace :=
  ∑ n ∈ Finset.range N, entireRemainder n w

theorem cutoff_eq {w : ℂ} (hw : 0 < w.re) (N : ℕ) :
    cutoff w hw N = finiteRemainder w N + scalarPart w N • constantProjection := by
  simp only [finiteRemainder, entireRemainder_eq hw, branchRemainder,
    Finset.sum_sub_distrib, ← Finset.sum_smul, scalarPart, cutoff]
  abel

/-- Removing the finite scalar sum makes the genuine cutoffs converge in operator norm. -/
theorem finiteRemainder_tendsto {w : ℂ} (hw : 0 < w.re) :
    Tendsto (finiteRemainder w) atTop (𝓝 (remainder w)) :=
  (remainder_locallyUniform.summable hw).hasSum.tendsto_sum_nat

private theorem decay_summable {w : ℂ} (hw : 0 < w.re) :
    Summable (fun n : ℕ => ((n+1 : ℕ) : ℝ)^(-w.re-1)) := by
  rw [show -w.re-1 = -(w.re+1) by ring]
  exact (summable_nat_add_iff (f := fun n : ℕ => (n : ℝ)^(-(w.re+1))) 1).mpr
    (RHTower.Sieve.summable_nat_rpow_neg (by linarith only [hw]))

/-- Degree-linear bound uniform in the number of retained branches. -/
theorem finiteRemainder_monomial {w : ℂ} (hw : 0 < w.re) (N j : ℕ) :
    ‖finiteRemainder w N (monomial j)‖ ≤
      (2*j*powerBound w + (5/2 : ℝ)*‖w‖*powerBound (w+1)) *
        ∑' n : ℕ, ((n+1 : ℕ) : ℝ)^(-w.re-1) := by
  have hC : 0 ≤ 2*j*powerBound w + (5/2 : ℝ)*‖w‖*powerBound (w+1) := by
    have := (powerBound_pos w).le
    have := (powerBound_pos (w+1)).le
    positivity
  rw [finiteRemainder, _root_.sum_apply]
  refine (norm_sum_le _ _).trans ?_
  calc
    _ ≤ ∑ n ∈ Finset.range N,
        (2*j*powerBound w + (5/2 : ℝ)*‖w‖*powerBound (w+1)) *
          ((n+1 : ℕ) : ℝ)^(-w.re-1) := by
      apply Finset.sum_le_sum
      intro n hn
      rw [entireRemainder_eq hw]
      exact MayerTrace.norm_remainder_monomial hw (Nat.succ_pos _) j
    _ = (2*j*powerBound w + (5/2 : ℝ)*‖w‖*powerBound (w+1)) *
        ∑ n ∈ Finset.range N, ((n+1 : ℕ) : ℝ)^(-w.re-1) := by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (sum_le_hasSum _ (fun n _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)
        (decay_summable hw).hasSum) hC

/-- Actual terminal power in the finite successor telescope. -/
def tailWeight (w : ℂ) (hw : 0 < w.re) (N : ℕ) : DiscSpace :=
  branch w hw (N+1) (Nat.succ_pos _) (constant 1)

theorem tailWeight_apply {w : ℂ} (hw : 0 < w.re) (N : ℕ) (z : Disc) :
    (tailWeight w hw N).1 z = (((N+1 : ℕ) : ℂ)+z.1)^(-w) := by
  rw [tailWeight, branch_apply]
  have hz : (((N+1 : ℕ) : ℂ)+z.1)⁻¹ ∈ outer :=
    closedBall_subset_closedBall (by norm_num : (1 : ℝ) ≤ 3/2)
      (inverse_branch_inner (Nat.succ_pos N) z.property)
  rw [plane_eq (constant 1) ⟨_, hz⟩]
  change _ * 1 = _
  rw [mul_one]

/-- The finite operator response retains exactly one terminal power. -/
theorem cutoff_response {w : ℂ} (hw : 0 < w.re) (N : ℕ) :
    response w + cutoff w hw N (response w) = constant 1 - tailWeight w hw N := by
  apply Subtype.ext
  ext z
  have he : (cutoff w hw N (response w)).1 z =
      (1+z.1)^(-w)-(((N+1 : ℕ) : ℂ)+z.1)^(-w) := by
    change evaluation z (cutoff w hw N (response w)) = _
    rw [cutoff, _root_.sum_apply, map_sum]
    change (∑ n ∈ Finset.range N, (branch w hw (n+1) (Nat.succ_pos n) (response w)).1 z) = _
    simp only [branch_response hw]
    exact partial_telescope w z.1 N
  change (response w).1 z + (cutoff w hw N (response w)).1 z =
    1 - (tailWeight w hw N).1 z
  rw [response_apply, he, tailWeight_apply]
  ring

/-- Remove the constant value of the terminal power before taking its norm. -/
def centeredTail (w : ℂ) (hw : 0 < w.re) (N : ℕ) : DiscSpace :=
  tailWeight w hw N - constant (((N+1 : ℕ) : ℂ)^(-w))

theorem norm_centeredTail {w : ℂ} (hw : 0 < w.re) (N : ℕ) :
    ‖centeredTail w hw N‖ ≤
      ((5/2 : ℝ)*‖w‖*powerBound (w+1))*((N+1 : ℕ) : ℝ)^(-w.re-1) := by
  change ‖(centeredTail w hw N).1‖ ≤ _
  apply (ContinuousMap.norm_le _ (by have := (powerBound_pos (w+1)).le; positivity)).mpr
  intro z
  change ‖(tailWeight w hw N).1 z - ((N+1 : ℕ) : ℂ)^(-w)‖ ≤ _
  rw [tailWeight_apply]
  exact norm_branch_weight_sub_le hw (Nat.succ_pos _) z.property


/-- A geometric majorant for linear growth of rescaled Cauchy monomials. -/
def degreeBound : ℝ := ∑' j : ℕ, ((j : ℝ)+1)*(8/9 : ℝ)^j

private theorem degree_summable : Summable (fun j : ℕ => ((j : ℝ)+1)*(8/9 : ℝ)^j) := by
  have h1 := summable_pow_mul_geometric_of_norm_lt_one 1
    (by norm_num : ‖(8/9 : ℝ)‖ < 1)
  have h0 := summable_geometric_of_norm_lt_one (by norm_num : ‖(8/9 : ℝ)‖ < 1)
  have he : (fun j : ℕ => ((j : ℝ)+1)*(8/9 : ℝ)^j) =
      fun j : ℕ => (j : ℝ)^1*(8/9 : ℝ)^j + (8/9 : ℝ)^j := by
    funext j
    ring
  rw [he]
  exact h1.add h0

theorem degreeBound_nonneg : 0 ≤ degreeBound :=
  tsum_nonneg fun j => mul_nonneg (by positivity) (pow_nonneg (by norm_num) _)

/-- Linear monomial growth is absorbed by the fixed geometric rate. -/
theorem degree_bound (j : ℕ) :
    ((j : ℝ)+1)*balanceRadius⁻¹^j ≤ degreeBound*rate^j := by
  have hj : ((j : ℝ)+1)*(8/9 : ℝ)^j ≤ degreeBound := by
    have hs := sum_le_hasSum ({j} : Finset ℕ)
      (fun k _ => mul_nonneg (by positivity : 0 ≤ (k : ℝ)+1)
        (pow_nonneg (by norm_num : (0 : ℝ) ≤ 8/9) _)) degree_summable.hasSum
    simpa only [Finset.sum_singleton, degreeBound] using hs
  calc
    _ = (((j : ℝ)+1)*(8/9 : ℝ)^j)*rate^j := by
      rw [mul_assoc, ← mul_pow]
      norm_num [balanceRadius, rate]
    _ ≤ _ := mul_le_mul_of_nonneg_right hj (pow_nonneg rate_bounds.1 _)

/-- A uniform constant for the Cauchy matrices of the finite remainders. -/
def remainderConstant (w : ℂ) : ℝ :=
  (2*powerBound w + (5/2 : ℝ)*‖w‖*powerBound (w+1)) *
    (∑' n : ℕ, ((n+1 : ℕ) : ℝ)^(-w.re-1)) * degreeBound

private theorem remainderConstant_nonneg (w : ℂ) : 0 ≤ remainderConstant w := by
  have := (powerBound_pos w).le
  have := (powerBound_pos (w+1)).le
  have ht : 0 ≤ ∑' n : ℕ, ((n+1 : ℕ) : ℝ)^(-w.re-1) :=
    tsum_nonneg fun _ => Real.rpow_nonneg (Nat.cast_nonneg _) _
  have := degreeBound_nonneg
  unfold remainderConstant
  positivity

/-- Uniform geometric control of the actual finite-remainder monomial images. -/
theorem finiteRemainder_scaled_monomial {w : ℂ} (hw : 0 < w.re) (N j : ℕ) :
    ‖((balanceRadius : ℂ)^j)⁻¹ • finiteRemainder w N (monomial j)‖ ≤
      remainderConstant w * rate^j := by
  have hP := (powerBound_pos w).le
  have hQ := (powerBound_pos (w+1)).le
  have hS : 0 ≤ ∑' n : ℕ, ((n+1 : ℕ) : ℝ)^(-w.re-1) :=
    tsum_nonneg fun _ => Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hj : 0 ≤ (j : ℝ) := Nat.cast_nonneg j
  have hpoly : 2*j*powerBound w + (5/2 : ℝ)*‖w‖*powerBound (w+1) ≤
      (2*powerBound w+(5/2 : ℝ)*‖w‖*powerBound (w+1))*((j : ℝ)+1) := by
    have hq : 0 ≤ (5/2 : ℝ)*‖w‖*powerBound (w+1) := by positivity
    nlinarith only [hP, mul_nonneg hj hq]
  rw [norm_smul, norm_inv, norm_pow, Complex.norm_real,
    Real.norm_of_nonneg balanceRadius_pos.le, ← inv_pow]
  calc
    _ ≤ balanceRadius⁻¹^j *
        ((2*j*powerBound w+(5/2 : ℝ)*‖w‖*powerBound (w+1))*
          ∑' n : ℕ, ((n+1 : ℕ) : ℝ)^(-w.re-1)) :=
      mul_le_mul_of_nonneg_left (finiteRemainder_monomial hw N j)
        (pow_nonneg (inv_nonneg.mpr balanceRadius_pos.le) _)
    _ ≤ balanceRadius⁻¹^j *
        (((2*powerBound w+(5/2 : ℝ)*‖w‖*powerBound (w+1))*((j : ℝ)+1))*
          ∑' n : ℕ, ((n+1 : ℕ) : ℝ)^(-w.re-1)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hpoly hS)
        (pow_nonneg (inv_nonneg.mpr balanceRadius_pos.le) _)
    _ = ((2*powerBound w+(5/2 : ℝ)*‖w‖*powerBound (w+1))*
          ∑' n : ℕ, ((n+1 : ℕ) : ℝ)^(-w.re-1)) *
        (((j : ℝ)+1)*balanceRadius⁻¹^j) := by ring
    _ ≤ ((2*powerBound w+(5/2 : ℝ)*‖w‖*powerBound (w+1))*
          ∑' n : ℕ, ((n+1 : ℕ) : ℝ)^(-w.re-1)) * (degreeBound*rate^j) :=
      mul_le_mul_of_nonneg_left (degree_bound j) (by positivity)
    _ = _ := by unfold remainderConstant; ring

/-- The branch cutoff and Cauchy cutoff are distinct; this bound is uniform in the former. -/
theorem finiteRemainder_geometric {w : ℂ} (hw : 0 < w.re) (N : ℕ) :
    GeomFredholm.GeomDecay (MayerPole.operatorMatrix (finiteRemainder w N))
      (remainderConstant w) rate := by
  refine ⟨remainderConstant_nonneg w, rate_bounds.1, rate_bounds.2, fun i j => ?_⟩
  apply ((functional i).le_opNorm _).trans
  exact (mul_le_mul (norm_functional_le i) (finiteRemainder_scaled_monomial hw N j)
    (norm_nonneg _) (pow_nonneg rate_bounds.1 _)).trans_eq (by ring)

open GeomFredholm

/-- Uniform geometric tails turn entrywise convergence into Fredholm convergence. -/
theorem tendsto_fdet_of_uniform_geometric
    {A : ℕ → ℕ → ℕ → ℂ} {M : ℕ → ℕ → ℂ} {C η : ℝ}
    (hA : ∀ᶠ n in atTop, GeomDecay (A n) C η)
    (hentry : ∀ i j, Tendsto (fun n => A n i j) atTop (𝓝 (M i j))) (lam : ℂ) :
    Tendsto (fun n => fdet (A n) lam) atTop (𝓝 (fdet M lam)) := by
  obtain ⟨n, hn⟩ := hA.exists
  have hM : GeomDecay M C η := ⟨hn.const_nonneg, hn.rate_nonneg, hn.rate_lt_one,
    fun i j => le_of_tendsto (hentry i j).norm (hA.mono fun n hn => hn.bound i j)⟩
  have hfinite (K : ℕ) : Tendsto (fun n => truncDet (A n) lam K) atTop
      (𝓝 (truncDet M lam K)) := by
    have hm : Tendsto (fun n => (1 - lam • trunc (A n) K)) atTop
        (𝓝 (1 - lam • trunc M K)) := by
      apply tendsto_pi_nhds.mpr
      intro i
      apply tendsto_pi_nhds.mpr
      intro j
      exact tendsto_const_nhds.sub ((hentry i j).const_mul lam)
    exact (continuous_id.matrix_det.continuousAt.tendsto).comp hm
  have herr : Tendsto (fun K : ℕ => incConst lam C η * η^K / (1-η)) atTop (𝓝 0) := by
    have hp := (tendsto_pow_atTop_nhds_zero_of_lt_one hM.rate_nonneg hM.rate_lt_one).const_mul
      (incConst lam C η)
    simpa only [mul_zero, zero_div] using hp.div_const (1-η)
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hthird : 0 < ε/3 := by linarith only [hε]
  obtain ⟨K, hK⟩ := (herr.eventually (gt_mem_nhds hthird)).exists
  filter_upwards [hA, (hfinite K).eventually (Metric.ball_mem_nhds _ hthird)] with n hAn hn
  have hleft := dist_truncDet_fdet_le hAn lam K
  have hright := dist_truncDet_fdet_le hM lam K
  have hmid : dist (truncDet (A n) lam K) (truncDet M lam K) < ε/3 := hn
  have htri := dist_triangle4 (fdet (A n) lam) (truncDet (A n) lam K)
    (truncDet M lam K) (fdet M lam)
  have hleft' : dist (fdet (A n) lam) (truncDet (A n) lam K) ≤
      incConst lam C η * η^K / (1-η) := by rwa [dist_comm]
  linarith only [htri, hleft', hright, hmid, hK]



/-- Constant value of the terminal power in the finite telescope. -/
def terminalScalar (w : ℂ) (N : ℕ) : ℂ := ((N+1 : ℕ) : ℂ)^(-w)

private theorem terminalScalar_norm {w : ℂ} (N : ℕ) :
    ‖terminalScalar w N‖ = ((N+1 : ℕ) : ℝ)^(-w.re) := by
  have hn : (0 : ℝ) < (N+1 : ℕ) := by positivity
  change ‖((N+1 : ℕ) : ℂ)^(-w)‖ = _
  rw [show ((N+1 : ℕ) : ℂ) = (((N+1 : ℕ) : ℝ) : ℂ) by simp,
    Complex.norm_cpow_eq_rpow_re_of_pos hn, Complex.neg_re]

/-- The terminal constant decays on the whole source half-plane. -/
theorem terminalScalar_tendsto {w : ℂ} (hw : 0 < w.re) :
    Tendsto (terminalScalar w) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  simp only [terminalScalar_norm]
  exact (_root_.tendsto_rpow_neg_atTop hw).comp
    (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))

/-- Each branch constant has norm at most one. -/
theorem scalarPart_norm {w : ℂ} (hw : 0 < w.re) (N : ℕ) :
    ‖scalarPart w N‖ ≤ N := by
  rw [scalarPart]
  refine (norm_sum_le _ _).trans ?_
  calc
    _ ≤ ∑ n ∈ Finset.range N, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro n hn
      change ‖terminalScalar w n‖ ≤ 1
      rw [terminalScalar_norm]
      exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast Nat.succ_pos n) (neg_nonpos.mpr hw.le)
    _ = _ := by simp

/-- Coefficient of the finite determinant-one shear. -/
def shearCoefficient (w : ℂ) (N : ℕ) : ℂ :=
  scalarPart w N / (1-terminalScalar w N)

/-- The shear denominator is bounded away from zero in the cutoff limit. -/
theorem eventually_shearCoefficient_bound {w : ℂ} (hw : 0 < w.re) :
    ∀ᶠ N : ℕ in atTop, (1-terminalScalar w N) ≠ 0 ∧ ‖shearCoefficient w N‖ ≤ 2*N := by
  have ht : Tendsto (fun N => ‖terminalScalar w N‖) atTop (𝓝 0) := by
    simpa only [norm_zero] using (terminalScalar_tendsto hw).norm
  have he : ∀ᶠ N : ℕ in atTop, ‖terminalScalar w N‖ < (1/2 : ℝ) := by
    simpa only [norm_zero] using ht.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1/2))
  filter_upwards [he] with N hN
  have htri := norm_add_le (1-terminalScalar w N) (terminalScalar w N)
  rw [sub_add_cancel, norm_one] at htri
  have hden : (1/2 : ℝ) ≤ ‖1-terminalScalar w N‖ := by linarith only [htri, hN]
  have hpos : 0 < ‖1-terminalScalar w N‖ := lt_of_lt_of_le (by norm_num) hden
  refine ⟨norm_ne_zero_iff.mp hpos.ne', ?_⟩
  rw [shearCoefficient, norm_div]
  apply (div_le_iff₀ hpos).mpr
  have hmul := mul_le_mul_of_nonneg_left hden (by positivity : (0 : ℝ) ≤ 2*N)
  have hscalar := scalarPart_norm hw N
  nlinarith only [hscalar, hmul]

/-- The centered terminal vector is the only residual after the shear. -/
def shearResidual (w : ℂ) (hw : 0 < w.re) (N : ℕ) : DiscSpace :=
  shearCoefficient w N • centeredTail w hw N

/-- Exact finite subtraction loses no constant mode and gains one full power in the tail. -/
theorem eventually_norm_shearResidual_le {w : ℂ} (hw : 0 < w.re) :
    ∀ᶠ N : ℕ in atTop, ‖shearResidual w hw N‖ ≤
      (5*‖w‖*powerBound (w+1))*((N+1 : ℕ) : ℝ)^(-w.re) := by
  filter_upwards [eventually_shearCoefficient_bound hw] with N hN
  have hn : (0 : ℝ) < (N+1 : ℕ) := by positivity
  have hnp : (N : ℝ) ≤ ((N+1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ N
  have hp := (powerBound_pos (w+1)).le
  rw [shearResidual, norm_smul]
  calc
    _ ≤ (2*(N : ℝ))*
        (((5/2 : ℝ)*‖w‖*powerBound (w+1))*((N+1 : ℕ) : ℝ)^(-w.re-1)) :=
      mul_le_mul hN.2 (norm_centeredTail hw N) (norm_nonneg _) (by positivity)
    _ ≤ (2*((N+1 : ℕ) : ℝ))*
        (((5/2 : ℝ)*‖w‖*powerBound (w+1))*((N+1 : ℕ) : ℝ)^(-w.re-1)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hnp (by norm_num)) (by positivity)
    _ = _ := by
      rw [Real.rpow_sub hn, Real.rpow_one]
      field_simp

/-- The exact shear residual tends to zero as a vector of the original disc algebra. -/
theorem shearResidual_tendsto {w : ℂ} (hw : 0 < w.re) :
    Tendsto (shearResidual w hw) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have ht := ((_root_.tendsto_rpow_neg_atTop hw).comp
    (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))).const_mul
      (5*‖w‖*powerBound (w+1))
  have ht' : Tendsto (fun N : ℕ => (5*‖w‖*powerBound (w+1))*
      ((N+1 : ℕ) : ℝ)^(-w.re)) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, mul_zero] using ht
  exact squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
    (eventually_norm_shearResidual_le hw) ht'


/-- Corrected finite operator after the exact successor shear. -/
def correctedOperator (w : ℂ) (hw : 0 < w.re) (N : ℕ) : DiscSpace →L[ℂ] DiscSpace :=
  finiteRemainder w N + (evaluation zeroPoint).smulRight (shearResidual w hw N)

/-- The corrected finite operators converge to the holomorphic remainder. -/
theorem correctedOperator_tendsto {w : ℂ} (hw : 0 < w.re) :
    Tendsto (correctedOperator w hw) atTop (𝓝 (remainder w)) := by
  have hr : Tendsto (fun N => (evaluation zeroPoint).smulRight (shearResidual w hw N))
      atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    simp only [ContinuousLinearMap.norm_smulRight_apply]
    simpa only [norm_zero, mul_zero] using
      (shearResidual_tendsto hw).norm.const_mul ‖evaluation zeroPoint‖
  have he : correctedOperator w hw = fun N => finiteRemainder w N +
      (evaluation zeroPoint).smulRight (shearResidual w hw N) := by
    funext N
    rfl
  rw [he]
  simpa only [add_zero] using (finiteRemainder_tendsto hw).add hr

private theorem evaluationWeight_bound (j : ℕ) : ‖evaluationWeight j‖ ≤ rate^j := by
  have h := MayerPole.geomDecay_projection.bound 0 j
  simpa only [MayerPole.projectionMatrix_eq, ite_true, pow_zero, one_mul, evaluationWeight] using h

private theorem evaluation_rankOne_matrix (v : DiscSpace) (i j : ℕ) :
    MayerPole.operatorMatrix ((evaluation zeroPoint).smulRight v) i j =
      functional i v * evaluationWeight j := by
  change functional i (((balanceRadius : ℂ)^j)⁻¹ •
    (((evaluation zeroPoint) (monomial j)) • v)) = _
  change functional i (((balanceRadius : ℂ)^j)⁻¹ • (((0 : ℂ)-1)^j • v)) = _
  rw [zero_sub, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  unfold evaluationWeight
  ring

/-- Uniform nuclear control survives the finite shear. -/
theorem eventually_correctedOperator_geometric {w : ℂ} (hw : 0 < w.re) :
    ∀ᶠ N in atTop, GeomDecay (MayerPole.operatorMatrix (correctedOperator w hw N))
      (remainderConstant w + 5*‖w‖*powerBound (w+1)) rate := by
  filter_upwards [eventually_norm_shearResidual_le hw] with N hN
  have hB : 0 ≤ 5*‖w‖*powerBound (w+1) := by
    have := (powerBound_pos (w+1)).le
    positivity
  have hp : ((N+1 : ℕ) : ℝ)^(-w.re) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast Nat.succ_pos N) (neg_nonpos.mpr hw.le)
  have hv : ‖shearResidual w hw N‖ ≤ 5*‖w‖*powerBound (w+1) :=
    hN.trans ((mul_le_mul_of_nonneg_left hp hB).trans_eq (mul_one _))
  refine ⟨add_nonneg (remainderConstant_nonneg w) hB, rate_bounds.1, rate_bounds.2, fun i j => ?_⟩
  have hentry : MayerPole.operatorMatrix (correctedOperator w hw N) i j =
      MayerPole.operatorMatrix (finiteRemainder w N) i j +
        functional i (shearResidual w hw N)*evaluationWeight j := by
    change functional i (((balanceRadius : ℂ)^j)⁻¹ •
      ((finiteRemainder w N + (evaluation zeroPoint).smulRight (shearResidual w hw N))
        (monomial j))) = _
    rw [_root_.add_apply, smul_add, map_add]
    exact congrArg (fun z => MayerPole.operatorMatrix (finiteRemainder w N) i j+z)
      (evaluation_rankOne_matrix (shearResidual w hw N) i j)
  rw [hentry]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul]
  have hfun := ((functional i).le_opNorm _).trans
    (mul_le_mul (norm_functional_le i) hv (norm_nonneg _) (pow_nonneg rate_bounds.1 _))
  have hproj := mul_le_mul hfun (evaluationWeight_bound j) (norm_nonneg _)
    (mul_nonneg (pow_nonneg rate_bounds.1 _) hB)
  exact (add_le_add ((finiteRemainder_geometric hw N).bound i j) hproj).trans_eq (by ring)

/-- Operator-norm convergence gives entrywise convergence of the actual Cauchy matrices. -/
theorem operatorMatrix_tendsto
    {T : ℕ → DiscSpace →L[ℂ] DiscSpace} {R : DiscSpace →L[ℂ] DiscSpace}
    (hT : Tendsto T atTop (𝓝 R)) (i j : ℕ) :
    Tendsto (fun N => MayerPole.operatorMatrix (T N) i j) atTop (𝓝 (MayerPole.operatorMatrix R i j)) := by
  have ht := (ContinuousLinearMap.apply ℂ DiscSpace (monomial j)).continuous.continuousAt.tendsto.comp hT
  have hs := ht.const_smul (((balanceRadius : ℂ)^j)⁻¹)
  exact (functional i).continuous.continuousAt.tendsto.comp hs

/-- Actual Cauchy determinants of the sheared finite operators converge. -/
theorem correctedDeterminant_tendsto {w : ℂ} (hw : 0 < w.re) :
    Tendsto (fun N => fdet (MayerPole.operatorMatrix (correctedOperator w hw N)) (-1))
      atTop (𝓝 (MayerPole.regularPart w (-1))) := by
  have ht := tendsto_fdet_of_uniform_geometric (eventually_correctedOperator_geometric hw)
    (operatorMatrix_tendsto (correctedOperator_tendsto hw)) (-1)
  have he : fdet (MayerPole.operatorMatrix (remainder w)) (-1) = MayerPole.regularPart w (-1) := by
    change fdet (MayerPole.operatorMatrix (remainder w)) (-1) =
      fdet (MayerPole.perturbedMatrix w 0) (-1)
    congr 1
    funext i j
    change MayerPole.remainderMatrix w i j =
      MayerPole.remainderMatrix w i j + 0*MayerPole.projectionMatrix i j
    rw [zero_mul, add_zero]
  rwa [he] at ht


/-- Cauchy matrix of the genuine finite-branch operator. -/
def rawMatrix (w : ℂ) (hw : 0 < w.re) (N : ℕ) : ℕ → ℕ → ℂ :=
  MayerPole.operatorMatrix (cutoff w hw N)

/-- The genuine finite Cauchy matrix retains exactly its finite scalar constant mode. -/
theorem rawMatrix_decomposition {w : ℂ} (hw : 0 < w.re) (N i j : ℕ) :
    rawMatrix w hw N i j = MayerPole.operatorMatrix (finiteRemainder w N) i j +
      scalarPart w N * MayerPole.projectionMatrix i j := by
  unfold rawMatrix
  rw [cutoff_eq hw]
  simp only [MayerPole.operatorMatrix, MayerPole.projectionMatrix, _root_.add_apply,
    _root_.smul_apply, smul_add, map_add, map_smul, smul_eq_mul]
  ring

/-- Every finite branch sum has its own geometric nuclear Cauchy bound. -/
theorem rawMatrix_geometric {w : ℂ} (hw : 0 < w.re) (N : ℕ) :
    GeomDecay (rawMatrix w hw N) (remainderConstant w+‖scalarPart w N‖) rate := by
  refine ⟨add_nonneg (remainderConstant_nonneg w) (norm_nonneg _),
    rate_bounds.1, rate_bounds.2, fun i j => ?_⟩
  rw [rawMatrix_decomposition hw]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul]
  have hP : ‖MayerPole.projectionMatrix i j‖ ≤ rate^i*rate^j := by
    simpa only [one_mul] using MayerPole.geomDecay_projection.bound i j
  exact (add_le_add ((finiteRemainder_geometric hw N).bound i j)
    (mul_le_mul_of_nonneg_left hP (norm_nonneg _))).trans_eq (by ring)

/-- The Hilbert realization of the genuine finite branch cutoff. -/
def rawHilbertOperator (w : ℂ) (hw : 0 < w.re) (N : ℕ) :
    SequenceSpace →L[ℂ] SequenceSpace :=
  HilbertSchmidt.toOperator (geometric_isHS (rawMatrix_geometric hw N))

private theorem branch_monomial_norm {w : ℂ} (hw : 0 < w.re)
    {n : ℕ} (hn : 1 ≤ n) (j : ℕ) :
    ‖branch w hw n hn (monomial j)‖ ≤ powerBound w*(n : ℝ)^(-w.re) := by
  have hB : 0 ≤ powerBound w*(n : ℝ)^(-w.re) :=
    mul_nonneg (powerBound_pos w).le (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  change ‖(branch w hw n hn (monomial j)).1‖ ≤ _
  apply (ContinuousMap.norm_le _ hB).mpr
  intro z
  rw [branch_apply]
  have hu := inverse_branch_inner hn z.property
  have hu' : ((n : ℂ)+z.1)⁻¹ ∈ outer :=
    closedBall_subset_closedBall (by norm_num : (1 : ℝ) ≤ 3/2) hu
  rw [plane_eq (monomial j) ⟨_, hu'⟩]
  change ‖((n : ℂ)+z.1)^(-w) * (((n : ℂ)+z.1)⁻¹-1)^j‖ ≤ _
  rw [norm_mul, norm_pow]
  have hr : ‖((n : ℂ)+z.1)⁻¹-1‖ ≤ 1 := by
    simpa only [mem_closedBall, dist_eq_norm] using hu
  exact (mul_le_mul_of_nonneg_left (pow_le_one₀ (norm_nonneg _) hr) (norm_nonneg _)).trans
    (by simpa only [mul_one] using norm_branch_weight_le hw hn z.property)

/-- Each actual branch is the sum of its Cauchy rank-one expansion. -/
theorem hasSum_branch_expansion {w : ℂ} (hw : 0 < w.re)
    {n : ℕ} (hn : 1 ≤ n) (f : DiscSpace) :
    HasSum (fun j => MayerTrace.traceCoefficient j f • branch w hw n hn (monomial j))
      (branch w hw n hn f) := by
  have hB : 0 ≤ powerBound w*(n : ℝ)^(-w.re) :=
    mul_nonneg (powerBound_pos w).le (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hnorm : Summable (fun j =>
      ‖MayerTrace.traceCoefficient j f • branch w hw n hn (monomial j)‖) := by
    have hgeo := (summable_geometric_of_lt_one
      (inv_nonneg.mpr coefficientRadius_pos.le) (by norm_num [coefficientRadius])).mul_right ‖f‖
    apply (hgeo.mul_right (powerBound w*(n : ℝ)^(-w.re))).of_nonneg_of_le (fun _ => norm_nonneg _)
    intro j
    rw [norm_smul]
    have hc := ((MayerTrace.traceCoefficient j).le_opNorm f).trans
      (mul_le_mul_of_nonneg_right
        (norm_coefficient_le coefficientRadius coefficientRadius_pos radii.2.2 j) (norm_nonneg _))
    exact mul_le_mul hc (branch_monomial_norm hw hn j) (norm_nonneg _)
      (mul_nonneg (pow_nonneg (inv_nonneg.mpr coefficientRadius_pos.le) _) (norm_nonneg _))
  have hs := hnorm.of_norm.hasSum
  have he : (∑' j, MayerTrace.traceCoefficient j f • branch w hw n hn (monomial j)) =
      branch w hw n hn f := by
    apply Subtype.ext
    ext z
    have hz := inverse_branch_inner hn z.property
    have hz' : ((n : ℂ)+z.1)⁻¹ ∈ outer :=
      closedBall_subset_closedBall (by norm_num : (1 : ℝ) ≤ 3/2) hz
    have hv := (evaluation z).hasSum hs
    have hd : DifferentiableOn ℂ (plane f) (closedBall 1 coefficientRadius) :=
      (differentiableOn_plane f).mono (closedBall_subset_ball radii.2.2)
    have ht := DiscCoefficients.hasSum_coeff coefficientRadius_pos zero_lt_one hd
      (closedBall_subset_ball (by norm_num [coefficientRadius] : (1 : ℝ) < coefficientRadius) hz)
    simp only [DiscCoefficients.coeff, Complex.ofReal_one, one_pow, one_mul, div_one] at ht
    have ht' := ht.mul_left (((n : ℂ)+z.1)^(-w))
    have hterms : (fun j => evaluation z
        (MayerTrace.traceCoefficient j f • branch w hw n hn (monomial j))) =
        fun j => ((n : ℂ)+z.1)^(-w) *
          (DiscCoefficients.cauchyCoeff 1 coefficientRadius j (plane f) *
            (((n : ℂ)+z.1)⁻¹-1)^j) := by
      funext j
      rw [map_smul, smul_eq_mul]
      change MayerTrace.traceCoefficient j f * (branch w hw n hn (monomial j)).1 z = _
      rw [branch_apply, plane_eq (monomial j) ⟨_, hz'⟩]
      change DiscCoefficients.cauchyCoeff 1 coefficientRadius j (plane f) *
        (((n : ℂ)+z.1)^(-w)*(((n : ℂ)+z.1)⁻¹-1)^j) = _
      ring
    rw [hterms] at hv
    have hv' := hv.unique ht'
    change (∑' j, MayerTrace.traceCoefficient j f • branch w hw n hn (monomial j)).1 z = _ at hv'
    rw [branch_apply]
    exact hv'
  rwa [he] at hs

/-- The finite branch cutoff has the same actual Cauchy expansion. -/
theorem hasSum_cutoff_expansion {w : ℂ} (hw : 0 < w.re) (N : ℕ) (f : DiscSpace) :
    HasSum (fun j => MayerTrace.traceCoefficient j f • cutoff w hw N (monomial j))
      (cutoff w hw N f) := by
  induction N with
  | zero => simp only [cutoff, Finset.range_zero, Finset.sum_empty, _root_.zero_apply, smul_zero]; exact hasSum_zero
  | succ N ih =>
    have he : cutoff w hw (N+1) = cutoff w hw N + branch w hw (N+1) (Nat.succ_pos N) := by
      exact Finset.sum_range_succ _ N
    simp only [he, _root_.add_apply, smul_add]
    exact ih.add (hasSum_branch_expansion hw (Nat.succ_pos N) f)

/-- The matrix realization intertwines the literal finite branch operator on every source function. -/
theorem rawHilbertOperator_analysis {w : ℂ} (hw : 0 < w.re) (N : ℕ) (f : DiscSpace) :
    rawHilbertOperator w hw N (analysisMap f) = analysisMap (cutoff w hw N f) := by
  apply lp.ext
  funext i
  rw [rawHilbertOperator, HilbertSchmidt.toOperator_apply, analysis_coordinate]
  have hs := (functional i).hasSum (hasSum_cutoff_expansion hw N f)
  have he : (fun j => rawMatrix w hw N i j * (analysisMap f : ℕ → ℂ) j) =
      fun j => functional i (MayerTrace.traceCoefficient j f • cutoff w hw N (monomial j)) := by
    funext j
    rw [analysis_coordinate]
    change functional i (((balanceRadius : ℂ)^j)⁻¹ • cutoff w hw N (monomial j)) *
      ((balanceRadius : ℂ)^j * MayerTrace.traceCoefficient j f) = _
    rw [map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    have hne : (balanceRadius : ℂ)^j ≠ 0 :=
      pow_ne_zero _ (Complex.ofReal_ne_zero.mpr balanceRadius_pos.ne')
    field_simp
  rw [he]
  exact hs.tsum_eq


/-- Source vector of the finite rank-one update induced by the successor response. -/
def correctionVector (w : ℂ) (hw : 0 < w.re) (N : ℕ) : DiscSpace :=
  (-shearCoefficient w N) • (constant 1-tailWeight w hw N)

private theorem correctionVector_zero {w : ℂ} (hw : 0 < w.re) (N : ℕ)
    (hN : 1-terminalScalar w N ≠ 0) :
    (correctionVector w hw N).1 zeroPoint = -scalarPart w N := by
  change -shearCoefficient w N * (1-(tailWeight w hw N).1 zeroPoint) = _
  rw [tailWeight_apply]
  change -shearCoefficient w N * (1-(((N+1 : ℕ) : ℂ)+0)^(-w)) = _
  rw [add_zero]
  change -shearCoefficient w N * (1-terminalScalar w N) = _
  rw [shearCoefficient]
  field_simp [hN]

/-- The finite correction is exactly the constant-free terminal residual. -/
theorem correctedOperator_eq_update {w : ℂ} (hw : 0 < w.re) (N : ℕ)
    (hN : 1-terminalScalar w N ≠ 0) :
    correctedOperator w hw N = cutoff w hw N +
      (evaluation zeroPoint).smulRight (correctionVector w hw N) := by
  have hb : shearCoefficient w N*(1-terminalScalar w N) = scalarPart w N := by
    rw [shearCoefficient]
    exact div_mul_cancel₀ _ hN
  apply ContinuousLinearMap.ext
  intro f
  apply Subtype.ext
  ext z
  rw [cutoff_eq hw]
  change (finiteRemainder w N f).1 z + f.1 zeroPoint *
      (shearCoefficient w N * ((tailWeight w hw N).1 z-terminalScalar w N)) =
    (finiteRemainder w N f).1 z+scalarPart w N*f.1 zeroPoint +
      f.1 zeroPoint*(-shearCoefficient w N*(1-(tailWeight w hw N).1 z))
  rw [← hb]
  ring

private theorem operatorMatrix_add (T U : DiscSpace →L[ℂ] DiscSpace) (i j : ℕ) :
    MayerPole.operatorMatrix (T+U) i j =
      MayerPole.operatorMatrix T i j + MayerPole.operatorMatrix U i j := by
  change functional i (((balanceRadius : ℂ)^j)⁻¹ • ((T+U) (monomial j))) = _
  rw [_root_.add_apply, smul_add, map_add]
  rfl

private theorem evaluation_rankOne_geometric (v : DiscSpace) :
    GeomDecay (MayerPole.operatorMatrix ((evaluation zeroPoint).smulRight v)) ‖v‖ rate := by
  refine ⟨norm_nonneg _, rate_bounds.1, rate_bounds.2, fun i j => ?_⟩
  rw [evaluation_rankOne_matrix, norm_mul]
  have hi := ((functional i).le_opNorm v).trans
    (mul_le_mul_of_nonneg_right (norm_functional_le i) (norm_nonneg v))
  exact (mul_le_mul hi (evaluationWeight_bound j) (norm_nonneg _)
    (mul_nonneg (pow_nonneg rate_bounds.1 _) (norm_nonneg v))).trans_eq (by ring)

private theorem evaluation_rankOne_diagonal (v : DiscSpace) :
    (∑' i, MayerPole.operatorMatrix ((evaluation zeroPoint).smulRight v) i i) = v.1 zeroPoint := by
  have hs := coefficientEvaluation_hasSum (analysisMap v)
  have he : (fun i => evaluationWeight i*(analysisMap v : ℕ → ℂ) i) =
      fun i => MayerPole.operatorMatrix ((evaluation zeroPoint).smulRight v) i i := by
    funext i
    rw [evaluation_rankOne_matrix, analysis_coordinate, mul_comm]
  rw [he] at hs
  exact hs.tsum_eq.trans (coefficientEvaluation_analysis v)

private theorem matrixOf_rawHilbertOperator {w : ℂ} (hw : 0 < w.re) (N : ℕ) :
    HilbertSchmidt.matrixOf (rawHilbertOperator w hw N) =
      fun p => rawMatrix w hw N p.1 p.2 :=
  HilbertSchmidt.matrixOf_toOperator _

private theorem matrixOf_evaluation_rankOne (v : DiscSpace) :
    HilbertSchmidt.matrixOf (coefficientEvaluation.smulRight (analysisMap v)) =
      fun p => MayerPole.operatorMatrix ((evaluation zeroPoint).smulRight v) p.1 p.2 := by
  funext p
  change (coefficientEvaluation.smulRight (analysisMap v) (lp.single 2 p.2 1) : ℕ → ℂ) p.1 = _
  rw [ContinuousLinearMap.smulRight_apply, coefficientEvaluation_single]
  change evaluationWeight p.2 * (analysisMap v : ℕ → ℂ) p.1 = _
  rw [analysis_coordinate, evaluation_rankOne_matrix, mul_comm]

private theorem fdet_eq_det2_of_matrix {A : SequenceSpace →L[ℂ] SequenceSpace}
    {M : ℕ → ℕ → ℂ} {C : ℝ} (hM : GeomDecay M C rate)
    (hA : HilbertSchmidt.matrixOf A = fun p => M p.1 p.2) :
    fdet M (-1) = _root_.RHTower.det2Op (HilbertSchmidt.lpBasis ℕ) A *
      Complex.exp (∑' i, M i i) := by
  rw [_root_.RHTower.det2Op, coordMatrix_canonical, hA]
  exact fdet_negative_one_eq_entireDet2 hM

/-- The finite successor response supplies the exact Hilbert rank-one update. -/
theorem det2_raw_update {w : ℂ} (hw : 0 < w.re) (N : ℕ)
    (hN : 1-terminalScalar w N ≠ 0) :
    _root_.RHTower.det2Op (HilbertSchmidt.lpBasis ℕ)
      (rawHilbertOperator w hw N + coefficientEvaluation.smulRight
        (analysisMap (correctionVector w hw N))) =
    _root_.RHTower.det2Op (HilbertSchmidt.lpBasis ℕ) (rawHilbertOperator w hw N) *
      Complex.exp (scalarPart w N) := by
  let y : SequenceSpace := (InnerProductSpace.toDual ℂ SequenceSpace).symm coefficientEvaluation
  have hy (x : SequenceSpace) : inner ℂ y x = coefficientEvaluation x :=
    InnerProductSpace.toDual_symm_apply
  have hu : (-shearCoefficient w N) • analysisMap (response w) +
      rawHilbertOperator w hw N ((-shearCoefficient w N) • analysisMap (response w)) =
      analysisMap (correctionVector w hw N) := by
    rw [map_smul, rawHilbertOperator_analysis hw, ← smul_add, ← map_add, cutoff_response hw]
    rw [correctionVector, map_smul]
  have he : InnerProductSpace.rankOne ℂ (analysisMap (correctionVector w hw N)) y =
      coefficientEvaluation.smulRight (analysisMap (correctionVector w hw N)) := by
    apply ContinuousLinearMap.ext
    intro x
    rw [InnerProductSpace.rankOne_apply, hy, ContinuousLinearMap.smulRight_apply]
  have h := det2Op_rankOne_update (HilbertSchmidt.lpBasis ℕ)
    (HilbertSchmidt.isHilbertSchmidt_toOperator (geometric_isHS (rawMatrix_geometric hw N)))
    ((-shearCoefficient w N) • analysisMap (response w))
    (analysisMap (correctionVector w hw N)) y hu
  rw [he, hy, hy, map_smul, coefficientEvaluation_response, smul_zero,
    add_zero, mul_one, coefficientEvaluation_analysis, correctionVector_zero hw N hN,
    neg_neg] at h
  exact h

/-- The genuine finite-branch determinant at the negative unit. -/
def rawDeterminant (w : ℂ) (hw : 0 < w.re) (N : ℕ) : ℂ := fdet (rawMatrix w hw N) (-1)

/-- The shear's trace exponential cancels exactly, before passing to any limit. -/
theorem rawDeterminant_eq_corrected {w : ℂ} (hw : 0 < w.re) (N : ℕ)
    (hN : 1-terminalScalar w N ≠ 0) {C : ℝ}
    (hC : GeomDecay (MayerPole.operatorMatrix (correctedOperator w hw N)) C rate) :
    rawDeterminant w hw N = fdet (MayerPole.operatorMatrix (correctedOperator w hw N)) (-1) := by
  have hmatrix : HilbertSchmidt.matrixOf
      (rawHilbertOperator w hw N + coefficientEvaluation.smulRight
        (analysisMap (correctionVector w hw N))) =
      fun p => MayerPole.operatorMatrix (correctedOperator w hw N) p.1 p.2 := by
    funext p
    change HilbertSchmidt.matrixOf (rawHilbertOperator w hw N) p +
      HilbertSchmidt.matrixOf (coefficientEvaluation.smulRight
        (analysisMap (correctionVector w hw N))) p = _
    rw [matrixOf_rawHilbertOperator, matrixOf_evaluation_rankOne, correctedOperator_eq_update hw N hN,
      operatorMatrix_add]
    rfl
  have hdiag : (∑' i, MayerPole.operatorMatrix (correctedOperator w hw N) i i) =
      (∑' i, rawMatrix w hw N i i)-scalarPart w N := by
    have he : (fun i => MayerPole.operatorMatrix (correctedOperator w hw N) i i) =
        fun i => rawMatrix w hw N i i +
          MayerPole.operatorMatrix ((evaluation zeroPoint).smulRight (correctionVector w hw N)) i i := by
      funext i
      rw [correctedOperator_eq_update hw N hN, operatorMatrix_add]
      rfl
    rw [he, (geometric_diagonal_summable (rawMatrix_geometric hw N)).tsum_add
      (geometric_diagonal_summable (evaluation_rankOne_geometric (correctionVector w hw N))),
      evaluation_rankOne_diagonal, correctionVector_zero hw N hN, sub_eq_add_neg]
  rw [rawDeterminant, fdet_eq_det2_of_matrix (rawMatrix_geometric hw N)
    (matrixOf_rawHilbertOperator hw N), fdet_eq_det2_of_matrix hC hmatrix,
    det2_raw_update hw N hN, hdiag, mul_assoc, ← Complex.exp_add]
  congr 2
  ring

/-- Raw finite-branch determinants converge even where the corresponding operators diverge. -/
theorem rawDeterminant_tendsto {w : ℂ} (hw : 0 < w.re) :
    Tendsto (rawDeterminant w hw) atTop (𝓝 (sourceDeterminant w (-1))) := by
  have he : (fun N => fdet (MayerPole.operatorMatrix (correctedOperator w hw N)) (-1)) =ᶠ[atTop]
      rawDeterminant w hw := by
    filter_upwards [eventually_shearCoefficient_bound hw, eventually_correctedOperator_geometric hw]
      with N hN hC
    exact (rawDeterminant_eq_corrected hw N hN.1 hC).symm
  rw [sourceDeterminant_negative_one hw]
  exact (correctedDeterminant_tendsto hw).congr' he


/-- The finite branch sum has a degree-independent bound on centered monomials. -/
theorem cutoff_monomial_bound {w : ℂ} (hw : 0 < w.re) (N j : ℕ) :
    ‖cutoff w hw N (monomial j)‖ ≤
      ∑ n ∈ Finset.range N, powerBound w*((n+1 : ℕ) : ℝ)^(-w.re) := by
  rw [cutoff, _root_.sum_apply]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ =>
    branch_monomial_norm hw (Nat.succ_pos n) j)

/-- The actual finite branch operator is the operator-norm sum of its Cauchy rank-one terms. -/
theorem hasSum_cutoff_rankTerms {w : ℂ} (hw : 0 < w.re) (N : ℕ) :
    HasSum (fun j => (MayerTrace.traceCoefficient j).smulRight (cutoff w hw N (monomial j)))
      (cutoff w hw N) := by
  have hnorm : Summable (fun j =>
      ‖(MayerTrace.traceCoefficient j).smulRight (cutoff w hw N (monomial j))‖) := by
    have hgeo := (summable_geometric_of_lt_one
      (inv_nonneg.mpr coefficientRadius_pos.le) (by norm_num [coefficientRadius])).mul_right
        (∑ n ∈ Finset.range N, powerBound w*((n+1 : ℕ) : ℝ)^(-w.re))
    apply hgeo.of_nonneg_of_le (fun _ => norm_nonneg _)
    intro j
    rw [ContinuousLinearMap.norm_smulRight_apply]
    exact mul_le_mul (norm_coefficient_le coefficientRadius coefficientRadius_pos radii.2.2 j)
      (cutoff_monomial_bound hw N j) (norm_nonneg _)
      (pow_nonneg (inv_nonneg.mpr coefficientRadius_pos.le) _)
  have hs := hnorm.of_norm.hasSum
  have he : (∑' j, (MayerTrace.traceCoefficient j).smulRight (cutoff w hw N (monomial j))) =
      cutoff w hw N := by
    apply ContinuousLinearMap.ext
    intro f
    have hv := (ContinuousLinearMap.apply ℂ DiscSpace f).hasSum hs
    exact hv.unique (hasSum_cutoff_expansion hw N f)
  rwa [he] at hs

/-- At actual zeta parameters, raw determinants converge although raw operator norms diverge. -/
theorem nontrivialZero_rawDeterminant_and_operator
    (ρ : RiemannGaussian.NontrivialZetaZero) :
    Tendsto (rawDeterminant ρ.1 ρ.zero_lt_re) atTop (𝓝 (sourceDeterminant ρ.1 (-1))) ∧
      Tendsto (fun N : ℕ => ‖cutoff ρ.1 ρ.zero_lt_re N‖) atTop atTop :=
  ⟨rawDeterminant_tendsto ρ.zero_lt_re, tendsto_nontrivialZero_cutoff_norm_atTop ρ⟩

#print axioms cutoff_response
#print axioms finiteRemainder_geometric
#print axioms shearResidual_tendsto
#print axioms correctedDeterminant_tendsto
#print axioms hasSum_branch_expansion
#print axioms hasSum_cutoff_expansion
#print axioms rawHilbertOperator_analysis
#print axioms correctedOperator_eq_update
#print axioms det2_raw_update
#print axioms rawDeterminant_eq_corrected
#print axioms rawDeterminant_tendsto
#print axioms hasSum_cutoff_rankTerms
#print axioms nontrivialZero_rawDeterminant_and_operator

end GaloisForLFunctions.RenormalizedIntersectionTheory.MayerRaw
