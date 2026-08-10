import GaloisForLFunctions.HTGeometry.ZetaTailBound
import GaloisForLFunctions.HTGeometry.AbelianZetaGas.DilationDivisor

/-!
# The depth tail of the grand response converges normally

For `Re(σ+u) > 0` the depth-`j` argument `j(σ+u)+v` has real part `j·a + Re v` with `a > 0`, so it
leaves every half-plane: beyond a finite depth it lies in `Re ≥ 2`, where the zeta tail bound
`‖ζ(s) − 1‖ ≤ 4·2^{−Re s}` is geometric in the depth.  The depth factors are therefore multipliable,
and the tail beyond that depth is zero-free.

This is the convergence half of Theorem 6.1's continuation statement.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Topology

noncomputable section

/-- The depth-`j` argument of the grand response. -/
def depthArg (σ : ℝ) (v : ℂ) (j : ℕ) (u : ℂ) : ℂ := (j : ℂ) * ((σ : ℝ) + u) + v

theorem re_depthArg (σ : ℝ) (v : ℂ) (j : ℕ) (u : ℂ) :
    (depthArg σ v j u).re = (j : ℝ) * (σ + u.re) + v.re := by
  simp [depthArg, Complex.add_re, Complex.mul_re]

/-- The depth threshold beyond which the argument lies in `Re ≥ 2`. -/
def depthThreshold (σ : ℝ) (v : ℂ) (u : ℂ) : ℕ := ⌈(2 - v.re) / (σ + u.re)⌉₊

theorem two_le_re_depthArg (σ : ℝ) (v : ℂ) (u : ℂ) (ha : 0 < σ + u.re) {j : ℕ}
    (hj : depthThreshold σ v u ≤ j) : 2 ≤ (depthArg σ v j u).re := by
  rw [re_depthArg]
  have hceil : (2 - v.re) / (σ + u.re) ≤ (j : ℝ) :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast hj)
  have := (div_le_iff₀ ha).mp hceil
  linarith

/-! ## The geometric majorant -/

theorem rpow_two_depthArg (σ : ℝ) (v : ℂ) (u : ℂ) (j : ℕ) :
    (2 : ℝ) ^ (-(depthArg σ v j u).re)
      = ((2 : ℝ) ^ (-(σ + u.re))) ^ j * (2 : ℝ) ^ (-v.re) := by
  rw [re_depthArg, neg_add, Real.rpow_add (by norm_num), ← Real.rpow_natCast
    ((2 : ℝ) ^ (-(σ + u.re))) j, ← Real.rpow_mul (by norm_num)]
  congr 2
  ring

theorem geomRatio_lt_one {a : ℝ} (ha : 0 < a) : (2 : ℝ) ^ (-a) < 1 := by
  rw [show (1 : ℝ) = (2 : ℝ) ^ (0 : ℝ) by norm_num]
  exact Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by linarith)

theorem geomRatio_nonneg (a : ℝ) : (0 : ℝ) ≤ (2 : ℝ) ^ (-a) :=
  Real.rpow_nonneg (by norm_num) _

/-- **The depth factors deviate from one geometrically.** -/
theorem summable_norm_zeta_depth_sub_one (σ : ℝ) (v : ℂ) (u : ℂ) (ha : 0 < σ + u.re) :
    Summable fun j : ℕ => ‖riemannZeta (depthArg σ v j u) - 1‖ := by
  have hmaj : Summable fun j : ℕ =>
      4 * (((2 : ℝ) ^ (-(σ + u.re))) ^ j * (2 : ℝ) ^ (-v.re)) := by
    refine Summable.mul_left 4 ?_
    exact (summable_geometric_of_lt_one (geomRatio_nonneg _) (geomRatio_lt_one ha)).mul_right _
  refine Summable.of_norm_bounded_eventually_nat hmaj ?_
  filter_upwards [eventually_ge_atTop (depthThreshold σ v u)] with j hj
  have hre := two_le_re_depthArg σ v u ha hj
  have hbound := norm_riemannZeta_sub_one_le_rpow hre
  rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), ← rpow_two_depthArg]
  exact hbound

/-- **The depth factors are multipliable.** -/
theorem multipliable_zeta_depth (σ : ℝ) (v : ℂ) (u : ℂ) (ha : 0 < σ + u.re) :
    Multipliable fun j : ℕ => riemannZeta (depthArg σ v j u) := by
  have hsum : Summable fun j : ℕ => ‖riemannZeta (depthArg σ v j u) - 1‖ :=
    summable_norm_zeta_depth_sub_one σ v u ha
  have hmul := Complex.multipliable_one_add_of_summable
    (f := fun j : ℕ => riemannZeta (depthArg σ v j u) - 1) hsum.of_norm
  refine hmul.congr fun j => ?_
  ring

/-- **The depth tail is zero-free.**  Beyond the threshold every factor lies in `Re ≥ 2`, where
`ζ` does not vanish, and the tail product is a convergent product of nonzero factors. -/
theorem tprod_zeta_depth_tail_ne_zero (σ : ℝ) (v : ℂ) (u : ℂ) (ha : 0 < σ + u.re) :
    (∏' j : ℕ, riemannZeta (depthArg σ v (j + depthThreshold σ v u) u)) ≠ 0 := by
  have hsum : Summable fun j : ℕ =>
      ‖riemannZeta (depthArg σ v (j + depthThreshold σ v u) u) - 1‖ := by
    have h := summable_norm_zeta_depth_sub_one σ v u ha
    exact (summable_nat_add_iff (depthThreshold σ v u)).mpr h
  have hval : (∏' j : ℕ, riemannZeta (depthArg σ v (j + depthThreshold σ v u) u))
      = ∏' j : ℕ, (1 + (riemannZeta (depthArg σ v (j + depthThreshold σ v u) u) - 1)) := by
    refine tprod_congr fun j => ?_
    ring
  rw [hval]
  refine tprod_one_add_ne_zero_of_summable ?_ hsum
  intro j
  have hre : 2 ≤ (depthArg σ v (j + depthThreshold σ v u) u).re :=
    two_le_re_depthArg σ v u ha (Nat.le_add_left _ _)
  have hne : riemannZeta (depthArg σ v (j + depthThreshold σ v u) u) ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re (by linarith)
  intro h0
  apply hne
  have : (1 : ℂ) + (riemannZeta (depthArg σ v (j + depthThreshold σ v u) u) - 1)
      = riemannZeta (depthArg σ v (j + depthThreshold σ v u) u) := by ring
  rw [this] at h0
  exact h0

/-! ## Uniform convergence and holomorphy of the tail -/

/-- The uniform depth threshold on the half-plane `a₀ ≤ σ + Re u`. -/
def depthTailThreshold (v : ℂ) (a₀ : ℝ) : ℕ := ⌈(2 - v.re) / a₀⌉₊

theorem two_le_re_depthArg_of_ge (σ : ℝ) (v : ℂ) {a₀ : ℝ} (ha₀ : 0 < a₀) {u : ℂ}
    (hu : a₀ ≤ σ + u.re) {j : ℕ} (hj : depthTailThreshold v a₀ ≤ j) :
    2 ≤ (depthArg σ v j u).re := by
  rw [re_depthArg]
  have hceil : (2 - v.re) / a₀ ≤ (j : ℝ) :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast hj)
  have hj0 : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
  have hmono : (j : ℝ) * a₀ ≤ (j : ℝ) * (σ + u.re) := mul_le_mul_of_nonneg_left hu hj0
  have := (div_le_iff₀ ha₀).mp hceil
  linarith

theorem norm_zeta_depthArg_sub_one_le (σ : ℝ) (v : ℂ) {a₀ : ℝ} (ha₀ : 0 < a₀) {u : ℂ}
    (hu : a₀ ≤ σ + u.re) {j : ℕ} (hj : depthTailThreshold v a₀ ≤ j) :
    ‖riemannZeta (depthArg σ v j u) - 1‖ ≤ 4 * (((2 : ℝ) ^ (-a₀)) ^ j * (2 : ℝ) ^ (-v.re)) := by
  have hre := two_le_re_depthArg_of_ge σ v ha₀ hu hj
  have hbound := norm_riemannZeta_sub_one_le_rpow hre
  have hj0 : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
  have hexp : -(depthArg σ v j u).re ≤ -((j : ℝ) * a₀ + v.re) := by
    rw [re_depthArg]
    have : (j : ℝ) * a₀ ≤ (j : ℝ) * (σ + u.re) := mul_le_mul_of_nonneg_left hu hj0
    linarith
  have hmono : (2 : ℝ) ^ (-(depthArg σ v j u).re) ≤ (2 : ℝ) ^ (-((j : ℝ) * a₀ + v.re)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
  have hsplit : (2 : ℝ) ^ (-((j : ℝ) * a₀ + v.re))
      = ((2 : ℝ) ^ (-a₀)) ^ j * (2 : ℝ) ^ (-v.re) := by
    rw [neg_add, Real.rpow_add (by norm_num), ← Real.rpow_natCast ((2 : ℝ) ^ (-a₀)) j,
      ← Real.rpow_mul (by norm_num)]
    congr 2
    ring
  calc ‖riemannZeta (depthArg σ v j u) - 1‖ ≤ 4 * (2 : ℝ) ^ (-(depthArg σ v j u).re) := hbound
    _ ≤ 4 * (2 : ℝ) ^ (-((j : ℝ) * a₀ + v.re)) := by linarith [hmono]
    _ = 4 * (((2 : ℝ) ^ (-a₀)) ^ j * (2 : ℝ) ^ (-v.re)) := by rw [hsplit]

theorem differentiableAt_zeta_depthArg (σ : ℝ) (v : ℂ) {a₀ : ℝ} (ha₀ : 0 < a₀) {u : ℂ}
    (hu : a₀ ≤ σ + u.re) {j : ℕ} (hj : depthTailThreshold v a₀ ≤ j) :
    DifferentiableAt ℂ (fun w : ℂ => riemannZeta (depthArg σ v j w)) u := by
  have hre := two_le_re_depthArg_of_ge σ v ha₀ hu hj
  have hne : depthArg σ v j u ≠ 1 := by
    intro h
    rw [h] at hre
    simp at hre
  have haff : DifferentiableAt ℂ (fun w : ℂ => depthArg σ v j w) u := by
    show DifferentiableAt ℂ (fun w : ℂ => (j : ℂ) * ((σ : ℝ) + w) + v) u
    exact (differentiableAt_const _ |>.mul ((differentiableAt_const _).add differentiableAt_id)).add
      (differentiableAt_const _)
  exact (differentiableAt_riemannZeta hne).comp u haff

/-- **The tail converges uniformly on every compact of the half-plane.** -/
theorem hasProdUniformlyOn_zeta_depthTail (σ : ℝ) (v : ℂ) {a₀ : ℝ} (ha₀ : 0 < a₀)
    {J : ℕ} (hJthr : depthTailThreshold v a₀ ≤ J)
    {K : Set ℂ} (hKsub : K ⊆ {u : ℂ | a₀ ≤ σ + u.re}) (hK : IsCompact K) :
    HasProdUniformlyOn
      (fun j : ℕ => fun u : ℂ => riemannZeta (depthArg σ v (j + J) u))
      (fun u : ℂ => ∏' j : ℕ, riemannZeta (depthArg σ v (j + J) u)) K := by
  have hmaj : Summable fun j : ℕ =>
      4 * (((2 : ℝ) ^ (-a₀)) ^ (j + J) * (2 : ℝ) ^ (-v.re)) := by
    refine Summable.mul_left 4 ?_
    refine Summable.mul_right _ ?_
    exact ((summable_geometric_of_lt_one (geomRatio_nonneg _)
      (geomRatio_lt_one ha₀)).comp_injective (add_left_injective J))
  have hbound : ∀ᶠ j : ℕ in Filter.cofinite, ∀ u ∈ K,
      ‖riemannZeta (depthArg σ v (j + J) u) - 1‖
        ≤ 4 * (((2 : ℝ) ^ (-a₀)) ^ (j + J) * (2 : ℝ) ^ (-v.re)) := by
    filter_upwards with j
    intro u hu
    exact norm_zeta_depthArg_sub_one_le σ v ha₀ (hKsub hu)
      (le_trans hJthr (Nat.le_add_left J j))
  have hcont : ∀ j : ℕ,
      ContinuousOn (fun u : ℂ => riemannZeta (depthArg σ v (j + J) u) - 1) K := by
    intro j
    refine ContinuousOn.sub ?_ continuousOn_const
    intro u hu
    exact ((differentiableAt_zeta_depthArg σ v ha₀ (hKsub hu)
      (le_trans hJthr (Nat.le_add_left J j))).continuousAt).continuousWithinAt
  have hmain := Summable.hasProdUniformlyOn_one_add hK hmaj hbound hcont
  have hfun : (fun (j : ℕ) (u : ℂ) => 1 + (riemannZeta (depthArg σ v (j + J) u) - 1))
      = fun (j : ℕ) (u : ℂ) => riemannZeta (depthArg σ v (j + J) u) := by
    funext j u
    ring
  have hval : (fun u : ℂ => ∏' j : ℕ, (1 + (riemannZeta (depthArg σ v (j + J) u) - 1)))
      = fun u : ℂ => ∏' j : ℕ, riemannZeta (depthArg σ v (j + J) u) := by
    funext u
    exact tprod_congr fun j => by ring
  rw [hfun, hval] at hmain
  exact hmain

/-- **The tail product is holomorphic on the half-plane.** -/
theorem differentiableOn_tprod_zeta_depthTail (σ : ℝ) (v : ℂ) {a₀ : ℝ} (ha₀ : 0 < a₀)
    {J : ℕ} (hJthr : depthTailThreshold v a₀ ≤ J) :
    DifferentiableOn ℂ
      (fun u : ℂ => ∏' j : ℕ, riemannZeta (depthArg σ v (j + J) u))
      {u : ℂ | a₀ < σ + u.re} := by
  have hopen : IsOpen {u : ℂ | a₀ < σ + u.re} := by
    have hcont : Continuous fun u : ℂ => σ + u.re := continuous_const.add Complex.continuous_re
    exact isOpen_lt continuous_const hcont
  have hprod : HasProdLocallyUniformlyOn
      (fun j : ℕ => fun u : ℂ => riemannZeta (depthArg σ v (j + J) u))
      (fun u : ℂ => ∏' j : ℕ, riemannZeta (depthArg σ v (j + J) u))
      {u : ℂ | a₀ < σ + u.re} := by
    refine hasProdLocallyUniformlyOn_of_forall_compact hopen ?_
    intro K hKsub hK
    refine hasProdUniformlyOn_zeta_depthTail σ v ha₀ hJthr (fun u hu => ?_) hK
    have hlt : a₀ < σ + u.re := hKsub hu
    exact le_of_lt hlt
  have ht := hasProdLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn.mp hprod
  have hd : ∀ᶠ S : Finset ℕ in Filter.atTop,
      DifferentiableOn ℂ (fun u : ℂ =>
        ∏ j ∈ S, riemannZeta (depthArg σ v (j + J) u))
        {u : ℂ | a₀ < σ + u.re} := by
    filter_upwards with S
    refine DifferentiableOn.fun_finsetProd fun j _ => ?_
    intro u hu
    exact ((differentiableAt_zeta_depthArg σ v ha₀ (le_of_lt hu)
      (le_trans hJthr (Nat.le_add_left J j))).differentiableWithinAt)
  exact ht.differentiableOn hd hopen

end

end GaloisForLFunctions.HTGeometry
