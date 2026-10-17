import GaloisForLFunctions.BiScaleUncertainty.MultiplicativeChainBesselAndOriginLeverage

/-!
# Pillar V: Multi-Node Clique Sphere Duality, Extremal Rays, and Clique-Rank Amplification

This module establishes **Layer II (Convex Duality & Clique Extremal Theory)** of
**Bi-Scale / Logarithmic-Grid Uncertainty Theory** (`GaloisForLFunctions.BiScaleUncertainty`).

Given a finite difference-orthogonal clique `{t_i}_{i ∈ s}` of a correlation kernel `h = autocorr f`
(meaning `h(t_i - t_j) = 0` for all distinct `i, j ∈ s`), Pillar II's multi-node Bessel inequality
(`autocorr_finset_bessel_sq_le`) confines the collar vector `u_i(y) = h(y - t_i)` to the
Euclidean ball `∑ i ∈ s, u_i(y)^2 ≤ h(0)^2` for every shift `y ∈ ℝ`.

Here we establish the exact convex-duality and extremal theory of this sphere constraint:
1. **Exact Quadratic Sphere Defect Identity (`clique_sphere_quadratic_defect_identity`):**
   Without any division, for any weights `w : ι → ℝ`, state `u : ι → ℝ`, and radius `R : ℝ` with
   `W₂ := √(∑ i ∈ s, w_i^2)`,
   `2 W₂ R ((∑ i ∈ s, w_i (R - u_i)) - (∑ i ∈ s, w_i - W₂) R) = W₂^2 (R^2 - ∑ i ∈ s, u_i^2) + ∑ i ∈ s, (W₂ u_i - w_i R)^2`.
2. **Sharpness & Extremal Ray Saturation (`clique_sphere_extremizer_achieves_bound`):**
   The dual factor `cliqueSphereDualityFactor s w = (∑ i ∈ s, w_i) - √(∑ i ∈ s, w_i^2)` is the
   exact minimum over the Euclidean ball `∑ i ∈ s, u_i^2 ≤ R^2`, uniquely attained on the boundary
   sphere along the extremal ray `u_i* = (w_i / W₂) R`.
3. **Clique-Rank Amplification Law (`autocorr_clique_uniform_collar_sum_ge`):**
   For an `M`-element difference-orthogonal clique (`M = s.card`), the uniform collar sum satisfies
   `(M - √M) h(0) ≤ ∑ i ∈ s, (h(0) - h(y - t_i))` for all `y ∈ ℝ`, so the per-node collar defect
   fraction `1 - 1/√M` approaches `1` as the clique size `M → ∞`.
4. **Multi-Node Clique Collar Integral Lower Bound (`integral_autocorr_clique_collar_ge`):**
   Integrates the pointwise clique duality bound across any collar interval `[a, b]`.
-/

open MeasureTheory Set Filter Topology Finset
open scoped BigOperators
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole

namespace GaloisForLFunctions.BiScaleUncertainty

noncomputable section

variable {ι : Type*}

/-! ## §1. Clique Sphere Weight Norm, Duality Factor, and Exact Quadratic Defect Identity -/

/-- The Euclidean `ℓ²` norm `W₂ = √(∑ i ∈ s, w_i^2)` of a clique weight vector `w` on `s`. -/
def cliqueSphereWeightNorm (s : Finset ι) (w : ι → ℝ) : ℝ :=
  Real.sqrt (∑ i ∈ s, w i ^ 2)

/-- The **Clique Sphere Duality Factor** `(∑ i ∈ s, w_i) - √(∑ i ∈ s, w_i^2)`, which gives the
exact minimum of `∑ i ∈ s, w_i (1 - u_i)` over the unit Euclidean ball `∑ i ∈ s, u_i^2 ≤ 1`. -/
def cliqueSphereDualityFactor (s : Finset ι) (w : ι → ℝ) : ℝ :=
  (∑ i ∈ s, w i) - cliqueSphereWeightNorm s w

/-- The canonical extremal ray `u_i* = (w_i / √(∑ j ∈ s, w_j^2)) R` on the Euclidean sphere
`∑ i ∈ s, u_i^2 = R^2` aligned with the weight vector `w`. -/
def cliqueSphereExtremizer (s : Finset ι) (w : ι → ℝ) (R : ℝ) (i : ι) : ℝ :=
  w i / cliqueSphereWeightNorm s w * R

theorem cliqueSphereWeightNorm_nonneg (s : Finset ι) (w : ι → ℝ) :
    0 ≤ cliqueSphereWeightNorm s w :=
  Real.sqrt_nonneg _

theorem cliqueSphereWeightNorm_sq (s : Finset ι) (w : ι → ℝ) :
    cliqueSphereWeightNorm s w ^ 2 = ∑ i ∈ s, w i ^ 2 :=
  Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg (w i))

/-- Nonnegativity of `cliqueSphereDualityFactor s w` for nonnegative weights `w_i ≥ 0`:
since `√(∑ w_i^2) ≤ ∑ w_i`, the duality factor is always nonnegative. -/
theorem cliqueSphereDualityFactor_nonneg (s : Finset ι) (w : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) :
    0 ≤ cliqueSphereDualityFactor s w := by
  unfold cliqueSphereDualityFactor cliqueSphereWeightNorm
  have hsum_nonneg : 0 ≤ ∑ i ∈ s, w i := Finset.sum_nonneg hw
  have hsq_le : (∑ i ∈ s, w i ^ 2) ≤ (∑ i ∈ s, w i) ^ 2 :=
    sum_sq_le_sq_sum_of_nonneg hw
  have hsqrt : Real.sqrt (∑ i ∈ s, w i ^ 2) ≤ ∑ i ∈ s, w i := by
    rw [← Real.sqrt_sq hsum_nonneg]
    exact Real.sqrt_le_sqrt hsq_le
  linarith

/-- **Exact Algebraic Simplification of the Clique Sphere Defect:**
`(∑ i ∈ s, w_i (R - u_i)) - cliqueSphereDualityFactor s w * R = W₂ R - ∑ i ∈ s, w_i u_i`. -/
theorem clique_sphere_defect_eq (s : Finset ι) (w u : ι → ℝ) (R : ℝ) :
    (∑ i ∈ s, w i * (R - u i)) - cliqueSphereDualityFactor s w * R =
      cliqueSphereWeightNorm s w * R - ∑ i ∈ s, w i * u i := by
  unfold cliqueSphereDualityFactor
  have h1 : (∑ i ∈ s, w i * (R - u i)) = (∑ i ∈ s, w i) * R - ∑ i ∈ s, w i * u i := by
    rw [Finset.sum_mul]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => by ring
  linarith

/-- **The Exact Quadratic Sphere Defect Identity:**
For any finite index set `s`, weights `w : ι → ℝ`, vector `u : ι → ℝ`, and radius `R : ℝ`,
with `W₂ = cliqueSphereWeightNorm s w`:
`2 W₂ R ((∑ i ∈ s, w_i (R - u_i)) - cliqueSphereDualityFactor s w * R) = W₂^2 (R^2 - ∑ i ∈ s, u_i^2) + ∑ i ∈ s, (W₂ u_i - w_i R)^2`.

This division-free identity decomposes the gap above the dual sphere bound into two manifestly
nonnegative squares: the radial Bessel slack `R^2 - ∑ u_i^2` and the angular alignment defect
`∑ (W₂ u_i - w_i R)^2`. -/
theorem clique_sphere_quadratic_defect_identity (s : Finset ι) (w u : ι → ℝ) (R : ℝ) :
    2 * cliqueSphereWeightNorm s w * R *
        ((∑ i ∈ s, w i * (R - u i)) - cliqueSphereDualityFactor s w * R) =
      cliqueSphereWeightNorm s w ^ 2 * (R ^ 2 - ∑ i ∈ s, u i ^ 2) +
        ∑ i ∈ s, (cliqueSphereWeightNorm s w * u i - w i * R) ^ 2 := by
  rw [clique_sphere_defect_eq]
  set W₂ := cliqueSphereWeightNorm s w
  have hW₂_sq : ∑ i ∈ s, w i ^ 2 = W₂ ^ 2 := (cliqueSphereWeightNorm_sq s w).symm
  have hexp :
      (∑ i ∈ s, (W₂ * u i - w i * R) ^ 2) =
        W₂ ^ 2 * (∑ i ∈ s, u i ^ 2) - 2 * W₂ * R * (∑ i ∈ s, w i * u i) +
          (∑ i ∈ s, w i ^ 2) * R ^ 2 := by
    calc
      (∑ i ∈ s, (W₂ * u i - w i * R) ^ 2)
          = ∑ i ∈ s, ((W₂ ^ 2 * u i ^ 2 - 2 * W₂ * R * (w i * u i)) + w i ^ 2 * R ^ 2) := by
        refine Finset.sum_congr rfl fun i _ => by ring
      _ = (∑ i ∈ s, (W₂ ^ 2 * u i ^ 2 - 2 * W₂ * R * (w i * u i))) +
            ∑ i ∈ s, w i ^ 2 * R ^ 2 := Finset.sum_add_distrib
      _ = (∑ i ∈ s, W₂ ^ 2 * u i ^ 2) - (∑ i ∈ s, 2 * W₂ * R * (w i * u i)) +
            (∑ i ∈ s, w i ^ 2) * R ^ 2 := by
        rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
      _ = W₂ ^ 2 * (∑ i ∈ s, u i ^ 2) - 2 * W₂ * R * (∑ i ∈ s, w i * u i) +
            (∑ i ∈ s, w i ^ 2) * R ^ 2 := by
        rw [← Finset.mul_sum, ← Finset.mul_sum]
  rw [hexp, hW₂_sq]
  ring

/-- **General Clique Sphere Lower Bound:**
Whenever `∑ i ∈ s, u_i^2 ≤ R^2` and `0 ≤ R`,
`cliqueSphereDualityFactor s w * R ≤ ∑ i ∈ s, w_i * (R - u_i)`. -/
theorem clique_sphere_weighted_sub_ge (s : Finset ι) (w u : ι → ℝ) (R : ℝ)
    (hR : 0 ≤ R) (hsphere : ∑ i ∈ s, u i ^ 2 ≤ R ^ 2) :
    cliqueSphereDualityFactor s w * R ≤ ∑ i ∈ s, w i * (R - u i) := by
  have hcs := sphere_weighted_sum_le_sqrt_mul s 0 w u 0 R hR (by linarith)
  simp only [zero_mul, zero_add, sq] at hcs
  have hcs' : ∑ i ∈ s, w i * u i ≤ cliqueSphereWeightNorm s w * R := by
    unfold cliqueSphereWeightNorm
    simpa only [sq] using hcs
  have hdef := clique_sphere_defect_eq s w u R
  linarith

/-- **Extremal Ray Lies on the Sphere:**
When `0 < cliqueSphereWeightNorm s w`, the extremal ray `cliqueSphereExtremizer s w R` satisfies
`∑ i ∈ s, (cliqueSphereExtremizer s w R i)^2 = R^2`. -/
theorem clique_sphere_extremizer_norm_sq (s : Finset ι) (w : ι → ℝ) (R : ℝ)
    (hW : 0 < cliqueSphereWeightNorm s w) :
    ∑ i ∈ s, cliqueSphereExtremizer s w R i ^ 2 = R ^ 2 := by
  set W₂ := cliqueSphereWeightNorm s w
  have hW_ne : W₂ ≠ 0 := ne_of_gt hW
  have hW_sq : ∑ i ∈ s, w i ^ 2 = W₂ ^ 2 := (cliqueSphereWeightNorm_sq s w).symm
  calc
    ∑ i ∈ s, cliqueSphereExtremizer s w R i ^ 2
        = ∑ i ∈ s, w i ^ 2 * (R ^ 2 / W₂ ^ 2) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      unfold cliqueSphereExtremizer
      ring
    _ = (∑ i ∈ s, w i ^ 2) * (R ^ 2 / W₂ ^ 2) := (Finset.sum_mul _ _ _).symm
    _ = W₂ ^ 2 * (R ^ 2 / W₂ ^ 2) := by rw [hW_sq]
    _ = R ^ 2 := mul_div_cancel₀ (R ^ 2) (pow_ne_zero 2 hW_ne)

/-- **Exact Extremal Saturation of the Clique Sphere Bound:**
When `0 < cliqueSphereWeightNorm s w`, the extremal vector `cliqueSphereExtremizer s w R`
achieves equality in `clique_sphere_weighted_sub_ge`:
`∑ i ∈ s, w_i * (R - cliqueSphereExtremizer s w R i) = cliqueSphereDualityFactor s w * R`. -/
theorem clique_sphere_extremizer_achieves_bound (s : Finset ι) (w : ι → ℝ) (R : ℝ)
    (hW : 0 < cliqueSphereWeightNorm s w) :
    ∑ i ∈ s, w i * (R - cliqueSphereExtremizer s w R i) =
      cliqueSphereDualityFactor s w * R := by
  set W₂ := cliqueSphereWeightNorm s w
  have hW_ne : W₂ ≠ 0 := ne_of_gt hW
  have hW_sq : ∑ i ∈ s, w i ^ 2 = W₂ ^ 2 := (cliqueSphereWeightNorm_sq s w).symm
  have hinner : ∑ i ∈ s, w i * cliqueSphereExtremizer s w R i = W₂ * R := by
    calc
      ∑ i ∈ s, w i * cliqueSphereExtremizer s w R i
          = ∑ i ∈ s, w i ^ 2 * (R / W₂) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        unfold cliqueSphereExtremizer
        ring
      _ = (∑ i ∈ s, w i ^ 2) * (R / W₂) := (Finset.sum_mul _ _ _).symm
      _ = W₂ ^ 2 * (R / W₂) := by rw [hW_sq]
      _ = W₂ * R := by
        field_simp [hW_ne]
  have hdef := clique_sphere_defect_eq s w (cliqueSphereExtremizer s w R) R
  linarith

/-! ## §2. Autocorrelation Clique Collar Bounds & Clique-Rank Amplification -/

/-- **Autocorrelation Weighted Clique Collar Lower Bound (Left-Shifted Form):**
For any pairwise difference-orthogonal clique `t : ι → ℝ` on `s`
(`∀ i ∈ s, ∀ j ∈ s, i ≠ j → autocorr f (t i - t j) = 0`), any weights `w : ι → ℝ`, and any
shift `y ∈ ℝ`,
`cliqueSphereDualityFactor s w * autocorr f 0 ≤ ∑ i ∈ s, w_i * (autocorr f 0 - autocorr f (y - t_i))`. -/
theorem autocorr_weighted_clique_collar_ge [DecidableEq ι] {f : ℝ → ℝ}
    (hfc : HasCompactSupport f) (hf : Continuous f)
    (s : Finset ι) (t : ι → ℝ)
    (horth : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → autocorr f (t i - t j) = 0)
    (w : ι → ℝ) (y : ℝ) :
    cliqueSphereDualityFactor s w * autocorr f 0 ≤
      ∑ i ∈ s, w i * (autocorr f 0 - autocorr f (y - t i)) :=
  clique_sphere_weighted_sub_ge s w (fun i => autocorr f (y - t i)) (autocorr f 0)
    (autocorr_zero_nonneg f) (autocorr_finset_bessel_sq_le hfc hf s t horth y)

/-- **Autocorrelation Weighted Clique Collar Lower Bound (Right-Shifted Form):**
By evenness `autocorr f (t_i - y) = autocorr f (y - t_i)` and replacing `y` by `-y`,
the same bound holds for `t_i + y`. -/
theorem autocorr_weighted_clique_right_collar_ge [DecidableEq ι] {f : ℝ → ℝ}
    (hfc : HasCompactSupport f) (hf : Continuous f)
    (s : Finset ι) (t : ι → ℝ)
    (horth : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → autocorr f (t i - t j) = 0)
    (w : ι → ℝ) (y : ℝ) :
    cliqueSphereDualityFactor s w * autocorr f 0 ≤
      ∑ i ∈ s, w i * (autocorr f 0 - autocorr f (t i + y)) := by
  have h := autocorr_weighted_clique_collar_ge hfc hf s t horth w (-y)
  refine le_trans h (le_of_eq ?_)
  refine Finset.sum_congr rfl fun i _ => ?_
  have heven : autocorr f (-y - t i) = autocorr f (t i + y) := by
    rw [show -y - t i = -(t i + y) by ring, autocorr_neg f (t i + y)]
  rw [heven]

/-- **Constant-Weight Evaluation of the Clique Sphere Duality Factor:**
When `w_i = c` with `0 ≤ c` for all `i ∈ s`,
`cliqueSphereDualityFactor s (fun _ => c) = c * ((s.card : ℝ) - √(s.card : ℝ))`. -/
theorem cliqueSphereDualityFactor_const (s : Finset ι) (c : ℝ) (hc : 0 ≤ c) :
    cliqueSphereDualityFactor s (fun _ => c) =
      c * ((s.card : ℝ) - Real.sqrt (s.card : ℝ)) := by
  unfold cliqueSphereDualityFactor cliqueSphereWeightNorm
  simp only [Finset.sum_const, nsmul_eq_mul]
  have hsqrt :
      Real.sqrt ((s.card : ℝ) * c ^ 2) = Real.sqrt (s.card : ℝ) * c := by
    rw [Real.sqrt_mul (Nat.cast_nonneg s.card), Real.sqrt_sq hc]
  rw [hsqrt]
  ring

/-- **Clique-Rank Amplification Law (Uniform Collar Sum):**
For any pairwise difference-orthogonal clique `t : ι → ℝ` on `s` of size `M = s.card` and
every `y ∈ ℝ`,
`((s.card : ℝ) - √(s.card : ℝ)) * autocorr f 0 ≤ ∑ i ∈ s, (autocorr f 0 - autocorr f (y - t_i))`.

As the clique size `M = s.card` grows (e.g., along a dyadic chain `{2^k}`), the average lower
bound per node `(1 - 1/√M) h(0)` converges to the full origin energy `h(0)`. -/
theorem autocorr_clique_uniform_collar_sum_ge [DecidableEq ι] {f : ℝ → ℝ}
    (hfc : HasCompactSupport f) (hf : Continuous f)
    (s : Finset ι) (t : ι → ℝ)
    (horth : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → autocorr f (t i - t j) = 0)
    (y : ℝ) :
    ((s.card : ℝ) - Real.sqrt (s.card : ℝ)) * autocorr f 0 ≤
      ∑ i ∈ s, (autocorr f 0 - autocorr f (y - t i)) := by
  have h := autocorr_weighted_clique_collar_ge hfc hf s t horth (fun _ => (1 : ℝ)) y
  have hfac := cliqueSphereDualityFactor_const s 1 zero_le_one
  rw [one_mul] at hfac
  rw [hfac] at h
  simpa only [one_mul] using h

/-- **Minimum-Weight Clique Amplification Bound:**
If `0 ≤ w_min` and `w_min ≤ w i` for all `i ∈ s`, then for every `y ∈ ℝ`,
`w_min * ((s.card : ℝ) - √(s.card : ℝ)) * autocorr f 0 ≤ ∑ i ∈ s, w i * (autocorr f 0 - autocorr f (y - t i))`. -/
theorem autocorr_clique_min_weight_collar_sum_ge [DecidableEq ι] {f : ℝ → ℝ}
    (hfc : HasCompactSupport f) (hf : Continuous f)
    (s : Finset ι) (t : ι → ℝ)
    (horth : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → autocorr f (t i - t j) = 0)
    (w : ι → ℝ) (w_min : ℝ) (hw_min : 0 ≤ w_min)
    (hw : ∀ i ∈ s, w_min ≤ w i) (y : ℝ) :
    w_min * ((s.card : ℝ) - Real.sqrt (s.card : ℝ)) * autocorr f 0 ≤
      ∑ i ∈ s, w i * (autocorr f 0 - autocorr f (y - t i)) := by
  have hunif := autocorr_clique_uniform_collar_sum_ge hfc hf s t horth y
  have hmul :
      w_min * (((s.card : ℝ) - Real.sqrt (s.card : ℝ)) * autocorr f 0) ≤
        w_min * ∑ i ∈ s, (autocorr f 0 - autocorr f (y - t i)) :=
    mul_le_mul_of_nonneg_left hunif hw_min
  rw [Finset.mul_sum] at hmul
  have hdom :
      (∑ i ∈ s, w_min * (autocorr f 0 - autocorr f (y - t i))) ≤
        ∑ i ∈ s, w i * (autocorr f 0 - autocorr f (y - t i)) := by
    refine Finset.sum_le_sum fun i hi => ?_
    exact mul_le_mul_of_nonneg_right (hw i hi) (autocorr_sub_nonneg hfc hf (y - t i))
  linarith

/-! ## §3. Multi-Node Clique Collar Integral Lower Bound -/

/-- Continuity of `y ↦ cliqueSphereDualityFactor s (fun i => w i y)` when each weight `w i` is
continuous on `[a, b]`. -/
theorem continuousOn_cliqueSphereDualityFactor (s : Finset ι) (w : ι → ℝ → ℝ) {a b : ℝ}
    (hw : ∀ i ∈ s, ContinuousOn (w i) (Icc a b)) :
    ContinuousOn (fun y => cliqueSphereDualityFactor s (fun i => w i y)) (Icc a b) := by
  unfold cliqueSphereDualityFactor cliqueSphereWeightNorm
  refine ContinuousOn.sub ?_ ?_
  · exact continuousOn_finsetSum s fun i hi => hw i hi
  · refine Continuous.comp_continuousOn Real.continuous_sqrt ?_
    exact continuousOn_finsetSum s fun i hi => (hw i hi).pow 2

/-- **Multi-Node Clique Collar Integral Lower Bound:**
For any pairwise difference-orthogonal clique `t : ι → ℝ` on `s`, any interval `[a, b]` with
`a ≤ b`, and any family of continuous collar weights `w : ι → ℝ → ℝ` on `[a, b]`,
`(∫ y in a..b, cliqueSphereDualityFactor s (fun i => w i y)) * autocorr f 0 ≤ ∫ y in a..b, ∑ i ∈ s, w i y * (autocorr f 0 - autocorr f (y - t i))`. -/
theorem integral_autocorr_clique_collar_ge [DecidableEq ι] {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (s : Finset ι) (t : ι → ℝ)
    (horth : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → autocorr f (t i - t j) = 0)
    (w : ι → ℝ → ℝ) {a b : ℝ} (hab : a ≤ b)
    (hw_cont : ∀ i ∈ s, ContinuousOn (w i) (Icc a b)) :
    (∫ y in a..b, cliqueSphereDualityFactor s (fun i => w i y)) * autocorr f 0 ≤
      ∫ y in a..b, ∑ i ∈ s, w i y * (autocorr f 0 - autocorr f (y - t i)) := by
  have hcont_h : Continuous (autocorr f) := continuous_autocorr hf hfc
  have hIcc : uIcc a b = Icc a b := Set.uIcc_of_le hab
  have hint_lhs :
      IntervalIntegrable
        (fun y => cliqueSphereDualityFactor s (fun i => w i y) * autocorr f 0)
        volume a b := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [hIcc]
    exact (continuousOn_cliqueSphereDualityFactor s w hw_cont).mul continuousOn_const
  have hint_rhs :
      IntervalIntegrable
        (fun y => ∑ i ∈ s, w i y * (autocorr f 0 - autocorr f (y - t i)))
        volume a b := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [hIcc]
    refine continuousOn_finsetSum s fun i hi => ?_
    exact (hw_cont i hi).mul
      (continuousOn_const.sub (hcont_h.comp (continuous_id.sub continuous_const)).continuousOn)
  have hmono :
      (∫ y in a..b, cliqueSphereDualityFactor s (fun i => w i y) * autocorr f 0) ≤
        ∫ y in a..b, ∑ i ∈ s, w i y * (autocorr f 0 - autocorr f (y - t i)) :=
    intervalIntegral.integral_mono_on hab hint_lhs hint_rhs fun y _ =>
      autocorr_weighted_clique_collar_ge hfc hf.continuous s t horth (fun i => w i y) y
  rwa [intervalIntegral.integral_mul_const] at hmono

end

end GaloisForLFunctions.BiScaleUncertainty
