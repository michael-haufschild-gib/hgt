import GaloisForLFunctions.BiScaleUncertainty.MultiplicativeChainBesselAndOriginLeverage
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Pillar VIII: Abstract Hilbert-Unitary Systems & The Multi-Node Schur–Krein Residual Coupling Theorem

This module provides the **abstract axiomatic Hilbert-space foundation** of
**Bi-Scale / Logarithmic-Grid Uncertainty Theory** (`GaloisForLFunctions.BiScaleUncertainty`)
and proves the **Multi-Node Schur–Krein Residual Coupling Theorem**.

## Mathematical Motivation

In an arbitrary real inner product space `E`, let `{e_i}_{i ∈ s}` be a finite pairwise orthogonal
family of vectors of common norm square `‖e_i‖² = R`. For any vector `x ∈ E`, we define its
**division-free scaled frame residual**
`scaledFrameResidual s e R x := R • x - ∑ i ∈ s, ⟪e_i, x⟫_ℝ • e_i`.

We prove:
1. **Exact Two-Vector Residual Inner Product Identity (`inner_scaledFrameResidual_eq`):**
   For any `x, y ∈ E`,
   `⟪scaledFrameResidual s e R x, scaledFrameResidual s e R y⟫_ℝ = R * (R * ⟪x, y⟫_ℝ - ∑ i ∈ s, ⟪e_i, x⟫_ℝ * ⟪e_i, y⟫_ℝ)`.
2. **Exact Multi-Node Parseval / Bessel Identity (`norm_sq_scaledFrameResidual_eq`):**
   Setting `y = x` gives
   `‖scaledFrameResidual s e R x‖² = R * (R * ‖x‖² - ∑ i ∈ s, ⟪e_i, x⟫_ℝ²)`.
3. **The Abstract Multi-Node Schur–Krein Residual Coupling Inequality
   (`abstract_schur_krein_residual_coupling`):**
   Applying Cauchy–Schwarz to the residuals of `x` and `y` yields:
   `(R * ⟪x, y⟫_ℝ - ∑ i ∈ s, ⟪e_i, x⟫_ℝ * ⟪e_i, y⟫_ℝ)² ≤ (R * ‖x‖² - ∑ i ∈ s, ⟪e_i, x⟫_ℝ²) * (R * ‖y‖² - ∑ i ∈ s, ⟪e_i, y⟫_ℝ²)`.
4. **Autocorrelation Two-Collar Schur–Krein Coupling (`autocorr_schur_krein_two_collar_coupling`
   & `autocorr_collar_inner_sq_le_of_zero_lag`):**
   For any pairwise difference-orthogonal clique `{t_i}_{i ∈ s}` of `h = autocorr f` and any two
   collar shifts `y, z ∈ ℝ`:
   `(h(0) h(z - y) - ∑ i ∈ s, h(y - t_i) h(z - t_i))² ≤ (h(0)² - ∑ i ∈ s, h(y - t_i)²) * (h(0)² - ∑ i ∈ s, h(z - t_i)²)`.
   In particular, whenever `z - y` is a zero node (`h(z - y) = 0`), the Euclidean inner product of
   the two collar vectors is bounded by the product of their Bessel slacks:
   `(∑ i ∈ s, h(y - t_i) h(z - t_i))² ≤ (h(0)² - ∑ i ∈ s, h(y - t_i)²) * (h(0)² - ∑ i ∈ s, h(z - t_i)²)`.
-/

open MeasureTheory Set Filter Topology Finset
open scoped BigOperators InnerProductSpace
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole

namespace GaloisForLFunctions.BiScaleUncertainty

noncomputable section

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ## §1. Division-Free Scaled Frame Projection & Residual in an Abstract Hilbert Space -/

/-- The unnormalized orthogonal-frame projection `∑ i ∈ s, ⟪e_i, x⟫_ℝ • e_i` onto a finite family
`e : ι → E`. -/
def scaledFrameProj (s : Finset ι) (e : ι → E) (x : E) : E :=
  ∑ i ∈ s, ⟪e i, x⟫_ℝ • e i

/-- The division-free scaled residual vector `R • x - ∑ i ∈ s, ⟪e_i, x⟫_ℝ • e_i` of `x` with
respect to an orthogonal family `e : ι → E` of common norm square `R`. -/
def scaledFrameResidual (s : Finset ι) (e : ι → E) (R : ℝ) (x : E) : E :=
  R • x - scaledFrameProj s e x

/-- Pairing any vector `y` with `scaledFrameProj s e x` yields `∑ i ∈ s, ⟪e_i, x⟫_ℝ * ⟪e_i, y⟫_ℝ`. -/
theorem inner_scaledFrameProj_left (s : Finset ι) (e : ι → E) (x y : E) :
    ⟪scaledFrameProj s e x, y⟫_ℝ = ∑ i ∈ s, ⟪e i, x⟫_ℝ * ⟪e i, y⟫_ℝ := by
  unfold scaledFrameProj
  rw [sum_inner]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [real_inner_smul_left]

theorem inner_scaledFrameProj_right (s : Finset ι) (e : ι → E) (x y : E) :
    ⟪x, scaledFrameProj s e y⟫_ℝ = ∑ i ∈ s, ⟪e i, x⟫_ℝ * ⟪e i, y⟫_ℝ := by
  rw [real_inner_comm, inner_scaledFrameProj_left]
  refine Finset.sum_congr rfl fun i _ => mul_comm _ _

/-- For a pairwise orthogonal family `e : ι → E` on `s` with common norm square `‖e_i‖² = R`,
the inner product of two frame projections `scaledFrameProj s e x` and `scaledFrameProj s e y`
equals `R * ∑ i ∈ s, ⟪e_i, x⟫_ℝ * ⟪e_i, y⟫_ℝ`. -/
theorem inner_scaledFrameProj_self [DecidableEq ι] (s : Finset ι) (e : ι → E) (R : ℝ)
    (horth : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ⟪e i, e j⟫_ℝ = 0)
    (hnorm : ∀ i ∈ s, ‖e i‖ ^ 2 = R) (x y : E) :
    ⟪scaledFrameProj s e x, scaledFrameProj s e y⟫_ℝ =
      R * ∑ i ∈ s, ⟪e i, x⟫_ℝ * ⟪e i, y⟫_ℝ := by
  unfold scaledFrameProj
  rw [sum_inner]
  have hterm (i : ι) (hi : i ∈ s) :
      ⟪⟪e i, x⟫_ℝ • e i, ∑ j ∈ s, ⟪e j, y⟫_ℝ • e j⟫_ℝ =
        R * (⟪e i, x⟫_ℝ * ⟪e i, y⟫_ℝ) := by
    rw [inner_sum, Finset.sum_eq_single i]
    · rw [real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq, hnorm i hi]
      ring
    · intro j hj hji
      rw [real_inner_smul_left, real_inner_smul_right, horth i hi j hj (Ne.symm hji),
        mul_zero, mul_zero]
    · intro hi'
      exact absurd hi hi'
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]

/-- **Exact Division-Free Two-Vector Residual Inner Product Identity:**
For any pairwise orthogonal family `e : ι → E` on `s` with `‖e_i‖² = R` and any `x, y ∈ E`,
`⟪scaledFrameResidual s e R x, scaledFrameResidual s e R y⟫_ℝ = R * (R * ⟪x, y⟫_ℝ - ∑ i ∈ s, ⟪e_i, x⟫_ℝ * ⟪e_i, y⟫_ℝ)`. -/
theorem inner_scaledFrameResidual_eq [DecidableEq ι] (s : Finset ι) (e : ι → E) (R : ℝ)
    (horth : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ⟪e i, e j⟫_ℝ = 0)
    (hnorm : ∀ i ∈ s, ‖e i‖ ^ 2 = R) (x y : E) :
    ⟪scaledFrameResidual s e R x, scaledFrameResidual s e R y⟫_ℝ =
      R * (R * ⟪x, y⟫_ℝ - ∑ i ∈ s, ⟪e i, x⟫_ℝ * ⟪e i, y⟫_ℝ) := by
  unfold scaledFrameResidual
  rw [inner_sub_left, inner_sub_right, inner_sub_right,
    real_inner_smul_left, real_inner_smul_right,
    real_inner_smul_left, inner_scaledFrameProj_right,
    real_inner_smul_right, inner_scaledFrameProj_left,
    inner_scaledFrameProj_self s e R horth hnorm x y]
  ring

/-- **Exact Multi-Node Parseval / Bessel Residual Identity:**
Setting `y = x` in `inner_scaledFrameResidual_eq` yields:
`‖scaledFrameResidual s e R x‖² = R * (R * ‖x‖² - ∑ i ∈ s, ⟪e_i, x⟫_ℝ²)`. -/
theorem norm_sq_scaledFrameResidual_eq [DecidableEq ι] (s : Finset ι) (e : ι → E) (R : ℝ)
    (horth : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ⟪e i, e j⟫_ℝ = 0)
    (hnorm : ∀ i ∈ s, ‖e i‖ ^ 2 = R) (x : E) :
    ‖scaledFrameResidual s e R x‖ ^ 2 =
      R * (R * ‖x‖ ^ 2 - ∑ i ∈ s, ⟪e i, x⟫_ℝ ^ 2) := by
  rw [← real_inner_self_eq_norm_sq, inner_scaledFrameResidual_eq s e R horth hnorm x x,
    real_inner_self_eq_norm_sq]
  congr 2
  refine Finset.sum_congr rfl fun i _ => (sq _).symm

/-- **Abstract Multi-Node Bessel Inequality:**
For any pairwise orthogonal family `e : ι → E` on `s` with `‖e_i‖² = R` (`0 ≤ R`) and any `x ∈ E`,
`∑ i ∈ s, ⟪e_i, x⟫_ℝ² ≤ R * ‖x‖²`. -/
theorem abstract_finset_bessel_sq_le [DecidableEq ι] (s : Finset ι) (e : ι → E) (R : ℝ)
    (hR : 0 ≤ R)
    (horth : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ⟪e i, e j⟫_ℝ = 0)
    (hnorm : ∀ i ∈ s, ‖e i‖ ^ 2 = R) (x : E) :
    (∑ i ∈ s, ⟪e i, x⟫_ℝ ^ 2) ≤ R * ‖x‖ ^ 2 := by
  rcases eq_or_lt_of_le hR with rfl | hR_pos
  · have hzero : ∑ i ∈ s, ⟪e i, x⟫_ℝ ^ 2 = 0 := by
      refine Finset.sum_eq_zero fun i hi => ?_
      have he0 : ‖e i‖ = 0 := sq_eq_zero_iff.mp (hnorm i hi)
      rw [norm_eq_zero.mp he0, inner_zero_left, sq, zero_mul]
    rw [hzero, zero_mul]
  · have hres : 0 ≤ ‖scaledFrameResidual s e R x‖ ^ 2 := sq_nonneg _
    rw [norm_sq_scaledFrameResidual_eq s e R horth hnorm x] at hres
    have hnonneg : 0 ≤ R * ‖x‖ ^ 2 - ∑ i ∈ s, ⟪e i, x⟫_ℝ ^ 2 :=
      nonneg_of_mul_nonneg_right hres hR_pos
    linarith

/-- **The Universal Abstract Multi-Node Schur–Krein Residual Coupling Inequality:**
For any pairwise orthogonal family `e : ι → E` on `s` with `‖e_i‖² = R` (`0 ≤ R`) and any two
vectors `x, y ∈ E`:
`(R * ⟪x, y⟫_ℝ - ∑ i ∈ s, ⟪e_i, x⟫_ℝ * ⟪e_i, y⟫_ℝ)² ≤ (R * ‖x‖² - ∑ i ∈ s, ⟪e_i, x⟫_ℝ²) * (R * ‖y‖² - ∑ i ∈ s, ⟪e_i, y⟫_ℝ²)`. -/
theorem abstract_schur_krein_residual_coupling [DecidableEq ι] (s : Finset ι) (e : ι → E) (R : ℝ)
    (hR : 0 ≤ R)
    (horth : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ⟪e i, e j⟫_ℝ = 0)
    (hnorm : ∀ i ∈ s, ‖e i‖ ^ 2 = R) (x y : E) :
    (R * ⟪x, y⟫_ℝ - ∑ i ∈ s, ⟪e i, x⟫_ℝ * ⟪e i, y⟫_ℝ) ^ 2 ≤
      (R * ‖x‖ ^ 2 - ∑ i ∈ s, ⟪e i, x⟫_ℝ ^ 2) *
        (R * ‖y‖ ^ 2 - ∑ i ∈ s, ⟪e i, y⟫_ℝ ^ 2) := by
  rcases eq_or_lt_of_le hR with rfl | hR_pos
  · have hzero_xy : ∑ i ∈ s, ⟪e i, x⟫_ℝ * ⟪e i, y⟫_ℝ = 0 := by
      refine Finset.sum_eq_zero fun i hi => ?_
      have he0 : ‖e i‖ = 0 := sq_eq_zero_iff.mp (hnorm i hi)
      rw [norm_eq_zero.mp he0, inner_zero_left, zero_mul]
    have hzero_x : ∑ i ∈ s, ⟪e i, x⟫_ℝ ^ 2 = 0 := by
      refine Finset.sum_eq_zero fun i hi => ?_
      have he0 : ‖e i‖ = 0 := sq_eq_zero_iff.mp (hnorm i hi)
      rw [norm_eq_zero.mp he0, inner_zero_left, sq, zero_mul]
    have hzero_y : ∑ i ∈ s, ⟪e i, y⟫_ℝ ^ 2 = 0 := by
      refine Finset.sum_eq_zero fun i hi => ?_
      have he0 : ‖e i‖ = 0 := sq_eq_zero_iff.mp (hnorm i hi)
      rw [norm_eq_zero.mp he0, inner_zero_left, sq, zero_mul]
    simp [hzero_xy, hzero_x, hzero_y]
  · set rx := scaledFrameResidual s e R x
    set ry := scaledFrameResidual s e R y
    have hcs : ⟪rx, ry⟫_ℝ ^ 2 ≤ ‖rx‖ ^ 2 * ‖ry‖ ^ 2 := by
      have habs := abs_real_inner_le_norm rx ry
      have hsq := mul_self_le_mul_self (abs_nonneg _) habs
      simpa only [← sq, sq_abs, mul_pow] using hsq
    rw [inner_scaledFrameResidual_eq s e R horth hnorm x y,
      norm_sq_scaledFrameResidual_eq s e R horth hnorm x,
      norm_sq_scaledFrameResidual_eq s e R horth hnorm y] at hcs
    have hR2_pos : 0 < R ^ 2 := sq_pos_of_pos hR_pos
    have hcs' :
        R ^ 2 * (R * ⟪x, y⟫_ℝ - ∑ i ∈ s, ⟪e i, x⟫_ℝ * ⟪e i, y⟫_ℝ) ^ 2 ≤
          R ^ 2 * ((R * ‖x‖ ^ 2 - ∑ i ∈ s, ⟪e i, x⟫_ℝ ^ 2) *
            (R * ‖y‖ ^ 2 - ∑ i ∈ s, ⟪e i, y⟫_ℝ ^ 2)) := by
      linarith
    exact le_of_mul_le_mul_left hcs' hR2_pos

/-! ## §2. Autocorrelation Two-Collar Schur–Krein Residual Coupling -/

/-- The division-free `L²` residual wave of `f(· + y)` after projecting out a finite family of
translates `{f(· + t_i)}_{i ∈ s}`:
`autocorrResidualWave f s t y u := h(0) * f(u + y) - ∑ i ∈ s, h(y - t_i) * f(u + t_i)`. -/
def autocorrResidualWave (f : ℝ → ℝ) (s : Finset ι) (t : ι → ℝ) (y u : ℝ) : ℝ :=
  autocorr f 0 * f (u + y) - ∑ i ∈ s, autocorr f (y - t i) * f (u + t i)

theorem continuous_autocorrResidualWave {f : ℝ → ℝ} (hf : Continuous f)
    (s : Finset ι) (t : ι → ℝ) (y : ℝ) :
    Continuous (autocorrResidualWave f s t y) := by
  unfold autocorrResidualWave
  refine (continuous_const.mul (hf.comp (continuous_add_const y))).sub ?_
  exact continuous_finsetSum s fun i _ =>
    continuous_const.mul (hf.comp (continuous_add_const (t i)))

theorem hasCompactSupport_finset_sum [DecidableEq ι] (s : Finset ι) (g : ι → ℝ → ℝ)
    (hg : ∀ i ∈ s, HasCompactSupport (g i)) :
    HasCompactSupport (fun u => ∑ i ∈ s, g i u) := by
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact HasCompactSupport.zero
  | @insert a s ha ih =>
    have hrew : (fun u => ∑ i ∈ insert a s, g i u) =
        fun u => g a u + ∑ i ∈ s, g i u := by
      funext u
      exact Finset.sum_insert ha
    rw [hrew]
    exact (hg a (Finset.mem_insert_self a s)).add
      (ih fun i hi => hg i (Finset.mem_insert_of_mem hi))

theorem hasCompactSupport_autocorrResidualWave [DecidableEq ι] {f : ℝ → ℝ}
    (hfc : HasCompactSupport f) (s : Finset ι) (t : ι → ℝ) (y : ℝ) :
    HasCompactSupport (autocorrResidualWave f s t y) := by
  unfold autocorrResidualWave
  refine ((hasCompactSupport_comp_add hfc y).mul_left).sub ?_
  exact hasCompactSupport_finset_sum s _ fun i _ =>
    (hasCompactSupport_comp_add hfc (t i)).mul_left

/-- **Exact `L²` Inner Product of Two Autocorrelation Residual Waves:**
For any pairwise difference-orthogonal clique `t : ι → ℝ` on `s`
(`∀ i ∈ s, ∀ j ∈ s, i ≠ j → autocorr f (t i - t j) = 0`) and any two shifts `y, z ∈ ℝ`,
`∫ u, autocorrResidualWave f s t y u * autocorrResidualWave f s t z u = h(0) * (h(0) * h(z - y) - ∑ i ∈ s, h(y - t_i) * h(z - t_i))`. -/
theorem integral_autocorrResidualWave_mul [DecidableEq ι] {f : ℝ → ℝ}
    (hfc : HasCompactSupport f) (hf : Continuous f)
    (s : Finset ι) (t : ι → ℝ)
    (horth : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → autocorr f (t i - t j) = 0)
    (y z : ℝ) :
    (∫ u, autocorrResidualWave f s t y u * autocorrResidualWave f s t z u) =
      autocorr f 0 *
        (autocorr f 0 * autocorr f (z - y) -
          ∑ i ∈ s, autocorr f (y - t i) * autocorr f (z - t i)) := by
  set R₀ := autocorr f 0
  set cy : ι → ℝ := fun i => autocorr f (y - t i)
  set cz : ι → ℝ := fun i => autocorr f (z - t i)
  set Py : ℝ → ℝ := fun u => ∑ i ∈ s, cy i * f (u + t i)
  set Pz : ℝ → ℝ := fun u => ∑ i ∈ s, cz i * f (u + t i)
  have hPy_c : Continuous Py :=
    continuous_finsetSum s fun i _ => continuous_const.mul (hf.comp (continuous_add_const (t i)))
  have hPz_c : Continuous Pz :=
    continuous_finsetSum s fun i _ => continuous_const.mul (hf.comp (continuous_add_const (t i)))
  have hfy_c : Continuous (fun u => f (u + y)) := hf.comp (continuous_add_const y)
  have hfy_cs : HasCompactSupport (fun u => f (u + y)) := hasCompactSupport_comp_add hfc y
  have hfz_c : Continuous (fun u => f (u + z)) := hf.comp (continuous_add_const z)
  have hfz_cs : HasCompactSupport (fun u => f (u + z)) := hasCompactSupport_comp_add hfc z
  have hi_fyfz : Integrable (fun u => R₀ ^ 2 * (f (u + y) * f (u + z))) :=
    (integrable_shift_mul_shift hf hfc y z).const_mul (R₀ ^ 2)
  have hi_fyPz : Integrable (fun u => R₀ * (f (u + y) * Pz u)) :=
    ((hfy_c.mul hPz_c).integrable_of_hasCompactSupport (hfy_cs.mul_right)).const_mul R₀
  have hi_fzPy : Integrable (fun u => R₀ * (f (u + z) * Py u)) :=
    ((hfz_c.mul hPy_c).integrable_of_hasCompactSupport (hfz_cs.mul_right)).const_mul R₀
  have hi_PyPz : Integrable (fun u => Py u * Pz u) := by
    have hPy_cs : HasCompactSupport Py :=
      hasCompactSupport_finset_sum s _ fun i _ => (hasCompactSupport_comp_add hfc (t i)).mul_left
    exact (hPy_c.mul hPz_c).integrable_of_hasCompactSupport (hPy_cs.mul_right)
  have hexp :
      (fun u => autocorrResidualWave f s t y u * autocorrResidualWave f s t z u) =
        fun u =>
          ((R₀ ^ 2 * (f (u + y) * f (u + z)) - R₀ * (f (u + y) * Pz u)) -
            R₀ * (f (u + z) * Py u)) + Py u * Pz u := by
    funext u
    unfold autocorrResidualWave
    dsimp [R₀, cy, cz, Py, Pz]
    ring
  have h_fyPz : (∫ u, f (u + y) * Pz u) = ∑ i ∈ s, cy i * cz i := by
    rw [integral_shift_mul_finset_sum hf hfc s cz t y]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hev : autocorr f (t i - y) = cy i := by
      dsimp [cy]
      rw [show t i - y = -(y - t i) by ring, autocorr_neg f (y - t i)]
    rw [hev, mul_comm]
  have h_fzPy : (∫ u, f (u + z) * Py u) = ∑ i ∈ s, cy i * cz i := by
    rw [integral_shift_mul_finset_sum hf hfc s cy t z]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hev : autocorr f (t i - z) = cz i := by
      dsimp [cz]
      rw [show t i - z = -(z - t i) by ring, autocorr_neg f (z - t i)]
    rw [hev]
  have h_PyPz : (∫ u, Py u * Pz u) = R₀ * ∑ i ∈ s, cy i * cz i := by
    have hrew : (fun u => Py u * Pz u) = fun u => ∑ i ∈ s, cy i * (f (u + t i) * Pz u) := by
      funext u
      simp only [Py, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => by ring
    have hint_i (i : ι) : Integrable (fun u => cy i * (f (u + t i) * Pz u)) :=
      (((hf.comp (continuous_add_const (t i))).mul hPz_c).integrable_of_hasCompactSupport
        ((hasCompactSupport_comp_add hfc (t i)).mul_right)).const_mul (cy i)
    rw [hrew, integral_finsetSum s (fun i _ => hint_i i)]
    have hinner (i : ι) (hi : i ∈ s) :
        (∫ u, cy i * (f (u + t i) * Pz u)) = R₀ * (cy i * cz i) := by
      rw [integral_const_mul, integral_shift_mul_finset_sum hf hfc s cz t (t i)]
      have hsingle : (∑ j ∈ s, cz j * autocorr f (t j - t i)) = cz i * R₀ := by
        rw [Finset.sum_eq_single i]
        · rw [sub_self]
        · intro j hj hji
          rw [horth j hj i hi hji, mul_zero]
        · intro hi'
          exact absurd hi hi'
      rw [hsingle]
      ring
    rw [Finset.sum_congr rfl hinner, ← Finset.mul_sum]
  have e1 :
      (∫ u, (((R₀ ^ 2 * (f (u + y) * f (u + z)) - R₀ * (f (u + y) * Pz u)) -
          R₀ * (f (u + z) * Py u)) + Py u * Pz u)) =
        (∫ u, ((R₀ ^ 2 * (f (u + y) * f (u + z)) - R₀ * (f (u + y) * Pz u)) -
          R₀ * (f (u + z) * Py u))) + ∫ u, Py u * Pz u :=
    integral_add ((hi_fyfz.sub hi_fyPz).sub hi_fzPy) hi_PyPz
  have e2 :
      (∫ u, ((R₀ ^ 2 * (f (u + y) * f (u + z)) - R₀ * (f (u + y) * Pz u)) -
          R₀ * (f (u + z) * Py u))) =
        (∫ u, (R₀ ^ 2 * (f (u + y) * f (u + z)) - R₀ * (f (u + y) * Pz u))) -
          ∫ u, R₀ * (f (u + z) * Py u) :=
    integral_sub (hi_fyfz.sub hi_fyPz) hi_fzPy
  have e3 :
      (∫ u, (R₀ ^ 2 * (f (u + y) * f (u + z)) - R₀ * (f (u + y) * Pz u))) =
        (∫ u, R₀ ^ 2 * (f (u + y) * f (u + z))) - ∫ u, R₀ * (f (u + y) * Pz u) :=
    integral_sub hi_fyfz hi_fyPz
  rw [hexp, e1, e2, e3,
    integral_const_mul, integral_const_mul, integral_const_mul,
    integral_shift_mul_shift f y z, h_fyPz, h_fzPy, h_PyPz]
  ring

/-- **Exact `L²` Norm Square of an Autocorrelation Residual Wave:**
`∫ u, (autocorrResidualWave f s t y u)^2 = h(0) * (h(0)^2 - ∑ i ∈ s, h(y - t_i)^2)`. -/
theorem integral_autocorrResidualWave_sq [DecidableEq ι] {f : ℝ → ℝ}
    (hfc : HasCompactSupport f) (hf : Continuous f)
    (s : Finset ι) (t : ι → ℝ)
    (horth : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → autocorr f (t i - t j) = 0)
    (y : ℝ) :
    (∫ u, autocorrResidualWave f s t y u ^ 2) =
      autocorr f 0 * (autocorr f 0 ^ 2 - ∑ i ∈ s, autocorr f (y - t i) ^ 2) := by
  have h := integral_autocorrResidualWave_mul hfc hf s t horth y y
  have hsq :
      (fun u => autocorrResidualWave f s t y u ^ 2) =
        fun u => autocorrResidualWave f s t y u * autocorrResidualWave f s t y u := by
    funext u; ring
  rw [hsq, h, sub_self]
  congr 1
  rw [← sq]
  congr 1
  refine Finset.sum_congr rfl fun i _ => (sq _).symm

/-- **The Two-Collar Schur–Krein Residual Coupling Inequality for Autocorrelations:**
For any pairwise difference-orthogonal clique `t : ι → ℝ` on `s`
(`∀ i ∈ s, ∀ j ∈ s, i ≠ j → autocorr f (t i - t j) = 0`) and any two collar shifts `y, z ∈ ℝ`:
`(h(0) * h(z - y) - ∑ i ∈ s, h(y - t_i) * h(z - t_i))^2 ≤ (h(0)^2 - ∑ i ∈ s, h(y - t_i)^2) * (h(0)^2 - ∑ i ∈ s, h(z - t_i)^2)`. -/
theorem autocorr_schur_krein_two_collar_coupling [DecidableEq ι] {f : ℝ → ℝ}
    (hfc : HasCompactSupport f) (hf : Continuous f)
    (s : Finset ι) (t : ι → ℝ)
    (horth : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → autocorr f (t i - t j) = 0)
    (y z : ℝ) :
    (autocorr f 0 * autocorr f (z - y) -
        ∑ i ∈ s, autocorr f (y - t i) * autocorr f (z - t i)) ^ 2 ≤
      (autocorr f 0 ^ 2 - ∑ i ∈ s, autocorr f (y - t i) ^ 2) *
        (autocorr f 0 ^ 2 - ∑ i ∈ s, autocorr f (z - t i) ^ 2) := by
  rcases eq_or_lt_of_le (autocorr_zero_nonneg f) with h0_eq | h0_pos
  · have hzero (x : ℝ) : autocorr f x = 0 :=
      autocorr_eq_zero_of_zero_eq_zero hfc hf h0_eq.symm x
    have hsum_yz : ∑ i ∈ s, autocorr f (y - t i) * autocorr f (z - t i) = 0 :=
      Finset.sum_eq_zero fun i _ => by rw [hzero, zero_mul]
    have hsum_y : ∑ i ∈ s, autocorr f (y - t i) ^ 2 = 0 :=
      Finset.sum_eq_zero fun i _ => by rw [hzero, sq, zero_mul]
    have hsum_z : ∑ i ∈ s, autocorr f (z - t i) ^ 2 = 0 :=
      Finset.sum_eq_zero fun i _ => by rw [hzero, sq, zero_mul]
    rw [← h0_eq, hsum_yz, hsum_y, hsum_z]
    ring_nf
    exact le_rfl
  · set Ry := autocorrResidualWave f s t y
    set Rz := autocorrResidualWave f s t z
    set A := autocorr f 0 *
      (autocorr f 0 * autocorr f (z - y) -
        ∑ i ∈ s, autocorr f (y - t i) * autocorr f (z - t i))
    set B := autocorr f 0 * (autocorr f 0 ^ 2 - ∑ i ∈ s, autocorr f (y - t i) ^ 2)
    set C := autocorr f 0 * (autocorr f 0 ^ 2 - ∑ i ∈ s, autocorr f (z - t i) ^ 2)
    have hRy_c := continuous_autocorrResidualWave hf s t y
    have hRy_cs := hasCompactSupport_autocorrResidualWave hfc s t y
    have hRz_c := continuous_autocorrResidualWave hf s t z
    have hRz_cs := hasCompactSupport_autocorrResidualWave hfc s t z
    have hi_y : Integrable (fun u => Ry u ^ 2) := integrable_sq hRy_c hRy_cs
    have hi_z : Integrable (fun u => Rz u ^ 2) := integrable_sq hRz_c hRz_cs
    have hi_yz : Integrable (fun u => Ry u * Rz u) :=
      (hRy_c.mul hRz_c).integrable_of_hasCompactSupport (hRy_cs.mul_right)
    have hInt_yz : (∫ u, Ry u * Rz u) = A :=
      integral_autocorrResidualWave_mul hfc hf s t horth y z
    have hInt_y : (∫ u, Ry u ^ 2) = B :=
      integral_autocorrResidualWave_sq hfc hf s t horth y
    have hInt_z : (∫ u, Rz u ^ 2) = C :=
      integral_autocorrResidualWave_sq hfc hf s t horth z
    have hdisc (α β : ℝ) : 0 ≤ α ^ 2 * B - 2 * (α * β) * A + β ^ 2 * C := by
      have h0 : 0 ≤ ∫ u, (α * Ry u - β * Rz u) ^ 2 := integral_nonneg fun u => sq_nonneg _
      have hrew : (fun u => (α * Ry u - β * Rz u) ^ 2) =
          fun u => (α ^ 2 * Ry u ^ 2 - 2 * (α * β) * (Ry u * Rz u)) + β ^ 2 * Rz u ^ 2 := by
        funext u; ring
      have d1 :
          (∫ u, ((α ^ 2 * Ry u ^ 2 - 2 * (α * β) * (Ry u * Rz u)) + β ^ 2 * Rz u ^ 2)) =
            (∫ u, (α ^ 2 * Ry u ^ 2 - 2 * (α * β) * (Ry u * Rz u))) + ∫ u, β ^ 2 * Rz u ^ 2 :=
        integral_add ((hi_y.const_mul (α ^ 2)).sub (hi_yz.const_mul (2 * (α * β))))
          (hi_z.const_mul (β ^ 2))
      have d2 :
          (∫ u, (α ^ 2 * Ry u ^ 2 - 2 * (α * β) * (Ry u * Rz u))) =
            (∫ u, α ^ 2 * Ry u ^ 2) - ∫ u, 2 * (α * β) * (Ry u * Rz u) :=
        integral_sub (hi_y.const_mul (α ^ 2)) (hi_yz.const_mul (2 * (α * β)))
      rw [hrew, d1, d2, integral_const_mul, integral_const_mul, integral_const_mul,
        hInt_y, hInt_yz, hInt_z] at h0
      linarith
    have hB_nonneg : 0 ≤ B := by
      rw [← hInt_y]
      exact integral_nonneg fun u => sq_nonneg _
    rcases eq_or_lt_of_le hB_nonneg with hB_zero | hB_pos
    · have hA_zero : A = 0 := by
        by_contra hA_ne
        have hinst := hdisc ((C + 1) / (2 * A)) 1
        rw [← hB_zero, mul_zero, zero_sub, mul_one, one_pow, one_mul] at hinst
        have hsimp : 2 * ((C + 1) / (2 * A)) * A = C + 1 := by
          field_simp [hA_ne]
        linarith
      have hA_def : A = autocorr f 0 *
          (autocorr f 0 * autocorr f (z - y) -
            ∑ i ∈ s, autocorr f (y - t i) * autocorr f (z - t i)) := rfl
      have hB_def : B = autocorr f 0 * (autocorr f 0 ^ 2 - ∑ i ∈ s, autocorr f (y - t i) ^ 2) := rfl
      rw [hA_zero] at hA_def
      rw [← hB_zero] at hB_def
      have hlhs : autocorr f 0 * autocorr f (z - y) -
          ∑ i ∈ s, autocorr f (y - t i) * autocorr f (z - t i) = 0 := by
        rcases mul_eq_zero.mp hA_def.symm with h0 | h0
        · linarith
        · exact h0
      have hrhs : autocorr f 0 ^ 2 - ∑ i ∈ s, autocorr f (y - t i) ^ 2 = 0 := by
        rcases mul_eq_zero.mp hB_def.symm with h0 | h0
        · linarith
        · exact h0
      rw [hlhs, hrhs]
      simp
    · have hinst := mul_nonneg hB_pos.le (hdisc A B)
      have hB2_pos : 0 < B ^ 2 := sq_pos_of_pos hB_pos
      have hfactor : B * (A ^ 2 * B - 2 * (A * B) * A + B ^ 2 * C) = B ^ 2 * (B * C - A ^ 2) := by
        ring
      rw [hfactor] at hinst
      have hBC : A ^ 2 ≤ B * C := by
        have := nonneg_of_mul_nonneg_right hinst hB2_pos
        linarith
      dsimp [A, B, C] at hBC
      have hR2_pos : 0 < autocorr f 0 ^ 2 := sq_pos_of_pos h0_pos
      have hBC' :
          autocorr f 0 ^ 2 *
              (autocorr f 0 * autocorr f (z - y) -
                ∑ i ∈ s, autocorr f (y - t i) * autocorr f (z - t i)) ^ 2 ≤
            autocorr f 0 ^ 2 *
              ((autocorr f 0 ^ 2 - ∑ i ∈ s, autocorr f (y - t i) ^ 2) *
                (autocorr f 0 ^ 2 - ∑ i ∈ s, autocorr f (z - t i) ^ 2)) := by
        linarith
      exact le_of_mul_le_mul_left hBC' hR2_pos

/-- **Zero-Lag Collar Orthogonality Bound:**
If `{t_i}_{i ∈ s}` is a difference-orthogonal clique of `h = autocorr f` and the lag difference
`z - y` is itself a zero node (`autocorr f (z - y) = 0`), then the square of the Euclidean inner
product of the two collar vectors `(h(y - t_i))_{i ∈ s}` and `(h(z - t_i))_{i ∈ s}` is bounded by
the product of their Bessel slacks:
`(∑ i ∈ s, h(y - t_i) * h(z - t_i))^2 ≤ (h(0)^2 - ∑ i ∈ s, h(y - t_i)^2) * (h(0)^2 - ∑ i ∈ s, h(z - t_i)^2)`. -/
theorem autocorr_collar_inner_sq_le_of_zero_lag [DecidableEq ι] {f : ℝ → ℝ}
    (hfc : HasCompactSupport f) (hf : Continuous f)
    (s : Finset ι) (t : ι → ℝ)
    (horth : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → autocorr f (t i - t j) = 0)
    {y z : ℝ} (hlag : autocorr f (z - y) = 0) :
    (∑ i ∈ s, autocorr f (y - t i) * autocorr f (z - t i)) ^ 2 ≤
      (autocorr f 0 ^ 2 - ∑ i ∈ s, autocorr f (y - t i) ^ 2) *
        (autocorr f 0 ^ 2 - ∑ i ∈ s, autocorr f (z - t i) ^ 2) := by
  have h := autocorr_schur_krein_two_collar_coupling hfc hf s t horth y z
  rw [hlag, mul_zero, zero_sub, neg_sq] at h
  exact h

end

end GaloisForLFunctions.BiScaleUncertainty
