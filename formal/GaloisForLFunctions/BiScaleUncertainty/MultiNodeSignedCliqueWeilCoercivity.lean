import GaloisForLFunctions.BiScaleUncertainty.WeilFullFunctionalAndPrimitiveHyperplaneBridge

/-!
# Pillar XXIV: Unconditional Multi-Node Signed Gram & Dyadic Coset Coercivity

This module develops **Pillar XXIV** of **Bi-Scale / Logarithmic-Grid Uncertainty Theory**
(`GaloisForLFunctions.BiScaleUncertainty`), lifting the multi-node Bessel/Gram origin-singularity
machinery (Pillars I, V, X, XIV) to **100% unconditional theorems** with **zero** grid-blindness or
difference-orthogonality hypotheses.

In Pillars I, V, and X, multi-node origin leverage required the conditional assumption that
`autocorr f (t_i) = 0` and `autocorr f (t_i - t_j) = 0` (`i ≠ j`). Here we prove the exact
non-orthogonal completion-of-squares and Cauchy–Schwarz Gram identities on `autocorr f`, retaining
both the signed diagonal node correlations `∑_{i ∈ s} w_i h_f(t_i)` and the off-diagonal Gram
interactions `∑_{i ∈ s} ∑_{j ∈ s.erase i} w_i w_j h_f(t_i - t_j)` on the right-hand side.

Crucially, for any dyadic coset `t_k = log((m + 1) · 2^{k + 1})`, the node difference
`t_i - t_j = (i - j) log 2` is **completely independent of the coset leader `m + 1`**, so every
off-diagonal Gram entry reduces unconditionally to a prime-`2`-power correlation
`h_f(log(2^{max(i, j) - min(i, j)}))`.

## Main Unconditional Results

1. **Exact Multi-Node Shift Gram Identity & Nonnegativity (`integral_finset_sum_shift_sq`,
   `autocorr_gram_quad_nonneg`, `autocorr_gram_quad_eq_diag_add_offDiag`):**
   - For every continuous compactly supported `f : ℝ → ℝ`, finite set `s : Finset ι`, weights
     `w : ι → ℝ`, and shifts `t : ι → ℝ`:
     $$\int_{\mathbb{R}} \left(\sum_{i \in s} w_i\,f(u + t_i)\right)^2 du
       = \sum_{i \in s} \sum_{j \in s} w_i\,w_j\,h_f(t_i - t_j)
       = \left(\sum_{i \in s} w_i^2\right) h_f(0)
         + \sum_{i \in s} \sum_{j \in s.\mathrm{erase}\,i} w_i\,w_j\,h_f(t_i - t_j) \ge 0.$$

2. **Unconditional Multi-Node Signed Collar Gram & Off-Diagonal Bounds
   (`autocorr_multi_node_signed_collar_gram_ge`, `autocorr_multi_node_signed_collar_offDiag_ge`,
   `integral_multi_node_signed_collar_offDiag_ge`):**
   - For every continuous compactly supported `f : ℝ → ℝ`, `s : Finset ι`, `w t : ι → ℝ`, `W₀ > 0`,
     and `y ∈ ℝ` (with **zero blindness or orthogonality hypotheses**):
     $$\left(\sum_{i \in s} w_i - \frac{\sum_{i \in s} w_i^2}{2 W_0}\right) h_f(0)
       \;\le\; W_0\bigl(h_f(0) - h_f(y)\bigr)
         + \sum_{i \in s} w_i\bigl(h_f(0) - h_f(t_i + y)\bigr)$$
     $$+\; \sum_{i \in s} w_i\,h_f(t_i)
       + \frac{1}{2 W_0} \sum_{i \in s} \sum_{j \in s.\mathrm{erase}\,i} w_i\,w_j\,h_f(t_i - t_j).$$

3. **Coset-Invariance of Dyadic Differences & Unconditional Dyadic Coset Bounds on
   `RealEvenPolarTestFn` and `RealSmoothEvenPolarTestFn` (`dyadicCosetNode_sub_eq`,
   `autocorr_dyadicCosetNode_sub_eq`,
   `RealEvenPolarTestFn.unconditional_multi_node_signed_collar_offDiag_bound`,
   `RealEvenPolarTestFn.unconditional_dyadic_coset_multi_node_signed_collar_bound`,
   `RealSmoothEvenPolarTestFn.unconditional_dyadic_coset_multi_node_signed_collar_bound`):**
   - Parameterizing `W₀ = exp c` (`c ∈ ℝ`), every multi-node and dyadic-coset signed collar theorem
     holds unconditionally for all `g : RealEvenPolarTestFn` (and `RealSmoothEvenPolarTestFn`) with
     **zero** hypotheses.
-/

open Complex MeasureTheory Set Filter Topology
open Zeta23
open RHTower RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole
open RHTower.EvenSector GaloisForLFunctions.HTGeometry
open scoped RealInnerProductSpace BigOperators

namespace GaloisForLFunctions.BiScaleUncertainty

noncomputable section

variable {f : ℝ → ℝ} {ι : Type*}

/-! ## §1. Exact Multi-Node Shift Gram Identity & Off-Diagonal Decomposition -/

/-- **Exact Multi-Node Shift Gram Identity (`integral_finset_sum_shift_sq`):**
For any continuous compactly supported `f : ℝ → ℝ`, finite index set `s : Finset ι`, weights
`w : ι → ℝ`, and shifts `t : ι → ℝ`, the `L²` norm square of `∑ i ∈ s, w i * f (u + t i)` equals
the full autocorrelation Gram quadratic form:
$$\int_{\mathbb{R}} \left(\sum_{i \in s} w_i\,f(u + t_i)\right)^2 du
  = \sum_{i \in s} \sum_{j \in s} w_i\,w_j\,\operatorname{autocorr}(f, t_i - t_j).$$ -/
theorem integral_finset_sum_shift_sq (hf : Continuous f) (hfc : HasCompactSupport f)
    (s : Finset ι) (w t : ι → ℝ) :
    (∫ u : ℝ, (∑ i ∈ s, w i * f (u + t i)) ^ 2) =
      ∑ i ∈ s, ∑ j ∈ s, w i * w j * autocorr f (t i - t j) := by
  set P : ℝ → ℝ := fun u => ∑ i ∈ s, w i * f (u + t i)
  have hPc : Continuous P :=
    continuous_finsetSum s fun i _ =>
      continuous_const.mul (hf.comp (continuous_add_const (t i)))
  have hrew : (fun u => P u ^ 2) =
      fun u => ∑ i ∈ s, w i * (f (u + t i) * P u) := by
    funext u
    simp only [P, sq]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => by ring
  have hint_term (i : ι) : Integrable fun u => w i * (f (u + t i) * P u) := by
    refine ((continuous_const.mul
      ((hf.comp (continuous_add_const (t i))).mul hPc)).integrable_of_hasCompactSupport ?_)
    exact ((hasCompactSupport_comp_add hfc (t i)).mul_right).mul_left
  rw [hrew, integral_finsetSum s (fun i _ => hint_term i)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_const_mul, integral_shift_mul_finset_sum hf hfc s w t (t i), Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hsymm : autocorr f (t j - t i) = autocorr f (t i - t j) := by
    rw [show t j - t i = -(t i - t j) by ring, autocorr_neg]
  rw [hsymm]
  ring

/-- **Positive-Semidefiniteness of the Autocorrelation Gram Form (`autocorr_gram_quad_nonneg`):**
For any continuous compactly supported `f : ℝ → ℝ`, `s : Finset ι`, and `w t : ι → ℝ`,
$$0 \;\le\; \sum_{i \in s} \sum_{j \in s} w_i\,w_j\,\operatorname{autocorr}(f, t_i - t_j).$$ -/
theorem autocorr_gram_quad_nonneg (hf : Continuous f) (hfc : HasCompactSupport f)
    (s : Finset ι) (w t : ι → ℝ) :
    0 ≤ ∑ i ∈ s, ∑ j ∈ s, w i * w j * autocorr f (t i - t j) := by
  rw [← integral_finset_sum_shift_sq hf hfc s w t]
  exact integral_nonneg fun _ => sq_nonneg _

/-- **Diagonal-plus-Off-Diagonal Decomposition of the Autocorrelation Gram Form:**
For any `[DecidableEq ι]`, `f : ℝ → ℝ`, `s : Finset ι`, and `w t : ι → ℝ`,
$$\sum_{i \in s} \sum_{j \in s} w_i\,w_j\,\operatorname{autocorr}(f, t_i - t_j)
  = \left(\sum_{i \in s} w_i^2\right) \operatorname{autocorr}(f, 0)
    + \sum_{i \in s} \sum_{j \in s.\mathrm{erase}\,i} w_i\,w_j\,\operatorname{autocorr}(f, t_i - t_j).$$ -/
theorem autocorr_gram_quad_eq_diag_add_offDiag [DecidableEq ι] (f : ℝ → ℝ)
    (s : Finset ι) (w t : ι → ℝ) :
    (∑ i ∈ s, ∑ j ∈ s, w i * w j * autocorr f (t i - t j)) =
      (∑ i ∈ s, w i ^ 2) * autocorr f 0 +
        ∑ i ∈ s, ∑ j ∈ s.erase i, w i * w j * autocorr f (t i - t j) := by
  rw [Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [← Finset.add_sum_erase s (fun j => w i * w j * autocorr f (t i - t j)) hi, sub_self]
  ring

/-! ## §2. Unconditional Multi-Node Signed Collar Gram & Off-Diagonal Inequalities -/

/-- **Unconditional Multi-Node Signed Collar Gram Inequality (`autocorr_multi_node_signed_collar_gram_ge`):**
For EVERY continuous compactly supported `f : ℝ → ℝ`, EVERY `s : Finset ι`, EVERY `w t : ι → ℝ`,
EVERY `W₀ > 0`, and EVERY `y ∈ ℝ` (with **zero** blindness or orthogonality hypotheses):
$$\left(\sum_{i \in s} w_i\right) \operatorname{autocorr}(f, 0)
  - \frac{1}{2 W_0} \sum_{i \in s} \sum_{j \in s} w_i\,w_j\,\operatorname{autocorr}(f, t_i - t_j)$$
$$\le\; W_0\bigl(\operatorname{autocorr}(f, 0) - \operatorname{autocorr}(f, y)\bigr)
  + \sum_{i \in s} w_i\bigl(\operatorname{autocorr}(f, 0) - \operatorname{autocorr}(f, t_i + y)\bigr)
  + \sum_{i \in s} w_i\,\operatorname{autocorr}(f, t_i).$$ -/
theorem autocorr_multi_node_signed_collar_gram_ge (hfc : HasCompactSupport f) (hf : Continuous f)
    (s : Finset ι) (w t : ι → ℝ) {W₀ : ℝ} (hW₀ : 0 < W₀) (y : ℝ) :
    (∑ i ∈ s, w i) * autocorr f 0 -
        (1 / (2 * W₀)) * ∑ i ∈ s, ∑ j ∈ s, w i * w j * autocorr f (t i - t j) ≤
      W₀ * (autocorr f 0 - autocorr f y) +
        ∑ i ∈ s, w i * (autocorr f 0 - autocorr f (t i + y)) +
        ∑ i ∈ s, w i * autocorr f (t i) := by
  set P : ℝ → ℝ := fun u => ∑ i ∈ s, w i * f (u + t i)
  set D : ℝ → ℝ := fun u => f (u + (-y)) - f (u + 0)
  have hPc : Continuous P :=
    continuous_finsetSum s fun i _ =>
      continuous_const.mul (hf.comp (continuous_add_const (t i)))
  have hDc : Continuous D :=
    (hf.comp (continuous_add_const (-y))).sub (hf.comp (continuous_add_const 0))
  have hDcs : HasCompactSupport D :=
    (hasCompactSupport_comp_add hfc (-y)).sub (hasCompactSupport_comp_add hfc 0)
  have hi_P2 : Integrable fun u => P u ^ 2 := by
    have hrew : (fun u => P u ^ 2) =
        fun u => ∑ i ∈ s, w i * (f (u + t i) * P u) := by
      funext u; simp only [P, sq]; rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun i _ => by ring
    rw [hrew]
    refine integrable_finsetSum s fun i _ => ?_
    exact ((continuous_const.mul
      ((hf.comp (continuous_add_const (t i))).mul hPc)).integrable_of_hasCompactSupport
        (((hasCompactSupport_comp_add hfc (t i)).mul_right).mul_left))
  have hi_D2 : Integrable fun u => D u ^ 2 :=
    integrable_sq hDc hDcs
  have hcs := sq_integral_mul_le hPc.aestronglyMeasurable hDc.aestronglyMeasurable hi_P2 hi_D2
  have hint_P2 : (∫ u, P u ^ 2) = ∑ i ∈ s, ∑ j ∈ s, w i * w j * autocorr f (t i - t j) :=
    integral_finset_sum_shift_sq hf hfc s w t
  have hint_D2 : (∫ u, D u ^ 2) = 2 * (autocorr f 0 - autocorr f y) := by
    have hD_eq : (fun u => D u ^ 2) = fun u => (f (u + -y) - f u) ^ 2 := by
      funext u
      simp only [D, add_zero]
    rw [hD_eq]
    have htrans := integral_add_right_eq_self (μ := volume) (fun u => (f u - f (u + y)) ^ 2) (-y)
    have hcongr : (fun u => (f (u + -y) - f u) ^ 2) =
        fun u => (f (u + -y) - f (u + -y + y)) ^ 2 := by
      funext u
      rw [neg_add_cancel_right]
    rw [hcongr, htrans, integral_sub_shift_sq hfc hf y]
  have hint_PD :
      (∫ u, P u * D u) =
        ∑ i ∈ s, w i * autocorr f (t i + y) - ∑ i ∈ s, w i * autocorr f (t i) := by
    have hsub : (fun u => P u * D u) =
        fun u => f (u + (-y)) * P u - f (u + 0) * P u := by
      funext u
      simp only [D]
      ring
    have hi1 : Integrable fun u => f (u + (-y)) * P u :=
      ((hf.comp (continuous_add_const (-y))).mul hPc).integrable_of_hasCompactSupport
        ((hasCompactSupport_comp_add hfc (-y)).mul_right)
    have hi2 : Integrable fun u => f (u + 0) * P u :=
      ((hf.comp (continuous_add_const 0)).mul hPc).integrable_of_hasCompactSupport
        ((hasCompactSupport_comp_add hfc 0).mul_right)
    rw [hsub, integral_sub hi1 hi2,
      integral_shift_mul_finset_sum hf hfc s w t (-y),
      integral_shift_mul_finset_sum hf hfc s w t 0]
    congr 1
    · refine Finset.sum_congr rfl fun i _ => by rw [sub_neg_eq_add]
    · refine Finset.sum_congr rfl fun i _ => by rw [sub_zero]
  set C := ∑ i ∈ s, ∑ j ∈ s, w i * w j * autocorr f (t i - t j)
  set A := autocorr f 0 - autocorr f y
  set B := ∑ i ∈ s, w i * autocorr f (t i + y) - ∑ i ∈ s, w i * autocorr f (t i)
  have hC_nn : 0 ≤ C := autocorr_gram_quad_nonneg hf hfc s w t
  have hA_nn : 0 ≤ A := autocorr_sub_nonneg hfc hf y
  have hB_sq : B ^ 2 ≤ 2 * C * A := by
    change (∫ u, P u * D u) ^ 2 ≤ (∫ u, P u ^ 2) * ∫ u, D u ^ 2 at hcs
    rw [hint_P2, hint_D2, hint_PD] at hcs
    linarith only [hcs]
  have hB_le_sqrt : B ≤ Real.sqrt (2 * C * A) := by
    refine le_trans (le_abs_self B) ?_
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt hB_sq
  have hyoung := signed_collar_young_bound (w := 1) hW₀ hC_nn hA_nn
  have hB_expand :
      B = (∑ i ∈ s, w i) * autocorr f 0 -
        (∑ i ∈ s, w i * (autocorr f 0 - autocorr f (t i + y))) -
        ∑ i ∈ s, w i * autocorr f (t i) := by
    dsimp [B]
    have h1 :
        (∑ i ∈ s, w i) * autocorr f 0 -
            (∑ i ∈ s, w i * (autocorr f 0 - autocorr f (t i + y))) =
          ∑ i ∈ s, w i * autocorr f (t i + y) := by
      rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [h1]
  linarith only [hB_le_sqrt, hyoung, hB_expand]

/-- **Unconditional Multi-Node Signed Collar Off-Diagonal Inequality
(`autocorr_multi_node_signed_collar_offDiag_ge`):**
For EVERY `[DecidableEq ι]`, continuous compactly supported `f : ℝ → ℝ`, `s : Finset ι`,
`w t : ι → ℝ`, `W₀ > 0`, and `y ∈ ℝ` (with **zero** blindness or orthogonality hypotheses):
$$\left(\sum_{i \in s} w_i - \frac{\sum_{i \in s} w_i^2}{2 W_0}\right) \operatorname{autocorr}(f, 0)$$
$$\le\; W_0\bigl(\operatorname{autocorr}(f, 0) - \operatorname{autocorr}(f, y)\bigr)
  + \sum_{i \in s} w_i\bigl(\operatorname{autocorr}(f, 0) - \operatorname{autocorr}(f, t_i + y)\bigr)$$
$$+\; \sum_{i \in s} w_i\,\operatorname{autocorr}(f, t_i)
  + \frac{1}{2 W_0} \sum_{i \in s} \sum_{j \in s.\mathrm{erase}\,i} w_i\,w_j\,\operatorname{autocorr}(f, t_i - t_j).$$ -/
theorem autocorr_multi_node_signed_collar_offDiag_ge [DecidableEq ι]
    (hfc : HasCompactSupport f) (hf : Continuous f)
    (s : Finset ι) (w t : ι → ℝ) {W₀ : ℝ} (hW₀ : 0 < W₀) (y : ℝ) :
    (∑ i ∈ s, w i - (∑ i ∈ s, w i ^ 2) / (2 * W₀)) * autocorr f 0 ≤
      W₀ * (autocorr f 0 - autocorr f y) +
        ∑ i ∈ s, w i * (autocorr f 0 - autocorr f (t i + y)) +
        ∑ i ∈ s, w i * autocorr f (t i) +
        (1 / (2 * W₀)) *
          ∑ i ∈ s, ∑ j ∈ s.erase i, w i * w j * autocorr f (t i - t j) := by
  have hbase := autocorr_multi_node_signed_collar_gram_ge hfc hf s w t hW₀ y
  rw [autocorr_gram_quad_eq_diag_add_offDiag f s w t] at hbase
  have hring :
      (∑ i ∈ s, w i - (∑ i ∈ s, w i ^ 2) / (2 * W₀)) * autocorr f 0 =
        (∑ i ∈ s, w i) * autocorr f 0 -
          (1 / (2 * W₀)) * ((∑ i ∈ s, w i ^ 2) * autocorr f 0) := by
    ring
  linarith only [hbase, hring]

/-! ## §3. Dyadic Coset Difference Invariance & Unconditional Explicit-Formula Synthesis -/

/-- **The `k`-th Node of the `(m + 1)`-th Dyadic Logarithmic Coset:**
$$\operatorname{dyadicCosetNode}(m, k) := \log\bigl(((m + 1) \cdot 2^{k + 1} : \mathbb{N})\bigr).$$ -/
def dyadicCosetNode (m k : ℕ) : ℝ :=
  Real.log (((m + 1) * 2 ^ (k + 1) : ℕ) : ℝ)

/-- **Coset-Invariance of Dyadic Node Differences (`dyadicCosetNode_sub_eq`):**
For every coset index `m : ℕ` and every pair of chain indices `i, j : ℕ`, the difference
`dyadicCosetNode m i - dyadicCosetNode m j` is **independent of `m`**:
$$\operatorname{dyadicCosetNode}(m, i) - \operatorname{dyadicCosetNode}(m, j)
  = \bigl((i : \mathbb{R}) - (j : \mathbb{R})\bigr)\,\log 2.$$ -/
theorem dyadicCosetNode_sub_eq (m i j : ℕ) :
    dyadicCosetNode m i - dyadicCosetNode m j = ((i : ℝ) - (j : ℝ)) * Real.log 2 := by
  unfold dyadicCosetNode
  have hm_pos : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hi_pos : (0 : ℝ) < (2 : ℝ) ^ (i + 1) := by positivity
  have hj_pos : (0 : ℝ) < (2 : ℝ) ^ (j + 1) := by positivity
  push_cast
  rw [Real.log_mul hm_pos.ne' hi_pos.ne', Real.log_mul hm_pos.ne' hj_pos.ne',
    Real.log_pow, Real.log_pow]
  push_cast
  ring

/-- **Prime-`2`-Power Reduction of Dyadic Coset Autocorrelation Differences (`autocorr_dyadicCosetNode_sub_eq`):**
For EVERY `f : ℝ → ℝ`, EVERY coset index `m : ℕ`, and EVERY `i, j : ℕ`, the off-diagonal
autocorrelation between `dyadicCosetNode m i` and `dyadicCosetNode m j` depends **only** on the
prime-`2` power `2^{max i j - min i j}` and is independent of `m`:
$$\operatorname{autocorr}\bigl(f, \operatorname{dyadicCosetNode}(m, i) - \operatorname{dyadicCosetNode}(m, j)\bigr)
  = \operatorname{autocorr}\bigl(f, \log(2^{\max(i, j) - \min(i, j)})\bigr).$$ -/
theorem autocorr_dyadicCosetNode_sub_eq (f : ℝ → ℝ) (m i j : ℕ) :
    autocorr f (dyadicCosetNode m i - dyadicCosetNode m j) =
      autocorr f (Real.log ((2 ^ (max i j - min i j) : ℕ) : ℝ)) := by
  rw [dyadicCosetNode_sub_eq]
  push_cast
  rw [Real.log_pow]
  rcases le_total i j with hij | hji
  · have hmax : max i j = j := max_eq_right hij
    have hmin : min i j = i := min_eq_left hij
    rw [hmax, hmin, Nat.cast_sub hij,
      show ((i : ℝ) - (j : ℝ)) * Real.log 2 = -(((j : ℝ) - (i : ℝ)) * Real.log 2) by ring,
      autocorr_neg]
  · have hmax : max i j = i := max_eq_left hji
    have hmin : min i j = j := min_eq_right hji
    rw [hmax, hmin, Nat.cast_sub hji]

/-- **Unconditional Multi-Node Signed Collar Bound on `RealEvenPolarTestFn`
(`RealEvenPolarTestFn.unconditional_multi_node_signed_collar_offDiag_bound`):**
For EVERY `g : RealEvenPolarTestFn`, EVERY finite index set `s : Finset ℕ`, EVERY weight/node
maps `w t : ℕ → ℝ`, and EVERY `c y : ℝ` (with **zero hypotheses**!), testing at positive origin
weight `W₀ = exp c > 0` yields:
$$\left(\sum_{i \in s} w_i - \frac{\sum_{i \in s} w_i^2}{2 e^c}\right) (\operatorname{weilTest}\,g\,g\,0).\mathrm{re}$$
$$\le\; e^c\bigl((\operatorname{weilTest}\,g\,g\,0).\mathrm{re} - (\operatorname{weilTest}\,g\,g\,y).\mathrm{re}\bigr)
  + \sum_{i \in s} w_i\bigl((\operatorname{weilTest}\,g\,g\,0).\mathrm{re} - (\operatorname{weilTest}\,g\,g\,(t_i + y)).\mathrm{re}\bigr)$$
$$+\; \sum_{i \in s} w_i\,(\operatorname{weilTest}\,g\,g\,(t_i)).\mathrm{re}
  + \frac{1}{2 e^c} \sum_{i \in s} \sum_{j \in s.\mathrm{erase}\,i} w_i\,w_j\,
    (\operatorname{weilTest}\,g\,g\,(t_i - t_j)).\mathrm{re}.$$ -/
theorem RealEvenPolarTestFn.unconditional_multi_node_signed_collar_offDiag_bound
    (g : RealEvenPolarTestFn) (s : Finset ℕ) (w t : ℕ → ℝ) (c y : ℝ) :
    (∑ i ∈ s, w i - (∑ i ∈ s, w i ^ 2) / (2 * Real.exp c)) *
        (EF.weilTest g.1.1.1 g.1.1.1 0).re ≤
      Real.exp c *
          ((EF.weilTest g.1.1.1 g.1.1.1 0).re - (EF.weilTest g.1.1.1 g.1.1.1 y).re) +
        (∑ i ∈ s,
          w i * ((EF.weilTest g.1.1.1 g.1.1.1 0).re -
            (EF.weilTest g.1.1.1 g.1.1.1 (t i + y)).re)) +
        (∑ i ∈ s, w i * (EF.weilTest g.1.1.1 g.1.1.1 (t i)).re) +
        (1 / (2 * Real.exp c)) *
          ∑ i ∈ s, ∑ j ∈ s.erase i,
            w i * w j * (EF.weilTest g.1.1.1 g.1.1.1 (t i - t j)).re := by
  have hbase := autocorr_multi_node_signed_collar_offDiag_ge
    g.hasCompactSupport_source g.contDiff_source.continuous s w t (Real.exp_pos c) y
  simp_rw [g.autocorr_eq] at hbase
  exact hbase

/-- **Unconditional Dyadic-Coset Multi-Node Signed Collar Bound on `RealEvenPolarTestFn`
(`RealEvenPolarTestFn.unconditional_dyadic_coset_multi_node_signed_collar_bound`):**
For EVERY `g : RealEvenPolarTestFn`, EVERY coset index `m : ℕ`, EVERY chain length `K : ℕ`,
EVERY weight family `w : ℕ → ℝ`, and EVERY `c y : ℝ` (with **zero hypotheses**!), the `K` nodes
`dyadicCosetNode m i = log((m + 1) · 2^{i + 1})` (`0 ≤ i < K`) satisfy:
$$\left(\sum_{i=0}^{K-1} w_i - \frac{\sum_{i=0}^{K-1} w_i^2}{2 e^c}\right) (\operatorname{weilTest}\,g\,g\,0).\mathrm{re}$$
$$\le\; e^c\bigl((\operatorname{weilTest}\,g\,g\,0).\mathrm{re} - (\operatorname{weilTest}\,g\,g\,y).\mathrm{re}\bigr)$$
$$+\; \sum_{i=0}^{K-1} w_i\bigl((\operatorname{weilTest}\,g\,g\,0).\mathrm{re}
  - (\operatorname{weilTest}\,g\,g\,(\operatorname{dyadicCosetNode}(m, i) + y)).\mathrm{re}\bigr)$$
$$+\; \sum_{i=0}^{K-1} w_i\,(\operatorname{weilTest}\,g\,g\,(\operatorname{dyadicCosetNode}(m, i))).\mathrm{re}$$
$$+\; \frac{1}{2 e^c} \sum_{i \in \operatorname{range} K} \sum_{j \in (\operatorname{range} K).\mathrm{erase}\,i}
  w_i\,w_j\,(\operatorname{weilTest}\,g\,g\,(\log(2^{\max(i, j) - \min(i, j)}))).\mathrm{re}.$$ -/
theorem RealEvenPolarTestFn.unconditional_dyadic_coset_multi_node_signed_collar_bound
    (g : RealEvenPolarTestFn) (m K : ℕ) (w : ℕ → ℝ) (c y : ℝ) :
    (∑ i ∈ Finset.range K, w i - (∑ i ∈ Finset.range K, w i ^ 2) / (2 * Real.exp c)) *
        (EF.weilTest g.1.1.1 g.1.1.1 0).re ≤
      Real.exp c *
          ((EF.weilTest g.1.1.1 g.1.1.1 0).re - (EF.weilTest g.1.1.1 g.1.1.1 y).re) +
        (∑ i ∈ Finset.range K,
          w i * ((EF.weilTest g.1.1.1 g.1.1.1 0).re -
            (EF.weilTest g.1.1.1 g.1.1.1 (dyadicCosetNode m i + y)).re)) +
        (∑ i ∈ Finset.range K,
          w i * (EF.weilTest g.1.1.1 g.1.1.1 (dyadicCosetNode m i)).re) +
        (1 / (2 * Real.exp c)) *
          ∑ i ∈ Finset.range K, ∑ j ∈ (Finset.range K).erase i,
            w i * w j *
              (EF.weilTest g.1.1.1 g.1.1.1
                (Real.log ((2 ^ (max i j - min i j) : ℕ) : ℝ))).re := by
  have hbase := autocorr_multi_node_signed_collar_offDiag_ge
    g.hasCompactSupport_source g.contDiff_source.continuous
    (Finset.range K) w (dyadicCosetNode m) (Real.exp_pos c) y
  have hoff :
      (∑ i ∈ Finset.range K, ∑ j ∈ (Finset.range K).erase i,
          w i * w j * autocorr g.source (dyadicCosetNode m i - dyadicCosetNode m j)) =
        ∑ i ∈ Finset.range K, ∑ j ∈ (Finset.range K).erase i,
          w i * w j * autocorr g.source (Real.log ((2 ^ (max i j - min i j) : ℕ) : ℝ)) := by
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [autocorr_dyadicCosetNode_sub_eq]
  rw [hoff] at hbase
  simp_rw [g.autocorr_eq] at hbase
  exact hbase

/-- **Unconditional Dyadic-Coset Multi-Node Signed Collar Bound on `RealSmoothEvenPolarTestFn`:** -/
theorem RealSmoothEvenPolarTestFn.unconditional_dyadic_coset_multi_node_signed_collar_bound
    (g : RealSmoothEvenPolarTestFn) (m K : ℕ) (w : ℕ → ℝ) (c y : ℝ) :
    (∑ i ∈ Finset.range K, w i - (∑ i ∈ Finset.range K, w i ^ 2) / (2 * Real.exp c)) *
        (EF.weilTest g.1.1.1.1 g.1.1.1.1 0).re ≤
      Real.exp c *
          ((EF.weilTest g.1.1.1.1 g.1.1.1.1 0).re -
            (EF.weilTest g.1.1.1.1 g.1.1.1.1 y).re) +
        (∑ i ∈ Finset.range K,
          w i * ((EF.weilTest g.1.1.1.1 g.1.1.1.1 0).re -
            (EF.weilTest g.1.1.1.1 g.1.1.1.1 (dyadicCosetNode m i + y)).re)) +
        (∑ i ∈ Finset.range K,
          w i * (EF.weilTest g.1.1.1.1 g.1.1.1.1 (dyadicCosetNode m i)).re) +
        (1 / (2 * Real.exp c)) *
          ∑ i ∈ Finset.range K, ∑ j ∈ (Finset.range K).erase i,
            w i * w j *
              (EF.weilTest g.1.1.1.1 g.1.1.1.1
                (Real.log ((2 ^ (max i j - min i j) : ℕ) : ℝ))).re :=
  RealEvenPolarTestFn.unconditional_dyadic_coset_multi_node_signed_collar_bound
    g.toRealEvenPolar m K w c y

end

end GaloisForLFunctions.BiScaleUncertainty
