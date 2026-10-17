import GaloisForLFunctions.BiScaleUncertainty.OddSectorAndPrimitiveHyperplaneBiScaleSynthesis

/-!
# Pillar XXVI: Unconditional Integrated Multi-Node & Dyadic-Coset Weil Coercivity

This module develops **Pillar XXVI** of **Bi-Scale / Logarithmic-Grid Uncertainty Theory**
(`GaloisForLFunctions.BiScaleUncertainty`), integrating the non-orthogonal multi-node signed Gram
collar inequalities of Pillar XXIV (`MultiNodeSignedCliqueWeilCoercivity`) across continuum collars
`[0, δ]` and shifted node collars `[t_i, t_i + δ]`, and synthesizing them unconditionally with the
explicit-formula spaces `RealEvenPolarTestFn`, `RealSmoothEvenPolarTestFn`, `RealWeilTestFn`,
`RealOddTestFn`, and `RealHyperplaneGenerator`.

## Why Integrated Multi-Node Collar Sharing Beats Single-Node Summation

When $K$ single-node collar bounds are summed independently (as in Pillar XVIII or XX), each of the
$K$ nodes consumes its own origin collar charge $W_{0, i} \int_0^\delta (h_f(0) - h_f(y))\,dy$,
forcing $\sum_{i=0}^{K-1} W_{0, i}$ to be shared across the origin budget.

By contrast, in `integral_multi_node_signed_collar_offDiag_ge` below, Cauchy–Schwarz is applied to
the **coherent sum of shifts** $P(u) = \sum_{i \in s} w_i\,f(u + t_i)$ against a **single** origin
difference $D_y(u) = f(u - y) - f(u)$, and then integrated over $y \in [0, \delta]$. Consequently:
1. All $K$ nodes in `s` share a **single** origin collar integral
   $W_0 \int_0^\delta (h_f(0) - h_f(y))\,dy$ without dividing $W_0$ by $K$!
2. Each node $t_i$ contributes its shifted collar integral
   $w_i \int_{t_i}^{t_i + \delta} (h_f(0) - h_f(x))\,dx$ plus its signed node correlation
   $\delta\,w_i\,h_f(t_i)$.
3. The price of sharing a single origin collar across $K$ nodes without dividing $W_0$ by $K$ is
   recorded **exact and unconditionally** by the off-diagonal Gram interaction sum
   $$\frac{\delta}{2 W_0} \sum_{i \in s} \sum_{j \in s.\mathrm{erase}\,i} w_i\,w_j\,h_f(t_i - t_j),$$
   which for any dyadic coset $t_k = \log((m + 1) \cdot 2^{k + 1})$ reduces unconditionally to
   prime-$2$-power correlations $h_f(\log(2^{\max(i, j) - \min(i, j)}))$ independent of $m$.
-/

open Complex MeasureTheory Set Filter Topology
open Zeta23
open RHTower RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole
open RHTower.EvenSector RHTower.WeilOneSided
open scoped RealInnerProductSpace BigOperators

namespace GaloisForLFunctions.BiScaleUncertainty

noncomputable section

variable {f : ℝ → ℝ} {ι : Type*}

/-! ## §1. Unconditional Integrated Multi-Node Signed Collar Inequalities -/

/-- **Unconditional Integrated Multi-Node Signed Collar Inequality
(`integral_multi_node_signed_collar_offDiag_ge`):**
For EVERY `[DecidableEq ι]`, `f ∈ C²_c(ℝ)`, finite set `s : Finset ι`, weight/node maps
`w t : ι → ℝ`, `W₀ > 0`, and collar width `δ ≥ 0` (with **zero** blindness or orthogonality
hypotheses):
$$\delta\left(\sum_{i \in s} w_i - \frac{\sum_{i \in s} w_i^2}{2 W_0}\right) h_f(0)$$
$$\le\; W_0 \int_0^\delta \bigl(h_f(0) - h_f(y)\bigr)\,dy
  + \sum_{i \in s} w_i \int_{t_i}^{t_i + \delta} \bigl(h_f(0) - h_f(x)\bigr)\,dx$$
$$+\; \delta \sum_{i \in s} w_i\,h_f(t_i)
  + \frac{\delta}{2 W_0} \sum_{i \in s} \sum_{j \in s.\mathrm{erase}\,i} w_i\,w_j\,h_f(t_i - t_j).$$ -/
theorem integral_multi_node_signed_collar_offDiag_ge [DecidableEq ι]
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (s : Finset ι) (w t : ι → ℝ) {W₀ δ : ℝ} (hW₀ : 0 < W₀) (hδ : 0 ≤ δ) :
    δ * ((∑ i ∈ s, w i - (∑ i ∈ s, w i ^ 2) / (2 * W₀)) * autocorr f 0) ≤
      W₀ * (∫ y in (0 : ℝ)..δ, (autocorr f 0 - autocorr f y)) +
        (∑ i ∈ s, w i * (∫ x in t i..(t i + δ), (autocorr f 0 - autocorr f x))) +
        δ * (∑ i ∈ s, w i * autocorr f (t i)) +
        (δ / (2 * W₀)) *
          ∑ i ∈ s, ∑ j ∈ s.erase i, w i * w j * autocorr f (t i - t j) := by
  have hc : Continuous (autocorr f) := continuous_autocorr hf hfc
  set C_lhs := (∑ i ∈ s, w i - (∑ i ∈ s, w i ^ 2) / (2 * W₀)) * autocorr f 0
  set C_diag := ∑ i ∈ s, w i * autocorr f (t i)
  set C_off := (1 / (2 * W₀)) *
    ∑ i ∈ s, ∑ j ∈ s.erase i, w i * w j * autocorr f (t i - t j)
  have hint_lhs : IntervalIntegrable (fun _ : ℝ => C_lhs) volume 0 δ :=
    intervalIntegrable_const
  have hint_orig : IntervalIntegrable
      (fun y : ℝ => W₀ * (autocorr f 0 - autocorr f y)) volume 0 δ :=
    (continuous_const.mul (continuous_const.sub hc)).intervalIntegrable 0 δ
  have hint_shift_term (i : ι) : IntervalIntegrable
      (fun y : ℝ => w i * (autocorr f 0 - autocorr f (t i + y))) volume 0 δ :=
    (continuous_const.mul
      (continuous_const.sub (hc.comp (continuous_const.add continuous_id)))).intervalIntegrable 0 δ
  have hint_shift : IntervalIntegrable
      (fun y : ℝ => ∑ i ∈ s, w i * (autocorr f 0 - autocorr f (t i + y))) volume 0 δ :=
    (continuous_finsetSum s fun i _ =>
      continuous_const.mul
        (continuous_const.sub (hc.comp (continuous_const.add continuous_id)))).intervalIntegrable 0 δ
  have hint_diag : IntervalIntegrable (fun _ : ℝ => C_diag) volume 0 δ :=
    intervalIntegrable_const
  have hint_off : IntervalIntegrable (fun _ : ℝ => C_off) volume 0 δ :=
    intervalIntegrable_const
  have hmono := intervalIntegral.integral_mono_on hδ hint_lhs
    (((hint_orig.add hint_shift).add hint_diag).add hint_off)
    (fun y _ => autocorr_multi_node_signed_collar_offDiag_ge hfc hf.continuous s w t hW₀ y)
  rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at hmono
  rw [intervalIntegral.integral_add ((hint_orig.add hint_shift).add hint_diag) hint_off,
    intervalIntegral.integral_add (hint_orig.add hint_shift) hint_diag,
    intervalIntegral.integral_add hint_orig hint_shift,
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const, smul_eq_mul, sub_zero,
    intervalIntegral.integral_const, smul_eq_mul, sub_zero,
    intervalIntegral.integral_finsetSum (fun i _ => hint_shift_term i)] at hmono
  have hshifts :
      (∑ i ∈ s, ∫ y in (0 : ℝ)..δ, w i * (autocorr f 0 - autocorr f (t i + y))) =
        ∑ i ∈ s, w i * (∫ x in t i..(t i + δ), (autocorr f 0 - autocorr f x)) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral_collar_shift (fun x : ℝ => autocorr f 0 - autocorr f x) (t i) δ]
  rw [hshifts] at hmono
  have hring : δ * C_off =
      (δ / (2 * W₀)) * ∑ i ∈ s, ∑ j ∈ s.erase i, w i * w j * autocorr f (t i - t j) := by
    dsimp [C_off]
    ring
  linarith only [hmono, hring]

/-! ## §2. Unconditional Archimedean Lévy Domination on Origin & Shifted Collars -/

/-- **Unconditional Origin-Collar Lévy Domination (`origin_collar_integral_le_biScaleLevyEnergy`):**
For EVERY `f ∈ C²_c(ℝ)` and EVERY `d : ℝ` (setting width `δ = exp d > 0` so positivity holds
unconditionally), since `archLevySinhWeight y ≥ archLevySinhWeight (exp d) > 0` on `(0, exp d]`,
$$\operatorname{archLevySinhWeight}(e^d) \int_0^{e^d} \bigl(h_f(0) - h_f(y)\bigr)\,dy
  \;\le\; \operatorname{biScaleLevyEnergy}(f).$$ -/
theorem origin_collar_integral_le_biScaleLevyEnergy
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (d : ℝ) :
    archLevySinhWeight (Real.exp d) *
        (∫ y in (0 : ℝ)..Real.exp d, (autocorr f 0 - autocorr f y)) ≤
      biScaleLevyEnergy f := by
  have hc : Continuous (autocorr f) := continuous_autocorr hf hfc
  set δ := Real.exp d
  have hδ_pos : 0 < δ := Real.exp_pos d
  rw [← intervalIntegral.integral_const_mul, intervalIntegral.integral_of_le hδ_pos.le]
  have hint_levy := integrableOn_biScaleLevyIntegrand hf hfc
  have hint_lhs : IntegrableOn
      (fun y : ℝ => archLevySinhWeight δ * (autocorr f 0 - autocorr f y)) (Ioc 0 δ) :=
    ((continuous_const.mul (continuous_const.sub hc)).integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have hint_rhs : IntegrableOn
      (fun y : ℝ => (autocorr f 0 - autocorr f y) * archLevySinhWeight y) (Ioc 0 δ) :=
    hint_levy.mono_set (fun _ hy => hy.1)
  have h1 :
      (∫ y in Ioc 0 δ, archLevySinhWeight δ * (autocorr f 0 - autocorr f y)) ≤
        ∫ y in Ioc 0 δ, (autocorr f 0 - autocorr f y) * archLevySinhWeight y := by
    refine setIntegral_mono_ae_restrict hint_lhs hint_rhs ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
    have hw := archLevySinhWeight_antitoneOn hy.1 hy.2
    have hD := autocorr_sub_nonneg hfc hf.continuous y
    calc
      archLevySinhWeight δ * (autocorr f 0 - autocorr f y)
          = (autocorr f 0 - autocorr f y) * archLevySinhWeight δ := mul_comm _ _
      _ ≤ (autocorr f 0 - autocorr f y) * archLevySinhWeight y :=
        mul_le_mul_of_nonneg_left hw hD
  have h2 :
      (∫ y in Ioc 0 δ, (autocorr f 0 - autocorr f y) * archLevySinhWeight y) ≤
        biScaleLevyEnergy f := by
    unfold biScaleLevyEnergy
    refine setIntegral_mono_set hint_levy ?_ ?_
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
      exact mul_nonneg (autocorr_sub_nonneg hfc hf.continuous y) (archLevySinhWeight_pos hy).le
    · exact Eventually.of_forall fun y hy => hy.1
  exact le_trans h1 h2

/-- **Unconditional Shifted-Collar Lévy Domination (`shifted_collar_integral_le_biScaleLevyEnergy`):**
For EVERY `f ∈ C²_c(ℝ)`, every node `t > 0`, and every `d : ℝ` (`δ = exp d > 0`),
$$\operatorname{archLevySinhWeight}(t + e^d) \int_t^{t + e^d} \bigl(h_f(0) - h_f(x)\bigr)\,dx
  \;\le\; \operatorname{biScaleLevyEnergy}(f).$$ -/
theorem shifted_collar_integral_le_biScaleLevyEnergy
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) {t : ℝ} (ht : 0 < t) (d : ℝ) :
    archLevySinhWeight (t + Real.exp d) *
        (∫ x in t..(t + Real.exp d), (autocorr f 0 - autocorr f x)) ≤
      biScaleLevyEnergy f := by
  have hc : Continuous (autocorr f) := continuous_autocorr hf hfc
  set δ := Real.exp d
  have hδ_pos : 0 < δ := Real.exp_pos d
  have hle : t ≤ t + δ := le_add_of_nonneg_right hδ_pos.le
  rw [← intervalIntegral.integral_const_mul, intervalIntegral.integral_of_le hle]
  have hint_levy := integrableOn_biScaleLevyIntegrand hf hfc
  have hint_lhs : IntegrableOn
      (fun x : ℝ => archLevySinhWeight (t + δ) * (autocorr f 0 - autocorr f x))
      (Ioc t (t + δ)) :=
    ((continuous_const.mul (continuous_const.sub hc)).integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have hint_rhs : IntegrableOn
      (fun x : ℝ => (autocorr f 0 - autocorr f x) * archLevySinhWeight x)
      (Ioc t (t + δ)) :=
    hint_levy.mono_set (fun _ hx => lt_trans ht hx.1)
  have h1 :
      (∫ x in Ioc t (t + δ), archLevySinhWeight (t + δ) * (autocorr f 0 - autocorr f x)) ≤
        ∫ x in Ioc t (t + δ), (autocorr f 0 - autocorr f x) * archLevySinhWeight x := by
    refine setIntegral_mono_ae_restrict hint_lhs hint_rhs ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    have hx_pos : 0 < x := lt_trans ht hx.1
    have hw := archLevySinhWeight_antitoneOn hx_pos hx.2
    have hD := autocorr_sub_nonneg hfc hf.continuous x
    calc
      archLevySinhWeight (t + δ) * (autocorr f 0 - autocorr f x)
          = (autocorr f 0 - autocorr f x) * archLevySinhWeight (t + δ) := mul_comm _ _
      _ ≤ (autocorr f 0 - autocorr f x) * archLevySinhWeight x :=
        mul_le_mul_of_nonneg_left hw hD
  have h2 :
      (∫ x in Ioc t (t + δ), (autocorr f 0 - autocorr f x) * archLevySinhWeight x) ≤
        biScaleLevyEnergy f := by
    unfold biScaleLevyEnergy
    refine setIntegral_mono_set hint_levy ?_ ?_
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      exact mul_nonneg (autocorr_sub_nonneg hfc hf.continuous x) (archLevySinhWeight_pos hx).le
    · exact Eventually.of_forall fun x hx => lt_trans ht hx.1
  exact le_trans h1 h2

/-! ## §3. Unconditional Integrated Dyadic-Coset Multi-Node Bounds Across All Sectors -/

/-- **Unconditional Integrated Dyadic-Coset Multi-Node Signed Collar Bound (`C²_c(ℝ)` form):**
For EVERY `f ∈ C²_c(ℝ)`, EVERY coset index `m : ℕ`, EVERY chain length `K : ℕ`, EVERY weight
family `w : ℕ → ℝ`, and EVERY `c d : ℝ` (with **zero hypotheses**!), testing at origin weight
`W₀ = exp c > 0` and collar width `δ = exp d > 0` yields: -/
theorem dyadic_coset_integrated_multi_node_signed_collar_ge
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (m K : ℕ) (w : ℕ → ℝ) (c d : ℝ) :
    Real.exp d *
        ((∑ i ∈ Finset.range K, w i - (∑ i ∈ Finset.range K, w i ^ 2) / (2 * Real.exp c)) *
          autocorr f 0) ≤
      Real.exp c * (∫ y in (0 : ℝ)..Real.exp d, (autocorr f 0 - autocorr f y)) +
        (∑ i ∈ Finset.range K,
          w i * (∫ x in dyadicCosetNode m i..(dyadicCosetNode m i + Real.exp d),
            (autocorr f 0 - autocorr f x))) +
        Real.exp d * (∑ i ∈ Finset.range K, w i * autocorr f (dyadicCosetNode m i)) +
        (Real.exp d / (2 * Real.exp c)) *
          ∑ i ∈ Finset.range K, ∑ j ∈ (Finset.range K).erase i,
            w i * w j * autocorr f (Real.log ((2 ^ (max i j - min i j) : ℕ) : ℝ)) := by
  have hbase := integral_multi_node_signed_collar_offDiag_ge hf hfc
    (Finset.range K) w (dyadicCosetNode m) (Real.exp_pos c) (Real.exp_pos d).le
  have hoff :
      (∑ i ∈ Finset.range K, ∑ j ∈ (Finset.range K).erase i,
          w i * w j * autocorr f (dyadicCosetNode m i - dyadicCosetNode m j)) =
        ∑ i ∈ Finset.range K, ∑ j ∈ (Finset.range K).erase i,
          w i * w j * autocorr f (Real.log ((2 ^ (max i j - min i j) : ℕ) : ℝ)) := by
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [autocorr_dyadicCosetNode_sub_eq]
  rw [hoff] at hbase
  exact hbase

/-- **Unconditional Integrated Dyadic-Coset Multi-Node Signed Collar Bound on `RealEvenPolarTestFn`:**
For EVERY `g : RealEvenPolarTestFn`, `m K : ℕ`, `w : ℕ → ℝ`, and `c d : ℝ` (with **zero
hypotheses**!): -/
theorem RealEvenPolarTestFn.unconditional_dyadic_coset_integrated_multi_node_signed_collar_bound
    (g : RealEvenPolarTestFn) (m K : ℕ) (w : ℕ → ℝ) (c d : ℝ) :
    Real.exp d *
        ((∑ i ∈ Finset.range K, w i - (∑ i ∈ Finset.range K, w i ^ 2) / (2 * Real.exp c)) *
          (EF.weilTest g.1.1.1 g.1.1.1 0).re) ≤
      Real.exp c *
          (∫ y in (0 : ℝ)..Real.exp d,
            ((EF.weilTest g.1.1.1 g.1.1.1 0).re - (EF.weilTest g.1.1.1 g.1.1.1 y).re)) +
        (∑ i ∈ Finset.range K,
          w i * (∫ x in dyadicCosetNode m i..(dyadicCosetNode m i + Real.exp d),
            ((EF.weilTest g.1.1.1 g.1.1.1 0).re - (EF.weilTest g.1.1.1 g.1.1.1 x).re))) +
        Real.exp d *
          (∑ i ∈ Finset.range K,
            w i * (EF.weilTest g.1.1.1 g.1.1.1 (dyadicCosetNode m i)).re) +
        (Real.exp d / (2 * Real.exp c)) *
          ∑ i ∈ Finset.range K, ∑ j ∈ (Finset.range K).erase i,
            w i * w j *
              (EF.weilTest g.1.1.1 g.1.1.1
                (Real.log ((2 ^ (max i j - min i j) : ℕ) : ℝ))).re := by
  have hbase := dyadic_coset_integrated_multi_node_signed_collar_ge
    g.contDiff_source g.hasCompactSupport_source m K w c d
  simp_rw [g.autocorr_eq] at hbase
  exact hbase

/-- **Unconditional Integrated Dyadic-Coset Multi-Node Signed Collar Bound on
`RealSmoothEvenPolarTestFn`:** -/
theorem RealSmoothEvenPolarTestFn.unconditional_dyadic_coset_integrated_multi_node_signed_collar_bound
    (g : RealSmoothEvenPolarTestFn) (m K : ℕ) (w : ℕ → ℝ) (c d : ℝ) :
    Real.exp d *
        ((∑ i ∈ Finset.range K, w i - (∑ i ∈ Finset.range K, w i ^ 2) / (2 * Real.exp c)) *
          (EF.weilTest g.1.1.1.1 g.1.1.1.1 0).re) ≤
      Real.exp c *
          (∫ y in (0 : ℝ)..Real.exp d,
            ((EF.weilTest g.1.1.1.1 g.1.1.1.1 0).re - (EF.weilTest g.1.1.1.1 g.1.1.1.1 y).re)) +
        (∑ i ∈ Finset.range K,
          w i * (∫ x in dyadicCosetNode m i..(dyadicCosetNode m i + Real.exp d),
            ((EF.weilTest g.1.1.1.1 g.1.1.1.1 0).re - (EF.weilTest g.1.1.1.1 g.1.1.1.1 x).re))) +
        Real.exp d *
          (∑ i ∈ Finset.range K,
            w i * (EF.weilTest g.1.1.1.1 g.1.1.1.1 (dyadicCosetNode m i)).re) +
        (Real.exp d / (2 * Real.exp c)) *
          ∑ i ∈ Finset.range K, ∑ j ∈ (Finset.range K).erase i,
            w i * w j *
              (EF.weilTest g.1.1.1.1 g.1.1.1.1
                (Real.log ((2 ^ (max i j - min i j) : ℕ) : ℝ))).re :=
  RealEvenPolarTestFn.unconditional_dyadic_coset_integrated_multi_node_signed_collar_bound
    g.toRealEvenPolar m K w c d

/-- **Unconditional Integrated Dyadic-Coset Multi-Node Signed Collar Bound on `RealWeilTestFn`:** -/
theorem RealWeilTestFn.unconditional_dyadic_coset_integrated_multi_node_signed_collar_bound
    (f : RealWeilTestFn) (m K : ℕ) (w : ℕ → ℝ) (c d : ℝ) :
    Real.exp d *
        ((∑ i ∈ Finset.range K, w i - (∑ i ∈ Finset.range K, w i ^ 2) / (2 * Real.exp c)) *
          (EF.weilTest f.1.1 f.1.1 0).re) ≤
      Real.exp c *
          (∫ y in (0 : ℝ)..Real.exp d,
            ((EF.weilTest f.1.1 f.1.1 0).re - (EF.weilTest f.1.1 f.1.1 y).re)) +
        (∑ i ∈ Finset.range K,
          w i * (∫ x in dyadicCosetNode m i..(dyadicCosetNode m i + Real.exp d),
            ((EF.weilTest f.1.1 f.1.1 0).re - (EF.weilTest f.1.1 f.1.1 x).re))) +
        Real.exp d *
          (∑ i ∈ Finset.range K,
            w i * (EF.weilTest f.1.1 f.1.1 (dyadicCosetNode m i)).re) +
        (Real.exp d / (2 * Real.exp c)) *
          ∑ i ∈ Finset.range K, ∑ j ∈ (Finset.range K).erase i,
            w i * w j *
              (EF.weilTest f.1.1 f.1.1
                (Real.log ((2 ^ (max i j - min i j) : ℕ) : ℝ))).re := by
  have hbase := dyadic_coset_integrated_multi_node_signed_collar_ge
    f.contDiff_source f.hasCompactSupport_source m K w c d
  simp_rw [f.autocorr_eq] at hbase
  exact hbase

/-- **Unconditional Integrated Dyadic-Coset Multi-Node Signed Collar Bound on `RealOddTestFn`:** -/
theorem RealOddTestFn.unconditional_dyadic_coset_integrated_multi_node_signed_collar_bound
    (f : RealOddTestFn) (m K : ℕ) (w : ℕ → ℝ) (c d : ℝ) :
    Real.exp d *
        ((∑ i ∈ Finset.range K, w i - (∑ i ∈ Finset.range K, w i ^ 2) / (2 * Real.exp c)) *
          (EF.weilTest f.1.1.1 f.1.1.1 0).re) ≤
      Real.exp c *
          (∫ y in (0 : ℝ)..Real.exp d,
            ((EF.weilTest f.1.1.1 f.1.1.1 0).re - (EF.weilTest f.1.1.1 f.1.1.1 y).re)) +
        (∑ i ∈ Finset.range K,
          w i * (∫ x in dyadicCosetNode m i..(dyadicCosetNode m i + Real.exp d),
            ((EF.weilTest f.1.1.1 f.1.1.1 0).re - (EF.weilTest f.1.1.1 f.1.1.1 x).re))) +
        Real.exp d *
          (∑ i ∈ Finset.range K,
            w i * (EF.weilTest f.1.1.1 f.1.1.1 (dyadicCosetNode m i)).re) +
        (Real.exp d / (2 * Real.exp c)) *
          ∑ i ∈ Finset.range K, ∑ j ∈ (Finset.range K).erase i,
            w i * w j *
              (EF.weilTest f.1.1.1 f.1.1.1
                (Real.log ((2 ^ (max i j - min i j) : ℕ) : ℝ))).re :=
  RealWeilTestFn.unconditional_dyadic_coset_integrated_multi_node_signed_collar_bound
    f.toRealWeilTestFn m K w c d

end

end GaloisForLFunctions.BiScaleUncertainty
