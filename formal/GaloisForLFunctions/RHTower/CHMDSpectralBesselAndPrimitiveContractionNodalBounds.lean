import GaloisForLFunctions.RHTower.CHMDEigenvectorCardinalReadoutAndFourTermNodalDecomposition

/-!
# Spectral Bessel Inequalities, Cardinal Spectral Deficit, and Primitive Contraction Nodal Bounds

This module builds on `CHMDEigenvectorCardinalReadoutAndFourTermNodalDecomposition` to establish:

1. **Exact Spectral Decomposition of `‖q.val.fst‖²`, `‖q.val.snd‖²`, and `‖q‖²` and Unconditional Edge/Graph Bessel Inequalities**:
   For any finite orthonormal family $\{w_i\}_{i=1}^m$ of eigenvectors
   $\operatorname{resolvent} w_i = \mu_i \cdot w_i$ ($\mu_i \ne 0$) and any $q \in \mathrm{SourceGraph}$:
   - $\|q.\mathrm{val}.\mathrm{fst}\|^2 = \sum_{i=1}^m \langle w_i, q.\mathrm{val}.\mathrm{fst}\rangle_{\mathbb{R}}^2 + \|(\operatorname{eigenGraphRem} \mu\,w\,q).\mathrm{val}.\mathrm{fst}\|^2$,
   - $\|q.\mathrm{val}.\mathrm{snd}\|^2 = \sum_{i=1}^m \frac{1 - \mu_i}{\mu_i}\,\langle w_i, q.\mathrm{val}.\mathrm{fst}\rangle_{\mathbb{R}}^2 + \|(\operatorname{eigenGraphRem} \mu\,w\,q).\mathrm{val}.\mathrm{snd}\|^2$,
   - $\|q\|^2 = \sum_{i=1}^m \frac{1}{\mu_i}\,\langle w_i, q.\mathrm{val}.\mathrm{fst}\rangle_{\mathbb{R}}^2 + \|\operatorname{eigenGraphRem} \mu\,w\,q\|^2$,
   yielding the unconditional edge and graph Bessel inequalities
   $$\sum_{i=1}^m \frac{1 - \mu_i}{\mu_i}\,\langle w_i, q.\mathrm{val}.\mathrm{fst}\rangle_{\mathbb{R}}^2 \le \|q.\mathrm{val}.\mathrm{snd}\|^2,
     \qquad
     \sum_{i=1}^m \frac{1}{\mu_i}\,\langle w_i, q.\mathrm{val}.\mathrm{fst}\rangle_{\mathbb{R}}^2 \le \|q\|^2.$$

2. **Odd-Polar Bessel Bound and Exact Cardinal Spectral Deficit at Nonreal $\Xi$-Zeros**:
   - Applying the graph Bessel inequality to `oddPolarVectorAt a ha` gives a shift-uniform upper
     bound on $\sum_{i=1}^m \frac{\mu_i}{(2\mu_i - 1)^2}\,\langle w_i, \operatorname{tanhL}\rangle_{\mathbb{R}}^2$.
   - Applying `sourceEnergy_eq_neg_sum_eigen_add_rem` to `F.imVector` for any nonreal $\Xi$-zero
     $a$ ($0 < \operatorname{Re}(a), \operatorname{Im}(a) \ne 0, \Xi(a) = 0$) gives the exact
     spectral deficit identity:
     $$\operatorname{cardinalOrbitMass}(a)^2 \sum_{i=1}^m \frac{\mu_i}{2\mu_i - 1}\,\bigl(\operatorname{Im}(\operatorname{massCosineReadout}(w_i, a))\bigr)^2
       = \operatorname{cardinalPositiveMass}(a) + \operatorname{sourceEnergy}(\operatorname{eigenGraphRem} \mu\,w\,(F.\mathrm{imVector})).$$

3. **Universal Rayleigh-to-Energy Lower Bound and Primitive Contraction Nodal Inequality**:
   - For every $q \in \mathrm{SourceGraph}$ and $\mu_{\max} > 0$,
     $\langle \operatorname{resolvent}(q.\mathrm{fst}), q.\mathrm{fst}\rangle_{\mathbb{R}} \le \mu_{\max}\,\|q.\mathrm{fst}\|^2$
     implies $\operatorname{sourceEnergy}(q) \ge -\frac{2\mu_{\max} - 1}{\mu_{\max}}\,\|q.\mathrm{fst}\|^2$.
   - Applying this to $q = \operatorname{primGraph}(\operatorname{absGraph} p)$ yields the universal
     nodal-cross / $L^1$-ground inequality:
     $$-\operatorname{sourceEnergy}(p) - 4\,\operatorname{sourcePair}(\operatorname{posGraph} p, \operatorname{negGraph} p)
       \le \frac{2\mu_{\max} - 1}{\mu_{\max}}\,\|p.\mathrm{val}.\mathrm{fst}\|^2
         + \frac{1 - \mu_{\max}}{\mu_{\max}} \cdot 2\,\langle (\operatorname{absGraph} p).\mathrm{val}.\mathrm{fst}, \operatorname{oneL}\rangle_{\mathbb{R}}^2,$$
     and for any eigenvector $p = \operatorname{rieszLift} v$ ($\operatorname{resolvent} v = \nu \cdot v$, $\nu > 0$):
     $$\frac{\nu - \mu_{\max}}{\nu \mu_{\max}}\,\|p.\mathrm{val}.\mathrm{fst}\|^2
       - 4\,\operatorname{sourcePair}(\operatorname{posGraph} p, \operatorname{negGraph} p)
       \le \frac{1 - \mu_{\max}}{\mu_{\max}} \cdot 2\,\langle (\operatorname{absGraph} p).\mathrm{val}.\mathrm{fst}, \operatorname{oneL}\rangle_{\mathbb{R}}^2.$$
-/

open MeasureTheory Set Filter Topology Complex Zeta23
open scoped InnerProductSpace BigOperators ComplexConjugate
noncomputable section

namespace RHTower.CHMDPolar
open CHMDDoobGraph CHMDClosedJump CHMDTranslation ThetaSourceWard

/-! ## Section 1: Exact Spectral Decomposition of `‖q.val.fst‖²`, `‖q.val.snd‖²`, and `‖q‖²` -/

theorem inner_eigenGraphProj_eigenGraphRem_fst {m : ℕ} {μ : Fin m → ℝ} {w : Fin m → MassSpace}
    (hμ : ∀ i, μ i ≠ 0) (hw : Orthonormal ℝ w) (heig : ∀ i, resolvent (w i) = μ i • w i)
    (p q : SourceGraph) :
    ⟪(eigenGraphProj μ w p).val.fst, (eigenGraphRem μ w q).val.fst⟫_ℝ = 0 := by
  rw [eigenGraphProj_fst hμ heig, sum_inner]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [real_inner_smul_left, inner_eigenGraphRem_fst hμ hw heig, mul_zero]

theorem norm_eigenGraphProj_fst_sq {m : ℕ} {μ : Fin m → ℝ} {w : Fin m → MassSpace}
    (hμ : ∀ i, μ i ≠ 0) (hw : Orthonormal ℝ w) (heig : ∀ i, resolvent (w i) = μ i • w i)
    (q : SourceGraph) :
    ‖(eigenGraphProj μ w q).val.fst‖ ^ 2 = ∑ i, ⟪w i, q.val.fst⟫_ℝ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, eigenGraphProj_fst hμ heig, hw.inner_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [conj_trivial, sq]

/-- **Pythagorean Decomposition of `‖q.val.fst‖ ^ 2` along a Finite Eigenvector Family**:
for any orthonormal family of eigenvectors `resolvent (w i) = μ i • w i` (`μ i ≠ 0`),
`‖q.val.fst‖ ^ 2 = ∑ i, ⟪w i, q.val.fst⟫_ℝ ^ 2 + ‖(eigenGraphRem μ w q).val.fst‖ ^ 2`. -/
theorem norm_fst_sq_eq_sum_eigen_add_rem {m : ℕ} {μ : Fin m → ℝ} {w : Fin m → MassSpace}
    (hμ : ∀ i, μ i ≠ 0) (hw : Orthonormal ℝ w) (heig : ∀ i, resolvent (w i) = μ i • w i)
    (q : SourceGraph) :
    ‖q.val.fst‖ ^ 2 =
      (∑ i, ⟪w i, q.val.fst⟫_ℝ ^ 2) + ‖(eigenGraphRem μ w q).val.fst‖ ^ 2 := by
  have hq : q.val.fst = (eigenGraphProj μ w q).val.fst + (eigenGraphRem μ w q).val.fst := by
    change q.val.fst = (eigenGraphProj μ w q).val.fst + (q.val.fst - (eigenGraphProj μ w q).val.fst)
    abel
  conv_lhs => rw [hq]
  rw [norm_add_sq_real, inner_eigenGraphProj_eigenGraphRem_fst hμ hw heig,
    mul_zero, add_zero, norm_eigenGraphProj_fst_sq hμ hw heig]

/-- **Exact Spectral-Gap Decomposition of Edge Energy `‖q.val.snd‖ ^ 2`**:
for any orthonormal family of eigenvectors `resolvent (w i) = μ i • w i` (`μ i ≠ 0`),
`‖q.val.snd‖ ^ 2 = ∑ i, ((1 - μ i) / μ i) * ⟪w i, q.val.fst⟫_ℝ ^ 2 + ‖(eigenGraphRem μ w q).val.snd‖ ^ 2`. -/
theorem norm_snd_sq_eq_sum_spectral_gap_add_rem {m : ℕ} {μ : Fin m → ℝ} {w : Fin m → MassSpace}
    (hμ : ∀ i, μ i ≠ 0) (hw : Orthonormal ℝ w) (heig : ∀ i, resolvent (w i) = μ i • w i)
    (q : SourceGraph) :
    ‖q.val.snd‖ ^ 2 =
      (∑ i, ((1 - μ i) / μ i) * ⟪w i, q.val.fst⟫_ℝ ^ 2) +
        ‖(eigenGraphRem μ w q).val.snd‖ ^ 2 := by
  have h1 : ‖q.val.snd‖ ^ 2 = sourceEnergy q + ‖q.val.fst‖ ^ 2 := by
    change ‖q.val.snd‖ ^ 2 = (‖q.val.snd‖ ^ 2 - ‖q.val.fst‖ ^ 2) + ‖q.val.fst‖ ^ 2
    ring
  have h2 : ‖(eigenGraphRem μ w q).val.snd‖ ^ 2 =
      sourceEnergy (eigenGraphRem μ w q) + ‖(eigenGraphRem μ w q).val.fst‖ ^ 2 := by
    change ‖(eigenGraphRem μ w q).val.snd‖ ^ 2 =
      (‖(eigenGraphRem μ w q).val.snd‖ ^ 2 - ‖(eigenGraphRem μ w q).val.fst‖ ^ 2) +
        ‖(eigenGraphRem μ w q).val.fst‖ ^ 2
    ring
  rw [h1, sourceEnergy_eq_neg_sum_eigen_add_rem hμ hw heig,
    norm_fst_sq_eq_sum_eigen_add_rem hμ hw heig, h2]
  have hsum : (-∑ i, ((2 * μ i - 1) / μ i) * ⟪w i, q.val.fst⟫_ℝ ^ 2) +
      (∑ i, ⟪w i, q.val.fst⟫_ℝ ^ 2) =
      ∑ i, ((1 - μ i) / μ i) * ⟪w i, q.val.fst⟫_ℝ ^ 2 := by
    rw [← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hi := hμ i
    field_simp [hi]
    ring
  linarith

/-- **Unconditional Edge Bessel Inequality for Resolvent Eigenvectors**:
for any orthonormal family of eigenvectors `resolvent (w i) = μ i • w i` (`μ i ≠ 0`) and any
`q : SourceGraph`,
`∑ i, ((1 - μ i) / μ i) * ⟪w i, q.val.fst⟫_ℝ ^ 2 ≤ ‖q.val.snd‖ ^ 2`. -/
theorem sum_spectral_gap_inner_sq_le_norm_snd_sq {m : ℕ} {μ : Fin m → ℝ} {w : Fin m → MassSpace}
    (hμ : ∀ i, μ i ≠ 0) (hw : Orthonormal ℝ w) (heig : ∀ i, resolvent (w i) = μ i • w i)
    (q : SourceGraph) :
    (∑ i, ((1 - μ i) / μ i) * ⟪w i, q.val.fst⟫_ℝ ^ 2) ≤ ‖q.val.snd‖ ^ 2 := by
  rw [norm_snd_sq_eq_sum_spectral_gap_add_rem hμ hw heig]
  linarith [sq_nonneg ‖(eigenGraphRem μ w q).val.snd‖]

/-- **Exact Spectral Decomposition of the `SourceGraph` Norm `‖q‖ ^ 2`**:
for any orthonormal family of eigenvectors `resolvent (w i) = μ i • w i` (`μ i ≠ 0`),
`‖q‖ ^ 2 = ∑ i, (1 / μ i) * ⟪w i, q.val.fst⟫_ℝ ^ 2 + ‖eigenGraphRem μ w q‖ ^ 2`. -/
theorem norm_graph_sq_eq_sum_inv_eigen_add_rem {m : ℕ} {μ : Fin m → ℝ} {w : Fin m → MassSpace}
    (hμ : ∀ i, μ i ≠ 0) (hw : Orthonormal ℝ w) (heig : ∀ i, resolvent (w i) = μ i • w i)
    (q : SourceGraph) :
    ‖q‖ ^ 2 =
      (∑ i, (1 / μ i) * ⟪w i, q.val.fst⟫_ℝ ^ 2) + ‖eigenGraphRem μ w q‖ ^ 2 := by
  have h1 := (sourceEnergy_add_two_mass q).symm
  have h2 := (sourceEnergy_add_two_mass (eigenGraphRem μ w q)).symm
  rw [h1, sourceEnergy_eq_neg_sum_eigen_add_rem hμ hw heig,
    norm_fst_sq_eq_sum_eigen_add_rem hμ hw heig, h2]
  have hsum : (-∑ i, ((2 * μ i - 1) / μ i) * ⟪w i, q.val.fst⟫_ℝ ^ 2) +
      2 * (∑ i, ⟪w i, q.val.fst⟫_ℝ ^ 2) =
      ∑ i, (1 / μ i) * ⟪w i, q.val.fst⟫_ℝ ^ 2 := by
    rw [← Finset.sum_neg_distrib, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hi := hμ i
    field_simp [hi]
    ring
  linarith

/-- **Unconditional Graph Bessel Inequality for Resolvent Eigenvectors**:
for any orthonormal family of eigenvectors `resolvent (w i) = μ i • w i` (`μ i ≠ 0`) and any
`q : SourceGraph`,
`∑ i, (1 / μ i) * ⟪w i, q.val.fst⟫_ℝ ^ 2 ≤ ‖q‖ ^ 2`. -/
theorem sum_inv_eigen_inner_sq_le_norm_graph_sq {m : ℕ} {μ : Fin m → ℝ} {w : Fin m → MassSpace}
    (hμ : ∀ i, μ i ≠ 0) (hw : Orthonormal ℝ w) (heig : ∀ i, resolvent (w i) = μ i • w i)
    (q : SourceGraph) :
    (∑ i, (1 / μ i) * ⟪w i, q.val.fst⟫_ℝ ^ 2) ≤ ‖q‖ ^ 2 := by
  rw [norm_graph_sq_eq_sum_inv_eigen_add_rem hμ hw heig]
  linarith [sq_nonneg ‖eigenGraphRem μ w q‖]

/-! ## Section 2: Odd-Polar Bessel Bound and Exact Cardinal Spectral Deficit at Nonreal $\Xi$-Zeros -/

/-- **Shift-Uniform Odd-Polar Bessel Bound on `⟪w_i, tanhL⟫²`**:
for every nonzero admissible shift `a` (`a ≠ 0`, `1 < 2 * exp(-2|a|)`) and every orthonormal family
of eigenvectors `resolvent (w i) = μ i • w i` with `μ i ≠ 0` and `μ i ≠ 1 / 2`,
`∑ i, (μ i / (2 * μ i - 1) ^ 2) * ⟪w i, tanhL⟫_ℝ ^ 2 ≤ ‖oddPolarVectorAt a ha‖ ^ 2`. -/
theorem sum_oddPolar_inner_tanhL_sq_le {a : ℝ} (hane : a ≠ 0)
    (ha : 1 < 2 * Real.exp (-2 * |a|)) {m : ℕ} {μ : Fin m → ℝ} {w : Fin m → MassSpace}
    (hμ0 : ∀ i, μ i ≠ 0) (hμhalf : ∀ i, μ i ≠ 1 / 2)
    (hw : Orthonormal ℝ w) (heig : ∀ i, resolvent (w i) = μ i • w i) :
    (∑ i, (μ i / (2 * μ i - 1) ^ 2) * ⟪w i, tanhL⟫_ℝ ^ 2) ≤
      ‖oddPolarVectorAt a ha‖ ^ 2 := by
  refine (le_of_eq ?_).trans (sum_inv_eigen_inner_sq_le_norm_graph_sq hμ0 hw heig (oddPolarVectorAt a ha))
  refine Finset.sum_congr rfl fun i _ => ?_
  have hp := eigenvector_oddPolarVectorAt_pairing hane ha (heig i)
  have hne : 2 * μ i - 1 ≠ 0 := by intro h; apply hμhalf i; linarith
  have hi0 := hμ0 i
  have h1 : (2 * μ i - 1) ^ 2 * ⟪w i, (oddPolarVectorAt a ha).val.fst⟫_ℝ ^ 2 =
      μ i ^ 2 * ⟪w i, tanhL⟫_ℝ ^ 2 := by
    have hp' : (2 * μ i - 1) * ⟪w i, (oddPolarVectorAt a ha).val.fst⟫_ℝ = -μ i * ⟪w i, tanhL⟫_ℝ := by
      linarith
    calc (2 * μ i - 1) ^ 2 * ⟪w i, (oddPolarVectorAt a ha).val.fst⟫_ℝ ^ 2
        = ((2 * μ i - 1) * ⟪w i, (oddPolarVectorAt a ha).val.fst⟫_ℝ) ^ 2 := by ring
      _ = (-μ i * ⟪w i, tanhL⟫_ℝ) ^ 2 := by rw [hp']
      _ = μ i ^ 2 * ⟪w i, tanhL⟫_ℝ ^ 2 := by ring
  calc (μ i / (2 * μ i - 1) ^ 2) * ⟪w i, tanhL⟫_ℝ ^ 2
      = (μ i ^ 2 * ⟪w i, tanhL⟫_ℝ ^ 2) / (μ i * (2 * μ i - 1) ^ 2) := by
        field_simp [hi0, hne]
    _ = ((2 * μ i - 1) ^ 2 * ⟪w i, (oddPolarVectorAt a ha).val.fst⟫_ℝ ^ 2) /
          (μ i * (2 * μ i - 1) ^ 2) := by rw [← h1]
    _ = (1 / μ i) * ⟪w i, (oddPolarVectorAt a ha).val.fst⟫_ℝ ^ 2 := by
        field_simp [hi0, hne]

theorem sourceEnergy_nonneg_of_mem_boundStateSpace_orthogonal {q : SourceGraph}
    (horth : q.val.fst ∈ boundStateSpaceᗮ) : 0 ≤ sourceEnergy q := by
  by_contra h
  exact fst_notMem_orthogonal_of_energy_neg (not_le.mp h) horth

/-- **Exact Cardinal Spectral Deficit Identity at Any Nonreal $\Xi$-Zero**:
for any `a : ℂ` with `0 < a.re`, `XiC a = 0`, and `a.im ≠ 0`, any `F : CardinalGraphFrame a`, and
any orthonormal family of eigenvectors `resolvent (w i) = μ i • w i` with `μ i ≠ 0` and
`μ i ≠ 1 / 2`,
`cardinalOrbitMass a ^ 2 * ∑ i, (μ i / (2 * μ i - 1)) * (massCosineReadout (w i) a).im ^ 2 = cardinalPositiveMass a + sourceEnergy (eigenGraphRem μ w F.imVector)`. -/
theorem cardinal_im_spectral_deficit_eq {a : ℂ} (F : CardinalGraphFrame a)
    (ha : 0 < a.re) (hz : XiC a = 0) (hi : a.im ≠ 0)
    {m : ℕ} {μ : Fin m → ℝ} {w : Fin m → MassSpace}
    (hμ0 : ∀ i, μ i ≠ 0) (hμhalf : ∀ i, μ i ≠ 1 / 2)
    (hw : Orthonormal ℝ w) (heig : ∀ i, resolvent (w i) = μ i • w i) :
    cardinalOrbitMass a ^ 2 *
        (∑ i, (μ i / (2 * μ i - 1)) * (massCosineReadout (w i) a).im ^ 2) =
      cardinalPositiveMass a + sourceEnergy (eigenGraphRem μ w F.imVector) := by
  have hE := sourceEnergy_eq_neg_sum_eigen_add_rem hμ0 hw heig F.imVector
  rw [F.im_energy, ← cardinalPositiveMass_eq_negative ha hi] at hE
  have hsum : (∑ i, ((2 * μ i - 1) / μ i) * ⟪w i, F.imVector.val.fst⟫_ℝ ^ 2) =
      cardinalOrbitMass a ^ 2 *
        (∑ i, (μ i / (2 * μ i - 1)) * (massCosineReadout (w i) a).im ^ 2) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hp := eigenvector_cardinal_im_pairing F ha hz (heig i)
    have hne : 2 * μ i - 1 ≠ 0 := by intro h; apply hμhalf i; linarith
    have hi0 := hμ0 i
    have hsq : (2 * μ i - 1) ^ 2 * ⟪w i, F.imVector.val.fst⟫_ℝ ^ 2 =
        μ i ^ 2 * cardinalOrbitMass a ^ 2 * (massCosineReadout (w i) a).im ^ 2 := by
      calc (2 * μ i - 1) ^ 2 * ⟪w i, F.imVector.val.fst⟫_ℝ ^ 2
          = ((1 - 2 * μ i) * ⟪w i, F.imVector.val.fst⟫_ℝ) ^ 2 := by ring
        _ = (μ i * cardinalOrbitMass a * (massCosineReadout (w i) a).im) ^ 2 := by rw [hp]
        _ = μ i ^ 2 * cardinalOrbitMass a ^ 2 * (massCosineReadout (w i) a).im ^ 2 := by ring
    calc ((2 * μ i - 1) / μ i) * ⟪w i, F.imVector.val.fst⟫_ℝ ^ 2
        = ((2 * μ i - 1) ^ 2 * ⟪w i, F.imVector.val.fst⟫_ℝ ^ 2) /
            (μ i * (2 * μ i - 1)) := by
          field_simp [hi0, hne]
      _ = (μ i ^ 2 * cardinalOrbitMass a ^ 2 * (massCosineReadout (w i) a).im ^ 2) /
            (μ i * (2 * μ i - 1)) := by rw [hsq]
      _ = cardinalOrbitMass a ^ 2 *
            ((μ i / (2 * μ i - 1)) * (massCosineReadout (w i) a).im ^ 2) := by
          field_simp [hi0, hne]
  linarith

/-- When the remainder `(eigenGraphRem μ w F.imVector).val.fst` is orthogonal to `boundStateSpace`,
the weighted sum of imaginary cosine readouts of `{w_i}` at `a` is bounded below by
`cardinalPositiveMass a > 0`. -/
theorem cardinalPositiveMass_le_sum_eigen_im_readout_sq {a : ℂ} (F : CardinalGraphFrame a)
    (ha : 0 < a.re) (hz : XiC a = 0) (hi : a.im ≠ 0)
    {m : ℕ} {μ : Fin m → ℝ} {w : Fin m → MassSpace}
    (hμ0 : ∀ i, μ i ≠ 0) (hμhalf : ∀ i, μ i ≠ 1 / 2)
    (hw : Orthonormal ℝ w) (heig : ∀ i, resolvent (w i) = μ i • w i)
    (horth : (eigenGraphRem μ w F.imVector).val.fst ∈ boundStateSpaceᗮ) :
    cardinalPositiveMass a ≤
      cardinalOrbitMass a ^ 2 *
        (∑ i, (μ i / (2 * μ i - 1)) * (massCosineReadout (w i) a).im ^ 2) := by
  rw [cardinal_im_spectral_deficit_eq F ha hz hi hμ0 hμhalf hw heig]
  linarith [sourceEnergy_nonneg_of_mem_boundStateSpace_orthogonal horth]

/-! ## Section 3: Universal Rayleigh-to-Energy Lower Bound and Primitive Contraction Nodal Inequality -/

/-- **Orthogonal Decomposition of `⟪resolvent u, u⟫` into Primitive and Ground Components**:
for every `q : SourceGraph`,
`⟪resolvent q.val.fst, q.val.fst⟫_ℝ = ⟪resolvent (primGraph q).val.fst, (primGraph q).val.fst⟫_ℝ + 2 * ⟪q.val.fst, oneL⟫_ℝ ^ 2`. -/
theorem inner_resolvent_primGraph_fst (q : SourceGraph) :
    ⟪resolvent q.val.fst, q.val.fst⟫_ℝ =
      ⟪resolvent (primGraph q).val.fst, (primGraph q).val.fst⟫_ℝ +
        2 * ⟪q.val.fst, oneL⟫_ℝ ^ 2 := by
  have hdecomp : q.val.fst = (primGraph q).val.fst + (2 * ⟪q.val.fst, oneL⟫_ℝ) • oneL := by
    rw [primGraph_fst, sub_add_cancel]
  have horth1 : ⟪resolvent (primGraph q).val.fst, oneL⟫_ℝ = 0 := by
    rw [inner_resolvent_oneL, real_inner_comm, inner_primGraph_oneL]
  have horth2 : ⟪oneL, (primGraph q).val.fst⟫_ℝ = 0 := by
    rw [real_inner_comm, inner_primGraph_oneL]
  conv_lhs => rw [hdecomp]
  rw [map_add, map_smul, resolvent_oneL, inner_add_left, inner_add_right, inner_add_right,
    real_inner_smul_right, real_inner_smul_left, real_inner_smul_left, real_inner_smul_right,
    horth1, horth2, real_inner_self_eq_norm_sq, norm_oneL_sq]
  ring

/-- **Universal Rayleigh-to-Energy Lower Bound on `SourceGraph`**:
for every `q : SourceGraph` and every `μ_max > 0`, if
`⟪resolvent q.val.fst, q.val.fst⟫_ℝ ≤ μ_max * ‖q.val.fst‖ ^ 2`, then
`sourceEnergy q ≥ -((2 * μ_max - 1) / μ_max) * ‖q.val.fst‖ ^ 2`. -/
theorem sourceEnergy_ge_of_inner_resolvent_le {q : SourceGraph} {μ_max : ℝ} (hμ : 0 < μ_max)
    (hray : ⟪resolvent q.val.fst, q.val.fst⟫_ℝ ≤ μ_max * ‖q.val.fst‖ ^ 2) :
    -((2 * μ_max - 1) / μ_max) * ‖q.val.fst‖ ^ 2 ≤ sourceEnergy q := by
  by_cases h0 : ‖q.val.fst‖ = 0
  · have hfst0 : q.val.fst = 0 := norm_eq_zero.mp h0
    have hE : sourceEnergy q = ‖q.val.snd‖ ^ 2 - ‖q.val.fst‖ ^ 2 := rfl
    rw [h0, hE, h0]
    nlinarith [sq_nonneg ‖q.val.snd‖]
  · have hpos : 0 < ‖q.val.fst‖ ^ 2 := sq_pos_of_ne_zero h0
    have hcs := norm_fst_pow_four_le_inner_resolvent_mul q
    have hnn : 0 ≤ sourceEnergy q + 2 * ‖q.val.fst‖ ^ 2 := by
      rw [sourceEnergy_add_two_mass]
      exact sq_nonneg ‖q‖
    have hmul : ‖q.val.fst‖ ^ 4 ≤
        (μ_max * ‖q.val.fst‖ ^ 2) * (sourceEnergy q + 2 * ‖q.val.fst‖ ^ 2) :=
      hcs.trans (mul_le_mul_of_nonneg_right hray hnn)
    have hpow4 : ‖q.val.fst‖ ^ 4 = ‖q.val.fst‖ ^ 2 * ‖q.val.fst‖ ^ 2 := by ring
    have hle1 : ‖q.val.fst‖ ^ 2 ≤ μ_max * (sourceEnergy q + 2 * ‖q.val.fst‖ ^ 2) := by
      nlinarith
    have hdiv : (1 / μ_max) * ‖q.val.fst‖ ^ 2 ≤ sourceEnergy q + 2 * ‖q.val.fst‖ ^ 2 := by
      rw [ one_div_mul_eq_div, div_le_iff₀' hμ ]
      exact hle1
    have hid : -((2 * μ_max - 1) / μ_max) * ‖q.val.fst‖ ^ 2 =
        (1 / μ_max) * ‖q.val.fst‖ ^ 2 - 2 * ‖q.val.fst‖ ^ 2 := by
      field_simp [hμ.ne']
      ring
    linarith

/-- **Universal Primitive-Contraction Nodal Cross-Jump Bound**:
for every `p : SourceGraph` and every `μ_max > 0`, if the primitive absolute-value contraction
`u_0 = (primGraph (absGraph p)).val.fst` satisfies
`⟪resolvent u_0, u_0⟫_ℝ ≤ μ_max * ‖u_0‖ ^ 2`, then
`-sourceEnergy p - 4 * sourcePair (posGraph p) (negGraph p) ≤ ((2 * μ_max - 1) / μ_max) * ‖p.val.fst‖ ^ 2 + ((1 - μ_max) / μ_max) * (2 * ⟪(absGraph p).val.fst, oneL⟫_ℝ ^ 2)`. -/
theorem nodal_cross_le_of_primGraph_absGraph_rayleigh_le {p : SourceGraph} {μ_max : ℝ}
    (hμ : 0 < μ_max)
    (hray : ⟪resolvent (primGraph (absGraph p)).val.fst, (primGraph (absGraph p)).val.fst⟫_ℝ ≤
      μ_max * ‖(primGraph (absGraph p)).val.fst‖ ^ 2) :
    -sourceEnergy p - 4 * sourcePair (posGraph p) (negGraph p) ≤
      ((2 * μ_max - 1) / μ_max) * ‖p.val.fst‖ ^ 2 +
        ((1 - μ_max) / μ_max) * (2 * ⟪(absGraph p).val.fst, oneL⟫_ℝ ^ 2) := by
  have h1 := sourceEnergy_ge_of_inner_resolvent_le hμ hray
  rw [sourceEnergy_primGraph, sourceEnergy_absGraph_eq, norm_primGraph_fst_sq,
    norm_absGraph_fst_sq] at h1
  have hid : -((2 * μ_max - 1) / μ_max) *
      (‖p.val.fst‖ ^ 2 - 2 * ⟪(absGraph p).val.fst, oneL⟫_ℝ ^ 2) -
      2 * ⟪(absGraph p).val.fst, oneL⟫_ℝ ^ 2 =
      -(((2 * μ_max - 1) / μ_max) * ‖p.val.fst‖ ^ 2 +
        ((1 - μ_max) / μ_max) * (2 * ⟪(absGraph p).val.fst, oneL⟫_ℝ ^ 2)) := by
    field_simp [hμ.ne']
    ring
  linarith

/-- **Eigenvector Nodal Cross-Jump / $L^1$-Ground Comparison Inequality**:
for every eigenvector `resolvent v = ν • v` (`ν > 0`) with `p = rieszLift v`, and every
`μ_max > 0`, if `u_0 = (primGraph (absGraph p)).val.fst` satisfies
`⟪resolvent u_0, u_0⟫_ℝ ≤ μ_max * ‖u_0‖ ^ 2`, then
`((ν - μ_max) / (ν * μ_max)) * ‖p.val.fst‖ ^ 2 - 4 * sourcePair (posGraph p) (negGraph p) ≤ ((1 - μ_max) / μ_max) * (2 * ⟪(absGraph p).val.fst, oneL⟫_ℝ ^ 2)`. -/
theorem eigenvector_nodal_cross_le_of_primGraph_absGraph_rayleigh_le
    {ν μ_max : ℝ} (hν : 0 < ν) (hμ : 0 < μ_max) {v : MassSpace}
    (heig : resolvent v = ν • v)
    (hray : ⟪resolvent (primGraph (absGraph (rieszLift v))).val.fst,
        (primGraph (absGraph (rieszLift v))).val.fst⟫_ℝ ≤
      μ_max * ‖(primGraph (absGraph (rieszLift v))).val.fst‖ ^ 2) :
    ((ν - μ_max) / (ν * μ_max)) * ‖(rieszLift v).val.fst‖ ^ 2 -
        4 * sourcePair (posGraph (rieszLift v)) (negGraph (rieszLift v)) ≤
      ((1 - μ_max) / μ_max) * (2 * ⟪(absGraph (rieszLift v)).val.fst, oneL⟫_ℝ ^ 2) := by
  set p := rieszLift v
  have h1 := nodal_cross_le_of_primGraph_absGraph_rayleigh_le hμ hray
  have hEp : sourceEnergy p = ((1 - 2 * ν) / ν) * ‖p.val.fst‖ ^ 2 := by
    have h2 : sourceEnergy p = ‖p.val.snd‖ ^ 2 - ‖p.val.fst‖ ^ 2 := rfl
    rw [h2, norm_rieszLift_snd_sq_of_eigenvector hν.ne' heig]
    field_simp [hν.ne']
    ring
  rw [hEp] at h1
  have hid : -(((1 - 2 * ν) / ν) * ‖p.val.fst‖ ^ 2) -
      ((2 * μ_max - 1) / μ_max) * ‖p.val.fst‖ ^ 2 =
      ((ν - μ_max) / (ν * μ_max)) * ‖p.val.fst‖ ^ 2 := by
    field_simp [hν.ne', hμ.ne']
    ring
  linarith

/-- **Threshold Special Case (`μ_max = 1/2`) of the Primitive-Contraction Nodal Bound**:
if `(primGraph (absGraph p)).val.fst ∈ boundStateSpaceᗮ`, then
`-sourceEnergy p - 4 * sourcePair (posGraph p) (negGraph p) ≤ 2 * ⟪(absGraph p).val.fst, oneL⟫_ℝ ^ 2`. -/
theorem nodal_cross_le_two_inner_oneL_sq_of_primGraph_absGraph_mem_orthogonal
    {p : SourceGraph} (horth : (primGraph (absGraph p)).val.fst ∈ boundStateSpaceᗮ) :
    -sourceEnergy p - 4 * sourcePair (posGraph p) (negGraph p) ≤
      2 * ⟪(absGraph p).val.fst, oneL⟫_ℝ ^ 2 := by
  have hE : 0 ≤ sourceEnergy (primGraph (absGraph p)) :=
    sourceEnergy_nonneg_of_mem_boundStateSpace_orthogonal horth
  rw [sourceEnergy_primGraph, sourceEnergy_absGraph_eq] at hE
  linarith

/-! ## Section 4: Shift-Independent Odd Cardinal Fourier-Re Mode and Odd Spectral Deficit Identity -/

/-- **Shift-Independent Odd Cardinal Fourier-Re Mode at Any Nonreal $\Xi$-Zero**:
for every `a : ℂ` with `0 < a.re`, `XiC a = 0`, and `a.im ≠ 0`, there exists an odd graph vector
`q_odd : SourceGraph` (`reflectGraph q_odd = -q_odd`) with
`sourceEnergy q_odd = -(cardinalOrbitMass a / 2)` such that:
1. for every odd `p : SourceGraph` (`reflectGraph p = -p`),
   `sourcePair p q_odd = -cardinalOrbitMass a * (graphFourierReadout p a).re`
   (the small-shift factor `δ a = (e^{iat} - e^{-iat}) / 2` cancels identically on the odd sector),
2. for every odd eigenvector `resolvent w = μ • w` (`reflectMass w = -w`),
   `(2 * μ - 1) * ⟪w, q_odd.val.fst⟫_ℝ = μ * cardinalOrbitMass a * (massFourierReadout w a).re`. -/
theorem exists_odd_cardinal_fourier_re_mode {a : ℂ} (ha : 0 < a.re) (hz : XiC a = 0)
    (hi : a.im ≠ 0) :
    ∃ q_odd : SourceGraph,
      reflectGraph q_odd = -q_odd ∧
      sourceEnergy q_odd = -(cardinalOrbitMass a / 2) ∧
      (∀ p : SourceGraph, reflectGraph p = -p →
        sourcePair p q_odd = -cardinalOrbitMass a * (graphFourierReadout p a).re) ∧
      (∀ {μ : ℝ} {w : MassSpace}, reflectMass w = -w → resolvent w = μ • w →
        (2 * μ - 1) * ⟪w, q_odd.val.fst⟫_ℝ =
          μ * cardinalOrbitMass a * (massFourierReadout w a).re) := by
  set t := CHMDThetaTranslate.radius
  have ht_pos : 0 < t := CHMDThetaTranslate.radius_pos
  have ht_le : |t| ≤ CHMDThetaTranslate.radius := by rw [abs_of_pos ht_pos]
  obtain ⟨u, v, hus, hvs, hu_pair, hv_pair⟩ := exists_translatedCardinalFrame ha hz t ht_le
  set uO := oddGraphPart u
  set vO := oddGraphPart v
  have hu_ft : ∀ z : ℂ, XiC z = 0 →
      graphFourierReadout u z = exp ((I * z) * (t : ℂ)) * cardinalOrbitValue a 1 z := by
    intro z hzero
    rw [graphFourierReadout_of_source hus, paperFT_translate_real]
    have h1 : (fun x => ((divisorCardinalSource a x).re : ℂ)) =
        (fun x => (cardinalRealSource a 1 x : ℂ)) := by
      funext x; simp [cardinalRealSource]
    rw [h1, cardinalRealSource_paperFT ha hz 1 hzero, mul_assoc]
  have hv_ft : ∀ z : ℂ, XiC z = 0 →
      graphFourierReadout v z = exp ((I * z) * (t : ℂ)) * cardinalOrbitValue a (-I) z := by
    intro z hzero
    rw [graphFourierReadout_of_source hvs, paperFT_translate_real]
    have h1 : (fun x => ((divisorCardinalSource a x).im : ℂ)) =
        (fun x => (cardinalRealSource a (-I) x : ℂ)) := by
      funext x; simp [cardinalRealSource, Complex.mul_re]
    rw [h1, cardinalRealSource_paperFT ha hz (-I) hzero, mul_assoc]
  let δ : ℂ → ℂ := fun z => (exp ((I * z) * (t : ℂ)) - exp (-(I * z) * (t : ℂ))) / 2
  have huO_shift : ∀ z : ℂ, XiC z = 0 →
      shiftedCosineReadout uO z t = -δ z ^ 2 * cardinalOrbitValue a 1 z := by
    intro z hzero
    have hstrip := (abs_im_lt_half_of_XiC_eq_zero hzero).le
    have hzn : XiC (-z) = 0 := by rw [XiC_even, hzero]
    have hexp : (I * -z) * (t : ℂ) = -(I * z) * (t : ℂ) := by ring
    rw [shiftedCosineReadout_oddGraphPart u hstrip t, hu_ft z hzero, hu_ft (-z) hzn,
      cardinalOrbitValue_neg, hexp]
    dsimp [δ]
    ring
  have hvO_shift : ∀ z : ℂ, XiC z = 0 →
      shiftedCosineReadout vO z t = -δ z ^ 2 * cardinalOrbitValue a (-I) z := by
    intro z hzero
    have hstrip := (abs_im_lt_half_of_XiC_eq_zero hzero).le
    have hzn : XiC (-z) = 0 := by rw [XiC_even, hzero]
    have hexp : (I * -z) * (t : ℂ) = -(I * z) * (t : ℂ) := by ring
    rw [shiftedCosineReadout_oddGraphPart v hstrip t, hv_ft z hzero, hv_ft (-z) hzn,
      cardinalOrbitValue_neg, hexp]
    dsimp [δ]
    ring
  have hδa_ne : δ a ≠ 0 := exp_sub_exp_neg_div_two_ne_zero hi ht_pos
  set lam : ℂ := (δ a)⁻¹
  set q_odd : SourceGraph := lam.re • uO - lam.im • vO
  have hq_odd : reflectGraph q_odd = -q_odd := by
    dsimp [q_odd]
    rw [reflectGraph_sub, reflectGraph_smul, reflectGraph_smul,
      reflectGraph_oddGraphPart, reflectGraph_oddGraphPart]
    module
  have hshift_sub : ∀ (p q : SourceGraph) (z : ℂ), |z.im| ≤ 1 / 2 →
      shiftedCosineReadout (p - q) z t =
        shiftedCosineReadout p z t - shiftedCosineReadout q z t := by
    intro p q z hst
    have hstn : |(-z).im| ≤ 1 / 2 := by simpa using hst
    unfold shiftedCosineReadout
    rw [graphFourierReadout_sub p q hst, graphFourierReadout_sub p q hstn]
    ring
  have hshift_smul : ∀ (r : ℝ) (p : SourceGraph) (z : ℂ), |z.im| ≤ 1 / 2 →
      shiftedCosineReadout (r • p) z t = (r : ℂ) * shiftedCosineReadout p z t := by
    intro r p z hst
    have hstn : |(-z).im| ≤ 1 / 2 := by simpa using hst
    unfold shiftedCosineReadout
    rw [graphFourierReadout_smul r p hst, graphFourierReadout_smul r p hstn]
    ring
  have hst_a : |a.im| ≤ 1 / 2 := (abs_im_lt_half_of_XiC_eq_zero hz).le
  have hq_pair_shift : ∀ p : SourceGraph, reflectGraph p = -p →
      sourcePair p q_odd =
        cardinalOrbitMass a * (lam * shiftedCosineReadout p a t).re := by
    intro p hp
    dsimp [q_odd]
    rw [sourcePair_sub_right, sourcePair_smul_right, sourcePair_smul_right,
      sourcePair_odd_oddGraphPart hp u, sourcePair_odd_oddGraphPart hp v,
      hu_pair p, hv_pair p, Complex.mul_re]
    ring
  have hq_pair_fourier : ∀ p : SourceGraph, reflectGraph p = -p →
      sourcePair p q_odd = -cardinalOrbitMass a * (graphFourierReadout p a).re := by
    intro p hp
    rw [hq_pair_shift p hp, shiftedCosineReadout_of_odd hp hst_a t]
    have hcancel : lam * (-δ a * graphFourierReadout p a) = -graphFourierReadout p a := by
      have h1 : lam * δ a = 1 := inv_mul_cancel₀ hδa_ne
      calc lam * (-δ a * graphFourierReadout p a)
          = -(lam * δ a) * graphFourierReadout p a := by ring
        _ = -graphFourierReadout p a := by rw [h1]; ring
    rw [hcancel, Complex.neg_re]
    ring
  refine ⟨q_odd, hq_odd, ?_, hq_pair_fourier, ?_⟩
  · have hval1 : cardinalOrbitValue a 1 a = 1 / 2 := by
      have hA : unsignedOrbitIndicator a a = 1 := by simp [unsignedOrbitIndicator]
      have hB : unsignedOrbitIndicator a (conj a) = 0 := by
        simpa [hA] using unsignedOrbitIndicators_disjoint ha hi a
      simp [cardinalOrbitValue, hA, hB]
    have hvalI : cardinalOrbitValue a (-I) a = -I / 2 := by
      have hA : unsignedOrbitIndicator a a = 1 := by simp [unsignedOrbitIndicator]
      have hB : unsignedOrbitIndicator a (conj a) = 0 := by
        simpa [hA] using unsignedOrbitIndicators_disjoint ha hi a
      simp [cardinalOrbitValue, hA, hB]
    have hq_shift_a : shiftedCosineReadout q_odd a t = -(1 / 2 : ℂ) * lam * δ a ^ 2 := by
      dsimp [q_odd]
      rw [hshift_sub _ _ _ hst_a, hshift_smul _ _ _ hst_a, hshift_smul _ _ _ hst_a,
        huO_shift a hz, hvO_shift a hz, hval1, hvalI]
      have hlam_eq : (lam.re : ℂ) + (lam.im : ℂ) * I = lam := Complex.re_add_im lam
      linear_combination -(1 / 2 : ℂ) * δ a ^ 2 * hlam_eq
    rw [← sourcePair_self, hq_pair_shift q_odd hq_odd, hq_shift_a]
    have hprod : lam * (-(1 / 2 : ℂ) * lam * δ a ^ 2) = -(1 / 2 : ℂ) := by
      have h1 : lam * δ a = 1 := inv_mul_cancel₀ hδa_ne
      calc lam * (-(1 / 2 : ℂ) * lam * δ a ^ 2)
          = -(1 / 2 : ℂ) * (lam * δ a) ^ 2 := by ring
        _ = -(1 / 2 : ℂ) := by rw [h1]; ring
    rw [hprod]
    norm_num
    ring
  · intro μ w hodd heig
    have hp_odd : reflectGraph (rieszLift w) = -rieszLift w := by
      rw [← rieszLift_reflectMass, hodd, ← neg_one_smul ℝ w, rieszLift_smul, neg_one_smul]
    have h1 := sourcePair_rieszLift_of_eigenvector heig q_odd
    have h2 := hq_pair_fourier (rieszLift w) hp_odd
    rw [graphFourierReadout_rieszLift_of_eigenvector heig] at h2
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at h2
    linarith

/-- **Exact Odd Cardinal Spectral Deficit Identity at Any Nonreal $\Xi$-Zero**:
for any `a : ℂ` with `0 < a.re`, `XiC a = 0`, and `a.im ≠ 0`, and any orthonormal family of
**odd** eigenvectors `resolvent (w i) = μ i • w i` (`reflectMass (w i) = -w i`, `μ i ≠ 0`,
`μ i ≠ 1 / 2`), there exists an odd graph vector `q_odd : SourceGraph` (`reflectGraph q_odd = -q_odd`)
such that
`cardinalOrbitMass a ^ 2 * ∑ i, (μ i / (2 * μ i - 1)) * (massFourierReadout (w i) a).re ^ 2 = cardinalOrbitMass a / 2 + sourceEnergy (eigenGraphRem μ w q_odd)`. -/
theorem odd_cardinal_re_spectral_deficit_eq {a : ℂ} (ha : 0 < a.re) (hz : XiC a = 0)
    (hi : a.im ≠ 0) {m : ℕ} {μ : Fin m → ℝ} {w : Fin m → MassSpace}
    (hμ0 : ∀ i, μ i ≠ 0) (hμhalf : ∀ i, μ i ≠ 1 / 2)
    (hodd : ∀ i, reflectMass (w i) = -w i)
    (hw : Orthonormal ℝ w) (heig : ∀ i, resolvent (w i) = μ i • w i) :
    ∃ q_odd : SourceGraph,
      reflectGraph q_odd = -q_odd ∧
      cardinalOrbitMass a ^ 2 *
          (∑ i, (μ i / (2 * μ i - 1)) * (massFourierReadout (w i) a).re ^ 2) =
        cardinalOrbitMass a / 2 + sourceEnergy (eigenGraphRem μ w q_odd) := by
  obtain ⟨q_odd, hq_odd, hq_E, _, hq_eig⟩ := exists_odd_cardinal_fourier_re_mode ha hz hi
  refine ⟨q_odd, hq_odd, ?_⟩
  have hE := sourceEnergy_eq_neg_sum_eigen_add_rem hμ0 hw heig q_odd
  rw [hq_E] at hE
  have hsum : (∑ i, ((2 * μ i - 1) / μ i) * ⟪w i, q_odd.val.fst⟫_ℝ ^ 2) =
      cardinalOrbitMass a ^ 2 *
        (∑ i, (μ i / (2 * μ i - 1)) * (massFourierReadout (w i) a).re ^ 2) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hp := hq_eig (hodd i) (heig i)
    have hne : 2 * μ i - 1 ≠ 0 := by intro h; apply hμhalf i; linarith
    have hi0 := hμ0 i
    have hsq : (2 * μ i - 1) ^ 2 * ⟪w i, q_odd.val.fst⟫_ℝ ^ 2 =
        μ i ^ 2 * cardinalOrbitMass a ^ 2 * (massFourierReadout (w i) a).re ^ 2 := by
      calc (2 * μ i - 1) ^ 2 * ⟪w i, q_odd.val.fst⟫_ℝ ^ 2
          = ((2 * μ i - 1) * ⟪w i, q_odd.val.fst⟫_ℝ) ^ 2 := by ring
        _ = (μ i * cardinalOrbitMass a * (massFourierReadout (w i) a).re) ^ 2 := by rw [hp]
        _ = μ i ^ 2 * cardinalOrbitMass a ^ 2 * (massFourierReadout (w i) a).re ^ 2 := by ring
    calc ((2 * μ i - 1) / μ i) * ⟪w i, q_odd.val.fst⟫_ℝ ^ 2
        = ((2 * μ i - 1) ^ 2 * ⟪w i, q_odd.val.fst⟫_ℝ ^ 2) /
            (μ i * (2 * μ i - 1)) := by
          field_simp [hi0, hne]
      _ = (μ i ^ 2 * cardinalOrbitMass a ^ 2 * (massFourierReadout (w i) a).re ^ 2) /
            (μ i * (2 * μ i - 1)) := by rw [hsq]
      _ = cardinalOrbitMass a ^ 2 *
            ((μ i / (2 * μ i - 1)) * (massFourierReadout (w i) a).re ^ 2) := by
          field_simp [hi0, hne]
  linarith

end RHTower.CHMDPolar
