import GaloisForLFunctions.HTGeometry.PolydiscCauchyFormula
import GaloisForLFunctions.HTGeometry.MultiIndexMultilinear
import GaloisForLFunctions.HTGeometry.MultiGeometricSeries
import Mathlib.Analysis.Analytic.Basic

/-!
# The power series of a holomorphic function of several variables

The Cauchy integral over the distinguished boundary of a polydisc against the reciprocal powers of
the coordinates defines, for every multi-index, a coefficient; the monomial maps of the multi-indices
of a fixed total degree, weighted by those coefficients, form the terms of a formal multilinear
series.  The coefficients are bounded by the maximum of the function on the torus divided by the
corresponding power of the radius, and the number of multi-indices of a given degree grows
polynomially, so the series has a positive radius of convergence.

* `polydiscCoeff` : the Cauchy coefficient of a multi-index.
* `polydiscSeries` : the formal multilinear series of a holomorphic function on a polydisc.
* `polydiscSeries_radius_le` : the radius of convergence is at least the radius of the polydisc.
-/

open MeasureTheory Complex Set
open scoped Real

namespace GaloisForLFunctions.HTGeometry

section TorusIntegralSums

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem torusIntegral_zero (c : Fin n → ℂ) (R : Fin n → ℝ) :
    (∯ _ζ in T(c, R), (0 : E)) = 0 := by
  show (∫ _θ in Icc (0 : Fin n → ℝ) fun _ => 2 * π,
    (∏ i, (R i : ℂ) * Complex.exp (_θ i * Complex.I) * Complex.I : ℂ) • (0 : E)) = 0
  simp

omit [NormedSpace ℂ E] in
/-- A finite sum of torus integrable functions is torus integrable. -/
theorem torusIntegrable_finsetSum {ι : Type*} (s : Finset ι) (F : ι → (Fin n → ℂ) → E)
    {c : Fin n → ℂ} {R : Fin n → ℝ} (h : ∀ i ∈ s, TorusIntegrable (F i) c R) :
    TorusIntegrable (fun ζ => ∑ i ∈ s, F i ζ) c R := by
  classical
  induction s using Finset.induction with
  | empty =>
      simpa using TorusIntegrable.torusIntegrable_const (0 : E) c R
  | insert a s ha ih =>
      have h1 : TorusIntegrable (F a) c R := h a (Finset.mem_insert_self a s)
      have h2 : TorusIntegrable (fun ζ => ∑ i ∈ s, F i ζ) c R :=
        ih fun i hi => h i (Finset.mem_insert_of_mem hi)
      have hfun : (fun ζ => ∑ i ∈ insert a s, F i ζ) = F a + fun ζ => ∑ i ∈ s, F i ζ := by
        funext ζ
        show ∑ i ∈ insert a s, F i ζ = F a ζ + ∑ i ∈ s, F i ζ
        rw [Finset.sum_insert ha]
      rw [hfun]
      exact h1.add h2

/-- The integral over a torus of a finite sum of integrable functions. -/
theorem torusIntegral_finsetSum {ι : Type*} (s : Finset ι) (F : ι → (Fin n → ℂ) → E)
    {c : Fin n → ℂ} {R : Fin n → ℝ} (h : ∀ i ∈ s, TorusIntegrable (F i) c R) :
    (∯ ζ in T(c, R), ∑ i ∈ s, F i ζ) = ∑ i ∈ s, ∯ ζ in T(c, R), F i ζ := by
  classical
  induction s using Finset.induction with
  | empty =>
      simp only [Finset.sum_empty]
      exact torusIntegral_zero c R
  | insert a s ha ih =>
      have h1 : TorusIntegrable (F a) c R := h a (Finset.mem_insert_self a s)
      have h2 : TorusIntegrable (fun ζ => ∑ i ∈ s, F i ζ) c R :=
        torusIntegrable_finsetSum s F fun i hi => h i (Finset.mem_insert_of_mem hi)
      have hfun : (fun ζ => ∑ i ∈ insert a s, F i ζ) = fun ζ => F a ζ + ∑ i ∈ s, F i ζ := by
        funext ζ
        rw [Finset.sum_insert ha]
      rw [hfun, torusIntegral_add h1 h2, ih fun i hi => h i (Finset.mem_insert_of_mem hi),
        Finset.sum_insert ha]

end TorusIntegralSums

section Coefficients

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

theorem norm_two_pi_I : ‖(2 * Real.pi * Complex.I : ℂ)‖ = 2 * Real.pi := by
  rw [norm_mul, Complex.norm_I, mul_one, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg Real.pi_pos.le]
  norm_num

theorem norm_torusMap_sub_center (c : Fin n → ℂ) (R : ℝ) (θ : Fin n → ℝ) (i : Fin n) :
    ‖torusMap c (fun _ => R) θ i - c i‖ = |R| := by
  show ‖c i + (R : ℂ) * Complex.exp (θ i * Complex.I) - c i‖ = |R|
  rw [add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    Complex.norm_exp_ofReal_mul_I, mul_one]

/-- **The Cauchy coefficient of a multi-index** on a polydisc. -/
noncomputable def polydiscCoeff (f : (Fin n → ℂ) → E) (c : Fin n → ℂ) (R : ℝ)
    (m : Fin n → ℕ) : E :=
  ((2 * Real.pi * Complex.I) ^ n : ℂ)⁻¹ •
    ∯ ζ in T(c, fun _ => R), (∏ i, (ζ i - c i) ^ (m i + 1))⁻¹ • f ζ

omit [CompleteSpace E] in
/-- The integrand of a Cauchy coefficient is continuous on the torus. -/
theorem polydiscCoeff_continuous {f : (Fin n → ℂ) → E} (hf : Differentiable ℂ f)
    (c : Fin n → ℂ) {R : ℝ} (hR : 0 < R) (m : Fin n → ℕ) :
    Continuous fun θ : Fin n → ℝ =>
      (∏ i, (torusMap c (fun _ => R) θ i - c i) ^ (m i + 1))⁻¹ • f (torusMap c (fun _ => R) θ) := by
  have hmap : Continuous fun θ : Fin n → ℝ => torusMap c (fun _ => R) θ :=
    continuous_torusMap c fun _ => R
  have hne : ∀ θ : Fin n → ℝ,
      (∏ i, (torusMap c (fun _ => R) θ i - c i) ^ (m i + 1)) ≠ 0 := by
    intro θ
    refine Finset.prod_ne_zero_iff.2 fun i _ => pow_ne_zero _ ?_
    intro hcon
    have := norm_torusMap_sub_center c R θ i
    rw [hcon, norm_zero] at this
    exact absurd this.symm (by positivity)
  refine Continuous.smul ?_ (hf.continuous.comp hmap)
  refine Continuous.inv₀ ?_ hne
  refine continuous_finsetProd _ fun i _ => ?_
  exact (((continuous_apply i).comp hmap).sub continuous_const).pow _

omit [CompleteSpace E] in
/-- The Cauchy coefficient integrand is torus integrable. -/
theorem polydiscCoeff_integrable {f : (Fin n → ℂ) → E} (hf : Differentiable ℂ f)
    (c : Fin n → ℂ) {R : ℝ} (hR : 0 < R) (m : Fin n → ℕ) :
    TorusIntegrable (fun ζ => (∏ i, (ζ i - c i) ^ (m i + 1))⁻¹ • f ζ) c (fun _ => R) :=
  torusIntegrable_of_continuous (polydiscCoeff_continuous hf c hR m)

omit [CompleteSpace E] in
/-- **The Cauchy coefficients are bounded by the maximum of the function on the torus** divided by
the power of the radius given by the total degree. -/
theorem norm_polydiscCoeff_le {f : (Fin n → ℂ) → E} (c : Fin n → ℂ)
    {R : ℝ} (hR : 0 < R) {M : ℝ}
    (hM : ∀ θ : Fin n → ℝ, ‖f (torusMap c (fun _ => R) θ)‖ ≤ M) (m : Fin n → ℕ) :
    ‖polydiscCoeff f c R m‖ ≤ M / R ^ (∑ i, m i) := by
  have hMnn : 0 ≤ M := le_trans (norm_nonneg _) (hM fun _ => 0)
  have hbound : ∀ θ : Fin n → ℝ,
      ‖(∏ i, (torusMap c (fun _ => R) θ i - c i) ^ (m i + 1))⁻¹ •
        f (torusMap c (fun _ => R) θ)‖ ≤ M / R ^ (∑ i, (m i + 1)) := by
    intro θ
    rw [norm_smul, norm_inv, norm_prod]
    have hnorm : ∀ i : Fin n, ‖(torusMap c (fun _ => R) θ i - c i) ^ (m i + 1)‖ =
        R ^ (m i + 1) := by
      intro i
      rw [norm_pow, norm_torusMap_sub_center, abs_of_pos hR]
    rw [Finset.prod_congr rfl fun i _ => hnorm i, ← Finset.prod_pow_eq_pow_sum]
    rw [div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_left (hM θ) (by positivity)
  have hint := norm_torusIntegral_le_of_norm_le_const
    (f := fun ζ => (∏ i, (ζ i - c i) ^ (m i + 1))⁻¹ • f ζ) (c := c) (R := fun _ : Fin n => R)
    hbound
  rw [polydiscCoeff, norm_smul, norm_inv, norm_pow, norm_two_pi_I]
  have hprod : (∏ _i : Fin n, |R|) = R ^ n := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, abs_of_pos hR]
  have hsum : ∑ i, (m i + 1) = (∑ i, m i) + n := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
      mul_one]
  rw [hprod, hsum] at hint
  calc ((2 * Real.pi) ^ n)⁻¹ * ‖∯ ζ in T(c, fun _ => R), (∏ i, (ζ i - c i) ^ (m i + 1))⁻¹ • f ζ‖
      ≤ ((2 * Real.pi) ^ n)⁻¹ * ((2 * π) ^ n * R ^ n * (M / R ^ ((∑ i, m i) + n))) := by
        refine mul_le_mul_of_nonneg_left hint ?_
        positivity
    _ = M / R ^ (∑ i, m i) := by
        rw [pow_add]
        field_simp

end Coefficients

section Series

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- **The formal multilinear series of a holomorphic function on a polydisc.** -/
noncomputable def polydiscSeries (f : (Fin n → ℂ) → E) (c : Fin n → ℂ) (R : ℝ) :
    FormalMultilinearSeries ℂ (Fin n → ℂ) E := fun k =>
  ∑ m ∈ (Finset.Nat.antidiagonalTuple n k).attach,
    (multiIndexCMM m.1 (Finset.Nat.mem_antidiagonalTuple.1 m.2)).smulRight
      (polydiscCoeff f c R m.1)

/-- The number of multi-indices of a given total degree is at most a polynomial in the degree. -/
theorem card_antidiagonalTuple_le (n k : ℕ) :
    (Finset.Nat.antidiagonalTuple n k).card ≤ (k + 1) ^ n := by
  classical
  have hsub : Finset.Nat.antidiagonalTuple n k ⊆
      Fintype.piFinset fun _ : Fin n => Finset.range (k + 1) := by
    intro m hm
    rw [Fintype.mem_piFinset]
    intro i
    rw [Finset.mem_range]
    have hle : m i ≤ k := by
      rw [← Finset.Nat.mem_antidiagonalTuple.1 hm]
      exact Finset.single_le_sum (f := m) (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
    omega
  calc (Finset.Nat.antidiagonalTuple n k).card
      ≤ (Fintype.piFinset fun _ : Fin n => Finset.range (k + 1)).card := Finset.card_le_card hsub
    _ = (k + 1) ^ n := by simp

omit [CompleteSpace E] in
/-- **The terms of the series are bounded** by the maximum of the function on the torus times the
number of multi-indices of that degree, divided by the power of the radius. -/
theorem norm_polydiscSeries_le {f : (Fin n → ℂ) → E} (c : Fin n → ℂ)
    {R : ℝ} (hR : 0 < R) {M : ℝ}
    (hM : ∀ θ : Fin n → ℝ, ‖f (torusMap c (fun _ => R) θ)‖ ≤ M) (k : ℕ) :
    ‖polydiscSeries f c R k‖ ≤ ((k + 1) ^ n : ℕ) * (M / R ^ k) := by
  have hMnn : 0 ≤ M := le_trans (norm_nonneg _) (hM fun _ => 0)
  have hterm : ∀ m ∈ (Finset.Nat.antidiagonalTuple n k).attach,
      ‖(multiIndexCMM m.1 (Finset.Nat.mem_antidiagonalTuple.1 m.2)).smulRight
        (polydiscCoeff f c R m.1)‖ ≤ M / R ^ k := by
    intro m _
    rw [ContinuousMultilinearMap.norm_smulRight]
    have h1 : ‖multiIndexCMM m.1 (Finset.Nat.mem_antidiagonalTuple.1 m.2)‖ ≤ 1 :=
      multiIndexCMM_norm_le _ _
    have h2 : ‖polydiscCoeff f c R m.1‖ ≤ M / R ^ (∑ i, m.1 i) :=
      norm_polydiscCoeff_le c hR hM m.1
    have hk : ∑ i, m.1 i = k := Finset.Nat.mem_antidiagonalTuple.1 m.2
    rw [hk] at h2
    calc ‖multiIndexCMM m.1 (Finset.Nat.mem_antidiagonalTuple.1 m.2)‖ *
          ‖polydiscCoeff f c R m.1‖
        ≤ 1 * (M / R ^ k) :=
          mul_le_mul h1 h2 (norm_nonneg _) zero_le_one
      _ = M / R ^ k := one_mul _
  calc ‖polydiscSeries f c R k‖
      ≤ ∑ _m ∈ (Finset.Nat.antidiagonalTuple n k).attach, M / R ^ k :=
        le_trans (norm_sum_le _ _) (Finset.sum_le_sum hterm)
    _ = ((Finset.Nat.antidiagonalTuple n k).card : ℝ) * (M / R ^ k) := by
        rw [Finset.sum_const, Finset.card_attach, nsmul_eq_mul]
    _ ≤ ((k + 1) ^ n : ℕ) * (M / R ^ k) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        exact_mod_cast card_antidiagonalTuple_le n k

end Series

end GaloisForLFunctions.HTGeometry
