import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Analysis.Normed.Module.RCLike.Basic

/-! Exact classification of real vectors annihilating all but the top initial moment. -/

open scoped BigOperators

noncomputable section
namespace RHTower

/-- Reciprocal node-difference products, before sup-norm normalization. -/
def finiteWeilMomentWeights {n : ℕ} (h : Fin (n + 1) → ℝ) : Fin (n + 1) → ℝ :=
  Lagrange.nodalWeight Finset.univ h

theorem finiteWeilMomentWeights_ne_zero {n : ℕ} (h : Fin (n + 1) → ℝ)
    (hinj : Function.Injective h) (i : Fin (n + 1)) : finiteWeilMomentWeights h i ≠ 0 :=
  Lagrange.nodalWeight_ne_zero hinj.injOn (Finset.mem_univ i)

theorem finiteWeilMomentWeights_norm_pos {n : ℕ} (h : Fin (n + 1) → ℝ)
    (hinj : Function.Injective h) : 0 < ‖finiteWeilMomentWeights h‖ := by
  apply norm_pos_iff.mpr
  intro hz
  exact finiteWeilMomentWeights_ne_zero h hinj 0 (congrFun hz 0)

/-- Initial moments of the interpolation weights are zero except for the top one. -/
theorem finiteWeilMomentWeights_moment {n : ℕ} (h : Fin (n + 1) → ℝ)
    (hinj : Function.Injective h) (p : ℕ) (hp : p ≤ n) :
    ∑ i, finiteWeilMomentWeights h i * h i ^ p = if n = p then 1 else 0 := by
  have hdeg : (Polynomial.X ^ p : Polynomial ℝ).degree <
      (Finset.univ : Finset (Fin (n + 1))).card := by
    rw [Polynomial.degree_X_pow, Finset.card_univ, Fintype.card_fin]
    exact_mod_cast (show p < n + 1 by omega)
  have hid := Lagrange.coeff_eq_sum (s := (Finset.univ : Finset (Fin (n + 1))))
    (v := h) hinj.injOn (P := (Polynomial.X ^ p : Polynomial ℝ)) hdeg
  simpa only [Finset.card_univ, Fintype.card_fin, Nat.add_sub_cancel,
    Polynomial.coeff_X_pow, Polynomial.eval_X_pow, finiteWeilMomentWeights,
    Lagrange.nodalWeight, Finset.prod_inv_distrib, div_eq_mul_inv, mul_comm] using hid.symm

/-- The first surviving moment is the exact scalar multiplying the nodal weights. -/
theorem finiteWeilMomentWeights_span {n : ℕ} (h : Fin (n + 1) → ℝ)
    (hinj : Function.Injective h) (c : Fin (n + 1) → ℝ)
    (hm : ∀ p < n, ∑ i, c i * h i ^ p = 0) :
    c = (∑ i, c i * h i ^ n) • finiteWeilMomentWeights h := by
  let a : ℝ := ∑ i, c i * h i ^ n
  have hz : (c - a • finiteWeilMomentWeights h) = 0 := by
    apply Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero hinj
    intro p
    change (∑ j, (c j - a * finiteWeilMomentWeights h j) * h j ^ (p : ℕ)) = 0
    simp only [sub_mul, Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum]
    rw [finiteWeilMomentWeights_moment h hinj p (by have := p.isLt; omega)]
    by_cases hp : n = (p : ℕ)
    · rw [← hp]
      simp only [if_true, mul_one, a, sub_self]
    · rw [if_neg hp, mul_zero, sub_zero]
      exact hm p (by have := p.isLt; omega)
  exact sub_eq_zero.mp hz

/-- Distinct nodes force every nonzero annihilator to have full support. -/
theorem finiteWeil_moment_annihilator_full_support {n : ℕ} (h : Fin (n + 1) → ℝ)
    (hinj : Function.Injective h) (c : Fin (n + 1) → ℝ) (hc : c ≠ 0)
    (hm : ∀ p < n, ∑ i, c i * h i ^ p = 0) : ∀ i, c i ≠ 0 := by
  have hs := finiteWeilMomentWeights_span h hinj c hm
  have ha : (∑ i, c i * h i ^ n) ≠ 0 := by
    intro ha
    apply hc
    rw [hs, ha, zero_smul]
  intro i
  rw [hs]
  exact mul_ne_zero ha (finiteWeilMomentWeights_ne_zero h hinj i)

/-- The canonical unit vector on the one-dimensional moment-annihilator line. -/
def finiteWeilNormalizedMomentDual {n : ℕ} (h : Fin (n + 1) → ℝ) : Fin (n + 1) → ℝ :=
  ‖finiteWeilMomentWeights h‖⁻¹ • finiteWeilMomentWeights h

theorem finiteWeilNormalizedMomentDual_norm {n : ℕ} (h : Fin (n + 1) → ℝ)
    (hinj : Function.Injective h) : ‖finiteWeilNormalizedMomentDual h‖ = 1 :=
  norm_smul_inv_norm (𝕜 := ℝ) (norm_pos_iff.mp (finiteWeilMomentWeights_norm_pos h hinj))

theorem finiteWeilNormalizedMomentDual_ne_zero {n : ℕ} (h : Fin (n + 1) → ℝ)
    (hinj : Function.Injective h) (i : Fin (n + 1)) : finiteWeilNormalizedMomentDual h i ≠ 0 :=
  mul_ne_zero (inv_ne_zero (finiteWeilMomentWeights_norm_pos h hinj).ne')
    (finiteWeilMomentWeights_ne_zero h hinj i)

theorem finiteWeilNormalizedMomentDual_moment {n : ℕ} (h : Fin (n + 1) → ℝ)
    (hinj : Function.Injective h) (p : ℕ) (hp : p < n) :
    ∑ i, finiteWeilNormalizedMomentDual h i * h i ^ p = 0 := by
  simp only [finiteWeilNormalizedMomentDual, Pi.smul_apply, smul_eq_mul, mul_assoc,
    ← Finset.mul_sum, finiteWeilMomentWeights_moment h hinj p hp.le, if_neg hp.ne', mul_zero]

/-- The canonical pairing is the top interpolation coefficient divided by the
sup norm of the unnormalized nodal weights. -/
theorem finiteWeilNormalizedMomentDual_pairing {n : ℕ} (h : Fin (n + 1) → ℝ)
    (hinj : Function.Injective h) (y : Fin (n + 1) → ℝ) :
    ∑ i, y i * finiteWeilNormalizedMomentDual h i =
      (Lagrange.interpolate Finset.univ h y).coeff n / ‖finiteWeilMomentWeights h‖ := by
  have hc := Lagrange.coeff_eq_sum (s := (Finset.univ : Finset (Fin (n + 1))))
    (v := h) hinj.injOn (P := Lagrange.interpolate Finset.univ h y)
    (Lagrange.degree_interpolate_lt y hinj.injOn)
  have hev (i : Fin (n + 1)) :
      (Lagrange.interpolate Finset.univ h y).eval (h i) = y i :=
    Lagrange.eval_interpolate_at_node y hinj.injOn (Finset.mem_univ i)
  have hid : (Lagrange.interpolate Finset.univ h y).coeff n =
      ∑ i, y i * finiteWeilMomentWeights h i := by
    simpa only [Finset.card_univ, Fintype.card_fin, Nat.add_sub_cancel, hev,
      finiteWeilMomentWeights, Lagrange.nodalWeight, Finset.prod_inv_distrib,
      div_eq_mul_inv] using hc
  rw [hid]
  simp only [finiteWeilNormalizedMomentDual, Pi.smul_apply, smul_eq_mul,
    div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Sup-norm normalization leaves exactly the two orientations of the canonical dual. -/
theorem finiteWeilNormalizedMomentDual_classification {n : ℕ} (h : Fin (n + 1) → ℝ)
    (hinj : Function.Injective h) (c : Fin (n + 1) → ℝ) (hc : ‖c‖ = 1)
    (hm : ∀ p < n, ∑ i, c i * h i ^ p = 0) :
    c = finiteWeilNormalizedMomentDual h ∨ c = -finiteWeilNormalizedMomentDual h := by
  let a : ℝ := ∑ i, c i * h i ^ n
  have hs : c = a • finiteWeilMomentWeights h := finiteWeilMomentWeights_span h hinj c hm
  have hpos := finiteWeilMomentWeights_norm_pos h hinj
  have hnorm := hc
  rw [hs, norm_smul, Real.norm_eq_abs] at hnorm
  have habs : |a| = ‖finiteWeilMomentWeights h‖⁻¹ :=
    (mul_eq_one_iff_eq_inv₀ hpos.ne').mp hnorm
  have hsign : a = ‖finiteWeilMomentWeights h‖⁻¹ ∨ a = -‖finiteWeilMomentWeights h‖⁻¹ :=
    abs_eq_abs.mp (by rw [abs_of_pos (inv_pos.mpr hpos)]; exact habs)
  rcases hsign with ha | ha
  · left
    rw [hs, ha]
    rfl
  · right
    rw [hs, ha]
    funext i
    change (-‖finiteWeilMomentWeights h‖⁻¹) * finiteWeilMomentWeights h i =
      -(‖finiteWeilMomentWeights h‖⁻¹ * finiteWeilMomentWeights h i)
    ring

end RHTower
