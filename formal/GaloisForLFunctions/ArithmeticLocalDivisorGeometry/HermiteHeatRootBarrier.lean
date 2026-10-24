import GaloisForLFunctions.ArithmeticLocalDivisorGeometry.HermiteRootEdge
import GaloisForLFunctions.ArithmeticLocalDivisorGeometry.HermiteHeatNormalization
import GaloisForLFunctions.ArithmeticLocalDivisorGeometry.PolynomialHeatDilation
import GaloisForLFunctions.HTGeometry.PolynomialHeatNonrealCount

/-!
# Sharp Hermite barriers for polynomial heat

Positive Hermite weights bound every stationary point of inverse heat. At the boundary,
all intermediate coefficients vanish; a stationary root determines the polynomial up to scale.
Global nonnegativity supplies stationarity without any parity assumption.
-/

open Polynomial
open GaloisForLFunctions.HTGeometry
namespace GaloisForLFunctions.ArithmeticLocalDivisorGeometry
noncomputable section

private theorem forwardHeat_sum {ι : Type*} (s : ℝ) (A : Finset ι) (f : ι → ℝ[X]) :
    forwardPolyHeat s (∑ i ∈ A, f i) = ∑ i ∈ A, forwardPolyHeat s (f i) := by
  classical
  induction A using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using forwardPolyHeat_C s 0
  | insert a A ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, forwardPolyHeat_add, ih]

/-- Inverse unit Gaussian heat expands a polynomial in the Hermite basis. -/
theorem inverseHeat_hermite_expansion (q : ℝ[X]) :
    forwardPolyHeat (-1 / 2) q =
      ∑ j ∈ Finset.range (q.natDegree + 1), C (q.coeff j) * hermiteReal j := by
  have h := congrArg (forwardPolyHeat (-1 / 2)) q.as_sum_range_C_mul_X_pow
  rw [forwardHeat_sum] at h
  simpa only [forwardPolyHeat_C_mul, forwardPolyHeat_neg_half_X_pow] using h

/-- The derivative of inverse heat has positive Hermite weights beyond the derivative edge. -/
theorem inverseHeat_derivative_eval (q : ℝ[X]) (x : ℝ) :
    (derivative (forwardPolyHeat (-1 / 2) q)).eval x =
      ∑ j ∈ Finset.range q.natDegree,
        q.coeff (j + 1) * ((j : ℝ) + 1) * (hermiteReal j).eval x := by
  have hzero : derivative (hermiteReal 0) = 0 := by simp [hermiteReal, hermite_zero]
  rw [inverseHeat_hermite_expansion, derivative_sum, eval_finsetSum, Finset.sum_range_succ']
  simp only [derivative_C_mul, derivative_hermiteReal_succ, hzero, eval_mul, eval_C,
    eval_zero, mul_zero, add_zero]
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem top_coeff_pos {q : ℝ[X]} {n : ℕ} (hdeg : q.natDegree = n + 2)
    (hq : CoeffNonneg q) : 0 < q.coeff (n + 2) := by
  have hne : q ≠ 0 := by intro hz; rw [hz, natDegree_zero] at hdeg; omega
  have hc : q.coeff (n + 2) ≠ 0 := by
    rw [← hdeg]
    exact leadingCoeff_ne_zero.mpr hne
  exact lt_of_le_of_ne (hq _) hc.symm

/-- Inverse heat of a coefficient-positive polynomial increases past its exact Hermite edge. -/
theorem inverseHeat_derivative_pos_of_edge_lt {q : ℝ[X]} {n : ℕ}
    (hdeg : q.natDegree = n + 2) (hq : CoeffNonneg q) {x : ℝ}
    (hx : hermiteEdge n < x) : 0 < (derivative (forwardPolyHeat (-1 / 2) q)).eval x := by
  rw [inverseHeat_derivative_eval, hdeg, show n + 2 = (n + 1) + 1 by omega,
    Finset.sum_range_succ]
  apply add_pos_of_nonneg_of_pos
  · exact Finset.sum_nonneg fun j hj => mul_nonneg
      (mul_nonneg (hq _) (by positivity))
      (hermite_eval_pos_of_edge_lt (by have := Finset.mem_range.mp hj; omega) hx).le
  · exact mul_pos (mul_pos (top_coeff_pos hdeg hq) (by positivity))
      (hermite_eval_pos_of_edge_lt (le_refl _) hx)

/-- Every stationary point lies at or below the largest zero of the preceding Hermite degree. -/
theorem inverseHeat_stationary_le_edge {q : ℝ[X]} {n : ℕ}
    (hdeg : q.natDegree = n + 2) (hq : CoeffNonneg q) {x : ℝ}
    (hx : (derivative (forwardPolyHeat (-1 / 2) q)).eval x = 0) : x ≤ hermiteEdge n := by
  by_contra hn
  have hp := inverseHeat_derivative_pos_of_edge_lt hdeg hq (lt_of_not_ge hn)
  rw [hx] at hp
  exact (lt_irrefl (0 : ℝ)) hp

/-- Boundary stationarity kills every intermediate heated coefficient, including odd orders. -/
theorem inverseHeat_edge_stationary_coeff {q : ℝ[X]} {n : ℕ}
    (hdeg : q.natDegree = n + 2) (hq : CoeffNonneg q)
    (hx : (derivative (forwardPolyHeat (-1 / 2) q)).eval (hermiteEdge n) = 0) :
    ∀ j ≤ n, q.coeff (j + 1) = 0 := by
  have he := inverseHeat_derivative_eval q (hermiteEdge n)
  rw [hx, hdeg, show n + 2 = (n + 1) + 1 by omega, Finset.sum_range_succ,
    hermiteEdge_isRoot, mul_zero, add_zero] at he
  have hnon : ∀ j ∈ Finset.range (n + 1),
      0 ≤ q.coeff (j + 1) * ((j : ℝ) + 1) * (hermiteReal j).eval (hermiteEdge n) := by
    intro j hj
    exact mul_nonneg (mul_nonneg (hq _) (by positivity))
      (hermite_eval_pos_at_edge (by have := Finset.mem_range.mp hj; omega)).le
  have hz := (Finset.sum_eq_zero_iff_of_nonneg hnon).mp he.symm
  intro j hj
  have hterm := hz j (Finset.mem_range.mpr (by omega))
  have hp : 0 < ((j : ℝ) + 1) * (hermiteReal j).eval (hermiteEdge n) :=
    mul_pos (by positivity) (hermite_eval_pos_at_edge hj)
  rw [mul_assoc] at hterm
  exact (mul_eq_zero.mp hterm).resolve_right hp.ne'

/-- Equality leaves precisely a constant term and the positive leading monomial after heat. -/
theorem inverseHeat_edge_stationary_shape {q : ℝ[X]} {n : ℕ}
    (hdeg : q.natDegree = n + 2) (hq : CoeffNonneg q)
    (hx : (derivative (forwardPolyHeat (-1 / 2) q)).eval (hermiteEdge n) = 0) :
    q = C (q.coeff 0) + C (q.coeff (n + 2)) * X ^ (n + 2) := by
  have hz := inverseHeat_edge_stationary_coeff hdeg hq hx
  have he := q.as_sum_range_C_mul_X_pow
  rw [hdeg, Finset.sum_range_succ, Finset.sum_range_succ'] at he
  have hsum : (∑ j ∈ Finset.range (n + 1), C (q.coeff (j + 1)) * X ^ (j + 1)) = (0 : ℝ[X]) := by
    apply Finset.sum_eq_zero
    intro j hj
    rw [hz j (by have := Finset.mem_range.mp hj; omega), map_zero, zero_mul]
  simpa only [hsum, zero_add, pow_zero, mul_one] using he

/-- A boundary stationary root determines the inverse heat up to a positive scalar. -/
theorem inverseHeat_edge_root_rigidity {q : ℝ[X]} {n : ℕ}
    (hdeg : q.natDegree = n + 2) (hq : CoeffNonneg q)
    (hstat : (derivative (forwardPolyHeat (-1 / 2) q)).eval (hermiteEdge n) = 0)
    (hroot : (forwardPolyHeat (-1 / 2) q).eval (hermiteEdge n) = 0) :
    ∃ c : ℝ, 0 < c ∧ forwardPolyHeat (-1 / 2) q =
      C c * (hermiteReal (n + 2) - C ((hermiteReal (n + 2)).eval (hermiteEdge n))) := by
  refine ⟨q.coeff (n + 2), top_coeff_pos hdeg hq, ?_⟩
  have he := congrArg (forwardPolyHeat (-1 / 2)) (inverseHeat_edge_stationary_shape hdeg hq hstat)
  rw [forwardPolyHeat_add, forwardPolyHeat_C, forwardPolyHeat_C_mul,
    forwardPolyHeat_neg_half_X_pow] at he
  have hv := congrArg (fun p : ℝ[X] => p.eval (hermiteEdge n)) he
  rw [hroot, eval_add, eval_mul, eval_C, eval_C] at hv
  have hconst : q.coeff 0 = -q.coeff (n + 2) * (hermiteReal (n + 2)).eval (hermiteEdge n) := by
    linarith only [hv]
  rw [he, hconst, map_mul, map_neg]
  ring

private theorem inverse_unit_heat (p : ℝ[X]) :
    forwardPolyHeat (-1 / 2) (forwardPolyHeat (1 / 2) p) = p := by
  rw [forwardPolyHeat_comp, show (-1 / 2 : ℝ) + 1 / 2 = 0 by ring, forwardPolyHeat_zero]

private theorem degree_unit_heat {p : ℝ[X]} {n : ℕ} (hdeg : p.natDegree = n + 2) :
    (forwardPolyHeat (1 / 2) p).natDegree = n + 2 := by
  have hp : p ≠ 0 := by intro hz; rw [hz, natDegree_zero] at hdeg; omega
  rw [forwardPolyHeat_eq_polyHeat, (natDegree_polyHeat _ hp).1, hdeg]

/-- Unit Gaussian heat bounds every stationary point; no parity or real-axis sign is needed. -/
theorem stationary_le_hermiteEdge_of_heat_cone {p : ℝ[X]} {n : ℕ}
    (hdeg : p.natDegree = n + 2) (hc : CoeffNonneg (forwardPolyHeat (1 / 2) p)) {x : ℝ}
    (hx : (derivative p).eval x = 0) : x ≤ hermiteEdge n := by
  apply inverseHeat_stationary_le_edge (degree_unit_heat hdeg) hc
  rwa [inverse_unit_heat]

/-- A zero of a globally nonnegative polynomial is stationary, hence obeys the sharp edge. -/
theorem nonnegative_root_le_hermiteEdge_of_heat_cone {p : ℝ[X]} {n : ℕ}
    (hdeg : p.natDegree = n + 2) (hp : ∀ x : ℝ, 0 ≤ p.eval x)
    (hc : CoeffNonneg (forwardPolyHeat (1 / 2) p)) {x : ℝ} (hx : p.eval x = 0) :
    x ≤ hermiteEdge n := by
  have hmin : IsLocalMin p.eval x := Filter.Eventually.of_forall fun y => by rw [hx]; exact hp y
  exact stationary_le_hermiteEdge_of_heat_cone hdeg hc (hmin.hasDerivAt_eq_zero (p.hasDerivAt x))

/-- At the boundary, a globally nonnegative polynomial is the shifted Hermite extremizer. -/
theorem nonnegative_edge_root_rigidity {p : ℝ[X]} {n : ℕ}
    (hdeg : p.natDegree = n + 2) (hp : ∀ x : ℝ, 0 ≤ p.eval x)
    (hc : CoeffNonneg (forwardPolyHeat (1 / 2) p))
    (hx : p.eval (hermiteEdge n) = 0) :
    ∃ c : ℝ, 0 < c ∧ p =
      C c * (hermiteReal (n + 2) - C ((hermiteReal (n + 2)).eval (hermiteEdge n))) := by
  have hmin : IsLocalMin p.eval (hermiteEdge n) :=
    Filter.Eventually.of_forall fun y => by rw [hx]; exact hp y
  have hd := hmin.hasDerivAt_eq_zero (p.hasDerivAt (hermiteEdge n))
  have h := inverseHeat_edge_root_rigidity (degree_unit_heat hdeg) hc
    (by rwa [inverse_unit_heat]) (by rwa [inverse_unit_heat])
  simpa only [inverse_unit_heat] using h

private theorem degree_positive_dilation {p : ℝ[X]} {n : ℕ}
    (hdeg : p.natDegree = n + 2) {r : ℝ} (hr : 0 < r) :
    (p.comp (C r * X)).natDegree = n + 2 := by
  rw [natDegree_comp, natDegree_C_mul hr.ne', natDegree_X, mul_one, hdeg]

/-- Dilation converts the exact stationary-point barrier to arbitrary positive Gaussian scale. -/
theorem stationary_le_scaled_hermiteEdge_of_heat_cone {p : ℝ[X]} {n : ℕ} {r : ℝ}
    (hr : 0 < r) (hdeg : p.natDegree = n + 2)
    (hc : CoeffNonneg (forwardPolyHeat (r ^ 2 / 2) p)) {x : ℝ}
    (hx : (derivative p).eval x = 0) : x ≤ r * hermiteEdge n := by
  have ht : (1 / 2 : ℝ) * r ^ 2 = r ^ 2 / 2 := by ring
  have hcone : CoeffNonneg (forwardPolyHeat (1 / 2) (p.comp (C r * X))) :=
    (coeffNonneg_heat_dilation_iff (1 / 2) hr p).mpr (by simpa only [ht] using hc)
  have harg : r * (x / r) = x := by field_simp
  have hstat : (derivative (p.comp (C r * X))).eval (x / r) = 0 := by
    rw [derivative_comp, derivative_C_mul, derivative_X, mul_one, eval_mul, eval_C,
      eval_comp, eval_mul, eval_C, eval_X, harg, hx, mul_zero]
  have h := stationary_le_hermiteEdge_of_heat_cone (degree_positive_dilation hdeg hr) hcone hstat
  have hb := (div_le_iff₀ hr).mp h
  simpa only [mul_comm] using hb

/-- The sharp Gaussian stationary-point barrier, with heat parameter `λ/2`. -/
theorem stationary_le_sqrt_mul_hermiteEdge {p : ℝ[X]} {n : ℕ} {lam : ℝ}
    (hlam : 0 < lam) (hdeg : p.natDegree = n + 2)
    (hc : CoeffNonneg (forwardPolyHeat (lam / 2) p)) {x : ℝ}
    (hx : (derivative p).eval x = 0) : x ≤ Real.sqrt lam * hermiteEdge n := by
  apply stationary_le_scaled_hermiteEdge_of_heat_cone (Real.sqrt_pos.mpr hlam) hdeg
    (by simpa only [Real.sq_sqrt hlam.le] using hc) hx

/-- Global nonnegativity turns every root into a stationary point; evenness is unnecessary. -/
theorem nonnegative_root_le_sqrt_mul_hermiteEdge {p : ℝ[X]} {n : ℕ} {lam : ℝ}
    (hlam : 0 < lam) (hdeg : p.natDegree = n + 2) (hp : ∀ y : ℝ, 0 ≤ p.eval y)
    (hc : CoeffNonneg (forwardPolyHeat (lam / 2) p)) {x : ℝ} (hx : p.eval x = 0) :
    x ≤ Real.sqrt lam * hermiteEdge n := by
  have hmin : IsLocalMin p.eval x := Filter.Eventually.of_forall fun y => by rw [hx]; exact hp y
  exact stationary_le_sqrt_mul_hermiteEdge hlam hdeg hc (hmin.hasDerivAt_eq_zero (p.hasDerivAt x))

/-- At every positive scale, boundary equality determines the entire polynomial. -/
theorem scaled_nonnegative_edge_root_rigidity {p : ℝ[X]} {n : ℕ} {r : ℝ}
    (hr : 0 < r) (hdeg : p.natDegree = n + 2) (hp : ∀ x : ℝ, 0 ≤ p.eval x)
    (hc : CoeffNonneg (forwardPolyHeat (r ^ 2 / 2) p))
    (hx : p.eval (r * hermiteEdge n) = 0) :
    ∃ c : ℝ, 0 < c ∧ p = C c *
      ((hermiteReal (n + 2)).comp (C r⁻¹ * X) - C ((hermiteReal (n + 2)).eval (hermiteEdge n))) := by
  have ht : (1 / 2 : ℝ) * r ^ 2 = r ^ 2 / 2 := by ring
  have hcone : CoeffNonneg (forwardPolyHeat (1 / 2) (p.comp (C r * X))) :=
    (coeffNonneg_heat_dilation_iff (1 / 2) hr p).mpr (by simpa only [ht] using hc)
  have hpos : ∀ x : ℝ, 0 ≤ (p.comp (C r * X)).eval x := by
    intro x
    simpa only [eval_comp, eval_mul, eval_C, eval_X] using hp (r * x)
  have hzero : (p.comp (C r * X)).eval (hermiteEdge n) = 0 := by
    simpa only [eval_comp, eval_mul, eval_C, eval_X] using hx
  obtain ⟨c, hcpos, he⟩ := nonnegative_edge_root_rigidity (degree_positive_dilation hdeg hr)
    hpos hcone hzero
  refine ⟨c, hcpos, ?_⟩
  have hinv : (C r * X).comp (C r⁻¹ * X) = (X : ℝ[X]) := by
    simp only [mul_comp, C_comp, X_comp]
    rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hr.ne', map_one, one_mul]
  have h := congrArg (fun q : ℝ[X] => q.comp (C r⁻¹ * X)) he
  simpa only [comp_assoc, hinv, comp_X, mul_comp, C_comp, sub_comp] using h

end
end GaloisForLFunctions.ArithmeticLocalDivisorGeometry
