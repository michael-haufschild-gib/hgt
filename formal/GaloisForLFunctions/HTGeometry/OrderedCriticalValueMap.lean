import GaloisForLFunctions.HTGeometry.PolynomialAntiderivative
import GaloisForLFunctions.HTGeometry.PolynomialCriticalZeroFiber
import GaloisForLFunctions.HTGeometry.HomogeneousProperMap
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.Analysis.Normed.Module.FiniteDimension

open Polynomial
open scoped BigOperators
namespace GaloisForLFunctions.HTGeometry.OrderedCriticalValueMap
noncomputable section

abbrev Parameter (n : ℕ) := (Fin n → ℂ) × ℂ

def position {n : ℕ} (v : Parameter n) : Fin (n + 1) → ℂ :=
  Fin.cons (-∑ i, v.1 i) v.1

@[simp] theorem position_succ {n : ℕ} (v : Parameter n) (i : Fin n) :
    position v i.succ = v.1 i := by simp [position]

@[simp] theorem sum_position {n : ℕ} (v : Parameter n) : ∑ j, position v j = 0 := by
  simp [position, Fin.sum_univ_succ]

theorem position_smul {n : ℕ} (t : ℂ) (v : Parameter n) (j : Fin (n + 1)) :
    position (t • v) j = t * position v j := by
  refine Fin.cases ?_ (fun i => ?_) j
  · simp [position, Finset.mul_sum]
  · simp [position]

def criticalProduct {n : ℕ} (v : Parameter n) : ℂ[X] :=
  ∏ j, (X - C (position v j))

@[simp] theorem natDegree_criticalProduct {n : ℕ} (v : Parameter n) :
    (criticalProduct v).natDegree = n + 1 := by
  simp [criticalProduct]

theorem monic_criticalProduct {n : ℕ} (v : Parameter n) : (criticalProduct v).Monic :=
  monic_prod_X_sub_C (position v) Finset.univ

theorem coeff_criticalProduct_pred {n : ℕ} (v : Parameter n) :
    (criticalProduct v).coeff n = 0 := by
  have h := prod_X_sub_C_coeff_card_pred (Finset.univ : Finset (Fin (n + 1)))
    (position v) (by simp)
  simpa only [Finset.card_univ, Fintype.card_fin, Nat.add_sub_cancel, sum_position,
    neg_zero, criticalProduct] using h

def polynomial {n : ℕ} (v : Parameter n) : ℂ[X] :=
  C (n + 2 : ℂ) * polyAntideriv (criticalProduct v) + C (v.2 ^ (n + 2))

@[simp] theorem derivative_polynomial {n : ℕ} (v : Parameter n) :
    (polynomial v).derivative = C (n + 2 : ℂ) * criticalProduct v := by
  simp [polynomial, derivative_polyAntideriv]

@[simp] theorem eval_polynomial_zero {n : ℕ} (v : Parameter n) :
    (polynomial v).eval 0 = v.2 ^ (n + 2) := by
  simp [polynomial, polyAntideriv, Polynomial.eval_finsetSum]

@[simp] theorem natDegree_polynomial {n : ℕ} (v : Parameter n) :
    (polynomial v).natDegree = n + 2 := by
  have hd : (n + 2 : ℂ) ≠ 0 := by exact_mod_cast (show n + 2 ≠ 0 by omega)
  have hh := congrArg Polynomial.natDegree (derivative_polynomial v)
  rw [natDegree_derivative, natDegree_C_mul hd, natDegree_criticalProduct] at hh
  omega

theorem monic_polynomial {n : ℕ} (v : Parameter n) : (polynomial v).Monic := by
  have hd : (n + 2 : ℂ) ≠ 0 := by exact_mod_cast (show n + 2 ≠ 0 by omega)
  have hh := congrArg Polynomial.leadingCoeff (derivative_polynomial v)
  rw [leadingCoeff_derivative, natDegree_polynomial,
    (monic_criticalProduct v).leadingCoeff_C_mul] at hh
  change (polynomial v).leadingCoeff = 1
  apply (mul_right_cancel₀ hd)
  simpa only [Nat.cast_add, Nat.cast_ofNat, one_mul] using hh

theorem centered_polynomial {n : ℕ} (v : Parameter n) : (polynomial v).nextCoeff = 0 := by
  have hd : (n + 1 : ℂ) ≠ 0 := by exact_mod_cast (show n + 1 ≠ 0 by omega)
  have hh := congrArg (fun p : ℂ[X] => p.coeff n) (derivative_polynomial v)
  rw [coeff_derivative, coeff_C_mul, coeff_criticalProduct_pred, mul_zero] at hh
  have hz : (polynomial v).coeff (n + 1) = 0 := (mul_eq_zero.mp hh).resolve_right hd
  rw [nextCoeff_of_natDegree_pos (by rw [natDegree_polynomial]; omega), natDegree_polynomial]
  simpa using hz

def values {n : ℕ} (v : Parameter n) : Fin (n + 1) → ℂ :=
  fun j => (polynomial v).eval (position v j)

/-- Every critical point of the realized polynomial is one of the supplied positions. -/
theorem derivative_root_position {n : ℕ} (v : Parameter n) {z : ℂ}
    (hz : (polynomial v).derivative.IsRoot z) : ∃ j, z = position v j := by
  have hd : (n + 2 : ℂ) ≠ 0 := by exact_mod_cast (show n + 2 ≠ 0 by omega)
  change (polynomial v).derivative.eval z = 0 at hz
  rw [derivative_polynomial, eval_mul, eval_C] at hz
  have hh := (mul_eq_zero.mp hz).resolve_left hd
  simp only [criticalProduct, eval_prod, eval_sub, eval_X, eval_C,
    Finset.prod_eq_zero_iff, Finset.mem_univ, true_and, sub_eq_zero] at hh
  exact hh

/-- The actual ordered critical-value parameter map has no nonzero point in its zero fiber. -/
theorem eq_zero_of_values_eq_zero {n : ℕ} (v : Parameter n) (hv : values v = 0) : v = 0 := by
  have hcrit : ∀ z, (polynomial v).derivative.IsRoot z → (polynomial v).IsRoot z := by
    intro z hz
    obtain ⟨j, rfl⟩ := derivative_root_position v hz
    exact congrFun hv j
  have hp := eq_X_pow_of_centered_critical_roots_zero (polynomial v)
    (by rw [natDegree_polynomial]; omega) (monic_polynomial v) (centered_polynomial v) hcrit
  rw [natDegree_polynomial] at hp
  have hpos : ∀ j, position v j = 0 := by
    intro j
    have hj : (polynomial v).eval (position v j) = 0 := congrFun hv j
    rw [hp, eval_pow, eval_X] at hj
    exact (pow_eq_zero_iff (by omega)).mp hj
  have hc : v.1 = 0 := by
    funext i
    simpa using hpos i.succ
  have hw : v.2 = 0 := by
    have hh := congrArg (fun p : ℂ[X] => p.eval 0) hp
    rw [eval_polynomial_zero, eval_pow, eval_X, zero_pow (by omega)] at hh
    exact (pow_eq_zero_iff (by omega)).mp hh
  exact Prod.ext hc hw

/-- Dilation of every critical position scales the critical product by its exact degree. -/
theorem criticalProduct_comp_smul {n : ℕ} (t : ℂ) (v : Parameter n) :
    (criticalProduct (t • v)).comp (C t * X) = C (t ^ (n + 1)) * criticalProduct v := by
  apply Polynomial.funext
  intro z
  simp only [eval_comp, eval_mul, eval_C, eval_X, criticalProduct, eval_prod, eval_sub,
    position_smul]
  simp_rw [← mul_sub]
  rw [Finset.prod_mul_distrib]
  simp

/-- The chosen primitive and powered constant give homogeneous polynomial realizations. -/
theorem polynomial_comp_smul {n : ℕ} (t : ℂ) (v : Parameter n) :
    (polynomial (t • v)).comp (C t * X) = C (t ^ (n + 2)) * polynomial v := by
  let p := (polynomial (t • v)).comp (C t * X)
  let q := C (t ^ (n + 2)) * polynomial v
  have hder : p.derivative = q.derivative := by
    dsimp [p, q]
    rw [derivative_comp, derivative_C_mul, derivative_X, mul_one, derivative_polynomial,
      mul_comp, C_comp, criticalProduct_comp_smul, derivative_C_mul, derivative_polynomial]
    apply Polynomial.funext
    intro z
    simp only [eval_mul, eval_C]
    ring
  have hzero : p.eval 0 = q.eval 0 := by
    dsimp [p, q]
    simp [eval_comp, mul_pow]
  have hconst := eq_C_of_derivative_eq_zero (p := p - q) (by rw [map_sub, hder, sub_self])
  have hc0 : (p - q).coeff 0 = 0 := by
    rw [coeff_zero_eq_eval_zero, eval_sub, hzero, sub_self]
  rw [hc0, C_0] at hconst
  exact sub_eq_zero.mp hconst

/-- The actual critical-value map is homogeneous of degree n+2. -/
theorem values_smul {n : ℕ} (t : ℂ) (v : Parameter n) :
    values (t • v) = t ^ (n + 2) • values v := by
  funext j
  have hh := congrArg (fun p : ℂ[X] => p.eval (position v j)) (polynomial_comp_smul t v)
  simpa only [values, position_smul, eval_comp, eval_mul, eval_C, eval_X,
    Pi.smul_apply, smul_eq_mul] using hh

/-- Each critical position depends continuously on the parameters. -/
theorem continuous_position (n : ℕ) (j : Fin (n + 1)) :
    Continuous (fun v : Parameter n => position v j) := by
  refine Fin.cases ?_ (fun i => ?_) j
  · simp only [position, Fin.cons_zero]
    fun_prop
  · simp only [position, Fin.cons_succ]
    fun_prop

/-- Every coefficient of the finite critical product is continuous in the parameters. -/
theorem continuous_coeff_criticalProduct (n k : ℕ) :
    Continuous (fun v : Parameter n => (criticalProduct v).coeff k) := by
  by_cases hk : k ≤ n + 1
  · have hformula : ∀ v : Parameter n, (criticalProduct v).coeff k =
        ∑ s ∈ (Finset.univ : Finset (Fin (n + 1))).powersetCard (n + 1 - k),
          ∏ j ∈ s, -(position v j) := by
      intro v
      have hh := Finset.prod_X_add_C_coeff (Finset.univ : Finset (Fin (n + 1)))
        (fun j => -(position v j)) (by simpa using hk)
      simpa only [map_neg, ← sub_eq_add_neg, Finset.card_univ, Fintype.card_fin,
        criticalProduct] using hh
    simp_rw [hformula]
    apply continuous_finsetSum
    intro s _
    apply continuous_finsetProd
    intro j _
    exact (continuous_position n j).neg
  · have hz : ∀ v : Parameter n, (criticalProduct v).coeff k = 0 := by
      intro v
      exact coeff_eq_zero_of_natDegree_lt (by rw [natDegree_criticalProduct]; omega)
    simp_rw [hz]
    exact continuous_const

/-- The concrete finite critical-value map is continuous. -/
theorem continuous_values (n : ℕ) : Continuous (values (n := n)) := by
  apply continuous_pi
  intro j
  have hformula : ∀ v : Parameter n, values v j =
      (n + 2 : ℂ) * (∑ k ∈ Finset.range (n + 2),
        (criticalProduct v).coeff k / ((k : ℂ) + 1) * (position v j) ^ (k + 1)) +
      v.2 ^ (n + 2) := by
    intro v
    simp [values, polynomial, polyAntideriv, natDegree_criticalProduct, eval_finsetSum]
  simp_rw [hformula]
  apply Continuous.add
  · apply Continuous.mul continuous_const
    apply continuous_finsetSum
    intro k _
    exact ((continuous_coeff_criticalProduct n k).div_const _).mul
      ((continuous_position n j).pow _)
  · fun_prop

/-- Properness for the actual ordered critical-value map; finite branch-point parameters cannot
escape while their ordered critical values stay in a compact set. -/
theorem isProperMap_values (n : ℕ) : IsProperMap (values (n := n)) := by
  apply isProperMap_of_homogeneous_zero_fiber (values (n := n)) (continuous_values n) (n + 2)
    (by omega)
  · intro r _ v
    have hv : r • v = (r : ℂ) • v := by
      apply Prod.ext
      · funext i; rfl
      · rfl
    rw [hv, values_smul]
    funext j
    simp only [Pi.smul_apply, Complex.real_smul, Complex.ofReal_pow, smul_eq_mul]
  · exact eq_zero_of_values_eq_zero

/-- The critical-value map using the actual additive polynomial constant. -/
def valuesWithConstant {n : ℕ} (v : Parameter n) : Fin (n + 1) → ℂ :=
  fun j => (C (n + 2 : ℂ) * polyAntideriv (criticalProduct v)).eval (position v j) + v.2

/-- The auxiliary constant-coordinate covering used only to prove properness. -/
def powerConstant {n : ℕ} (v : Parameter n) : Parameter n := (v.1, v.2 ^ (n + 2))

@[simp] theorem valuesWithConstant_comp_powerConstant (n : ℕ) :
    (valuesWithConstant (n := n)) ∘ powerConstant = values := by
  funext v j
  simp [valuesWithConstant, powerConstant, values, polynomial,
    criticalProduct, position]

theorem continuous_powerConstant (n : ℕ) : Continuous (powerConstant (n := n)) := by
  unfold powerConstant
  fun_prop

theorem surjective_powerConstant (n : ℕ) : Function.Surjective (powerConstant (n := n)) := by
  rintro ⟨c, b⟩
  obtain ⟨w, hw⟩ := IsAlgClosed.exists_pow_nat_eq b (show 0 < n + 2 by omega)
  exact ⟨(c, w), Prod.ext rfl hw⟩

theorem continuous_valuesWithConstant (n : ℕ) :
    Continuous (valuesWithConstant (n := n)) := by
  have hh : ∀ (v : Parameter n) j,
      valuesWithConstant v j = values (v.1, 0) j + v.2 := by
    intro v j
    simp [valuesWithConstant, values, polynomial, criticalProduct, position]
  apply continuous_pi
  intro j
  simp_rw [hh]
  exact (((continuous_apply j).comp (continuous_values n)).comp
    (continuous_fst.prodMk continuous_const)).add continuous_snd

/-- Properness descends to the map with the genuine additive constant coordinate. -/
theorem isProperMap_valuesWithConstant (n : ℕ) :
    IsProperMap (valuesWithConstant (n := n)) := by
  apply isProperMap_of_comp_of_surj (continuous_powerConstant n) (continuous_valuesWithConstant n)
    (f_surj := surjective_powerConstant n)
  rw [valuesWithConstant_comp_powerConstant]
  exact isProperMap_values n

end
end GaloisForLFunctions.HTGeometry.OrderedCriticalValueMap
