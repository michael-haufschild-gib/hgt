import GaloisForLFunctions.HTGeometry.OrderedCriticalValueMap
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Topology.IsLocalHomeomorph

open Polynomial
open scoped BigOperators
namespace GaloisForLFunctions.HTGeometry.OrderedCriticalValueMap
noncomputable section

/-- The monic centered polynomial with its genuine additive constant. -/
def additivePolynomial {n : ℕ} (v : Parameter n) : ℂ[X] :=
  C (n + 2 : ℂ) * polyAntideriv (criticalProduct v) + C v.2

@[simp] theorem additivePolynomial_powerConstant {n : ℕ} (v : Parameter n) :
    additivePolynomial (powerConstant v) = polynomial v := by
  simp [additivePolynomial, powerConstant, polynomial, criticalProduct, position]

@[simp] theorem derivative_additivePolynomial {n : ℕ} (v : Parameter n) :
    (additivePolynomial v).derivative = C (n + 2 : ℂ) * criticalProduct v := by
  simp [additivePolynomial, derivative_polyAntideriv]

@[simp] theorem eval_additivePolynomial_zero {n : ℕ} (v : Parameter n) :
    (additivePolynomial v).eval 0 = v.2 := by
  simp [additivePolynomial, polyAntideriv, eval_finsetSum]

@[simp] theorem natDegree_additivePolynomial {n : ℕ} (v : Parameter n) :
    (additivePolynomial v).natDegree = n + 2 := by
  obtain ⟨w, rfl⟩ := surjective_powerConstant n v
  rw [additivePolynomial_powerConstant, natDegree_polynomial]

theorem monic_additivePolynomial {n : ℕ} (v : Parameter n) :
    (additivePolynomial v).Monic := by
  obtain ⟨w, rfl⟩ := surjective_powerConstant n v
  rw [additivePolynomial_powerConstant]
  exact monic_polynomial w

theorem centered_additivePolynomial {n : ℕ} (v : Parameter n) :
    (additivePolynomial v).nextCoeff = 0 := by
  obtain ⟨w, rfl⟩ := surjective_powerConstant n v
  rw [additivePolynomial_powerConstant]
  exact centered_polynomial w

theorem coeff_additivePolynomial_pred {n : ℕ} (v : Parameter n) :
    (additivePolynomial v).coeff (n + 1) = 0 := by
  have hh := centered_additivePolynomial v
  rw [nextCoeff_of_natDegree_pos (by rw [natDegree_additivePolynomial]; omega),
    natDegree_additivePolynomial] at hh
  simpa using hh

theorem coeff_additivePolynomial_top {n : ℕ} (v : Parameter n) :
    (additivePolynomial v).coeff (n + 2) = 1 := by
  simpa only [← natDegree_additivePolynomial v, coeff_natDegree] using
    (monic_additivePolynomial v).leadingCoeff

theorem coeff_additivePolynomial_succ {n : ℕ} (v : Parameter n) (k : ℕ) :
    (additivePolynomial v).coeff (k + 1) =
      (n + 2 : ℂ) * (criticalProduct v).coeff k / ((k : ℂ) + 1) := by
  have hk : ((k : ℂ) + 1) ≠ 0 := by exact_mod_cast (show k + 1 ≠ 0 by omega)
  have hh := congrArg (fun p : ℂ[X] => p.coeff k) (derivative_additivePolynomial v)
  rw [coeff_derivative, coeff_C_mul] at hh
  exact (eq_div_iff hk).mpr (by simpa only [Nat.cast_add, Nat.cast_one] using hh)

/-- Monicity and centering isolate all variable coefficients below degree n+1. -/
theorem additivePolynomial_expansion {n : ℕ} (v : Parameter n) :
    additivePolynomial v = X ^ (n + 2) +
      ∑ k ∈ Finset.range (n + 1), C ((additivePolynomial v).coeff k) * X ^ k := by
  conv_lhs => rw [(additivePolynomial v).as_sum_range_C_mul_X_pow,
    natDegree_additivePolynomial, Finset.sum_range_succ, Finset.sum_range_succ]
  rw [coeff_additivePolynomial_top, coeff_additivePolynomial_pred, C_1, C_0, zero_mul,
    one_mul, add_zero, add_comm]

/-- Every critical position is complex smooth in the parameters. -/
theorem contDiff_position (n : ℕ) (j : Fin (n + 1)) :
    ContDiff ℂ ⊤ (fun v : Parameter n => position v j) := by
  refine Fin.cases ?_ (fun i => ?_) j
  · simp only [position, Fin.cons_zero]
    fun_prop
  · simp only [position, Fin.cons_succ]
    fun_prop

theorem contDiff_coeff_criticalProduct (n k : ℕ) :
    ContDiff ℂ ⊤ (fun v : Parameter n => (criticalProduct v).coeff k) := by
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
    apply ContDiff.sum
    intro s _
    apply contDiff_prod
    intro j _
    exact (contDiff_position n j).neg
  · have hz : ∀ v : Parameter n, (criticalProduct v).coeff k = 0 := by
      intro v
      exact coeff_eq_zero_of_natDegree_lt (by rw [natDegree_criticalProduct]; omega)
    simp_rw [hz]
    exact contDiff_const

theorem contDiff_coeff_additivePolynomial (n k : ℕ) :
    ContDiff ℂ ⊤ (fun v : Parameter n => (additivePolynomial v).coeff k) := by
  cases k with
  | zero =>
    simp_rw [coeff_zero_eq_eval_zero, eval_additivePolynomial_zero]
    fun_prop
  | succ k =>
    simp_rw [coeff_additivePolynomial_succ]
    exact (contDiff_const.mul (contDiff_coeff_criticalProduct n k)).div_const _

/-- The finite critical-value parameter map is complex smooth. -/
theorem contDiff_valuesWithConstant (n : ℕ) : ContDiff ℂ ⊤ (valuesWithConstant (n := n)) := by
  apply contDiff_pi.mpr
  intro j
  have heq : ∀ v : Parameter n, valuesWithConstant v j = (additivePolynomial v).eval (position v j) := by
    intro v
    simp [valuesWithConstant, additivePolynomial]
  have hex : ∀ v : Parameter n, valuesWithConstant v j = (position v j) ^ (n + 2) +
      ∑ k ∈ Finset.range (n + 1), (additivePolynomial v).coeff k * (position v j) ^ k := by
    intro v
    rw [heq]
    conv_lhs => rw [additivePolynomial_expansion]
    simp [eval_finsetSum]
  simp_rw [hex]
  apply ContDiff.add ((contDiff_position n j).pow _)
  apply ContDiff.sum
  intro k _
  exact (contDiff_coeff_additivePolynomial n k).mul ((contDiff_position n j).pow _)

/-- Coefficientwise variation of the monic centered polynomial; the two fixed top coefficients
contribute nothing. -/
def tangentPolynomial {n : ℕ} (v h : Parameter n) : ℂ[X] :=
  ∑ k ∈ Finset.range (n + 1),
    C (fderiv ℂ (fun w : Parameter n => (additivePolynomial w).coeff k) v h) * X ^ k

theorem natDegree_tangentPolynomial_le {n : ℕ} (v h : Parameter n) :
    (tangentPolynomial v h).natDegree ≤ n := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro j hj
  simp only [tangentPolynomial, finsetSum_coeff, coeff_C_mul_X_pow]
  apply Finset.sum_eq_zero
  intro k hk
  have hk' := Finset.mem_range.mp hk
  simp [show j ≠ k by omega]

private theorem fderiv_coefficient_sum {n : ℕ} (v h : Parameter n) (c : ℂ) (u : ℕ → ℂ) :
    fderiv ℂ (fun w : Parameter n => c + ∑ k ∈ Finset.range (n + 1),
      (additivePolynomial w).coeff k * u k) v h =
      ∑ k ∈ Finset.range (n + 1),
        fderiv ℂ (fun w : Parameter n => (additivePolynomial w).coeff k) v h * u k := by
  have hd k := ((contDiff_coeff_additivePolynomial n k).differentiable (by simp) v).hasFDerivAt
  have hh := (hasFDerivAt_const c v).add
    (HasFDerivAt.fun_sum (fun k (_ : k ∈ Finset.range (n + 1)) => (hd k).mul_const (u k)))
  have he := congrArg (fun L : Parameter n →L[ℂ] ℂ => L h) hh.fderiv
  simpa [Pi.add_def, mul_comm] using he

/-- The tangent polynomial evaluates to the parameter differential at every fixed argument. -/
theorem eval_tangentPolynomial {n : ℕ} (v h : Parameter n) (z : ℂ) :
    (tangentPolynomial v h).eval z =
      fderiv ℂ (fun w : Parameter n => (additivePolynomial w).eval z) v h := by
  have he : (fun w : Parameter n => (additivePolynomial w).eval z) =
      fun w => z ^ (n + 2) + ∑ k ∈ Finset.range (n + 1), (additivePolynomial w).coeff k * z ^ k := by
    funext w
    conv_lhs => rw [additivePolynomial_expansion]
    simp [eval_finsetSum]
  rw [he, fderiv_coefficient_sum]
  simp [tangentPolynomial, eval_finsetSum]

/-- Polynomial differentiation commutes with coefficientwise parameter variation. -/
theorem derivative_eval_tangentPolynomial {n : ℕ} (v h : Parameter n) (z : ℂ) :
    (tangentPolynomial v h).derivative.eval z =
      fderiv ℂ (fun w : Parameter n => (additivePolynomial w).derivative.eval z) v h := by
  have he : (fun w : Parameter n => (additivePolynomial w).derivative.eval z) =
      fun w => (n + 2 : ℂ) * z ^ (n + 1) +
        ∑ k ∈ Finset.range (n + 1), (additivePolynomial w).coeff k *
          ((k : ℂ) * z ^ (k - 1)) := by
    funext w
    conv_lhs => rw [additivePolynomial_expansion]
    norm_num [eval_finsetSum, derivative_X_pow, add_assoc]
  rw [he, fderiv_coefficient_sum]
  simp only [tangentPolynomial, map_sum, derivative_C_mul, derivative_X_pow,
    eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]

/-- Joint evaluation of the normalized polynomial family. -/
def jointEvaluation {n : ℕ} (u : Parameter n × ℂ) : ℂ :=
  (additivePolynomial u.1).eval u.2

theorem contDiff_jointEvaluation (n : ℕ) : ContDiff ℂ ⊤ (jointEvaluation (n := n)) := by
  have he : jointEvaluation (n := n) = fun u : Parameter n × ℂ => u.2 ^ (n + 2) +
      ∑ k ∈ Finset.range (n + 1), (additivePolynomial u.1).coeff k * u.2 ^ k := by
    funext u
    unfold jointEvaluation
    conv_lhs => rw [additivePolynomial_expansion]
    simp [eval_finsetSum]
  rw [he]
  apply ContDiff.add (contDiff_snd.pow _)
  apply ContDiff.sum
  intro k _
  exact ((contDiff_coeff_additivePolynomial n k).comp contDiff_fst).mul (contDiff_snd.pow _)

@[simp] theorem derivative_eval_position {n : ℕ} (v : Parameter n) (j : Fin (n + 1)) :
    (additivePolynomial v).derivative.eval (position v j) = 0 := by
  rw [derivative_additivePolynomial, eval_mul, eval_C]
  suffices (criticalProduct v).eval (position v j) = 0 by rw [this, mul_zero]
  simp only [criticalProduct, eval_prod, eval_sub, eval_X, eval_C]
  exact Finset.prod_eq_zero_iff.mpr ⟨j, Finset.mem_univ j, sub_self _⟩

/-- At a critical point, motion of the evaluation point contributes zero to the differential. -/
theorem fderiv_values_component_eq_tangent {n : ℕ} (v h : Parameter n) (j : Fin (n + 1)) :
    fderiv ℂ (fun w : Parameter n => valuesWithConstant w j) v h =
      (tangentPolynomial v h).eval (position v j) := by
  let a := position v j
  let L := fderiv ℂ (jointEvaluation (n := n)) (v, a)
  let D := fderiv ℂ (fun w : Parameter n => position w j) v
  have hJ : HasFDerivAt (jointEvaluation (n := n)) L (v, a) :=
    ((contDiff_jointEvaluation n).differentiable (by simp) (v, a)).hasFDerivAt
  have hpos : HasFDerivAt (fun w : Parameter n => position w j) D v :=
    ((contDiff_position n j).differentiable (by simp) v).hasFDerivAt
  have hl : HasFDerivAt (fun w : Parameter n => (additivePolynomial w).eval a)
      (L.comp (ContinuousLinearMap.inl ℂ (Parameter n) ℂ)) v := by
    simpa only [Function.comp_def, jointEvaluation, L] using
      hJ.comp v (hasFDerivAt_prodMk_left (𝕜 := ℂ) v a)
  have hr : HasFDerivAt (fun z : ℂ => (additivePolynomial v).eval z)
      (L.comp (ContinuousLinearMap.inr ℂ (Parameter n) ℂ)) a := by
    simpa only [Function.comp_def, jointEvaluation, L] using
      hJ.comp a (hasFDerivAt_prodMk_right (𝕜 := ℂ) v a)
  have hm : HasFDerivAt (fun w : Parameter n => (additivePolynomial w).eval (position w j))
      (L.comp ((ContinuousLinearMap.id ℂ (Parameter n)).prod D)) v := by
    simpa only [Function.comp_def, jointEvaluation, L, D, a, id_eq] using
      hJ.comp v ((hasFDerivAt_id (𝕜 := ℂ) v).prodMk hpos)
  have hz : ∀ t : ℂ, L (0, t) = 0 := by
    intro t
    have hp := (additivePolynomial v).hasFDerivAt a
    have hzder : (additivePolynomial v).derivative.eval a = 0 := derivative_eval_position v j
    rw [hzder] at hp
    have hh := congrArg (fun T : ℂ →L[ℂ] ℂ => T t) (hr.unique hp)
    simpa using hh
  have he : (fun w : Parameter n => valuesWithConstant w j) =
      fun w => (additivePolynomial w).eval (position w j) := by
    funext w
    simp [valuesWithConstant, additivePolynomial]
  rw [he, hm.fderiv, eval_tangentPolynomial, hl.fderiv]
  change L (h, D h) = L (h, 0)
  rw [show (h, D h) = (h, 0) + (0, D h) by simp, map_add, hz, add_zero]

/-- The parameter derivative of the critical product, evaluated at one critical position,
contains only the variation of that position. -/
theorem fderiv_criticalProduct_at_position {n : ℕ} (v h : Parameter n) (j : Fin (n + 1)) :
    fderiv ℂ (fun w : Parameter n => (criticalProduct w).eval (position v j)) v h =
      -(∏ k ∈ (Finset.univ : Finset (Fin (n + 1))).erase j,
          (position v j - position v k)) *
        fderiv ℂ (fun w : Parameter n => position w j) v h := by
  let a := position v j
  have hg k := (hasFDerivAt_const a v).sub
    (((contDiff_position n k).differentiable (by simp) v).hasFDerivAt)
  have hp := HasFDerivAt.finsetProd (u := (Finset.univ : Finset (Fin (n + 1))))
    (fun k _ => hg k)
  have he : (fun w : Parameter n => (criticalProduct w).eval a) =
      fun w => ∏ k, (a - position w k) := by
    funext w
    simp [criticalProduct, eval_prod]
  simp only [Pi.sub_apply] at hp
  rw [he, hp.fderiv]
  simp only [sum_apply, smul_apply, zero_sub, neg_apply, smul_eq_mul]
  rw [Finset.sum_eq_single j]
  · dsimp [a]
    ring
  · intro k _ hkj
    have hprod : ∏ l ∈ (Finset.univ : Finset (Fin (n + 1))).erase k,
        (a - position v l) = 0 := by
      apply Finset.prod_eq_zero_iff.mpr
      exact ⟨j, Finset.mem_erase.mpr ⟨Ne.symm hkj, Finset.mem_univ j⟩, sub_self _⟩
    rw [hprod, zero_mul]
  · intro hj
    exact (hj (Finset.mem_univ j)).elim

/-- A zero differential at distinct critical positions forces zero parameter variation. -/
theorem eq_zero_of_fderiv_values_eq_zero {n : ℕ} (v h : Parameter n)
    (hv : Function.Injective (position v))
    (hh : fderiv ℂ (valuesWithConstant (n := n)) v h = 0) : h = 0 := by
  have hB := (contDiff_valuesWithConstant n).differentiable (by simp) v
  have hroots : ∀ j, (tangentPolynomial v h).eval (position v j) = 0 := by
    intro j
    rw [← fderiv_values_component_eq_tangent, fderiv_apply hB j]
    simp [hh]
  have ht : tangentPolynomial v h = 0 :=
    eq_zero_of_natDegree_lt_card_of_eval_eq_zero _ hv hroots
      (by simpa only [Fintype.card_fin] using Nat.lt_succ_of_le (natDegree_tangentPolynomial_le v h))
  have hpos : ∀ j, fderiv ℂ (fun w : Parameter n => position w j) v h = 0 := by
    intro j
    let a := position v j
    have hQ : DifferentiableAt ℂ (fun w : Parameter n => (criticalProduct w).eval a) v := by
      have hc : ContDiff ℂ ⊤ (fun w : Parameter n => ∏ k, (a - position w k)) :=
        contDiff_prod fun k _ => contDiff_const.sub (contDiff_position n k)
      simpa only [criticalProduct, eval_prod, eval_sub, eval_X, eval_C] using
        hc.differentiable (by simp) v
    have hz := derivative_eval_tangentPolynomial v h a
    rw [ht, map_zero, eval_zero] at hz
    have he : (fun w : Parameter n => (additivePolynomial w).derivative.eval a) =
        fun w => (n + 2 : ℂ) * (criticalProduct w).eval a := by
      funext w
      simp
    rw [he, fderiv_const_mul hQ] at hz
    have hd : (n + 2 : ℂ) ≠ 0 := by exact_mod_cast (show n + 2 ≠ 0 by omega)
    have hzQ : fderiv ℂ (fun w : Parameter n => (criticalProduct w).eval a) v h = 0 := by
      apply (mul_eq_zero.mp (show (n + 2 : ℂ) *
        fderiv ℂ (fun w : Parameter n => (criticalProduct w).eval a) v h = 0 from by
          simpa using hz.symm)).resolve_left hd
    rw [fderiv_criticalProduct_at_position] at hzQ
    have hprod : ∏ k ∈ (Finset.univ : Finset (Fin (n + 1))).erase j,
        (position v j - position v k) ≠ 0 := by
      apply Finset.prod_ne_zero_iff.mpr
      intro k hk
      apply sub_ne_zero.mpr
      intro heq
      exact (Finset.mem_erase.mp hk).1 (hv heq).symm
    exact (mul_eq_zero.mp hzQ).resolve_left (neg_ne_zero.mpr hprod)
  have hc : h.1 = 0 := by
    funext i
    have hp : HasFDerivAt (fun w : Parameter n => w.1 i)
        ((ContinuousLinearMap.proj i).comp
          (ContinuousLinearMap.fst ℂ (Fin n → ℂ) ℂ)) v :=
      ((ContinuousLinearMap.proj i).comp
        (ContinuousLinearMap.fst ℂ (Fin n → ℂ) ℂ)).hasFDerivAt
    have hi := hpos i.succ
    simp only [position_succ, hp.fderiv, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.proj_apply] at hi
    change h.1 i = 0 at hi
    exact hi
  have hb : h.2 = 0 := by
    have hz := eval_tangentPolynomial v h 0
    rw [ht, eval_zero] at hz
    simp only [eval_additivePolynomial_zero, fderiv_snd] at hz
    exact hz.symm
  exact Prod.ext hc hb

/-- At distinct critical positions, the critical-value differential is injective. -/
theorem injective_fderiv_valuesWithConstant {n : ℕ} (v : Parameter n)
    (hv : Function.Injective (position v)) :
    Function.Injective (fderiv ℂ (valuesWithConstant (n := n)) v) := by
  intro h k hhk
  have hh : fderiv ℂ (valuesWithConstant (n := n)) v (h - k) = 0 := by
    rw [map_sub, hhk, sub_self]
  exact sub_eq_zero.mp (eq_zero_of_fderiv_values_eq_zero v (h - k) hv hh)

/-- The concrete critical-value map is a local coordinate at every tuple of distinct critical
positions; this does not require the critical values themselves to be distinct. -/
theorem exists_openPartialHomeomorph_valuesWithConstant {n : ℕ} (v : Parameter n)
    (hv : Function.Injective (position v)) :
    ∃ e : OpenPartialHomeomorph (Parameter n) (Fin (n + 1) → ℂ),
      (e : Parameter n → (Fin (n + 1) → ℂ)) = valuesWithConstant ∧ v ∈ e.source := by
  let D := fderiv ℂ (valuesWithConstant (n := n)) v
  have hD : Function.Injective D := injective_fderiv_valuesWithConstant v hv
  have hdim : Module.finrank ℂ (Parameter n) = Module.finrank ℂ (Fin (n + 1) → ℂ) := by
    simp [Parameter, Module.finrank_prod]
  let L : Parameter n ≃L[ℂ] (Fin (n + 1) → ℂ) :=
    (D.toLinearMap.linearEquivOfInjective hD hdim).toContinuousLinearEquiv
  have hL : (L : Parameter n →L[ℂ] (Fin (n + 1) → ℂ)) = D :=
    ContinuousLinearMap.ext (fun h => rfl)
  have hc := (contDiff_valuesWithConstant n).contDiffAt (x := v)
  have hd : HasFDerivAt (valuesWithConstant (n := n))
      (L : Parameter n →L[ℂ] (Fin (n + 1) → ℂ)) v := by
    rw [hL]
    exact ((contDiff_valuesWithConstant n).differentiable (by simp) v).hasFDerivAt
  exact ⟨hc.toOpenPartialHomeomorph _ hd (by simp), rfl,
    hc.mem_toOpenPartialHomeomorph_source hd (by simp)⟩

/-- Distinct ordered critical values imply distinct ordered critical positions. -/
theorem injective_position_of_injective_values {n : ℕ} (v : Parameter n)
    (hv : Function.Injective (valuesWithConstant v)) : Function.Injective (position v) := by
  intro i j hij
  apply hv
  simp only [valuesWithConstant, hij]

/-- The additive critical-value map is locally a homeomorphism on the distinct-position locus. -/
theorem isLocalHomeomorphOn_valuesWithConstant (n : ℕ) :
    IsLocalHomeomorphOn (valuesWithConstant (n := n))
      {v | Function.Injective (position v)} := by
  intro v hv
  obtain ⟨e, he, hv⟩ := exists_openPartialHomeomorph_valuesWithConstant v hv
  exact ⟨e, hv, he.symm⟩

/-- Every parameter lying over distinct critical values has a local inverse. -/
theorem isLocalHomeomorphOn_valuesWithConstant_distinct (n : ℕ) :
    IsLocalHomeomorphOn (valuesWithConstant (n := n))
      {v | Function.Injective (valuesWithConstant v)} := by
  intro v hv
  exact isLocalHomeomorphOn_valuesWithConstant n v
    (injective_position_of_injective_values v hv)

end
end GaloisForLFunctions.HTGeometry.OrderedCriticalValueMap
