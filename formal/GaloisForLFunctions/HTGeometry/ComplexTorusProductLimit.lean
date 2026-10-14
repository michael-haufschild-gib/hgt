import GaloisForLFunctions.HTGeometry.ComplexPrefixLimit
import GaloisForLFunctions.HTGeometry.TorusFiniteProductIntegral
import GaloisForLFunctions.HTGeometry.L2PairingEnergy
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import Mathlib.MeasureTheory.Function.LpSpace.Complete

/-! # Complex mean-one products on the full torus

The prefix inner-product identity needs mean one, not positivity. An exact
bounded product of local squared norms therefore gives a complex L² limit.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Filter
open scoped BigOperators ComplexConjugate Topology

noncomputable section

variable {ι : Type*} [Countable ι]

def torusFiniteProduct (f : ι → C(UnitAddCircle, ℂ)) (P : Finset ι) :
    C(UnitAddTorus ι, ℂ) where
  toFun x := ∏ i ∈ P, f i (x i)
  continuous_toFun := continuous_finsetProd P fun i _ =>
    (f i).continuous.comp (continuous_apply i)

def torusFiniteProductLp (f : ι → C(UnitAddCircle, ℂ)) (P : Finset ι) :
    Lp ℂ 2 (torusHaar ι) :=
  (torusFiniteProduct f P).toLp 2 (torusHaar ι) ℂ

theorem coeFn_torusFiniteProductLp (f : ι → C(UnitAddCircle, ℂ)) (P : Finset ι) :
    torusFiniteProductLp f P =ᵐ[torusHaar ι] torusFiniteProduct f P :=
  ContinuousMap.coeFn_toLp (torusHaar ι) (torusFiniteProduct f P)

theorem norm_sq_torusFiniteProductLp (f : ι → C(UnitAddCircle, ℂ)) (P : Finset ι) :
    ‖torusFiniteProductLp f P‖ ^ 2 =
      ∏ i ∈ P, ∫ θ, ‖f i θ‖ ^ 2 ∂AddCircle.haarAddCircle := by
  rw [_root_.HTGeometry.norm_l2_sq_eq_integral_norm_sq]
  calc
    _ = ∫ x, ‖torusFiniteProduct f P x‖ ^ 2 ∂torusHaar ι := by
      apply integral_congr_ae
      filter_upwards [coeFn_torusFiniteProductLp f P] with x hx
      rw [hx]
    _ = ∫ x, ∏ i ∈ P, ‖f i (x i)‖ ^ 2 ∂torusHaar ι := by
      simp only [torusFiniteProduct, ContinuousMap.coe_mk, norm_prod, Finset.prod_pow]
    _ = _ := integral_torus_finite_product P (fun i θ => ‖f i θ‖ ^ 2)
      (fun i => (f i).continuous.norm.pow 2)

theorem inner_torusFiniteProductLp (f : ι → C(UnitAddCircle, ℂ)) (P Q : Finset ι) :
    inner ℂ (torusFiniteProductLp f P) (torusFiniteProductLp f Q) =
      ∫ x, conj (∏ i ∈ P, f i (x i)) * (∏ i ∈ Q, f i (x i)) ∂torusHaar ι := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [coeFn_torusFiniteProductLp f P, coeFn_torusFiniteProductLp f Q] with x hx hy
  rw [hx, hy, RCLike.inner_apply']
  rfl

theorem integral_torus_product_conj_mul_of_subset
    (f : ι → C(UnitAddCircle, ℂ))
    (hmean : ∀ i, ∫ θ, f i θ ∂AddCircle.haarAddCircle = 1)
    {P Q : Finset ι} (hPQ : P ⊆ Q) :
    (∫ x, conj (∏ i ∈ P, f i (x i)) * (∏ i ∈ Q, f i (x i)) ∂torusHaar ι) =
      ∏ i ∈ P, ∫ θ, conj (f i θ) * f i θ ∂AddCircle.haarAddCircle := by
  classical
  let g : ι → UnitAddCircle → ℂ := fun i θ =>
    if i ∈ P then conj (f i θ) * f i θ else f i θ
  have hpoint (x : UnitAddTorus ι) :
      conj (∏ i ∈ P, f i (x i)) * (∏ i ∈ Q, f i (x i)) = ∏ i ∈ Q, g i (x i) := by
    have hext : (∏ i ∈ P, conj (f i (x i))) =
        ∏ i ∈ Q, if i ∈ P then conj (f i (x i)) else 1 := by
      calc
        _ = ∏ i ∈ P, if i ∈ P then conj (f i (x i)) else 1 := by simp
        _ = _ := Finset.prod_subset hPQ (by intro i _ hi; simp [hi])
    rw [map_prod, hext, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    by_cases hi : i ∈ P <;> simp [g, hi]
  simp_rw [hpoint]
  rw [integral_torus_finite_product Q g (fun i => ?_)]
  · have hi (i : ι) : (∫ θ, g i θ ∂AddCircle.haarAddCircle) =
        if i ∈ P then (∫ θ, conj (f i θ) * f i θ ∂AddCircle.haarAddCircle) else 1 := by
      by_cases hi : i ∈ P <;> simp [g, hi, hmean]
    simp_rw [hi]
    symm
    calc
      _ = ∏ i ∈ P, if i ∈ P then
          (∫ θ, conj (f i θ) * f i θ ∂AddCircle.haarAddCircle) else 1 := by simp
      _ = _ := Finset.prod_subset hPQ (by intro i _ hi; simp [hi])
  · by_cases hi : i ∈ P
    · simp only [g, if_pos hi]
      fun_prop
    · simpa only [g, if_neg hi] using (f i).continuous

theorem re_inner_torusFiniteProductLp_of_subset
    (f : ι → C(UnitAddCircle, ℂ))
    (hmean : ∀ i, ∫ θ, f i θ ∂AddCircle.haarAddCircle = 1)
    {P Q : Finset ι} (hPQ : P ⊆ Q) :
    (inner ℂ (torusFiniteProductLp f P) (torusFiniteProductLp f Q)).re =
      ‖torusFiniteProductLp f P‖ ^ 2 := by
  have heq : inner ℂ (torusFiniteProductLp f P) (torusFiniteProductLp f Q) =
      inner ℂ (torusFiniteProductLp f P) (torusFiniteProductLp f P) := by
    rw [inner_torusFiniteProductLp, inner_torusFiniteProductLp,
      integral_torus_product_conj_mul_of_subset f hmean hPQ,
      integral_torus_product_conj_mul_of_subset f hmean (Finset.Subset.refl P)]
  rw [heq]
  exact (norm_sq_eq_re_inner (𝕜 := ℂ) _).symm

theorem exists_complexTorusProduct_limit
    (f : ι → C(UnitAddCircle, ℂ))
    (hmean : ∀ i, ∫ θ, f i θ ∂AddCircle.haarAddCircle = 1)
    (P : ℕ → Finset ι) (hP : Monotone P) {B : ℝ}
    (hB : ∀ N, (∏ i ∈ P N, ∫ θ, ‖f i θ‖ ^ 2 ∂AddCircle.haarAddCircle) ≤ B ^ 2) :
    ∃ g : Lp ℂ 2 (torusHaar ι),
      Tendsto (fun N => torusFiniteProductLp f (P N)) atTop (𝓝 g) := by
  apply exists_limit_of_prefix_re_inner
  · intro n m hnm
    exact re_inner_torusFiniteProductLp_of_subset f hmean (hP hnm)
  · refine ⟨B ^ 2, ?_⟩
    rintro _ ⟨N, rfl⟩
    change ‖torusFiniteProductLp f (P N)‖ ^ 2 ≤ B ^ 2
    rw [norm_sq_torusFiniteProductLp]
    exact hB N

end

end GaloisForLFunctions.HTGeometry
