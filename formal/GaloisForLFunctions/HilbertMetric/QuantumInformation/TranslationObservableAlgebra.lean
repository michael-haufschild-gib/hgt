import GaloisForLFunctions.HilbertMetric.QuantumInformation.TranslationObservableClosure
import Mathlib.Topology.Algebra.StarSubalgebra

/-!
# The concrete closed Weyl and finite-rank observable algebra

Weyl multiplication preserves integer modulation frequencies. Rank-one
operators form a two-sided ideal under bounded multiplication, and adjoints
preserve both generator classes. Thus the concrete domain of weak averaging
is a closed unital star subalgebra of bounded operators.
-/

noncomputable section
open InnerProductSpace ContinuousLinearMap
open scoped BigOperators Classical
namespace GaloisForLFunctions.HilbertMetric.ShiftAverage

private def weylIsometry (a ω : ℝ) : Space →ₗᵢ[ℂ] Space :=
  { (weylWord a ω).toLinearMap with norm_map' := norm_weylWord a ω }

private theorem translation_zero_operator : translation 0 = 1 := by
  apply ContinuousLinearMap.ext
  exact shift_zero

private theorem weylWord_right_inverse (a ω : ℝ) :
    weylWord a ω * ((Circle.exp (ω * a) : ℂ) • weylWord (-a) (-ω)) = 1 := by
  rw [mul_smul_comm, weylWord_mul, smul_smul, ← Circle.coe_mul, ← Circle.exp_add]
  rw [show ω * a + -ω * a = 0 by ring, Circle.exp_zero, Circle.coe_one,
    one_smul, add_neg_cancel, add_neg_cancel, weylWord_zero_frequency, translation_zero_operator]

/-- The Weyl adjoint has the exact inverse cocycle phase. -/
theorem adjoint_weylWord (a ω : ℝ) :
    adjoint (weylWord a ω) = (Circle.exp (ω * a) : ℂ) • weylWord (-a) (-ω) := by
  apply ContinuousLinearMap.ext
  intro v
  apply ext_inner_left ℂ
  intro u
  rw [adjoint_inner_right]
  have hi := (weylIsometry a ω).inner_map_map u
    (((Circle.exp (ω * a) : ℂ) • weylWord (-a) (-ω)) v)
  change inner ℂ (weylWord a ω u)
    ((weylWord a ω * ((Circle.exp (ω * a) : ℂ) • weylWord (-a) (-ω))) v) = _ at hi
  rw [weylWord_right_inverse, one_apply_eq_self] at hi
  exact hi

private theorem generator_mem_finite (g : ObservableGenerator) :
    generatorObservable g ∈ LinearMap.range evaluateSymbol := by
  refine ⟨Finsupp.single g 1, ?_⟩
  simp only [evaluateSymbol, Finsupp.linearCombination_single, one_smul]

private theorem mul_rankOne_eq (A : Observable) (x y : Space) :
    A * rankOne ℂ x y = rankOne ℂ (A x) y := by
  ext v
  simp only [mul_apply_eq_comp, rankOne_apply, map_smul]

private theorem rankOne_mul_eq (A : Observable) (x y : Space) :
    rankOne ℂ x y * A = rankOne ℂ x (adjoint A y) := by
  ext v
  simp only [mul_apply_eq_comp, rankOne_apply, adjoint_inner_left]

private theorem generator_mul_mem_finite (g h : ObservableGenerator) :
    generatorObservable g * generatorObservable h ∈ LinearMap.range evaluateSymbol := by
  cases g with
  | inr p =>
    rw [generatorObservable, rankOne_mul_eq]
    exact generator_mem_finite (.inr (p.1, adjoint (generatorObservable h) p.2))
  | inl p =>
    cases h with
    | inr q =>
      rw [generatorObservable, generatorObservable, mul_rankOne_eq]
      exact generator_mem_finite (.inr (weylWord p.1 (2 * Real.pi * (p.2 : ℝ)) q.1, q.2))
    | inl q =>
      rw [generatorObservable, generatorObservable, weylWord_mul]
      have he : 2 * Real.pi * (p.2 : ℝ) + 2 * Real.pi * (q.2 : ℝ) =
          2 * Real.pi * ((p.2 + q.2 : ℤ) : ℝ) := by push_cast; ring
      rw [he]
      exact (LinearMap.range evaluateSymbol).smul_mem _
        (generator_mem_finite (.inl (p.1 + q.1, p.2 + q.2)))

private theorem generator_star_mem_finite (g : ObservableGenerator) :
    star (generatorObservable g) ∈ LinearMap.range evaluateSymbol := by
  cases g with
  | inl p =>
    change adjoint (weylWord p.1 (2 * Real.pi * (p.2 : ℝ))) ∈ _
    rw [adjoint_weylWord]
    have he : -(2 * Real.pi * (p.2 : ℝ)) = 2 * Real.pi * ((-p.2 : ℤ) : ℝ) := by
      push_cast
      ring
    rw [he]
    exact (LinearMap.range evaluateSymbol).smul_mem _
      (generator_mem_finite (.inl (-p.1, -p.2)))
  | inr p =>
    change adjoint (rankOne ℂ p.1 p.2) ∈ _
    rw [adjoint_rankOne]
    exact generator_mem_finite (.inr (p.2, p.1))

private theorem finite_mul_mem {A B : Observable}
    (hA : A ∈ LinearMap.range evaluateSymbol) (hB : B ∈ LinearMap.range evaluateSymbol) :
    A * B ∈ LinearMap.range evaluateSymbol := by
  obtain ⟨p, rfl⟩ := hA
  obtain ⟨q, rfl⟩ := hB
  change (∑ g ∈ p.support, p g • generatorObservable g) *
    (∑ h ∈ q.support, q h • generatorObservable h) ∈ LinearMap.range evaluateSymbol
  simp_rw [Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm, smul_smul]
  exact (LinearMap.range evaluateSymbol).sum_mem fun g _ =>
    (LinearMap.range evaluateSymbol).sum_mem fun h _ =>
      (LinearMap.range evaluateSymbol).smul_mem _ (generator_mul_mem_finite g h)

private theorem finite_star_mem {A : Observable} (hA : A ∈ LinearMap.range evaluateSymbol) :
    star A ∈ LinearMap.range evaluateSymbol := by
  obtain ⟨p, rfl⟩ := hA
  change star (∑ g ∈ p.support, p g • generatorObservable g) ∈ LinearMap.range evaluateSymbol
  rw [star_sum]
  apply (LinearMap.range evaluateSymbol).sum_mem
  intro g _
  rw [star_smul]
  exact (LinearMap.range evaluateSymbol).smul_mem _ (generator_star_mem_finite g)

private theorem one_mem_finite : (1 : Observable) ∈ LinearMap.range evaluateSymbol := by
  have h := generator_mem_finite (.inl (0, 0))
  simpa only [generatorObservable, Int.cast_zero, mul_zero,
    weylWord_zero_frequency, translation_zero_operator] using h

/-- The actual finite span is already a unital star subalgebra. -/
def finiteObservableAlgebra : StarSubalgebra ℂ Observable where
  carrier := LinearMap.range evaluateSymbol
  mul_mem' := finite_mul_mem
  add_mem' := (LinearMap.range evaluateSymbol).add_mem
  algebraMap_mem' c := by
    rw [Algebra.algebraMap_eq_smul_one]
    exact (LinearMap.range evaluateSymbol).smul_mem c one_mem_finite
  star_mem' := finite_star_mem

/-- The norm-closed algebra generated by actual integer Weyl and rank-one operators. -/
def closedObservableAlgebra : StarSubalgebra ℂ Observable :=
  finiteObservableAlgebra.topologicalClosure

/-- The generated algebra has exactly the previously constructed averaging domain. -/
theorem closedObservableAlgebra_carrier :
    (closedObservableAlgebra : Set Observable) = (observableDomain : Set Observable) := rfl

/-- Products of concrete closed-domain observables remain in the averaging domain. -/
theorem observableDomain_mul_mem (A B : ObservableDomain) :
    (A : Observable) * (B : Observable) ∈ observableDomain :=
  closedObservableAlgebra.mul_mem A.property B.property

/-- The actual averaging domain is closed under Hilbert adjoints. -/
theorem observableDomain_adjoint_mem (A : ObservableDomain) :
    adjoint (A : Observable) ∈ observableDomain :=
  closedObservableAlgebra.star_mem' A.property

#print axioms adjoint_weylWord
#print axioms closedObservableAlgebra_carrier
#print axioms observableDomain_mul_mem
#print axioms observableDomain_adjoint_mem
end GaloisForLFunctions.HilbertMetric.ShiftAverage
