import GaloisForLFunctions.HTGeometry.CompactMonicRootCovering
import GaloisForLFunctions.HTGeometry.OrderedCriticalValueDifferential
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Topology.Algebra.Module.LocallyConvex

open Polynomial Set Topology
open scoped unitInterval
namespace GaloisForLFunctions.HTGeometry.OrderedCriticalValueMap
noncomputable section

/-- Polynomial cutting out a fiber of the actual additive family. -/
def fiberPolynomial {n : ℕ} (v : Parameter n) (w : ℂ) : ℂ[X] :=
  additivePolynomial v - C w

@[simp] theorem natDegree_fiberPolynomial {n : ℕ} (v : Parameter n) (w : ℂ) :
    (fiberPolynomial v w).natDegree = n + 2 := by
  rw [fiberPolynomial, natDegree_sub_C, natDegree_additivePolynomial]

theorem monic_fiberPolynomial {n : ℕ} (v : Parameter n) (w : ℂ) :
    (fiberPolynomial v w).Monic := by
  change (fiberPolynomial v w).coeff (fiberPolynomial v w).natDegree = 1
  rw [natDegree_fiberPolynomial]
  simp [fiberPolynomial, coeff_additivePolynomial_top]

def fiberCoefficients {n : ℕ} (v : Parameter n) (w : ℂ) : Fin (n + 2) → ℂ :=
  fun i => (fiberPolynomial v w).coeff i

@[simp] theorem monicCoeffPolynomial_fiberCoefficients {n : ℕ}
    (v : Parameter n) (w : ℂ) :
    monicCoeffPolynomial (n + 2) (fiberCoefficients v w) = fiberPolynomial v w := by
  have h (d : ℕ) (hd : (fiberPolynomial v w).natDegree = d) :
      monicCoeffPolynomial d (fun i => (fiberPolynomial v w).coeff i) =
        fiberPolynomial v w := by
    subst d
    exact monicCoeffPolynomial_coeff_of_monic _ (monic_fiberPolynomial v w)
  exact h _ (natDegree_fiberPolynomial v w)

theorem continuous_fiberCoefficients {T : Type*} [TopologicalSpace T] {n : ℕ}
    {v : T → Parameter n} {w : T → ℂ} (hv : Continuous v) (hw : Continuous w) :
    Continuous fun x => fiberCoefficients (v x) (w x) := by
  apply continuous_pi
  intro i
  simp only [fiberCoefficients, fiberPolynomial, coeff_sub, coeff_C]
  exact ((contDiff_coeff_additivePolynomial n i).continuous.comp hv).sub
    (by split_ifs <;> fun_prop)

/-- Avoiding all supplied critical values discharges the simple-root condition. -/
theorem derivative_fiberPolynomial_ne_zero {n : ℕ} (v : Parameter n) (w z : ℂ)
    (havoid : ∀ j, w ≠ valuesWithConstant v j)
    (hz : (fiberPolynomial v w).eval z = 0) :
    (fiberPolynomial v w).derivative.eval z ≠ 0 := by
  intro hzero
  have hcrit : (polynomial v).derivative.IsRoot z := by
    change (polynomial v).derivative.eval z = 0
    simpa only [fiberPolynomial, derivative_sub, derivative_C, sub_zero,
      derivative_additivePolynomial, derivative_polynomial] using hzero
  obtain ⟨j, rfl⟩ := derivative_root_position v hcrit
  apply havoid j
  have hval : (additivePolynomial v).eval (position v j) = w := by
    simpa only [fiberPolynomial, eval_sub, eval_C, sub_eq_zero] using hz
  rw [← hval]
  simp only [additivePolynomial, valuesWithConstant, eval_add, eval_C]

/-- A chosen polynomial root extends uniquely over a compact simply connected family
of regular target values, including parameter collisions elsewhere. -/
theorem existsUnique_additivePolynomial_root_section {T : Type*} [TopologicalSpace T]
    [CompactSpace T] [T2Space T] [SimplyConnectedSpace T] [LocallyPathConnectedSpace T]
    {n : ℕ} {v : T → Parameter n} {w : T → ℂ}
    (hv : Continuous v) (hw : Continuous w)
    (havoid : ∀ x j, w x ≠ valuesWithConstant (v x) j)
    (x₀ : T) (z₀ : ℂ) (hz₀ : (additivePolynomial (v x₀)).eval z₀ = w x₀) :
    ∃! z : C(T, ℂ), z x₀ = z₀ ∧ ∀ x, (additivePolynomial (v x)).eval (z x) = w x := by
  have hsimple : ∀ x z, (monicCoeffPolynomial (n + 2)
      (fiberCoefficients (v x) (w x))).eval z = 0 →
      (monicCoeffPolynomial (n + 2) (fiberCoefficients (v x) (w x))).derivative.eval z ≠ 0 := by
    intro x z hz
    simp only [monicCoeffPolynomial_fiberCoefficients] at hz ⊢
    exact derivative_fiberPolynomial_ne_zero _ _ _ (havoid x) hz
  have hroot : (monicCoeffPolynomial (n + 2)
      (fiberCoefficients (v x₀) (w x₀))).eval z₀ = 0 := by
    simpa only [monicCoeffPolynomial_fiberCoefficients, fiberPolynomial,
      eval_sub, eval_C, sub_eq_zero] using hz₀
  simpa only [monicCoeffPolynomial_fiberCoefficients, fiberPolynomial,
    eval_sub, eval_C, sub_eq_zero] using
    existsUnique_monic_root_section (by omega : 0 < n + 2)
      (continuous_fiberCoefficients hv hw) hsimple x₀ z₀ hroot

/-- Interval continuation can be based at either endpoint or any interior point. -/
theorem existsUnique_additivePolynomial_root_interval {n : ℕ}
    (v : C(I, Parameter n)) (w : C(I, ℂ))
    (havoid : ∀ t j, w t ≠ valuesWithConstant (v t) j)
    (t₀ : I) (z₀ : ℂ) (hz₀ : (additivePolynomial (v t₀)).eval z₀ = w t₀) :
    ∃! z : C(I, ℂ), z t₀ = z₀ ∧ ∀ t, (additivePolynomial (v t)).eval (z t) = w t := by
  letI : ContractibleSpace I :=
    (convex_Icc (0 : ℝ) 1).contractibleSpace ⟨0, by simp⟩
  letI : LocallyPathConnectedSpace I :=
    (convex_Icc (0 : ℝ) 1).locallyPathConnectedSpace
  exact existsUnique_additivePolynomial_root_section v.continuous w.continuous
    havoid t₀ z₀ hz₀

/-- Unique continuation of each actual polynomial sheet across an entire deformation square. -/
theorem existsUnique_additivePolynomial_root_square {n : ℕ}
    (v : C(I, Parameter n)) (γ : C(I, ℂ))
    (havoid : ∀ t s j, γ s ≠ valuesWithConstant (v t) j)
    (z₀ : ℂ) (hz₀ : (additivePolynomial (v 0)).eval z₀ = γ 0) :
    ∃! z : C(I × I, ℂ), z (0, 0) = z₀ ∧
      ∀ q, (additivePolynomial (v q.1)).eval (z q) = γ q.2 := by
  letI : ContractibleSpace I :=
    (convex_Icc (0 : ℝ) 1).contractibleSpace ⟨0, by simp⟩
  letI : LocallyPathConnectedSpace ↥((I : Set ℝ) ×ˢ (I : Set ℝ)) :=
    ((convex_Icc (0 : ℝ) 1).prod (convex_Icc (0 : ℝ) 1)).locallyPathConnectedSpace
  letI : LocallyPathConnectedSpace (I × I) :=
    (Homeomorph.Set.prod (I : Set ℝ) (I : Set ℝ)).symm.isOpenEmbedding.locallyPathConnectedSpace
  exact existsUnique_additivePolynomial_root_section
    (v.continuous.comp continuous_fst) (γ.continuous.comp continuous_snd)
    (fun q j => havoid q.1 q.2 j) (0, 0) z₀ hz₀

end
end GaloisForLFunctions.HTGeometry.OrderedCriticalValueMap
