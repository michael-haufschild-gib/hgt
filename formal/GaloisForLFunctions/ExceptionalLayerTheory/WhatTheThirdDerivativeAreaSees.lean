import GaloisForLFunctions.ExceptionalLayerTheory.ArbitraryDerivativeOrdersSeparateTheMultiplicityCounts
import GaloisForLFunctions.GaloisTheoryOfZeros.TheArithmeticClassesOfAdditiveZeroRelations
import GaloisForLFunctions.HTGeometry.AlgebraicClosureAlgClosed
import GaloisForLFunctions.RHTower.MobiusProductFibreVariation
import Mathlib.Data.Rat.Lemmas

/-!
# What one third-derivative area determines

The third derivative gives the sum of the square roots of the zero
multiplicities. Galois characters separate this sum into its rational
square classes. Within one square class the weights are commensurable.
Consequently this single area distinguishes any two histograms supported
on squarefree orders, even without a bound on the number of candidate orders.
-/

noncomputable section
open Complex Filter Topology RHTower
open scoped Classical
namespace GaloisForLFunctions.ExceptionalLayerTheory

private abbrev A := algebraicClosure ℚ ℂ

private def algebraicSqrt (m : ℕ) : A := by
  refine ⟨((Real.sqrt (m:ℝ):ℝ):ℂ),mem_algebraicClosure_iff.mpr ?_⟩
  apply IsIntegral.isAlgebraic
  apply IsIntegral.of_pow (by decide : 0<2)
  have hs : ((Real.sqrt (m:ℝ):ℝ):ℂ)^2=(m:ℂ) := by
    exact_mod_cast Real.sq_sqrt (Nat.cast_nonneg m : (0:ℝ) ≤ m)
  rw [hs]
  simpa only [map_natCast] using (isIntegral_algebraMap (R:=ℚ) (A:=ℂ) (x:=(m:ℚ)))

private theorem sqrt_sum_vanishes {ι : Type*} (S : Finset ι) (m : ι → ℕ) (c : ι → ℤ) :
    (∑ i ∈ S, (c i:A)*algebraicSqrt (m i)=0) ↔
      ∑ i ∈ S, (c i:ℝ)*Real.sqrt (m i:ℝ)=0 := by
  have h (i : ι) : algebraMap A ℂ (algebraicSqrt (m i))=((Real.sqrt (m i:ℝ):ℝ):ℂ) := rfl
  rw [←(algebraMap A ℂ).injective.eq_iff,←Complex.ofReal_injective.eq_iff]
  simp only [map_sum,map_mul,map_intCast,map_zero,h,Complex.ofReal_sum,Complex.ofReal_mul,
    Complex.ofReal_intCast,Complex.ofReal_zero]

/-- An integer relation between positive square-root weights holds exactly
when it holds separately in every square class represented by an index. -/
theorem sqrt_order_relation_iff_square_classes {ι : Type*} (S : Finset ι)
    (m : ι → ℕ) (hm : ∀ i, 0 < m i) (c : ι → ℤ) :
    (∑ i ∈ S, (c i:ℝ)*Real.sqrt (m i:ℝ)=0) ↔
      ∀ j, ∑ i ∈ S with IsSquare (m i*m j), (c i:ℝ)*Real.sqrt (m i:ℝ)=0 := by
  classical
  letI : IsAlgClosure ℚ A := ⟨HTGeometry.algebraicClosure_isAlgClosed ℚ ℂ,inferInstance⟩
  letI : IsGalois ℚ A := ⟨⟩
  have hs (i : ι) : algebraicSqrt (m i)^2=algebraMap ℚ A (m i:ℚ) := by
    apply Subtype.ext
    change ((Real.sqrt (m i:ℝ):ℝ):ℂ)^2=((algebraMap ℚ A (m i:ℚ):A):ℂ)
    rw [map_natCast]
    exact_mod_cast Real.sq_sqrt (Nat.cast_nonneg (m i) : (0:ℝ) ≤ m i)
  have hn (i : ι) : algebraicSqrt (m i)≠0 := by
    intro h
    have he := hs i
    rw [h,zero_pow (by decide : 2≠0),map_natCast] at he
    exact (Nat.cast_ne_zero.mpr (hm i).ne') he.symm
  have h := GaloisTheoryOfZeros.radical_relation_iff_square_components
    (fun i => algebraicSqrt (m i)) (fun i => (m i:ℚ)) hs hn S (fun i => (c i:ℚ))
  simpa only [map_intCast,←Nat.cast_mul,Rat.isSquare_natCast_iff,sqrt_sum_vanishes] using h

private theorem third_weight (k : ℕ) : orderAreaWeight 3 k=Real.sqrt ((k+1:ℕ):ℝ) := by
  rw [orderAreaWeight,Real.sqrt_eq_rpow]
  norm_num

/-- The full ambiguity of a third-order area, for any two integer
multiplicity histograms. -/
theorem third_area_equal_iff_square_classes {W : ℕ} (a b : Fin W → ℕ) :
    divisorAreaMoment 3 (fun k => (a k:ℝ))=divisorAreaMoment 3 (fun k => (b k:ℝ)) ↔
      ∀ j : Fin W, ∑ i : Fin W with IsSquare ((i.val+1)*(j.val+1)),
        ((a i:ℝ)-(b i:ℝ))*Real.sqrt ((i.val+1:ℕ):ℝ)=0 := by
  have h := sqrt_order_relation_iff_square_classes Finset.univ (fun k : Fin W => k.val+1)
    (fun k => Nat.succ_pos _) (fun k => (a k:ℤ)-(b k:ℤ))
  rw [←sub_eq_zero,divisorAreaMoment,divisorAreaMoment,←Finset.sum_sub_distrib]
  simpa only [third_weight,←mul_sub,Int.cast_sub,Int.cast_natCast,mul_comm] using h

/-- One third-order area distinguishes squarefree-supported integer histograms. -/
theorem third_area_injective_on_squarefree_orders {W : ℕ} (a b : Fin W → ℕ)
    (hs : ∀ i, ¬Squarefree (i.val+1) → a i=b i)
    (he : divisorAreaMoment 3 (fun k => (a k:ℝ))=divisorAreaMoment 3 (fun k => (b k:ℝ))) :
    a=b := by
  classical
  funext j
  by_cases hj : Squarefree (j.val+1)
  · have h := (third_area_equal_iff_square_classes a b).mp he j
    rw [Finset.sum_eq_single j] at h
    · have hp : 0<Real.sqrt ((j.val+1:ℕ):ℝ) := Real.sqrt_pos.mpr (by positivity)
      exact_mod_cast sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_right hp.ne')
    · intro i hi hne
      have hn : ¬Squarefree (i.val+1) := by
        intro hsf
        have heq := (MobiusProductFibre.squarefree_pair_isSquare_iff hsf hj).mp (Finset.mem_filter.mp hi).2
        exact hne (Fin.ext (Nat.succ.inj heq))
      rw [hs i hn,sub_self,zero_mul]
    · intro hnot
      exact (hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ _,⟨j.val+1,rfl⟩⟩)).elim
  · exact hs j hj

/-- At every positive scale d the two multisets [d,9d,9d,9d] and
[4d,4d,4d,16d] have the same cardinality, winding and third-order area. -/
theorem ambiguity_at_each_square_scale (d : ℕ) :
    d+3*(9*d)=3*(4*d)+16*d ∧
    Real.sqrt (d:ℝ)+3*Real.sqrt (9*(d:ℝ)) =
      3*Real.sqrt (4*(d:ℝ))+Real.sqrt (16*(d:ℝ)) := by
  constructor
  · ring
  · rw [Real.sqrt_mul (by norm_num : (0:ℝ)≤9),Real.sqrt_mul (by norm_num : (0:ℝ)≤4),
      Real.sqrt_mul (by norm_num : (0:ℝ)≤16)]
    norm_num
    <;> ring

#print axioms sqrt_order_relation_iff_square_classes
#print axioms third_area_equal_iff_square_classes
#print axioms third_area_injective_on_squarefree_orders
#print axioms ambiguity_at_each_square_scale
end GaloisForLFunctions.ExceptionalLayerTheory
