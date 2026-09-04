import GaloisForLFunctions.HTGeometry.EntireFirstOrderWimanInitialData
import GaloisForLFunctions.HTGeometry.PuiseuxHahnLeadingTerm

/-!
# Exact Wiman-edge cancellation at the clock infinity place

The Wiman package selects a maximal Newton face for the top value/derivative symbol.  This module
expands that symbol literally in the rational Hahn field after the substitutions
`U = s⁻¹` and `T = c U^p`.  Every coefficient monomial is retained.  The selected edge-root
identity cancels the complete lowest Hahn grade, while maximality proves that no smaller grade is
present.  Consequently the order rises strictly above the Newton boundary.
-/

open HahnSeries

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Literal Hahn expansion of the top symbol under `U = s⁻¹`, `T = c U^p`. -/
noncomputable def firstOrderInfinityInitialSeries
    (S : Finset (ℕ × ℕ)) (A : ℕ × ℕ → Polynomial ℂ) (d : ℕ)
    (p : ℚ) (c : ℂ) : HahnSeries ℚ ℂ :=
  ∑ i ∈ firstOrderTopNewtonFace S A d,
    ∑ n ∈ (A i).support,
      HahnSeries.single (-((n : ℚ) + (i.2 : ℚ) * p)) ((A i).coeff n * c ^ i.2)

private theorem coeff_finset_sum {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (g : ι → HahnSeries ℚ ℂ) (w : ℚ) :
    (∑ i ∈ s, g i).coeff w = ∑ i ∈ s, (g i).coeff w := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi, HahnSeries.coeff_add, ih]

private theorem lt_orderTop_of_coeff_eq_zero' (x : HahnSeries ℚ ℂ) (w : ℚ)
    (hle : (w : WithTop ℚ) ≤ x.orderTop) (hcoeff : x.coeff w = 0) :
    (w : WithTop ℚ) < x.orderTop := by
  rcases lt_or_eq_of_le hle with h | h
  · exact h
  · exact absurd hcoeff (HahnSeries.coeff_orderTop_ne h.symm)

/-- The coefficient at the Newton boundary is exactly the selected edge polynomial. -/
theorem firstOrderInfinityInitialSeries_coeff_eq_edge
    (S : Finset (ℕ × ℕ)) (A : ℕ × ℕ → Polynomial ℂ) (d : ℕ)
    (p : ℚ) (c : ℂ) (i₀ : ℕ × ℕ)
    (hmax : ∀ i ∈ firstOrderTopNewtonFace S A d,
      firstOrderNewtonWeight A (p : ℝ) i ≤ firstOrderNewtonWeight A (p : ℝ) i₀) :
    (firstOrderInfinityInitialSeries S A d p c).coeff
        (-((A i₀).natDegree + (i₀.2 : ℚ) * p)) =
      (firstOrderNewtonEdgePolynomial
        (firstOrderMaxNewtonFace S A d (p : ℝ)
          (firstOrderNewtonWeight A (p : ℝ) i₀)) A).eval c := by
  classical
  rw [firstOrderInfinityInitialSeries]
  rw [coeff_finset_sum]
  have hcoeff :
      (∑ i ∈ firstOrderTopNewtonFace S A d,
        (∑ n ∈ (A i).support,
          HahnSeries.single (-((n : ℚ) + (i.2 : ℚ) * p))
            ((A i).coeff n * c ^ i.2)).coeff
              (-((A i₀).natDegree + (i₀.2 : ℚ) * p))) =
        ∑ i ∈ firstOrderTopNewtonFace S A d,
          ∑ n ∈ (A i).support,
            (if -((n : ℚ) + (i.2 : ℚ) * p) =
                -((A i₀).natDegree + (i₀.2 : ℚ) * p)
              then (A i).coeff n * c ^ i.2 else 0) := by
    apply Finset.sum_congr rfl
    intro i hi
    exact coeff_sum_single (A i).support
      (fun n => -((n : ℚ) + (i.2 : ℚ) * p))
      (fun n => (A i).coeff n * c ^ i.2)
      (-((A i₀).natDegree + (i₀.2 : ℚ) * p))
  rw [hcoeff]
  rw [firstOrderNewtonEdgePolynomial, Polynomial.eval_finsetSum]
  rw [firstOrderMaxNewtonFace, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i hi
  have hiA : A i ≠ 0 := (Finset.mem_filter.mp hi).2.2
  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  by_cases hw : firstOrderNewtonWeight A (p : ℝ) i =
      firstOrderNewtonWeight A (p : ℝ) i₀
  · rw [if_pos hw]
    rw [Finset.sum_eq_single_of_mem (A i).natDegree
      (Polynomial.natDegree_mem_support_of_nonzero hiA)]
    · rw [if_pos]
      · rw [Polynomial.coeff_natDegree]
      · apply neg_inj.mpr
        rw [firstOrderNewtonWeight, firstOrderNewtonWeight] at hw
        exact_mod_cast hw
    · intro n hn hne
      rw [if_neg]
      intro heq
      have hnle := Polynomial.le_natDegree_of_mem_supp n hn
      have heq' : (n : ℚ) + (i.2 : ℚ) * p =
          (A i₀).natDegree + (i₀.2 : ℚ) * p := by linarith
      have hwq : ((A i).natDegree : ℚ) + (i.2 : ℚ) * p =
          (A i₀).natDegree + (i₀.2 : ℚ) * p := by
        have hw' := hw
        rw [firstOrderNewtonWeight, firstOrderNewtonWeight] at hw'
        exact_mod_cast hw'
      have : n = (A i).natDegree := by
        have : (n : ℚ) = (A i).natDegree := by linarith
        exact_mod_cast this
      exact hne this
  · rw [if_neg hw]
    apply Finset.sum_eq_zero
    intro n hn
    rw [if_neg]
    intro heq
    have hnle := Polynomial.le_natDegree_of_mem_supp n hn
    have hle := hmax i hi
    have heq' : (n : ℚ) + (i.2 : ℚ) * p =
        (A i₀).natDegree + (i₀.2 : ℚ) * p := by linarith
    have hnleq : (n : ℚ) ≤ (A i).natDegree := by exact_mod_cast hnle
    have hleq : ((A i).natDegree : ℚ) + (i.2 : ℚ) * p ≤
        (A i₀).natDegree + (i₀.2 : ℚ) * p := by
      have hle' := hle
      rw [firstOrderNewtonWeight, firstOrderNewtonWeight] at hle'
      exact_mod_cast hle'
    have hdeg : n = (A i).natDegree := by
      have : (n : ℚ) = (A i).natDegree := by linarith
      exact_mod_cast this
    apply hw
    rw [firstOrderNewtonWeight, firstOrderNewtonWeight]
    exact_mod_cast (show ((A i).natDegree : ℚ) + (i.2 : ℚ) * p =
      (A i₀).natDegree + (i₀.2 : ℚ) * p by simpa [hdeg] using heq')

/-- The chosen Wiman edge root cancels the entire boundary coefficient at `U = ∞`. -/
theorem entireFirstOrderWiman_infinityInitialCoefficient_zero
    {f : ℂ → ℂ} (data : EntireFirstOrderWimanInitialData f) :
    (firstOrderInfinityInitialSeries data.indexSupport data.coeff data.totalDegree
      data.slope data.root).coeff
        (-((data.coeff data.firstIndex).natDegree +
          (data.firstIndex.2 : ℚ) * data.slope)) = 0 := by
  rw [firstOrderInfinityInitialSeries_coeff_eq_edge data.indexSupport data.coeff
    data.totalDegree data.slope data.root data.firstIndex]
  · have hweight := (Finset.mem_filter.mp data.first_mem_face).2
    rw [hweight]
    exact data.edge_root
  · intro i hi
    calc
      firstOrderNewtonWeight data.coeff (data.slope : ℝ) i ≤ data.weight :=
        data.weight_maximal i hi
      _ = firstOrderNewtonWeight data.coeff (data.slope : ℝ) data.firstIndex :=
        (Finset.mem_filter.mp data.first_mem_face).2.symm

/-- Maximality excludes every grade below the Newton boundary; edge cancellation then raises the
Hahn order strictly above it. -/
theorem firstOrderInfinityInitialSeries_lt_orderTop
    (S : Finset (ℕ × ℕ)) (A : ℕ × ℕ → Polynomial ℂ) (d : ℕ)
    (p : ℚ) (c : ℂ) (i₀ : ℕ × ℕ)
    (hmax : ∀ i ∈ firstOrderTopNewtonFace S A d,
      firstOrderNewtonWeight A (p : ℝ) i ≤ firstOrderNewtonWeight A (p : ℝ) i₀)
    (hroot : (firstOrderNewtonEdgePolynomial
      (firstOrderMaxNewtonFace S A d (p : ℝ)
        (firstOrderNewtonWeight A (p : ℝ) i₀)) A).IsRoot c) :
    ((-((A i₀).natDegree + (i₀.2 : ℚ) * p) : ℚ) : WithTop ℚ) <
      (firstOrderInfinityInitialSeries S A d p c).orderTop := by
  let w : ℚ := (A i₀).natDegree + (i₀.2 : ℚ) * p
  apply lt_orderTop_of_coeff_eq_zero'
  · rw [HahnSeries.le_orderTop_iff_forall]
    intro γ hγ
    have hγ' : γ < -w := by exact_mod_cast hγ
    rw [firstOrderInfinityInitialSeries, coeff_finset_sum]
    apply Finset.sum_eq_zero
    intro i hi
    rw [coeff_sum_single]
    apply Finset.sum_eq_zero
    intro n hn
    rw [if_neg]
    intro heq
    have hnle : n ≤ (A i).natDegree := Polynomial.le_natDegree_of_mem_supp n hn
    have hile := hmax i hi
    have hnleq : (n : ℚ) ≤ (A i).natDegree := by exact_mod_cast hnle
    have hileq : ((A i).natDegree : ℚ) + (i.2 : ℚ) * p ≤ w := by
      have hile' := hile
      rw [firstOrderNewtonWeight, firstOrderNewtonWeight] at hile'
      exact_mod_cast hile'
    have hexp : -w ≤ -((n : ℚ) + (i.2 : ℚ) * p) := by linarith
    rw [heq] at hexp
    exact (not_le_of_gt hγ') hexp
  · change (firstOrderInfinityInitialSeries S A d p c).coeff (-w) = 0
    rw [firstOrderInfinityInitialSeries_coeff_eq_edge S A d p c i₀ hmax]
    exact hroot

/-- Every exact Wiman package therefore gives strict top-symbol cancellation at the selected
rational infinity slope, with no phase or genericity premise. -/
theorem entireFirstOrderWiman_infinityInitial_lt_orderTop
    {f : ℂ → ℂ} (data : EntireFirstOrderWimanInitialData f) :
    ((-((data.coeff data.firstIndex).natDegree +
        (data.firstIndex.2 : ℚ) * data.slope) : ℚ) : WithTop ℚ) <
      (firstOrderInfinityInitialSeries data.indexSupport data.coeff data.totalDegree
        data.slope data.root).orderTop := by
  apply firstOrderInfinityInitialSeries_lt_orderTop
  · intro i hi
    calc
      firstOrderNewtonWeight data.coeff (data.slope : ℝ) i ≤ data.weight :=
        data.weight_maximal i hi
      _ = firstOrderNewtonWeight data.coeff (data.slope : ℝ) data.firstIndex :=
        (Finset.mem_filter.mp data.first_mem_face).2.symm
  · have hweight := (Finset.mem_filter.mp data.first_mem_face).2
    rw [hweight]
    exact data.edge_root

end

end GaloisForLFunctions.HTGeometry
