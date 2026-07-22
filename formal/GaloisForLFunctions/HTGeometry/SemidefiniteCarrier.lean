import GaloisForLFunctions.HTGeometry.LeafDistinct
import GaloisForLFunctions.HTGeometry.ChristoffelPointMass

/-!
# A degenerate direction confines every representative

If `⟪p, p⟫ = 0` for some nonzero polynomial `p`, then every representing measure integrates `p²` to
zero, so `p` vanishes almost everywhere and the measure is carried by the finite root set of `p` —
in particular by a compact interval.

This is the mechanism that makes positive definiteness *derivable* from the existence of two
distinct
representatives, rather than an extra hypothesis: a degenerate direction would confine both to
compact
sets, where the moments determine the measure.
-/

open scoped BigOperators
open MeasureTheory Polynomial

namespace HTGeometry

variable {s : ℕ → ℝ}

/-- **A degenerate direction confines the measure to a compact interval.** -/
theorem exists_carried_of_momentInner_eq_zero {nu : Measure ℝ}
    (hnu : GaloisForLFunctions.HTGeometry.HasHamburgerMoments s nu)
    {p : Polynomial ℝ} (hp0 : p ≠ 0) (hzero : momentInner s p p = 0) :
    ∃ B : ℝ, 0 < B ∧ nu (Set.Icc (-B) B)ᶜ = 0 := by
  classical
  have hs : ∀ k, s k = ∫ x, (x : ℝ) ^ k ∂nu := fun k => (hnu k).2.symm
  have hint : ∀ k, Integrable (fun x : ℝ => (x : ℝ) ^ k) nu := fun k => (hnu k).1
  -- the square integrates to zero
  have hsq : ∫ x, (Polynomial.eval x p) ^ 2 ∂nu = 0 := by
    rw [← momentFunctional_pow_two_eq_integral_sq s hs hint p, pow_two, ← momentInner_def]
    exact hzero
  have hintsq : Integrable (fun x : ℝ => (Polynomial.eval x p) ^ 2) nu := by
    have hpe := integrable_eval hint (p ^ 2)
    refine hpe.congr (Filter.Eventually.of_forall fun x => ?_)
    simp [eval_pow]
  have hae : (fun x : ℝ => (Polynomial.eval x p) ^ 2) =ᵐ[nu] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae
      (Filter.Eventually.of_forall fun x => sq_nonneg _) hintsq).mp hsq
  -- so the measure lives on the roots of `p`
  obtain ⟨B0, hB0⟩ := (p.roots.toFinset.image (fun x => |x|)).exists_le
  refine ⟨max B0 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  refine measure_mono_null (fun x hx => ?_) (by
    rw [Filter.EventuallyEq, ae_iff] at hae
    exact hae)
  -- a point outside the interval is not a root, so the square is nonzero there
  simp only [Set.mem_compl_iff, Set.mem_Icc, not_and_or, not_le] at hx
  simp only [Set.mem_setOf_eq, Pi.zero_apply]
  intro hcontra
  have hproot : p.eval x = 0 := by
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hcontra
    exact this
  have hmemroots : x ∈ p.roots.toFinset := by
    simp only [Multiset.mem_toFinset, mem_roots hp0, IsRoot.def]
    exact hproot
  have habs : |x| ≤ B0 := hB0 _ (Finset.mem_image_of_mem _ hmemroots)
  rcases hx with hlt | hlt
  · have : -(max B0 1) ≤ x := by
      have : |x| ≤ max B0 1 := le_trans habs (le_max_left _ _)
      exact neg_le_of_abs_le this
    linarith
  · have : x ≤ max B0 1 := by
      have : |x| ≤ max B0 1 := le_trans habs (le_max_left _ _)
      exact le_of_abs_le this
    linarith

/-- **Two distinct representatives force positive definiteness.**  A degenerate direction would
confine both to a common compact interval, where matching moments make them equal. -/
theorem positiveMomentForm_of_two_representatives {nu1 nu2 : Measure ℝ}
    [IsFiniteMeasure nu1] [IsFiniteMeasure nu2]
    (h1 : GaloisForLFunctions.HTGeometry.HasHamburgerMoments s nu1)
    (h2 : GaloisForLFunctions.HTGeometry.HasHamburgerMoments s nu2)
    (hne : nu1 ≠ nu2) : PositiveMomentForm s := by
  by_contra hnp
  have hall : ¬ ∀ p : Polynomial ℝ, p ≠ 0 → 0 < momentInner s p p := fun hh => hnp ⟨hh⟩
  obtain ⟨p, hp⟩ := not_forall.mp hall
  obtain ⟨hp0, hnlt⟩ := Classical.not_imp.mp hp
  have hnn : 0 ≤ momentInner s p p := by
    rw [momentInner_def, ← pow_two]
    exact momentFunctional_pow_two_nonneg s (fun k => (h1 k).2.symm) (fun k => (h1 k).1) p
  have hzero : momentInner s p p = 0 := le_antisymm (not_lt.mp hnlt) hnn
  obtain ⟨B1, hB1, hc1⟩ := exists_carried_of_momentInner_eq_zero h1 hp0 hzero
  obtain ⟨B2, hB2, hc2⟩ := exists_carried_of_momentInner_eq_zero h2 hp0 hzero
  set B : ℝ := max B1 B2 with hBdef
  have hBpos : 0 < B := lt_of_lt_of_le hB1 (le_max_left _ _)
  have hwiden : ∀ {C : ℝ}, C ≤ B → (Set.Icc (-B) B)ᶜ ⊆ (Set.Icc (-C) C)ᶜ := by
    intro C hC
    refine Set.compl_subset_compl.mpr ?_
    exact Set.Icc_subset_Icc (by linarith) hC
  have hc1' : nu1 (Set.Icc (-B) B)ᶜ = 0 :=
    le_antisymm (le_trans (measure_mono (hwiden (le_max_left B1 B2))) (le_of_eq hc1))
      (by simp)
  have hIcc : Set.Icc (-B) B = Set.Icc (0 - B) (0 + B) := by norm_num
  rw [hIcc] at hc1'
  exact hne (measure_eq_of_moments_eq_of_one_carried hBpos hc1'
    (fun k => (h1 k).2.symm) (fun k => (h1 k).1)
    (fun k => (h2 k).2.symm) (fun k => (h2 k).1))

/-- **An extremal family forces strict moment positivity.**  No positivity input is needed:
the leaves at `0` and `1` are distinct representatives of the same moment sequence, so the
semidefinite moment form cannot have a nonzero null direction. -/
theorem positiveMomentForm_of_extremalFamily
    (F : GaloisForLFunctions.HTGeometry.ClassicalNevanlinnaExtremalFamily s) :
    PositiveMomentForm s := by
  haveI hf0 : IsFiniteMeasure (F.leaf ((0 : ℝ) : OnePoint ℝ) : Measure ℝ) := inferInstance
  haveI hf1 : IsFiniteMeasure (F.leaf ((1 : ℝ) : OnePoint ℝ) : Measure ℝ) := inferInstance
  exact positiveMomentForm_of_two_representatives
    (F.leaf_moments ((0 : ℝ) : OnePoint ℝ)) (F.leaf_moments ((1 : ℝ) : OnePoint ℝ))
    (leaf_ne_of_ne F zero_ne_one)

/-- Every atom of every extremal leaf is bounded by the moment sequence's Christoffel limit,
without a separate positive-definiteness hypothesis. -/
theorem leaf_measureReal_singleton_le_christoffelLimit_unconditional
    (F : GaloisForLFunctions.HTGeometry.ClassicalNevanlinnaExtremalFamily s)
    (t : OnePoint ℝ) (x : ℝ) :
    (F.leaf t : Measure ℝ).real {x} ≤ christoffelLimit s x :=
  leaf_measureReal_singleton_le_christoffelLimit
    (positiveMomentForm_of_extremalFamily F) F t x

/-- **Unconditional node escape.**  Every extremal family has Gauss nodes outside every compact
interval.  The canonical leaves at `0` and `1` discharge both positive definiteness and the former
choice of two distinct parameters. -/
theorem exists_node_outside_of_extremalFamily_unconditional
    (F : GaloisForLFunctions.HTGeometry.ClassicalNevanlinnaExtremalFamily s)
    {B : ℝ} (hB : 0 < B) :
    ∃ n : ℕ, ∃ xi ∈ gaussNodes s n, xi ∉ Set.Icc (-B) B := by
  exact exists_node_outside_of_extremalFamily
    (positiveMomentForm_of_extremalFamily F) F zero_ne_one hB

end HTGeometry
