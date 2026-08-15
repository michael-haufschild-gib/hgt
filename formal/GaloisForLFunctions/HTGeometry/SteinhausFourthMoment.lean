import GaloisForLFunctions.HTGeometry.TorusPhaseTrigCalculus

/-!
# The fourth moment of a random phase combination

Independent uniform coordinate phases are the coordinate characters of the unit torus, so the
fourth moment of a linear combination of them is a Parseval sum over the pair frequencies.  Two
pairs carry the same frequency exactly when they agree as unordered pairs, so every frequency is
shared by at most two ordered pairs and the fourth moment is at most twice the square of the
squared coefficient sum.

This is the Steinhaus fourth-moment estimate in the form used by phase-seed collision bounds; the
constant two is the number of index pairings, as in the two-design identity.
-/

open MeasureTheory Complex UnitAddTorus Set

noncomputable section

namespace GaloisForLFunctions.HTGeometry

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

set_option linter.unusedSectionVars false

variable {d : Type*} [Fintype d] [DecidableEq d]

section PairFrequency

/-- The frequency of an ordered pair of coordinates. -/
def pairFreq (p : d × d) : d → ℤ := Pi.single p.1 1 + Pi.single p.2 1

/-- **Pair frequencies determine unordered pairs.** -/
theorem pairFreq_eq_iff {p q : d × d} (h : pairFreq p = pairFreq q) :
    q = p ∨ q = (p.2, p.1) := by
  classical
  obtain ⟨y, y'⟩ := p
  obtain ⟨z, z'⟩ := q
  have hev : ∀ k : d, ((if k = y then (1 : ℤ) else 0) + if k = y' then 1 else 0) =
      ((if k = z then (1 : ℤ) else 0) + if k = z' then 1 else 0) := by
    intro k
    have := congrFun h k
    simpa [pairFreq, Pi.single_apply] using this
  have hz := hev z
  have hz' := hev z'
  have hy := hev y
  have hy' := hev y'
  by_cases hzy : z = y
  · by_cases hz'y' : z' = y'
    · exact Or.inl (by rw [hzy, hz'y'])
    · by_cases hz'y : z' = y
      · have hyy' : y = y' := by
          by_contra hne
          simp [hzy, hz'y, Ne.symm hne] at hy'
        exact Or.inl (by rw [hzy, hz'y, hyy'])
      · exfalso
        simp [hzy, hz'y, hz'y'] at hz'
  · by_cases hzy' : z = y'
    · by_cases hz'y : z' = y
      · exact Or.inr (by rw [hzy', hz'y])
      · by_cases hz'y' : z' = y'
        · have hyy' : y = y' := by
            by_contra hne
            simp [hzy', hz'y', hne] at hy
          exact Or.inl (by rw [hzy', hyy'.symm, hz'y', hyy'.symm])
        · exfalso
          simp [hzy', hz'y, hz'y'] at hz'
    · exfalso
      rcases eq_or_ne z z' with hzz' | hzz'
      · subst hzz'
        simp [hzy, hzy'] at hz
      · simp [hzy, hzy', hzz'] at hz

end PairFrequency

section FourthMoment

/-- **Steinhaus fourth moment.**  A linear combination of independent uniform coordinate phases has
fourth moment at most twice the square of its squared coefficient sum. -/
theorem integral_box_phase_fourth_le (c : d → ℂ) :
    (∫ x in torusBox d, ‖∑ y, c y * charLift (Pi.single y 1) x‖ ^ 4) ≤
      2 * (∑ y, ‖c y‖ ^ 2) ^ 2 := by
  classical
  set S : ℝ := ∑ y, ‖c y‖ ^ 2 with hS
  set a : d × d → ℂ := fun p => c p.1 * c p.2 with ha
  have hsq : ∀ x : d → ℝ, (∑ y, c y * charLift (Pi.single y 1) x) ^ 2 =
      trigLift (Finset.univ : Finset (d × d)) pairFreq a x := by
    intro x
    rw [sq, Finset.sum_mul_sum, trigLift, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun y' _ => ?_
    rw [ha, pairFreq, charLift_add_index]
    ring
  have hpt : ∀ x : d → ℝ, ‖∑ y, c y * charLift (Pi.single y 1) x‖ ^ 4 =
      ‖trigLift (Finset.univ : Finset (d × d)) pairFreq a x‖ ^ 2 := by
    intro x
    rw [← hsq x, norm_pow, ← pow_mul]
  simp_rw [hpt]
  have hpars := ofReal_integral_box_normSq_trigLift (Finset.univ : Finset (d × d)) pairFreq a
  have hnn : 0 ≤ ∫ x in torusBox d,
      ‖trigLift (Finset.univ : Finset (d × d)) pairFreq a x‖ ^ 2 :=
    integral_nonneg fun x => sq_nonneg _
  have hnorm : (∫ x in torusBox d,
      ‖trigLift (Finset.univ : Finset (d × d)) pairFreq a x‖ ^ 2) =
      ‖∑ p : d × d, ∑ q : d × d,
        if pairFreq p = pairFreq q then a p * (starRingEnd ℂ) (a q) else 0‖ := by
    rw [← hpars, Complex.norm_real, Real.norm_of_nonneg hnn]
  rw [hnorm]
  refine le_trans (norm_sum_le _ _) ?_
  have hrow : ∀ p : d × d,
      ‖∑ q : d × d, if pairFreq p = pairFreq q then a p * (starRingEnd ℂ) (a q) else 0‖ ≤
        2 * ‖a p‖ ^ 2 := by
    intro p
    refine le_trans (norm_sum_le _ _) ?_
    have hbound : ∀ q : d × d,
        ‖if pairFreq p = pairFreq q then a p * (starRingEnd ℂ) (a q) else 0‖ ≤
          (if q = p ∨ q = (p.2, p.1) then ‖a p‖ ^ 2 else 0) := by
      intro q
      by_cases hq : pairFreq p = pairFreq q
      · rw [if_pos hq, norm_mul, RCLike.norm_conj]
        have hcase := pairFreq_eq_iff hq
        rw [if_pos hcase]
        rcases hcase with hc | hc
        · rw [hc, sq]
        · rw [hc]
          simp only [ha, norm_mul, sq]
          exact le_of_eq (by ring)
      · rw [if_neg hq, norm_zero]
        split <;> positivity
    refine le_trans (Finset.sum_le_sum fun q _ => hbound q) ?_
    have hsub : (Finset.univ : Finset (d × d)).filter (fun q => q = p ∨ q = (p.2, p.1)) ⊆
        {p, (p.2, p.1)} := by
      intro q hq
      rw [Finset.mem_filter] at hq
      rcases hq.2 with h | h <;> simp [h]
    calc (∑ q : d × d, if q = p ∨ q = (p.2, p.1) then ‖a p‖ ^ 2 else 0)
        = ∑ _q ∈ (Finset.univ : Finset (d × d)).filter
            (fun q => q = p ∨ q = (p.2, p.1)), ‖a p‖ ^ 2 := by
          rw [Finset.sum_filter]
      _ ≤ ∑ _q ∈ ({p, (p.2, p.1)} : Finset (d × d)), ‖a p‖ ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun q _ _ => sq_nonneg _)
      _ ≤ 2 * ‖a p‖ ^ 2 := by
          rw [Finset.sum_const, nsmul_eq_mul]
          have hcard : ({p, (p.2, p.1)} : Finset (d × d)).card ≤ 2 := Finset.card_insert_le _ _
          have : ((({p, (p.2, p.1)} : Finset (d × d)).card : ℝ)) ≤ 2 := by exact_mod_cast hcard
          nlinarith [sq_nonneg ‖a p‖]
  refine le_trans (Finset.sum_le_sum fun p _ => hrow p) ?_
  have hsum : (∑ p : d × d, 2 * ‖a p‖ ^ 2) = 2 * S ^ 2 := by
    rw [← Finset.mul_sum]
    congr 1
    rw [Fintype.sum_prod_type, hS, sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun y' _ => ?_
    rw [ha]
    simp only []
    rw [norm_mul, mul_pow]
  rw [hsum]

end FourthMoment

end GaloisForLFunctions.HTGeometry
