import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.GammaVarianceCoercivity
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.HaarCellGammaPayment

/-!
# Gamma payment inside arbitrary complete-cell sections

Each adjacent pair retains an independent average and detail coefficient.
Its local variance is exactly the balanced square mass. The original Gamma
energy therefore pays every logarithmic detail charge, even with all pair
averages present.
-/

noncomputable section
open MeasureTheory Set
open _root_.RHTower

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri.LogCells
open BiarithmeticGaugeGeometry HTGeometry IntervalVariance

/-- The literal constant profile on a complete adjacent pair. -/
def coarseProfile (a : ℕ) (x : ℝ) : ℝ := rawCell (2 * a) x + rawCell (2 * a + 1) x

/-- Arbitrary independent averages on complete adjacent pairs. -/
def averageSectionProfile (q : ℕ → ℝ) (X : ℕ) (x : ℝ) : ℝ :=
  ∑ a ∈ Finset.Icc 1 X, q a * coarseProfile a x

/-- Both source directions on each complete pair, with independent coefficients. -/
def completePairProfile (q d : ℕ → ℝ) (X : ℕ) (x : ℝ) : ℝ :=
  averageSectionProfile q X x + haarSectionProfile d X x

private theorem coarseProfile_on_pair {a : ℕ} {x : ℝ}
    (hx : x ∈ Ioo (Real.log ((2 * a : ℕ) : ℝ)) (Real.log ((2 * a + 2 : ℕ) : ℝ))) :
    coarseProfile a x = 1 := by
  unfold coarseProfile rawCell
  by_cases hm : x < Real.log ((2 * a + 1 : ℕ) : ℝ)
  · have hl : x ∈ Ico (Real.log ((2 * a : ℕ) : ℝ)) (Real.log ((2 * a + 1 : ℕ) : ℝ)) :=
      ⟨hx.1.le, hm⟩
    have hr : x ∉ Ico (Real.log ((2 * a + 1 : ℕ) : ℝ))
        (Real.log ((2 * a + 1 + 1 : ℕ) : ℝ)) := fun h => (not_lt_of_ge h.1) hm
    rw [indicator_of_mem hl, indicator_of_notMem hr]
    norm_num
  · have hl : x ∉ Ico (Real.log ((2 * a : ℕ) : ℝ)) (Real.log ((2 * a + 1 : ℕ) : ℝ)) :=
      fun h => hm h.2
    have hr : x ∈ Ico (Real.log ((2 * a + 1 : ℕ) : ℝ))
        (Real.log ((2 * a + 1 + 1 : ℕ) : ℝ)) :=
      ⟨le_of_not_gt hm, by simpa only [Nat.add_assoc] using hx.2⟩
    rw [indicator_of_notMem hl, indicator_of_mem hr]
    norm_num

private theorem coarseProfile_zero_outside_pair {a : ℕ} (ha : 1 ≤ a) {x : ℝ}
    (hx : x ∉ Ico (Real.log ((2 * a : ℕ) : ℝ)) (Real.log ((2 * a + 2 : ℕ) : ℝ))) :
    coarseProfile a x = 0 := by
  have hlo : Real.log ((2 * a : ℕ) : ℝ) ≤ Real.log ((2 * a + 1 : ℕ) : ℝ) :=
    Real.log_le_log (by positivity) (by exact_mod_cast (show 2 * a ≤ 2 * a + 1 by omega))
  have hhi : Real.log ((2 * a + 1 : ℕ) : ℝ) ≤ Real.log ((2 * a + 2 : ℕ) : ℝ) :=
    Real.log_le_log (by positivity) (by exact_mod_cast (show 2 * a + 1 ≤ 2 * a + 2 by omega))
  have hl : x ∉ Ico (Real.log ((2 * a : ℕ) : ℝ)) (Real.log ((2 * a + 1 : ℕ) : ℝ)) :=
    fun h => hx ⟨h.1, h.2.trans_le hhi⟩
  have hr : x ∉ Ico (Real.log ((2 * a + 1 : ℕ) : ℝ))
      (Real.log ((2 * a + 1 + 1 : ℕ) : ℝ)) := by
    intro h
    exact hx ⟨hlo.trans h.1, by simpa only [Nat.add_assoc] using h.2⟩
  simp only [coarseProfile, rawCell, indicator_of_notMem hl, indicator_of_notMem hr, add_zero]

private theorem averageSectionProfile_on_pair (q : ℕ → ℝ) {X a : ℕ}
    (ha : 1 ≤ a) (haX : a ≤ X) {x : ℝ}
    (hx : x ∈ Ioo (Real.log ((2 * a : ℕ) : ℝ)) (Real.log ((2 * a + 2 : ℕ) : ℝ))) :
    averageSectionProfile q X x = q a := by
  classical
  unfold averageSectionProfile
  rw [Finset.sum_eq_single a]
  · rw [coarseProfile_on_pair hx, mul_one]
  · intro b hb hba
    have hb1 := (Finset.mem_Icc.mp hb).1
    have hz : coarseProfile b x = 0 := by
      apply coarseProfile_zero_outside_pair hb1
      intro hxB
      rcases lt_or_gt_of_ne hba with hlt | hgt
      · have he : Real.log ((2 * b + 2 : ℕ) : ℝ) ≤ Real.log ((2 * a : ℕ) : ℝ) :=
          Real.log_le_log (by positivity) (by exact_mod_cast (show 2 * b + 2 ≤ 2 * a by omega))
        linarith only [hx.1, hxB.2, he]
      · have he : Real.log ((2 * a + 2 : ℕ) : ℝ) ≤ Real.log ((2 * b : ℕ) : ℝ) :=
          Real.log_le_log (by positivity) (by exact_mod_cast (show 2 * a + 2 ≤ 2 * b by omega))
        linarith only [hx.2, hxB.1, he]
    rw [hz, mul_zero]
  · intro hn
    exact False.elim (hn (Finset.mem_Icc.mpr ⟨ha, haX⟩))

private theorem completePairProfile_on_pair (q d : ℕ → ℝ) {X a : ℕ}
    (ha : 1 ≤ a) (haX : a ≤ X) {x : ℝ}
    (hx : x ∈ Ioo (Real.log ((2 * a : ℕ) : ℝ)) (Real.log ((2 * a + 2 : ℕ) : ℝ))) :
    completePairProfile q d X x = q a + d a * haarProfile a x := by
  rw [completePairProfile, averageSectionProfile_on_pair q ha haX hx,
    haarSectionProfile_on_pair d ha haX hx]

/-- Every choice of the two original cell coefficients occurs in the average-detail family. -/
theorem completePairProfile_eq_cells (u v : ℕ → ℝ) (X : ℕ) (x : ℝ) :
    completePairProfile (fun a => haarRightCoeff a * u a + haarLeftCoeff a * v a)
      (fun a => u a - v a) X x =
      ∑ a ∈ Finset.Icc 1 X, (u a * rawCell (2 * a) x + v a * rawCell (2 * a + 1) x) := by
  unfold completePairProfile averageSectionProfile haarSectionProfile
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  simp only [coarseProfile, haarProfile]
  calc
    _ = (u a * (haarLeftCoeff a + haarRightCoeff a)) * rawCell (2 * a) x +
        (v a * (haarLeftCoeff a + haarRightCoeff a)) * rawCell (2 * a + 1) x := by ring
    _ = _ := by rw [haarCoeff_sum (Finset.mem_Icc.mp ha).1, mul_one, mul_one]

private theorem averageSectionProfile_bv (q : ℕ → ℝ) (X : ℕ) :
    BoundedVariationOn (averageSectionProfile q X) univ := by
  have hcoarse (a : ℕ) : BoundedVariationOn (coarseProfile a) univ := by
    change BoundedVariationOn (fun x => rawCell (2 * a) x + rawCell (2 * a + 1) x) univ
    simpa only [neg_one_mul, sub_neg_eq_add] using
      boundedVariationOn_sub (rawCell_bv (2 * a)) (bv_const_mul (-1) (rawCell_bv (2 * a + 1)))
  have hsum (s : Finset ℕ) : BoundedVariationOn (fun x => ∑ a ∈ s, q a * coarseProfile a x) univ := by
    classical
    induction s using Finset.induction_on with
    | empty =>
      simpa only [Finset.sum_empty] using
        ((monotone_const : Monotone (fun _ : ℝ => (0 : ℝ))).monotoneOn univ).boundedVariationOn
          (C := 0) (fun x _ => by simp)
    | @insert a s ha ih =>
      simpa only [Finset.sum_insert ha, neg_one_mul, sub_neg_eq_add] using
        boundedVariationOn_sub (bv_const_mul (q a) (hcoarse a)) (bv_const_mul (-1) ih)
  exact hsum _

private theorem averageSectionProfile_compact (q : ℕ → ℝ) (X : ℕ) :
    HasCompactSupport (averageSectionProfile q X) := by
  apply HasCompactSupport.intro (isCompact_Icc (a := (0 : ℝ)) (b := Real.log ((2 * X + 2 : ℕ) : ℝ)))
  intro x hx
  unfold averageSectionProfile
  apply Finset.sum_eq_zero
  intro a ha
  have ha1 := (Finset.mem_Icc.mp ha).1
  have haX := (Finset.mem_Icc.mp ha).2
  have hz : coarseProfile a x = 0 := by
    apply coarseProfile_zero_outside_pair ha1
    intro hi
    have hlo : 0 ≤ Real.log ((2 * a : ℕ) : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ 2 * a by omega))
    have hhi : Real.log ((2 * a + 2 : ℕ) : ℝ) ≤ Real.log ((2 * X + 2 : ℕ) : ℝ) :=
      Real.log_le_log (by positivity) (by exact_mod_cast (show 2 * a + 2 ≤ 2 * X + 2 by omega))
    exact hx ⟨hlo.trans hi.1, hi.2.le.trans hhi⟩
  rw [hz, mul_zero]

theorem completePairProfile_bv (q d : ℕ → ℝ) (X : ℕ) :
    BoundedVariationOn (completePairProfile q d X) univ := by
  change BoundedVariationOn (fun x => averageSectionProfile q X x + haarSectionProfile d X x) univ
  simpa only [neg_one_mul, sub_neg_eq_add] using
    boundedVariationOn_sub (averageSectionProfile_bv q X) (bv_const_mul (-1) (haarSectionProfile_bv d X))

theorem completePairProfile_compact (q d : ℕ → ℝ) (X : ℕ) :
    HasCompactSupport (completePairProfile q d X) :=
  (averageSectionProfile_compact q X).add (haarSectionProfile_compact d X)

/-- The local average is exactly the independent average coefficient. -/
theorem intervalMean_completePairProfile (q d : ℕ → ℝ) {X a : ℕ} (ha : 1 ≤ a) (haX : a ≤ X) :
    intervalMean (Real.log ((2 * a : ℕ) : ℝ)) (Real.log ((2 * a + 2 : ℕ) : ℝ))
      (completePairProfile q d X) = q a := by
  have hw := logCellWidth_pos ha
  have hab : Real.log ((2 * a : ℕ) : ℝ) < Real.log ((2 * a + 2 : ℕ) : ℝ) := by
    apply sub_pos.mp
    rw [haarPairWidth ha]
    exact hw
  unfold intervalMean
  rw [setIntegral_congr_fun measurableSet_Ioo (fun x hx => completePairProfile_on_pair q d ha haX hx),
    integral_add (HTGeometry.CauchyDifference.integrableOn_Ioo_of_continuous continuous_const)
      (((integrable_haarProfile a).const_mul (d a)).integrableOn),
    setIntegral_const, Real.volume_real_Ioo_of_le hab.le, smul_eq_mul,
    integral_const_mul, setIntegral_haarProfile_pair ha, mul_zero, add_zero]
  rw [mul_comm, mul_div_assoc, div_self (ne_of_gt (sub_pos.mpr hab)), mul_one]

/-- Pair averages leave the exact balanced variance unchanged. -/
theorem intervalVariance_completePairProfile (q d : ℕ → ℝ) {X a : ℕ} (ha : 1 ≤ a) (haX : a ≤ X) :
    intervalVariance (Real.log ((2 * a : ℕ) : ℝ)) (Real.log ((2 * a + 2 : ℕ) : ℝ))
      (completePairProfile q d X) = haarMass a * d a ^ 2 := by
  unfold intervalVariance
  rw [intervalMean_completePairProfile q d ha haX]
  have he : ∀ x ∈ Ioo (Real.log ((2 * a : ℕ) : ℝ)) (Real.log ((2 * a + 2 : ℕ) : ℝ)),
      (completePairProfile q d X x - q a) ^ 2 = d a ^ 2 * haarProfile a x ^ 2 := by
    intro x hx
    rw [completePairProfile_on_pair q d ha haX hx]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioo he, integral_const_mul,
    setIntegral_haarProfile_pair_sq ha, mul_comm]

/-- The full source pays its logarithmic detail charge with arbitrary pair averages present. -/
theorem completePairProfile_levyEnergy_ge (q c : ℕ → ℝ) (X : ℕ) :
    (∑ a ∈ Finset.Icc 1 X, Real.log (a : ℝ) * haarMass a * c a ^ 2) ≤
      levyEnergy (completePairProfile q c X) := by
  let S := Finset.Icc 1 X
  let L : S → ℝ := fun i => Real.log ((2 * (i : ℕ) : ℕ) : ℝ)
  let U : S → ℝ := fun i => Real.log ((2 * (i : ℕ) + 2 : ℕ) : ℝ)
  have hpos (i : S) : 1 ≤ (i : ℕ) := (Finset.mem_Icc.mp i.property).1
  have hwidth (i : S) : U i - L i = logCellWidth (i : ℕ) := haarPairWidth (hpos i)
  have hw0 (i : S) : 0 < U i - L i := by rw [hwidth]; exact logCellWidth_pos (hpos i)
  have hwidth1 (i : S) : U i - L i ≤ 1 := by
    rw [hwidth]
    exact (logCellWidth_le_inv (hpos i)).trans
      ((div_le_one (by exact_mod_cast (show 0 < (i : ℕ) by have := hpos i; omega))).mpr
        (by exact_mod_cast hpos i))
  have hsep (i j : S) (hij : i ≠ j) : U i ≤ L j ∨ U j ≤ L i := by
    have hne : (i : ℕ) ≠ (j : ℕ) := fun h => hij (Subtype.ext h)
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · left
      apply Real.log_le_log (by have := hpos i; positivity)
      exact_mod_cast (show 2 * (i : ℕ) + 2 ≤ 2 * (j : ℕ) by omega)
    · right
      apply Real.log_le_log (by have := hpos j; positivity)
      exact_mod_cast (show 2 * (j : ℕ) + 2 ≤ 2 * (i : ℕ) by omega)
  have h := levyEnergy_ge_sum_log_variance L U (fun i => sub_pos.mp (hw0 i)) hwidth1 hsep
    (completePairProfile_bv q c X) (completePairProfile_compact q c X)
  apply le_trans ?_ h
  rw [← Finset.sum_coe_sort]
  apply Finset.sum_le_sum
  intro i _hi
  rw [intervalVariance_completePairProfile q c (hpos i) (Finset.mem_Icc.mp i.property).2]
  have hlog : Real.log ((i : ℕ) : ℝ) ≤ Real.log (1 / (U i - L i)) := by
    apply Real.log_le_log (by exact_mod_cast (show 0 < (i : ℕ) by have := hpos i; omega))
    apply (le_div_iff₀ (hw0 i)).mpr
    rw [hwidth]
    have hle := mul_le_mul_of_nonneg_left (logCellWidth_le_inv (hpos i))
      (Nat.cast_nonneg (i : ℕ))
    have hi0 : ((i : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (show (i : ℕ) ≠ 0 by have := hpos i; omega)
    simpa only [mul_one_div_cancel hi0] using hle
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hlog
    (mul_nonneg (haarMass_pos (hpos i)).le (sq_nonneg _))

/-- In the original cell coordinates, Gamma pays every adjacent coefficient difference. -/
theorem cellPairSum_levyEnergy_ge (u v : ℕ → ℝ) (X : ℕ) :
    (∑ a ∈ Finset.Icc 1 X, Real.log (a : ℝ) * haarMass a * (u a - v a) ^ 2) ≤
      levyEnergy (fun x => ∑ a ∈ Finset.Icc 1 X,
        (u a * rawCell (2 * a) x + v a * rawCell (2 * a + 1) x)) := by
  have h := completePairProfile_levyEnergy_ge
    (fun a => haarRightCoeff a * u a + haarLeftCoeff a * v a) (fun a => u a - v a) X
  have he := funext (completePairProfile_eq_cells u v X)
  rw [he] at h
  exact h

#print axioms completePairProfile_eq_cells
#print axioms intervalVariance_completePairProfile
#print axioms completePairProfile_levyEnergy_ge
#print axioms cellPairSum_levyEnergy_ge

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri.LogCells
