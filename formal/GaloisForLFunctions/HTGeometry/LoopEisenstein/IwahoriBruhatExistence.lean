import GaloisForLFunctions.HTGeometry.LoopEisenstein.LaurentIwahoriCriteria
import GaloisForLFunctions.HTGeometry.LoopEisenstein.SL2PivotReduction

/-!
# Existence of affine Iwahori Bruhat representatives

Valuation-sensitive elimination reduces every Laurent special-linear matrix
to a monomial diagonal or Weyl matrix using actual Iwahori factors.
-/

namespace GaloisForLFunctions.HTGeometry.LoopEisenstein

noncomputable section

variable (F : Type*) [Field F]

/-- Equality of actual Iwahori double cosets, expressed by two explicit factors. -/
def iwahoriEquivalent (g h : SL2 (LaurentSeries F)) : Prop :=
  ∃ l ∈ laurentIwahori F, ∃ r ∈ laurentIwahori F, l * g * r = h

theorem iwahoriEquivalent_refl (g : SL2 (LaurentSeries F)) : iwahoriEquivalent F g g :=
  ⟨1, (laurentIwahori F).one_mem, 1, (laurentIwahori F).one_mem, by rw [one_mul, mul_one]⟩

theorem iwahoriEquivalent_symm {g h : SL2 (LaurentSeries F)}
    (hgh : iwahoriEquivalent F g h) : iwahoriEquivalent F h g := by
  obtain ⟨l, hl, r, hr, h⟩ := hgh
  refine ⟨l⁻¹, (laurentIwahori F).inv_mem hl, r⁻¹, (laurentIwahori F).inv_mem hr, ?_⟩
  rw [← h]
  group

theorem iwahoriEquivalent_trans {g h k : SL2 (LaurentSeries F)}
    (hgh : iwahoriEquivalent F g h) (hhk : iwahoriEquivalent F h k) :
    iwahoriEquivalent F g k := by
  obtain ⟨l₁, hl₁, r₁, hr₁, h₁⟩ := hgh
  obtain ⟨l₂, hl₂, r₂, hr₂, h₂⟩ := hhk
  refine ⟨l₂ * l₁, (laurentIwahori F).mul_mem hl₂ hl₁,
    r₁ * r₂, (laurentIwahori F).mul_mem hr₁ hr₂, ?_⟩
  calc
    _ = l₂ * (l₁ * g * r₁) * r₂ := by simp only [mul_assoc]
    _ = k := by rw [h₁, h₂]

/-- The two families of concrete representatives indexed by the infinite affine Weyl group. -/
def affineWeylMatrix : AffineA1.Weyl → SL2 (LaurentSeries F)
  | .r m => sl2Diagonal (laurentXUnit F ^ (-(show ℤ from m)))
  | .sr m => sl2WeylLower (laurentXUnit F ^ (-(show ℤ from m)))

/-- One of the four pivots has exactly the valuation inequalities required by its shears. -/
theorem iwahori_pivot_cases (g : SL2 (LaurentSeries F)) :
    (g 1 0 ≠ 0 ∧ laurentValuation F (g 0 0) ≤ laurentValuation F (g 1 0) ∧
      laurentValuation F (g 1 1) ≤ laurentValuation F (g 1 0)) ∨
    (g 0 1 ≠ 0 ∧ laurentValuation F (g 0 0) < laurentValuation F (g 0 1) ∧
      laurentValuation F (g 1 1) < laurentValuation F (g 0 1)) ∨
    (g 0 0 ≠ 0 ∧ laurentValuation F (g 0 1) ≤ laurentValuation F (g 0 0) ∧
      laurentValuation F (g 1 0) < laurentValuation F (g 0 0)) ∨
    (g 1 1 ≠ 0 ∧ laurentValuation F (g 0 1) ≤ laurentValuation F (g 1 1) ∧
      laurentValuation F (g 1 0) < laurentValuation F (g 1 1)) := by
  by_cases hc : max (laurentValuation F (g 0 0)) (laurentValuation F (g 1 1)) ≤
      laurentValuation F (g 1 0)
  · left
    have hca := (le_max_left _ _).trans hc
    have hcd := (le_max_right _ _).trans hc
    refine ⟨?_, hca, hcd⟩
    intro hzero
    have ha : g 0 0 = 0 := by
      by_contra hne
      have hpos : 0 < laurentValuation F (g 0 0) :=
        pos_iff_ne_zero.2 ((Valuation.ne_zero_iff _).2 hne)
      rw [hzero, map_zero] at hca
      exact (not_le_of_gt hpos) hca
    have hdet := Matrix.SpecialLinearGroup.det_coe g
    rw [Matrix.det_fin_two, ha, hzero, zero_mul, mul_zero, sub_zero] at hdet
    exact zero_ne_one hdet
  have hclt := lt_of_not_ge hc
  by_cases hb : max (laurentValuation F (g 0 0)) (laurentValuation F (g 1 1)) <
      laurentValuation F (g 0 1)
  · right; left
    refine ⟨?_, lt_of_le_of_lt (le_max_left _ _) hb, lt_of_le_of_lt (le_max_right _ _) hb⟩
    intro hzero
    rw [hzero, map_zero] at hb
    exact (not_lt_of_ge zero_le) hb
  have hble := le_of_not_gt hb
  by_cases had : laurentValuation F (g 0 0) ≤ laurentValuation F (g 1 1)
  · rw [max_eq_right had] at hclt hble
    right; right; right
    refine ⟨?_, hble, hclt⟩
    intro hzero
    rw [hzero, map_zero] at hclt
    exact (not_lt_of_ge zero_le) hclt
  · have hda := le_of_lt (lt_of_not_ge had)
    rw [max_eq_left hda] at hclt hble
    right; right; left
    refine ⟨?_, hble, hclt⟩
    intro hzero
    rw [hzero, map_zero] at hclt
    exact (not_lt_of_ge zero_le) hclt

theorem iwahoriEquivalent_diagonal_monomial (a : (LaurentSeries F)ˣ) :
    iwahoriEquivalent F (sl2Diagonal a)
      (sl2Diagonal (laurentXUnit F ^ (a : LaurentSeries F).order)) := by
  let u := laurentUnitPowerSeriesPart F a
  have hu := sl2Diagonal_powerSeriesUnit_mem_laurentIwahori F u
  refine ⟨1, (laurentIwahori F).one_mem,
    (sl2Diagonal (powerSeriesLaurentUnit F u))⁻¹, (laurentIwahori F).inv_mem hu, ?_⟩
  have ha : sl2Diagonal a = sl2Diagonal (laurentXUnit F ^ (a : LaurentSeries F).order) *
      sl2Diagonal (powerSeriesLaurentUnit F u) := by
    rw [← sl2Diagonal_mul]
    exact congrArg sl2Diagonal (laurentUnit_monomial_factor F a)
  rw [one_mul, ha, mul_assoc, mul_inv_cancel, mul_one]

theorem iwahoriEquivalent_weyl_monomial (a : (LaurentSeries F)ˣ) :
    iwahoriEquivalent F (sl2WeylLower a)
      (sl2WeylLower (laurentXUnit F ^ (a : LaurentSeries F).order)) := by
  let u := laurentUnitPowerSeriesPart F a
  have hu := sl2Diagonal_powerSeriesUnit_mem_laurentIwahori F u
  refine ⟨1, (laurentIwahori F).one_mem,
    (sl2Diagonal (powerSeriesLaurentUnit F u))⁻¹, (laurentIwahori F).inv_mem hu, ?_⟩
  have ha : sl2WeylLower a = sl2WeylLower (laurentXUnit F ^ (a : LaurentSeries F).order) *
      sl2Diagonal (powerSeriesLaurentUnit F u) := by
    rw [sl2WeylLower_mul_diagonal]
    exact congrArg sl2WeylLower (laurentUnit_monomial_factor F a)
  rw [one_mul, ha, mul_assoc, mul_inv_cancel, mul_one]

private theorem upper_shear_mem {s t : LaurentSeries F} (ht : t ≠ 0)
    (hst : laurentValuation F s ≤ laurentValuation F t) :
    sl2Upper (-s / t) ∈ laurentIwahori F := by
  apply sl2Upper_mem_laurentIwahori
  simpa using laurentValuation_div_le_one F ht hst

private theorem lower_shear_mem {s t : LaurentSeries F} (ht : t ≠ 0)
    (hst : laurentValuation F s < laurentValuation F t) :
    sl2Lower (-s / t) ∈ laurentIwahori F := by
  apply sl2Lower_mem_laurentIwahori
  simpa using laurentValuation_div_lt_one F ht hst

/-- Every Laurent matrix has a diagonal or antidiagonal pivot representative using Iwahori factors. -/
theorem exists_iwahori_pivot (g : SL2 (LaurentSeries F)) :
    ∃ a : (LaurentSeries F)ˣ,
      iwahoriEquivalent F g (sl2Diagonal a) ∨ iwahoriEquivalent F g (sl2WeylLower a) := by
  rcases iwahori_pivot_cases F g with ⟨hc, hac, hdc⟩ | ⟨hb, hab, hdb⟩ |
    ⟨ha, hba, hca⟩ | ⟨hd, hbd, hcd⟩
  · refine ⟨Units.mk0 (g 1 0) hc, Or.inr ?_⟩
    exact ⟨sl2Upper (-g 0 0 / g 1 0), upper_shear_mem F hc hac,
      sl2Upper (-g 1 1 / g 1 0), upper_shear_mem F hc hdc,
      sl2_pivot_lower_left g (Units.mk0 (g 1 0) hc) rfl⟩
  · refine ⟨-(Units.mk0 (g 0 1) hb)⁻¹, Or.inr ?_⟩
    exact ⟨sl2Lower (-g 1 1 / g 0 1), lower_shear_mem F hb hdb,
      sl2Lower (-g 0 0 / g 0 1), lower_shear_mem F hb hab,
      sl2_pivot_upper_right g (Units.mk0 (g 0 1) hb) rfl⟩
  · refine ⟨Units.mk0 (g 0 0) ha, Or.inl ?_⟩
    exact ⟨sl2Lower (-g 1 0 / g 0 0), lower_shear_mem F ha hca,
      sl2Upper (-g 0 1 / g 0 0), upper_shear_mem F ha hba,
      sl2_pivot_upper_left g (Units.mk0 (g 0 0) ha) rfl⟩
  · refine ⟨(Units.mk0 (g 1 1) hd)⁻¹, Or.inl ?_⟩
    exact ⟨sl2Upper (-g 0 1 / g 1 1), upper_shear_mem F hd hbd,
      sl2Lower (-g 1 0 / g 1 1), lower_shear_mem F hd hcd,
      sl2_pivot_lower_right g (Units.mk0 (g 1 1) hd) rfl⟩

/-- Every full formal Laurent SL₂ matrix lies in an actual affine Weyl Iwahori double coset. -/
theorem exists_iwahori_bruhat (g : SL2 (LaurentSeries F)) :
    ∃ w : AffineA1.Weyl, iwahoriEquivalent F g (affineWeylMatrix F w) := by
  obtain ⟨a, h | h⟩ := exists_iwahori_pivot F g
  · refine ⟨.r (-(a : LaurentSeries F).order), ?_⟩
    simpa only [affineWeylMatrix, neg_neg] using
      iwahoriEquivalent_trans F h (iwahoriEquivalent_diagonal_monomial F a)
  · refine ⟨.sr (-(a : LaurentSeries F).order), ?_⟩
    simpa only [affineWeylMatrix, neg_neg] using
      iwahoriEquivalent_trans F h (iwahoriEquivalent_weyl_monomial F a)

end

end GaloisForLFunctions.HTGeometry.LoopEisenstein
