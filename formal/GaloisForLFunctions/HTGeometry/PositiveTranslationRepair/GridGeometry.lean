import GaloisForLFunctions.HTGeometry.PositiveTranslationRepair.LowerGridStep

/-! Lower grid approximations retain positive outer bands and confine their negative
part to a fixed core. Symmetric grids can have arbitrarily small mesh. -/

open MeasureTheory Set

noncomputable section
namespace GaloisForLFunctions.HTGeometry.PositiveTranslationRepair

theorem lowerGridStep_left_endpoint {f : ℝ → ℝ} {L a h x : ℝ} {M : ℕ}
    (hh : 0 < h) (hx : x ∈ Ioc a (a + M * h)) :
    ∃ y : ℝ, a ≤ y ∧ y ≤ a + M * h ∧ x - h ≤ y ∧ y < x ∧
      lowerGridStep f L a h M x = f y - L * h := by
  obtain ⟨j, hj, hxj⟩ := exists_gridCell_of_mem M hx
  refine ⟨a + j * h, ?_, ?_, ?_, hxj.1, ?_⟩
  · exact le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) hh.le)
  · have hj' : (j : ℝ) ≤ M := by exact_mod_cast (Finset.mem_range.mp hj).le
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_right hj' hh.le)
  · have hx' := hxj.2
    linarith only [hx']
  · exact gridStep_eq_of_mem hh hj hxj

/-- Uniformly positive left endpoints confine all negative cells to a fixed interval. -/
theorem lowerGridStep_nonneg_outside {f : ℝ → ℝ} {L A R h u : ℝ} {M : ℕ}
    (hh : 0 < h) (hh1 : h ≤ 1) (hend : -R + M * h = R)
    (hu : L * h ≤ u) (hf : ∀ y, A + 1 ≤ |y| → |y| ≤ R → u ≤ f y)
    {x : ℝ} (hx : A + 2 ≤ |x|) :
    0 ≤ lowerGridStep f L (-R) h M x := by
  by_cases hxR : x ∈ Ioc (-R) R
  · obtain ⟨y, hylo, hyhi, hyx, hyx', he⟩ :=
      lowerGridStep_left_endpoint (f := f) (L := L) (a := -R) (M := M) (x := x) hh
        (by simpa only [hend] using hxR)
    rw [hend] at hyhi
    have hyR : |y| ≤ R := abs_le.mpr ⟨hylo, hyhi⟩
    have hyA : A + 1 ≤ |y| := by
      by_contra hn
      have hy := abs_lt.mp (lt_of_not_ge hn)
      have hx' : |x| < A + 2 := abs_lt.mpr
        ⟨by linarith only [hy.1, hyx'], by linarith only [hy.2, hyx, hh1]⟩
      exact hx'.not_ge hx
    rw [he]
    exact sub_nonneg.mpr (hu.trans (hf y hyA hyR))
  · rw [lowerGridStep, gridStep_eq_zero hh.le (by simpa only [hend] using hxR)]

theorem lowerGridStep_lower_bound {f : ℝ → ℝ} {L A R h u B : ℝ} {M : ℕ}
    (hB : 0 ≤ B) (hh : 0 < h) (hend : -R + M * h = R)
    (hu : L * h ≤ u) (hhL : L * h ≤ 1)
    (houter : ∀ y, A + 1 ≤ |y| → |y| ≤ R → u ≤ f y)
    (hinner : ∀ y, |y| ≤ A + 1 → |f y| ≤ B) (x : ℝ) :
    -(B + 1) ≤ lowerGridStep f L (-R) h M x := by
  by_cases hx : x ∈ Ioc (-R) R
  · obtain ⟨y, hylo, hyhi, _, _, he⟩ :=
      lowerGridStep_left_endpoint (f := f) (L := L) (a := -R) (M := M) (x := x) hh
        (by simpa only [hend] using hx)
    rw [hend] at hyhi
    rw [he]
    by_cases hy : A + 1 ≤ |y|
    · have hp := hu.trans (houter y hy (abs_le.mpr ⟨hylo, hyhi⟩))
      linarith only [hp, hB]
    · have hb := (abs_le.mp (hinner y (lt_of_not_ge hy).le)).1
      linarith only [hb, hhL]
  · rw [lowerGridStep, gridStep_eq_zero hh.le (by simpa only [hend] using hx)]
    linarith only [hB]

/-- Positive source bands remain uniformly positive after sufficiently fine lower sampling. -/
theorem lowerGridStep_pos_on_outer_bands {f : ℝ → ℝ} {L A R h m : ℝ} {M : ℕ}
    (hh : 0 < h) (hh1 : h ≤ 1) (hend : -R + M * h = R)
    (hR : A + 5 < R) (hhL : L * h ≤ m / 2)
    (hm : ∀ y, A + 2 ≤ |y| → |y| ≤ A + 5 → m ≤ f y)
    {x : ℝ} (hx : A + 3 ≤ |x| ∧ |x| ≤ A + 4) :
    m / 2 ≤ lowerGridStep f L (-R) h M x := by
  have hxR : x ∈ Ioc (-R) R := by
    have hx' := abs_le.mp hx.2
    constructor <;> linarith only [hx'.1, hx'.2, hR]
  obtain ⟨y, _, _, hyx, hyx', he⟩ :=
      lowerGridStep_left_endpoint (f := f) (L := L) (a := -R) (M := M) (x := x) hh
        (by simpa only [hend] using hxR)
  have hxy : |x - y| ≤ 1 := by
    rw [abs_of_nonneg (sub_nonneg.mpr hyx'.le)]
    linarith only [hyx, hh1]
  have hyl : A + 2 ≤ |y| := by
    have ht := abs_sub_abs_le_abs_sub x y
    linarith only [ht, hx.1, hxy]
  have hyu : |y| ≤ A + 5 := by
    have ht := abs_sub_abs_le_abs_sub y x
    rw [abs_sub_comm y x] at ht
    linarith only [ht, hx.2, hxy]
  rw [he]
  linarith only [hm y hyl hyu, hhL]

/-- An arbitrarily fine uniform mesh can have prescribed symmetric endpoints. -/
theorem exists_symmetric_mesh {R δ : ℝ} (hR : 0 < R) (hδ : 0 < δ) :
    ∃ M : ℕ, 0 < M ∧ 0 < 2 * R / M ∧ 2 * R / M < δ ∧
      -R + M * (2 * R / M) = R := by
  obtain ⟨M, hM⟩ := exists_nat_gt (max 0 (2 * R / δ))
  have hM0 : (0 : ℝ) < M := lt_of_le_of_lt (le_max_left _ _) hM
  have hMD : 2 * R / δ < M := lt_of_le_of_lt (le_max_right _ _) hM
  refine ⟨M, by exact_mod_cast hM0, div_pos (mul_pos two_pos hR) hM0, ?_, ?_⟩
  · apply (div_lt_iff₀ hM0).mpr
    have h := (div_lt_iff₀ hδ).mp hMD
    simpa only [mul_comm] using h
  · field_simp [hM0.ne']
    ring

#print axioms lowerGridStep_pos_on_outer_bands
end GaloisForLFunctions.HTGeometry.PositiveTranslationRepair
