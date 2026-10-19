import GaloisForLFunctions.TransHorizonIncidenceMechanics.FermiPhysicalOptimalConstants
import GaloisForLFunctions.TransHorizonIncidenceMechanics.FermiHorizonThreePhysicalGram

/-!
# Strict separation of the physical signed and nonnegative inverse constants

The common leading logarithmic asymptotic does not force finite-horizon
cone equality. At horizon three the nonnegative physical ratio attains its
maximum with both coefficients two and three strictly positive and with
coefficient one zero. Its odd pronic mean is positive, so the exact centering
law produces a signed input with a strictly larger physical ratio. Thus
`fermiNonnegativePhysicalInverseConstant 3 < fermiPhysicalInverseConstant 3`.

The proof uses exact pronic comparisons, compactness of the normalized
nonnegative interval, and the previously verified common-energy shift.
The generic two-variable Rayleigh algebra below is classical supporting
machinery, not an independently claimed contribution.
-/

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

set_option autoImplicit false

open BezoutValuationIncidence Set

private def coneNumerator (A B C a b : ℝ) : ℝ := A * a^2 + 2 * B * a * b + C * b^2

private def coneDenominator (D E F a b : ℝ) : ℝ := D * a^2 + 2 * E * a * b + F * b^2

private theorem cone_denominator_pos {D E F a b : ℝ}
    (hD : 0 < D) (hE : 0 ≤ E) (hF : 0 < F)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : 0 < a + b) :
    0 < coneDenominator D E F a b := by
  have hcross : 0 ≤ 2 * E * a * b := by positivity
  unfold coneDenominator
  rcases lt_or_eq_of_le ha with ha | rfl
  · have hfirst := mul_pos hD (sq_pos_of_pos ha)
    have hlast := mul_nonneg hF.le (sq_nonneg b)
    linarith
  · have hbpos : 0 < b := by linarith
    have hlast := mul_pos hF (sq_pos_of_pos hbpos)
    simpa using hlast

private theorem cone_ratio_normalization (A B C D E F : ℝ) {a b : ℝ}
    (hD : 0 < D) (hE : 0 ≤ E) (hF : 0 < F)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : 0 < a + b) :
    coneNumerator A B C a b / coneDenominator D E F a b =
      coneNumerator A B C (1 - b / (a + b)) (b / (a + b)) /
        coneDenominator D E F (1 - b / (a + b)) (b / (a + b)) := by
  have hb' : 0 ≤ b / (a + b) := div_nonneg hb hab.le
  have ha' : 0 ≤ 1 - b / (a + b) := by
    exact sub_nonneg.mpr ((div_le_one hab).2 (le_add_of_nonneg_left ha))
  have hQ := cone_denominator_pos hD hE hF ha hb hab
  have hQ' := cone_denominator_pos hD hE hF ha' hb'
    (show 0 < 1 - b / (a + b) + b / (a + b) by ring_nf; norm_num)
  rw [div_eq_div_iff hQ.ne' hQ'.ne']
  unfold coneNumerator coneDenominator
  field_simp [hab.ne']
  ring

private theorem cone_ratio_improves_endpoint {A B C D E F : ℝ}
    (hD : 0 < D) (hE : 0 ≤ E) (hF : 0 < F)
    (hcross : A / D * E < B) :
    ∃ b : ℝ, 0 < b ∧ A / D <
      coneNumerator A B C 1 b / coneDenominator D E F 1 b := by
  let g := 2 * (B - A / D * E)
  let h := C - A / D * F
  let b := g / (|h| + 1)
  have hg : 0 < g := mul_pos (by norm_num) (sub_pos.mpr hcross)
  have hden : 0 < |h| + 1 := by positivity
  have hb : 0 < b := div_pos hg hden
  have hcancel : b * (|h| + 1) = g := div_mul_cancel₀ _ hden.ne'
  have hnonneg : 0 ≤ b * (h + |h|) := by
    apply mul_nonneg hb.le
    linarith [neg_abs_le h]
  have hlinear : 0 < g + h * b := by nlinarith only [hcancel, hnonneg, hb]
  have hgain : 0 < g * b + h * b^2 := by
    calc
      (0 : ℝ) < b * (g + h * b) := mul_pos hb hlinear
      _ = g * b + h * b^2 := by ring
  refine ⟨b, hb, ?_⟩
  have hQ := cone_denominator_pos hD hE hF (by norm_num : (0 : ℝ) ≤ 1) hb.le
    (add_pos (by norm_num) hb)
  rw [lt_div_iff₀ hQ]
  have hratio : A / D * D = A := div_mul_cancel₀ _ hD.ne'
  dsimp [g, h] at hgain
  unfold coneNumerator coneDenominator
  nlinarith only [hgain, hratio]

private theorem cone_ratio_attains_interior_max {A B C D E F : ℝ}
    (hD : 0 < D) (hE : 0 ≤ E) (hF : 0 < F)
    (hcross : A / D * E < B) (hend : C / F ≤ A / D) :
    ∃ t ∈ Ioo (0 : ℝ) 1,
      A / D < coneNumerator A B C (1 - t) t / coneDenominator D E F (1 - t) t ∧
      ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → 0 < a + b →
        coneNumerator A B C a b / coneDenominator D E F a b ≤
          coneNumerator A B C (1 - t) t / coneDenominator D E F (1 - t) t := by
  let f : ℝ → ℝ := fun t =>
    coneNumerator A B C (1 - t) t / coneDenominator D E F (1 - t) t
  have hQ (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      0 < coneDenominator D E F (1 - t) t :=
    cone_denominator_pos hD hE hF (sub_nonneg.mpr ht.2) ht.1 (by linarith)
  have hcont : ContinuousOn f (Icc (0 : ℝ) 1) := by
    apply ContinuousOn.div
    · unfold coneNumerator
      fun_prop
    · unfold coneDenominator
      fun_prop
    · intro t ht
      exact (hQ t ht).ne'
  obtain ⟨t, ht, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (show (Icc (0 : ℝ) 1).Nonempty from ⟨0, by simp⟩) hcont
  obtain ⟨b, hb, hbetter⟩ := cone_ratio_improves_endpoint hD hE hF hcross
  have hb' : b / (1 + b) ∈ Icc (0 : ℝ) 1 := by
    constructor
    · positivity
    · exact (div_le_one (add_pos (by norm_num) hb)).2 (le_add_of_nonneg_left (by norm_num))
  have hnormalize := cone_ratio_normalization A B C D E F hD hE hF
    (by norm_num : (0 : ℝ) ≤ 1) hb.le (add_pos (by norm_num) hb)
  have hgt : A / D < f t := by
    have hm := hmax hb'
    change f (b / (1 + b)) ≤ f t at hm
    rw [hnormalize] at hbetter
    exact lt_of_lt_of_le hbetter hm
  have ht0 : 0 < t := by
    rcases lt_or_eq_of_le ht.1 with hlt | heq
    · exact hlt
    · subst t
      simp [f, coneNumerator, coneDenominator] at hgt
  have ht1 : t < 1 := by
    rcases lt_or_eq_of_le ht.2 with hlt | heq
    · exact hlt
    · subst t
      simp [f, coneNumerator, coneDenominator] at hgt
      exact False.elim ((not_lt_of_ge hend) hgt)
  refine ⟨t, ⟨ht0, ht1⟩, hgt, ?_⟩
  intro a b ha hb hab
  rw [cone_ratio_normalization A B C D E F hD hE hF ha hb hab]
  apply hmax
  constructor
  · exact div_nonneg hb hab.le
  · exact (div_le_one hab).2 (le_add_of_nonneg_left ha)


private theorem horizon_three_denominator_coefficient_pos :
    0 < fermiDilatedPronicMass 3 - fermiDilatedPronicMass 6 + fermiDilatedPronicMass 12 := by
  have h36 := fermiDilatedPronicMass_three_six_bound
  have h6 := fermiDilatedPronicMass_pos (by norm_num : 0 < 6)
  have h12 := fermiDilatedPronicMass_pos (by norm_num : 0 < 12)
  linarith

private theorem horizon_three_denominator_pos {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : 0 < a + b) :
    0 < fermiHorizonThreeDenominator a b := by
  exact cone_denominator_pos
    (fermiDilatedPronicMass_pos (by norm_num : 0 < 4))
    (fermiDilatedPronicMass_pos (by norm_num : 0 < 12)).le
    horizon_three_denominator_coefficient_pos ha hb hab

private theorem horizon_three_pure_ratio_lower :
    (10 / 3 : ℝ) ≤ fermiDilatedPronicMass 2 / fermiDilatedPronicMass 4 := by
  exact (le_div_iff₀ (fermiDilatedPronicMass_pos (by norm_num : 0 < 4))).2
    fermiDilatedPronicMass_two_four_bounds.1

private theorem horizon_three_cross_gain :
    (fermiDilatedPronicMass 2 / fermiDilatedPronicMass 4) * fermiDilatedPronicMass 12 <
      fermiDilatedPronicMass 6 := by
  have h4 := fermiDilatedPronicMass_pos (by norm_num : 0 < 4)
  have h12 := fermiDilatedPronicMass_pos (by norm_num : 0 < 12)
  have hR : fermiDilatedPronicMass 2 / fermiDilatedPronicMass 4 ≤ (100 / 27 : ℝ) :=
    (div_le_iff₀ h4).2 fermiDilatedPronicMass_two_four_bounds.2
  calc
    _ ≤ (100 / 27 : ℝ) * fermiDilatedPronicMass 12 :=
      mul_le_mul_of_nonneg_right hR h12.le
    _ < (26 / 7 : ℝ) * fermiDilatedPronicMass 12 :=
      mul_lt_mul_of_pos_right (by norm_num) h12
    _ ≤ _ := fermiDilatedPronicMass_six_twelve_bound

private theorem horizon_three_other_endpoint_bound :
    fermiDilatedPronicMass 3 /
        (fermiDilatedPronicMass 3 - fermiDilatedPronicMass 6 + fermiDilatedPronicMass 12) ≤
      fermiDilatedPronicMass 2 / fermiDilatedPronicMass 4 := by
  have hsmall : fermiDilatedPronicMass 3 /
      (fermiDilatedPronicMass 3 - fermiDilatedPronicMass 6 + fermiDilatedPronicMass 12) ≤ 2 := by
    rw [div_le_iff₀ horizon_three_denominator_coefficient_pos]
    have h36 := fermiDilatedPronicMass_three_six_bound
    have h12 := fermiDilatedPronicMass_pos (by norm_num : 0 < 12)
    linarith
  exact le_trans hsmall (by linarith [horizon_three_pure_ratio_lower])

private theorem horizon_three_interior_max :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ a + b = 1 ∧
      1 < fermiHorizonThreeNumerator a b / fermiHorizonThreeDenominator a b ∧
      ∀ u v : ℝ, 0 ≤ u → 0 ≤ v → 0 < u + v →
        fermiHorizonThreeNumerator u v / fermiHorizonThreeDenominator u v ≤
          fermiHorizonThreeNumerator a b / fermiHorizonThreeDenominator a b := by
  obtain ⟨t, ht, hgt, hmax⟩ := cone_ratio_attains_interior_max
    (fermiDilatedPronicMass_pos (by norm_num : 0 < 4))
    (fermiDilatedPronicMass_pos (by norm_num : 0 < 12)).le
    horizon_three_denominator_coefficient_pos horizon_three_cross_gain
    horizon_three_other_endpoint_bound
  refine ⟨1 - t, t, by linarith [ht.2], ht.1, by ring, ?_, ?_⟩
  · have hR := horizon_three_pure_ratio_lower
    change fermiDilatedPronicMass 2 / fermiDilatedPronicMass 4 <
      fermiHorizonThreeNumerator (1 - t) t / fermiHorizonThreeDenominator (1 - t) t at hgt
    linarith
  · exact hmax

private theorem ratio_set_bounded (N : ℕ) (D : Set (ℕ → ℝ)) :
    BddAbove {t : ℝ | ∃ c ∈ D, 0 < fermiSelectedTotalPronicEnergy N c ∧
      t = sieveTotalPronicEnergy N c / fermiSelectedTotalPronicEnergy N c} := by
  let d := Nat.log 2 N + 1
  refine ⟨((d : ℝ) + 4) * ((d : ℝ) + 1), ?_⟩
  rintro t ⟨c, _, hQ, rfl⟩
  exact (div_le_iff₀ hQ).2 (sieveTotalPronicEnergy_le_depth_selected N c)

private theorem signed_ratio_le_constant (N : ℕ) (c : ℕ → ℝ)
    (hQ : 0 < fermiSelectedTotalPronicEnergy N c) :
    sieveTotalPronicEnergy N c / fermiSelectedTotalPronicEnergy N c ≤
      fermiPhysicalInverseConstant N := by
  change _ ≤ sSup {t : ℝ | ∃ b ∈ (Set.univ : Set (ℕ → ℝ)),
    0 < fermiSelectedTotalPronicEnergy N b ∧
      t = sieveTotalPronicEnergy N b / fermiSelectedTotalPronicEnergy N b}
  exact le_csSup (ratio_set_bounded N Set.univ) ⟨c, Set.mem_univ c, hQ, rfl⟩

private theorem horizon_three_cone_constant_eq {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b)
    (hlarge : 1 < fermiHorizonThreeNumerator a b / fermiHorizonThreeDenominator a b)
    (hmax : ∀ u v : ℝ, 0 ≤ u → 0 ≤ v → 0 < u + v →
      fermiHorizonThreeNumerator u v / fermiHorizonThreeDenominator u v ≤
        fermiHorizonThreeNumerator a b / fermiHorizonThreeDenominator a b) :
    fermiNonnegativePhysicalInverseConstant 3 =
      fermiHorizonThreeNumerator a b / fermiHorizonThreeDenominator a b := by
  let D : Set (ℕ → ℝ) := {c | ∀ d, 0 ≤ c d}
  let R : Set ℝ := {t | ∃ c ∈ D, 0 < fermiSelectedTotalPronicEnergy 3 c ∧
    t = sieveTotalPronicEnergy 3 c / fermiSelectedTotalPronicEnergy 3 c}
  have hE := fermiHorizonThreeWeight_physical_energies a b
  have hmem : fermiHorizonThreeNumerator a b / fermiHorizonThreeDenominator a b ∈ R := by
    refine ⟨fermiHorizonThreeWeight a b, fermiHorizonThreeWeight_nonneg ha.le hb.le, ?_, ?_⟩
    · rw [hE.2]
      exact horizon_three_denominator_pos ha.le hb.le (by linarith)
    · rw [hE.1, hE.2]
  change sSup R = _
  apply le_antisymm
  · apply csSup_le ⟨_, hmem⟩
    rintro t ⟨c, hc, hQ, rfl⟩
    by_cases hPC : fermiSelectedTotalPronicEnergy 3 c < sieveTotalPronicEnergy 3 c
    · let w := fermiOddShiftWeight c (c 1)
      have hw : ∀ d, 0 ≤ w d :=
        (fermiOddShiftWeight_nonneg_iff c hc _).2 ⟨by linarith [hc 1, hc 2], le_rfl⟩
      have hw1 : w 1 = 0 := by simp [w, fermiOddShiftWeight, sieveUnitShiftWeight]
      have hQw : 0 < fermiSelectedTotalPronicEnergy 3 w :=
        fermiOddShiftWeight_selected_pos (by norm_num) c hPC (c 1)
      have hEw := fermiHorizonThree_physical_energies w hw1
      have hsum : 0 < w 2 + w 3 := by
        by_contra hn
        have h2 := hw 2
        have h3 := hw 3
        have hz2 : w 2 = 0 := by linarith
        have hz3 : w 3 = 0 := by linarith
        rw [hEw.2] at hQw
        simp [fermiHorizonThreeDenominator, hz2, hz3] at hQw
      calc
        _ ≤ sieveTotalPronicEnergy 3 w / fermiSelectedTotalPronicEnergy 3 w :=
          fermiOddShiftWeight_unit_ratio_ge (by norm_num) c hc hPC
        _ = fermiHorizonThreeNumerator (w 2) (w 3) /
            fermiHorizonThreeDenominator (w 2) (w 3) := by rw [hEw.1, hEw.2]
        _ ≤ _ := hmax (w 2) (w 3) (hw 2) (hw 3) hsum
    · have hle : sieveTotalPronicEnergy 3 c / fermiSelectedTotalPronicEnergy 3 c ≤ 1 :=
        (div_le_one hQ).2 (le_of_not_gt hPC)
      exact le_trans hle hlarge.le
  · exact le_csSup (ratio_set_bounded 3 D) hmem

/-- A positive two-parameter input attains the literal nonnegative physical supremum at horizon three. -/
theorem fermiHorizonThree_positive_extremal_exists :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ a + b = 1 ∧
      0 < fermiSelectedTotalPronicEnergy 3 (fermiHorizonThreeWeight a b) ∧
      fermiNonnegativePhysicalInverseConstant 3 =
        sieveTotalPronicEnergy 3 (fermiHorizonThreeWeight a b) /
          fermiSelectedTotalPronicEnergy 3 (fermiHorizonThreeWeight a b) ∧
      1 < sieveTotalPronicEnergy 3 (fermiHorizonThreeWeight a b) /
        fermiSelectedTotalPronicEnergy 3 (fermiHorizonThreeWeight a b) := by
  obtain ⟨a, b, ha, hb, hab, hlarge, hmax⟩ := horizon_three_interior_max
  have hE := fermiHorizonThreeWeight_physical_energies a b
  refine ⟨a, b, ha, hb, hab, ?_, ?_, ?_⟩
  · rw [hE.2]
    exact horizon_three_denominator_pos ha.le hb.le (by linarith)
  · rw [hE.1, hE.2]
    exact horizon_three_cone_constant_eq ha hb hlarge hmax
  · rwa [hE.1, hE.2]

/-- The signed and nonnegative physical inverse constants differ strictly at horizon three. -/
theorem fermiPhysicalInverseConstant_three_strict_cone_gap :
    fermiNonnegativePhysicalInverseConstant 3 < fermiPhysicalInverseConstant 3 := by
  obtain ⟨a, b, ha, hb, _, hQ, hK, hlarge⟩ := fermiHorizonThree_positive_extremal_exists
  let c := fermiHorizonThreeWeight a b
  have hc : ∀ d, 0 ≤ c d := fermiHorizonThreeWeight_nonneg ha.le hb.le
  have hPQ : fermiSelectedTotalPronicEnergy 3 c < sieveTotalPronicEnergy 3 c := by
    have h := (lt_div_iff₀ hQ).mp hlarge
    linarith
  have hA : 0 < fermiOddPronicMean 3 c := by
    have h := fermiOddPronicMean_gt_unit_of_odd_coefficient (N := 3) (d := 3)
      (by norm_num) c hc (by norm_num) le_rfl (by norm_num)
      (by simpa [c, fermiHorizonThreeWeight] using hb)
    simpa [c, fermiHorizonThreeWeight] using h
  have hcenterQ := fermiOddCenteredWeight_selected_pos (by norm_num : 2 ≤ 3) c hPQ
  have hgain := fermiOddCenteredWeight_strict_improves (by norm_num : 2 ≤ 3) c hPQ hA.ne'
  rw [hK]
  exact lt_of_lt_of_le hgain
    (signed_ratio_le_constant 3 (fermiOddCenteredWeight 3 c) hcenterQ)

end GaloisForLFunctions.TransHorizonIncidenceMechanics
