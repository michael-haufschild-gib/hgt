import GaloisForLFunctions.HTGeometry.FirstAtomOddTailAlgebra

/-! # Quantitative first-atom odd reserves on inverse scales at most one seventh -/
namespace HTGeometry
noncomputable section
set_option maxHeartbeats 2000000

/-- The common denominator remains uniformly positive on the larger inverse-scale interval. -/
theorem firstAtomOddScaleSeven_denominator_lower {u : ℝ} (hu : u ≤ 1/7) :
    9 ≤ firstAtomOddTailDenominator u := by
  have h : 3 ≤ 4-6*u := by linarith
  unfold firstAtomOddTailDenominator
  nlinarith [sq_nonneg (4-6*u-3)]

/-- Exact positive Bernstein expansions bound the order-1 profile on the full interval. -/
theorem firstAtomOddScaleSeven_profile1_bounds {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1/7) :
    0 ≤ firstAtomOddTailProfile1 u ∧ firstAtomOddTailProfile1 u ≤ 9 := by
  have ht : 0 ≤ 1-7*u := by linarith
  have hD : 0 < firstAtomOddTailDenominator u := by
    have h := firstAtomOddScaleSeven_denominator_lower hu1
    linarith
  have hn : 0 ≤ firstAtomOddTailNumerator1 u := by
    have heq : firstAtomOddTailNumerator1 u =
      (128 : ℝ)*(7*u)^(0 : ℕ)*(1-7*u)^(2 : ℕ) +
      (1408/7 : ℝ)*(7*u)^(1 : ℕ)*(1-7*u)^(1 : ℕ) +
      (4064/49 : ℝ)*(7*u)^(2 : ℕ)*(1-7*u)^(0 : ℕ) := by unfold firstAtomOddTailNumerator1; ring
    rw [heq]
    positivity
  have hh : 0 ≤ 9*firstAtomOddTailDenominator u-firstAtomOddTailNumerator1 u := by
    have heq : 9*firstAtomOddTailDenominator u-firstAtomOddTailNumerator1 u =
      (16 : ℝ)*(7*u)^(0 : ℕ)*(1-7*u)^(2 : ℕ) +
      (176/7 : ℝ)*(7*u)^(1 : ℕ)*(1-7*u)^(1 : ℕ) +
      (292/49 : ℝ)*(7*u)^(2 : ℕ)*(1-7*u)^(0 : ℕ) := by unfold firstAtomOddTailDenominator firstAtomOddTailNumerator1; ring
    rw [heq]
    positivity
  refine ⟨div_nonneg hn hD.le, ?_⟩
  unfold firstAtomOddTailProfile1
  apply (div_le_iff₀ hD).mpr
  linarith only [hh]

/-- Exact positive Bernstein expansions bound the order-2 profile on the full interval. -/
theorem firstAtomOddScaleSeven_profile2_bounds {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1/7) :
    0 ≤ firstAtomOddTailProfile2 u ∧ firstAtomOddTailProfile2 u ≤ 210 := by
  have ht : 0 ≤ 1-7*u := by linarith
  have hD : 0 < firstAtomOddTailDenominator u := by
    have h := firstAtomOddScaleSeven_denominator_lower hu1
    linarith
  have hn : 0 ≤ firstAtomOddTailNumerator2 u := by
    have heq : firstAtomOddTailNumerator2 u =
      (3072 : ℝ)*(7*u)^(0 : ℕ)*(1-7*u)^(3 : ℕ) +
      (54784/7 : ℝ)*(7*u)^(1 : ℕ)*(1-7*u)^(2 : ℕ) +
      (333056/49 : ℝ)*(7*u)^(2 : ℕ)*(1-7*u)^(1 : ℕ) +
      (698752/343 : ℝ)*(7*u)^(3 : ℕ)*(1-7*u)^(0 : ℕ) := by unfold firstAtomOddTailNumerator2; ring
    rw [heq]
    positivity
  have hh : 0 ≤ 210*firstAtomOddTailDenominator u-firstAtomOddTailNumerator2 u := by
    have heq : 210*firstAtomOddTailDenominator u-firstAtomOddTailNumerator2 u =
      (288 : ℝ)*(7*u)^(0 : ℕ)*(1-7*u)^(3 : ℕ) +
      (5696/7 : ℝ)*(7*u)^(1 : ℕ)*(1-7*u)^(2 : ℕ) +
      (27304/49 : ℝ)*(7*u)^(2 : ℕ)*(1-7*u)^(1 : ℕ) +
      (12728/343 : ℝ)*(7*u)^(3 : ℕ)*(1-7*u)^(0 : ℕ) := by unfold firstAtomOddTailDenominator firstAtomOddTailNumerator2; ring
    rw [heq]
    positivity
  refine ⟨div_nonneg hn hD.le, ?_⟩
  unfold firstAtomOddTailProfile2
  apply (div_le_iff₀ hD).mpr
  linarith only [hh]

/-- Exact positive Bernstein expansions bound the order-3 profile on the full interval. -/
theorem firstAtomOddScaleSeven_profile3_bounds {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1/7) :
    0 ≤ firstAtomOddTailProfile3 u ∧ firstAtomOddTailProfile3 u ≤ 8500 := by
  have ht : 0 ≤ 1-7*u := by linarith
  have hD : 0 < firstAtomOddTailDenominator u := by
    have h := firstAtomOddScaleSeven_denominator_lower hu1
    linarith
  have hn : 0 ≤ firstAtomOddTailNumerator3 u := by
    have heq : firstAtomOddTailNumerator3 u =
      (122880 : ℝ)*(7*u)^(0 : ℕ)*(1-7*u)^(4 : ℕ) +
      (430080 : ℝ)*(7*u)^(1 : ℕ)*(1-7*u)^(3 : ℕ) +
      (28110848/49 : ℝ)*(7*u)^(2 : ℕ)*(1-7*u)^(2 : ℕ) +
      (119262208/343 : ℝ)*(7*u)^(3 : ℕ)*(1-7*u)^(1 : ℕ) +
      (194998784/2401 : ℝ)*(7*u)^(4 : ℕ)*(1-7*u)^(0 : ℕ) := by unfold firstAtomOddTailNumerator3; ring
    rw [heq]
    positivity
  have hh : 0 ≤ 8500*firstAtomOddTailDenominator u-firstAtomOddTailNumerator3 u := by
    have heq : 8500*firstAtomOddTailDenominator u-firstAtomOddTailNumerator3 u =
      (13120 : ℝ)*(7*u)^(0 : ℕ)*(1-7*u)^(4 : ℕ) +
      (389440/7 : ℝ)*(7*u)^(1 : ℕ)*(1-7*u)^(3 : ℕ) +
      (3611152/49 : ℝ)*(7*u)^(2 : ℕ)*(1-7*u)^(2 : ℕ) +
      (11637792/343 : ℝ)*(7*u)^(3 : ℕ)*(1-7*u)^(1 : ℕ) +
      (6587216/2401 : ℝ)*(7*u)^(4 : ℕ)*(1-7*u)^(0 : ℕ) := by unfold firstAtomOddTailDenominator firstAtomOddTailNumerator3; ring
    rw [heq]
    positivity
  refine ⟨div_nonneg hn hD.le, ?_⟩
  unfold firstAtomOddTailProfile3
  apply (div_le_iff₀ hD).mpr
  linarith only [hh]

/-- Exact positive Bernstein expansions bound the order-4 profile on the full interval. -/
theorem firstAtomOddScaleSeven_profile4_bounds {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1/7) :
    0 ≤ firstAtomOddTailProfile4 u ∧ firstAtomOddTailProfile4 u ≤ 500000 := by
  have ht : 0 ≤ 1-7*u := by linarith
  have hD : 0 < firstAtomOddTailDenominator u := by
    have h := firstAtomOddScaleSeven_denominator_lower hu1
    linarith
  have hn : 0 ≤ firstAtomOddTailNumerator4 u := by
    have heq : firstAtomOddTailNumerator4 u =
      (6881280 : ℝ)*(7*u)^(0 : ℕ)*(1-7*u)^(5 : ℕ) +
      (30474240 : ℝ)*(7*u)^(1 : ℕ)*(1-7*u)^(4 : ℕ) +
      (382795776/7 : ℝ)*(7*u)^(2 : ℕ)*(1-7*u)^(3 : ℕ) +
      (17108230144/343 : ℝ)*(7*u)^(3 : ℕ)*(1-7*u)^(2 : ℕ) +
      (55688646656/2401 : ℝ)*(7*u)^(4 : ℕ)*(1-7*u)^(1 : ℕ) +
      (74082998272/16807 : ℝ)*(7*u)^(5 : ℕ)*(1-7*u)^(0 : ℕ) := by unfold firstAtomOddTailNumerator4; ring
    rw [heq]
    positivity
  have hh : 0 ≤ 500000*firstAtomOddTailDenominator u-firstAtomOddTailNumerator4 u := by
    have heq : 500000*firstAtomOddTailDenominator u-firstAtomOddTailNumerator4 u =
      (1118720 : ℝ)*(7*u)^(0 : ℕ)*(1-7*u)^(5 : ℕ) +
      (42680320/7 : ℝ)*(7*u)^(1 : ℕ)*(1-7*u)^(4 : ℕ) +
      (586429568/49 : ℝ)*(7*u)^(2 : ℕ)*(1-7*u)^(3 : ℕ) +
      (3653769856/343 : ℝ)*(7*u)^(3 : ℕ)*(1-7*u)^(2 : ℕ) +
      (10069353344/2401 : ℝ)*(7*u)^(4 : ℕ)*(1-7*u)^(1 : ℕ) +
      (8923001728/16807 : ℝ)*(7*u)^(5 : ℕ)*(1-7*u)^(0 : ℕ) := by unfold firstAtomOddTailDenominator firstAtomOddTailNumerator4; ring
    rw [heq]
    positivity
  refine ⟨div_nonneg hn hD.le, ?_⟩
  unfold firstAtomOddTailProfile4
  apply (div_le_iff₀ hD).mpr
  linarith only [hh]

/-- Exact positive Bernstein expansions bound the order-5 profile on the full interval. -/
theorem firstAtomOddScaleSeven_profile5_bounds {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1/7) :
    0 ≤ firstAtomOddTailProfile5 u ∧ firstAtomOddTailProfile5 u ≤ 40000000 := by
  have ht : 0 ≤ 1-7*u := by linarith
  have hD : 0 < firstAtomOddTailDenominator u := by
    have h := firstAtomOddScaleSeven_denominator_lower hu1
    linarith
  have hn : 0 ≤ firstAtomOddTailNumerator5 u := by
    have heq : firstAtomOddTailNumerator5 u =
      (495452160 : ℝ)*(7*u)^(0 : ℕ)*(1-7*u)^(6 : ℕ) +
      (2642411520 : ℝ)*(7*u)^(1 : ℕ)*(1-7*u)^(5 : ℕ) +
      (41547202560/7 : ℝ)*(7*u)^(2 : ℕ)*(1-7*u)^(4 : ℕ) +
      (2470885785600/343 : ℝ)*(7*u)^(3 : ℕ)*(1-7*u)^(3 : ℕ) +
      (11987050692608/2401 : ℝ)*(7*u)^(4 : ℕ)*(1-7*u)^(2 : ℕ) +
      (31525079400448/16807 : ℝ)*(7*u)^(5 : ℕ)*(1-7*u)^(1 : ℕ) +
      (35127684767744/117649 : ℝ)*(7*u)^(6 : ℕ)*(1-7*u)^(0 : ℕ) := by unfold firstAtomOddTailNumerator5; ring
    rw [heq]
    positivity
  have hh : 0 ≤ 40000000*firstAtomOddTailDenominator u-firstAtomOddTailNumerator5 u := by
    have heq : 40000000*firstAtomOddTailDenominator u-firstAtomOddTailNumerator5 u =
      (144547840 : ℝ)*(7*u)^(0 : ℕ)*(1-7*u)^(6 : ℕ) +
      (6463119360/7 : ℝ)*(7*u)^(1 : ℕ)*(1-7*u)^(5 : ℕ) +
      (113809582080/49 : ℝ)*(7*u)^(2 : ℕ)*(1-7*u)^(4 : ℕ) +
      (1019034214400/343 : ℝ)*(7*u)^(3 : ℕ)*(1-7*u)^(3 : ℕ) +
      (4900309307392/2401 : ℝ)*(7*u)^(4 : ℕ)*(1-7*u)^(2 : ℕ) +
      (11939880599552/16807 : ℝ)*(7*u)^(5 : ℕ)*(1-7*u)^(1 : ℕ) +
      (11355675232256/117649 : ℝ)*(7*u)^(6 : ℕ)*(1-7*u)^(0 : ℕ) := by unfold firstAtomOddTailDenominator firstAtomOddTailNumerator5; ring
    rw [heq]
    positivity
  refine ⟨div_nonneg hn hD.le, ?_⟩
  unfold firstAtomOddTailProfile5
  apply (div_le_iff₀ hD).mpr
  linarith only [hh]

/-- The exact first-atom odd determinant exceeds eighty billion at every scale at least seven. -/
theorem firstAtomOddScaleSeven_det_lower {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1/7) :
    80000000000 ≤ firstAtomOddTailDet u := by
  have ht : 0 ≤ 1-7*u := by linarith
  have hD : 0 < firstAtomOddTailDenominator u := by
    have h := firstAtomOddScaleSeven_denominator_lower hu1
    linarith
  have heq : firstAtomOddTailDetNumerator u-80000000000*firstAtomOddTailDenominator u^(3 : ℕ) =
      (68144185999360 : ℝ)*(7*u)^(0 : ℕ)*(1-7*u)^(9 : ℕ) +
      (2393357439467520/7 : ℝ)*(7*u)^(1 : ℕ)*(1-7*u)^(8 : ℕ) +
      (34156278259384320/49 : ℝ)*(7*u)^(2 : ℕ)*(1-7*u)^(7 : ℕ) +
      (247435529614786560/343 : ℝ)*(7*u)^(3 : ℕ)*(1-7*u)^(6 : ℕ) +
      (925770342287278080/2401 : ℝ)*(7*u)^(4 : ℕ)*(1-7*u)^(5 : ℕ) +
      (2008897805636075520/16807 : ℝ)*(7*u)^(5 : ℕ)*(1-7*u)^(4 : ℕ) +
      (9659078704708976640/117649 : ℝ)*(7*u)^(6 : ℕ)*(1-7*u)^(3 : ℕ) +
      (67172105267002736640/823543 : ℝ)*(7*u)^(7 : ℕ)*(1-7*u)^(2 : ℕ) +
      (31222742243027189760/823543 : ℝ)*(7*u)^(8 : ℕ)*(1-7*u)^(1 : ℕ) +
      (36972855565869383680/5764801 : ℝ)*(7*u)^(9 : ℕ)*(1-7*u)^(0 : ℕ) := by unfold firstAtomOddTailDetNumerator firstAtomOddTailDenominator; ring
  have h : 0 ≤ firstAtomOddTailDetNumerator u-80000000000*firstAtomOddTailDenominator u^(3 : ℕ) := by
    rw [heq]
    positivity
  rw [firstAtomOddTailDet_eq_ratio u hD.ne']
  apply (le_div_iff₀ (pow_pos hD 3)).mpr
  linarith only [h]

/-- The exact first-atom leading odd minor has a sharp enough uniform upper reserve. -/
theorem firstAtomOddScaleSeven_head_upper {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1/7) :
    firstAtomOddTailProfile1 u*firstAtomOddTailProfile3 u-firstAtomOddTailProfile2 u^(2 : ℕ) ≤ 27000 := by
  have ht : 0 ≤ 1-7*u := by linarith
  have hD : 0 < firstAtomOddTailDenominator u := by
    have h := firstAtomOddScaleSeven_denominator_lower hu1
    linarith
  have heq : 27000*firstAtomOddTailDenominator u^(2 : ℕ)-
      (firstAtomOddTailNumerator1 u*firstAtomOddTailNumerator3 u-firstAtomOddTailNumerator2 u^(2 : ℕ)) =
      (620544 : ℝ)*(7*u)^(0 : ℕ)*(1-7*u)^(6 : ℕ) +
      (27058176/7 : ℝ)*(7*u)^(1 : ℕ)*(1-7*u)^(5 : ℕ) +
      (433253376/49 : ℝ)*(7*u)^(2 : ℕ)*(1-7*u)^(4 : ℕ) +
      (3319323648/343 : ℝ)*(7*u)^(3 : ℕ)*(1-7*u)^(3 : ℕ) +
      (1794218112/343 : ℝ)*(7*u)^(4 : ℕ)*(1-7*u)^(2 : ℕ) +
      (2878974720/2401 : ℝ)*(7*u)^(5 : ℕ)*(1-7*u)^(1 : ℕ) +
      (116326272/2401 : ℝ)*(7*u)^(6 : ℕ)*(1-7*u)^(0 : ℕ) := by
        unfold firstAtomOddTailDenominator firstAtomOddTailNumerator1
          firstAtomOddTailNumerator2 firstAtomOddTailNumerator3
        ring
  have h : 0 ≤ 27000*firstAtomOddTailDenominator u^(2 : ℕ)-
      (firstAtomOddTailNumerator1 u*firstAtomOddTailNumerator3 u-firstAtomOddTailNumerator2 u^(2 : ℕ)) := by
    rw [heq]
    positivity
  have he : firstAtomOddTailProfile1 u*firstAtomOddTailProfile3 u-firstAtomOddTailProfile2 u^(2 : ℕ) =
      (firstAtomOddTailNumerator1 u*firstAtomOddTailNumerator3 u-firstAtomOddTailNumerator2 u^(2 : ℕ))/
        firstAtomOddTailDenominator u^(2 : ℕ) := by
    unfold firstAtomOddTailProfile1 firstAtomOddTailProfile2 firstAtomOddTailProfile3
    field_simp
  rw [he]
  apply (div_le_iff₀ (pow_pos hD 2)).mpr
  linarith only [h]

end
end HTGeometry
