import GaloisForLFunctions.RHTower.XiPrimeMarkedFiniteSixthExactCarrier

/-!
# Strict three-moment cone for the finite K-RVM head

The completed source lies strictly inside the quantitative three-moment
admission cone. In that cone, a nonnegative finite head matches the first
three power sums exactly. This permits perturbing the source moments by a
sufficiently small cofinite reserve; the construction and control of that
reserve remain separate tasks.
-/

namespace RHTower
noncomputable section

/-- The source Stein margin is strictly stronger than the reverse-head
rounding defect. -/
theorem routeK_sourceStrongHankel_247_243_strict :
    247 * routeKQuarticHalfEnergy ^ (2 : ℕ) <
      243 * routeKQuarticHalfMass * (normalizedPrimeArchMoment 2 / 2) := by
  have hM1 := normalizedPrimeArchMoment_one_lt_seventeen_over_twoHundredThousand
  have hM1pos := normalizedPrimeArchMoment_one_pos
  have hM1sq : normalizedPrimeArchMoment 1 ^ (2 : ℕ) <
      (17 / 200000 : ℝ) ^ (2 : ℕ) := by nlinarith
  have hmargin := normalizedPrimeArch_firstHankelMargin_ge_stein
  rw [routeKQuarticHalfEnergy, routeKQuarticHalfMass,
    routeKSourceZerothMoment_eq_normalizedPrimeArchMoment,
    routeKSourceFirstMoment_eq_normalizedPrimeArchMoment]
  nlinarith

/-- A strict quantitative Hankel margin places the target cubic moment
strictly above the reverse endpoint. -/
theorem reverseResidual_lowerBracket_strict
    {E F G a b k : ℝ} (hk : 9 ≤ k) (hE : 0 < E)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hba : b ≤ a)
    (hfirst : k * a + b = E)
    (hsecond : k * a ^ (2 : ℕ) + b ^ (2 : ℕ) = F)
    (hstrong : 247 * F ^ (2 : ℕ) < 243 * E * G) :
    k * a ^ (3 : ℕ) + b ^ (3 : ℕ) < G := by
  let D := k * a * b * (a - b) ^ (2 : ℕ)
  have hk0 : 0 ≤ k := by linarith
  have hD0 : 0 ≤ D := by dsimp [D]; positivity
  have hbound : 27 * k * D ≤ 4 * F ^ (2 : ℕ) := by
    simpa only [D] using
      reverseResidual_hankelGap_le_four_over_twentySeven hk0 ha hba hsecond.symm
  have hcount : 9 * (27 * D) ≤ k * (27 * D) :=
    mul_le_mul_of_nonneg_right hk (by positivity)
  have hDsharp : 243 * D ≤ 4 * F ^ (2 : ℕ) := by
    nlinarith [hbound, hcount]
  have hidentity :
      E * (k * a ^ (3 : ℕ) + b ^ (3 : ℕ)) - F ^ (2 : ℕ) = D := by
    rw [← hfirst, ← hsecond]
    dsimp [D]
    ring
  by_contra hnot
  have hge : G ≤ k * a ^ (3 : ℕ) + b ^ (3 : ℕ) := le_of_not_gt hnot
  have hmul := mul_le_mul_of_nonneg_left hge hE.le
  nlinarith [hDsharp, hidentity]

/-- The source's reverse two-level head has a strict sixth-trace deficit. -/
theorem exists_routeKReverseTwoLevelHead_strictly_below_sixth :
    ∃ N : ℕ, 10 ≤ N ∧ ∃ a b : ℝ, 0 ≤ b ∧ b < a ∧
      ((N : ℝ) - 1) * a + b = routeKQuarticHalfMass ∧
      ((N : ℝ) - 1) * a ^ (2 : ℕ) + b ^ (2 : ℕ) = routeKQuarticHalfEnergy ∧
      ((N : ℝ) - 1) * a ^ (3 : ℕ) + b ^ (3 : ℕ) <
        normalizedPrimeArchMoment 2 / 2 ∧
      ThreeLevelSpectralFeasible routeKQuarticHalfMass
        routeKQuarticHalfEnergy a N := by
  obtain ⟨N, hN, a, b, hb, hba, hfirst, hsecond, hfeasible⟩ :=
    exists_routeKReverseTwoLevelHead
  have hNr : (10 : ℝ) ≤ N := by exact_mod_cast hN
  have hk : (9 : ℝ) ≤ (N : ℝ) - 1 := by linarith
  have ha : 0 ≤ a := le_trans hb hba.le
  exact ⟨N, hN, a, b, hb, hba, hfirst, hsecond,
    reverseResidual_lowerBracket_strict hk routeKQuarticHalfMass_pos
      ha hb hba.le hfirst hsecond routeK_sourceStrongHankel_247_243_strict,
    hfeasible⟩

/-- Every triple in this explicit strict cone admits a finite nonnegative
unit-multiplicity carrier matching all three moments. The count may depend
on the triple. -/
theorem exists_finiteThreeMomentHead_of_strictCone
    {E F G : ℝ} (hE : 0 < E) (hF : 0 < F)
    (h9 : 9 * F < E ^ (2 : ℕ))
    (hstrong : 247 * F ^ (2 : ℕ) < 243 * E * G)
    (hceil : G ^ (2 : ℕ) < F ^ (3 : ℕ)) :
    ∃ N : ℕ, 10 ≤ N ∧ ∃ x : ℝ,
      0 ≤ x ∧
      (∀ i : Fin (N-1), 0 ≤ reverseResidualSelectorAux
        (E-x) (F-x^2) (N-1) (N-3) i) ∧
      x + (∑ i : Fin (N-1), reverseResidualSelectorAux
        (E-x) (F-x^2) (N-1) (N-3) i) = E ∧
      x^2 + (∑ i : Fin (N-1),
        (reverseResidualSelectorAux (E-x) (F-x^2)
          (N-1) (N-3) i)^2) = F ∧
      x^3 + (∑ i : Fin (N-1),
        (reverseResidualSelectorAux (E-x) (F-x^2)
          (N-1) (N-3) i)^3) = G := by
  have hFlt : F < E ^ (2 : ℕ) := by nlinarith [h9]
  have hGpos : 0 < G := by nlinarith [hstrong, sq_pos_of_pos hF]
  obtain ⟨n, hnthree, a, b, hb, hba, hfirst, hsecond, _⟩ :=
    exists_reverseTwoLevelEndpoint_at_effectiveRank hE hF (by nlinarith [h9])
  have hvar := reverseTwoLevel_variance_identity hfirst hsecond
  have hn : 10 ≤ n := by
    by_contra hnot
    have hnine : n ≤ 9 := by omega
    have hnr : (n : ℝ) ≤ 9 := by exact_mod_cast hnine
    have hnm1 : 0 ≤ (n : ℝ) - 1 := by
      have : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
      linarith
    have hvariance : 0 ≤ (n : ℝ) * F - E ^ (2 : ℕ) := by
      rw [hvar]
      exact mul_nonneg hnm1 (sq_nonneg (a-b))
    have hupper := mul_le_mul_of_nonneg_right hnr hF.le
    linarith
  have hnr : (10 : ℝ) ≤ n := by exact_mod_cast hn
  have hk : (9 : ℝ) ≤ (n : ℝ) - 1 := by linarith
  have ha : 0 < a := lt_of_le_of_lt hb hba
  have hcubic : ((n : ℝ)-1)*a^3+b^3 < G :=
    reverseResidual_lowerBracket_strict hk hE ha.le hb hba.le
      hfirst hsecond hstrong
  obtain ⟨N, hNn, hNthree, hlowN, hupperCubic⟩ :=
    exists_twoLevelThirdMoment_gt_above hE hF hFlt.le hGpos.le hceil n
  have hNten : 10 ≤ N := le_trans hn hNn
  have hNtwo : 2 ≤ N := by omega
  let L : ℝ := twoLevelLarge E F N
  let s : ℝ := twoLevelSmall E F N
  have hs : 0 < s := twoLevelSmall_pos hE hNtwo hlowN hFlt
  have hL : 0 < L := twoLevelLarge_pos hE hNtwo
  have hUfirst : L + ((N:ℝ)-1)*s = E := twoLevel_firstMoment hNtwo
  have hUsecond : L^2 + ((N:ℝ)-1)*s^2 = F :=
    twoLevel_secondMoment hNtwo hlowN
  have hLthird : 3*L < E :=
    twoLevelLarge_lt_third_mass_of_nine_energy_lt_mass_sq hE hNtwo hlowN h9
  have hLowAdmit : OneHeadResidualAdmissible E F N a :=
    reverse_head_delete_large_admissible hn hNn ha hb hba.le hfirst hsecond
  have hUpAdmit : OneHeadResidualAdmissible E F N L :=
    uniform_tail_delete_large_admissible hNten hL.le hs hUfirst hUsecond
  have horder : a ≤ L :=
    oneHeadResidualBudget_le_twoLevelLarge hNtwo hlowN hLowAdmit.2.2.2.1
  have hLhalf : 2*L ≤ E := by linarith
  have hAdmitOn (x : ℝ) (hx : x ∈ Set.Icc a L) :
      OneHeadResidualAdmissible E F N x :=
    oneHeadResidualAdmissible_on_Icc horder hLhalf hLowAdmit hUpAdmit hx
  have hposOn (x : ℝ) (hx : x ∈ Set.Icc a L) :
      0 < E-x ∧ 0 < F-x^2 := by
    have h := hAdmitOn x hx
    exact ⟨h.2.1,h.2.2.1⟩
  have hNreal : (10:ℝ) ≤ N := by exact_mod_cast hNten
  have hUpperRank2 : 2*(F-L^2) ≤ (E-L)^2 := by
    have hA : E-L=((N:ℝ)-1)*s := by linarith [hUfirst]
    have hB : F-L^2=((N:ℝ)-1)*s^2 := by linarith [hUsecond]
    rw [hA,hB]
    have hq : 0 ≤ ((N:ℝ)-1)*((N:ℝ)-3) :=
      mul_nonneg (by linarith) (by linarith)
    have hprod := mul_nonneg hq (sq_nonneg s)
    nlinarith
  have hRankOn (x : ℝ) (hx : x ∈ Set.Icc a L) :
      2*(F-x^2) ≤ (E-x)^2 :=
    oneHeadResidualRankTwo_on_Icc hx.2 (by linarith [hLthird]) hUpperRank2
  have hLowerBracket : oneHeadReverseCubic E F N a ≤ G := by
    change a^3 + (∑ i : Fin (N-1),
      (reverseResidualSelectorAux (E-a) (F-a^2) (N-1) (N-3) i)^3) ≤ G
    rw [reverse_head_delete_large_cubic hn hNn ha hb hba.le hfirst hsecond]
    exact hcubic.le
  have hUpperBracket : G ≤ oneHeadReverseCubic E F N L := by
    change G ≤ L^3 + (∑ i : Fin (N-1),
      (reverseResidualSelectorAux (E-L) (F-L^2) (N-1) (N-3) i)^3)
    rw [uniform_tail_delete_large_cubic hNten hs hUfirst hUsecond]
    exact hupperCubic.le
  obtain ⟨x,hx,hcubicMatch⟩ := exists_oneHeadReverseCubic_match
    horder hposOn hLowerBracket hUpperBracket
  obtain ⟨hx0,hApos,hBpos,hbudget,_⟩ := hAdmitOn x hx
  have hrank2 : (2:ℝ) ≤ (E-x)^2/(F-x^2) :=
    (le_div_iff₀ hBpos).mpr (hRankOn x hx)
  have hNcast : ((((N-3)+2:ℕ):ℝ))=(N:ℝ)-1 := by
    have hnat : (N-3)+2=N-1 := by omega
    rw [hnat, Nat.cast_sub (by omega : 1 ≤ N)]
    norm_num
  have hrankMax : (E-x)^2/(F-x^2) ≤ (((N-3)+2:ℕ):ℝ) := by
    rw [hNcast]
    apply (div_le_iff₀ hBpos).mpr
    unfold oneHeadResidualBudget at hbudget
    linarith
  obtain ⟨hpt,hresMass,hresEnergy⟩ := reverseResidualSelectorAux_branch_moments
    hApos hBpos hrank2 hrankMax (show (N-3)+2 ≤ N-1 by omega)
  refine ⟨N,hNten,x,hx0,hpt,?_,?_,?_⟩
  · linarith only [hresMass]
  · linarith only [hresEnergy]
  · change oneHeadReverseCubic E F N x = G
    exact hcubicMatch

end
end RHTower
