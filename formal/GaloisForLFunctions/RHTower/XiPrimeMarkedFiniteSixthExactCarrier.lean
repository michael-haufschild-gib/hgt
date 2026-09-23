import GaloisForLFunctions.RHTower.FiniteReverseResidualSixthIVT
import GaloisForLFunctions.RHTower.XiPrimeMarkedFiniteSixthLowerBracket
import GaloisForLFunctions.RHTower.XiPrimeMarkedFiniteSixthHeadBudget

/-!
# Exact finite sixth-moment carrier for the completed prime--archimedean source

The source's reverse lower head and sufficiently large upper two-level head
admit one common slot count. A continuous reverse residual selector connects
them while preserving the first two moments and nonnegative atoms. Their
proved opposite cubic brackets give an exact third power sum by IVT. This
finite result does not match the full source moment sequence or locate Xi
zeros.
-/

namespace RHTower
noncomputable section

/-- Unconditional positive finite head matching the actual completed source
quadratic, quartic, and sixth traces exactly. -/
theorem exists_routeKFiniteSixthMatchedHead :
    ∃ N : ℕ, 10 ≤ N ∧ ∃ x : ℝ,
      0 ≤ x ∧
      (∀ i : Fin (N-1), 0 ≤ reverseResidualSelectorAux
        (routeKQuarticHalfMass-x) (routeKQuarticHalfEnergy-x^2)
        (N-1) (N-3) i) ∧
      x + (∑ i : Fin (N-1), reverseResidualSelectorAux
        (routeKQuarticHalfMass-x) (routeKQuarticHalfEnergy-x^2)
        (N-1) (N-3) i) = routeKQuarticHalfMass ∧
      x^2 + (∑ i : Fin (N-1),
        (reverseResidualSelectorAux
          (routeKQuarticHalfMass-x) (routeKQuarticHalfEnergy-x^2)
          (N-1) (N-3) i)^2) = routeKQuarticHalfEnergy ∧
      x^3 + (∑ i : Fin (N-1),
        (reverseResidualSelectorAux
          (routeKQuarticHalfMass-x) (routeKQuarticHalfEnergy-x^2)
          (N-1) (N-3) i)^3) = normalizedPrimeArchMoment 2 / 2 := by
  let E : ℝ := routeKQuarticHalfMass
  let F : ℝ := routeKQuarticHalfEnergy
  let G : ℝ := normalizedPrimeArchMoment 2 / 2
  obtain ⟨n, hn, a, b, hb, hba, hfirst, hsecond, hcubic, _⟩ :=
    exists_routeKReverseTwoLevelHead_below_sixth
  obtain ⟨N, hNn, hNthree, hlowN, hupperCubic⟩ :=
    exists_routeKFiniteHead_sixth_surplus_above n
  have ha : 0 < a := lt_of_le_of_lt hb hba
  have hNten : 10 ≤ N := le_trans hn hNn
  have hNtwo : 2 ≤ N := by omega
  have hEpos : 0 < E := routeKQuarticHalfMass_pos
  have hFpos : 0 < F := routeKQuarticHalfEnergy_pos
  have h9 : 9 * F < E^2 := routeKQuarticHalfMass_sq_gt_nine_mul_halfEnergy
  have hFlt : F < E^2 := by nlinarith
  let L : ℝ := twoLevelLarge E F N
  let s : ℝ := twoLevelSmall E F N
  have hs : 0 < s := twoLevelSmall_pos hEpos hNtwo hlowN hFlt
  have hL : 0 < L := twoLevelLarge_pos hEpos hNtwo
  have hUfirst : L + ((N:ℝ)-1)*s = E := twoLevel_firstMoment hNtwo
  have hUsecond : L^2 + ((N:ℝ)-1)*s^2 = F :=
    twoLevel_secondMoment hNtwo hlowN
  have hLthird : 3*L < E :=
    twoLevelLarge_lt_third_mass_of_nine_energy_lt_mass_sq hEpos hNtwo hlowN h9
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
    exact hcubic
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
  · linarith [hresMass]
  · nlinarith [hresEnergy]
  · change oneHeadReverseCubic E F N x = G
    exact hcubicMatch

end
end RHTower
