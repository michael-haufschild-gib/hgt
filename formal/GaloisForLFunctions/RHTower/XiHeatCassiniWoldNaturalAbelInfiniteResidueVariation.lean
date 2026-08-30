import GaloisForLFunctions.RHTower.XiHeatCassiniWoldNaturalAbelFullCriticalDivisor

/-!
# Infinite residue variation of the natural Wold Abel germ

Every global right-radial residue profile of an admissible natural Wold Abel continuation fails to
decay along the cofinite filter.  In particular, no such profile is summable.  This rules out the
entire infinite-but-finite-variation polar-repair branch left open by the finite-support no-go.
-/

open Complex Filter Set Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-- An admissible continuation has a summable radial residue profile when one summable function
records its right-radial residue at every positive critical-wall height. -/
def WoldNatAbelSummableRadialResidueProfile (F : ℂ → ℂ) : Prop :=
  ∃ r : ℝ → ℂ, Summable r ∧
    ∀ tau : ℝ, 0 < tau →
      Tendsto (fun x : ℝ =>
        (x : ℂ) * F ((linePt tau - 1) + (x : ℂ)))
        (𝓝[>] (0 : ℝ)) (𝓝 (r tau))

/-- **Cofinite residue non-decay.**  No global radial residue profile of an admissible natural Wold
Abel continuation tends to zero along the cofinite filter.  Hardy zeros occur beyond every finite
exceptional set, while full critical-divisor inheritance forces a negative-integer residue there. -/
theorem woldNatAbelRadialResidueProfile_not_tendsto_cofinite_zero
    {F : ℂ → ℂ}
    (hF : AnalyticOnNhd ℂ F (xiHeatCassiniWoldResidualODESector 1))
    (hEq : Set.EqOn F (fun s : ℂ => abelDirichlet woldNatDifferenceCoeff s)
      {s : ℂ | s ∈ xiHeatCassiniWoldResidualODESector 1 ∧ 0 < s.re})
    {r : ℝ → ℂ}
    (hres : ∀ tau : ℝ, 0 < tau →
      Tendsto (fun x : ℝ =>
        (x : ℂ) * F ((linePt tau - 1) + (x : ℂ)))
        (𝓝[>] (0 : ℝ)) (𝓝 (r tau))) :
    ¬ Tendsto r Filter.cofinite (𝓝 0) := by
  intro hcof
  have hsmallEventually : ∀ᶠ tau in Filter.cofinite, ‖r tau‖ < 1 := by
    have hball : ∀ᶠ tau in Filter.cofinite, r tau ∈ Metric.ball (0 : ℂ) 1 :=
      hcof.eventually (Metric.ball_mem_nhds (0 : ℂ) one_pos)
    simpa only [mem_ball_zero_iff] using hball
  have hbad : {tau : ℝ | ¬ ‖r tau‖ < 1}.Finite :=
    Filter.eventually_cofinite.mp hsmallEventually
  let B : Finset ℝ := hbad.toFinset
  obtain ⟨T0, hT0, hHardy⟩ := exists_riemannZeta_line_zero_dyadic
  let T : ℝ := T0 + (∑ u ∈ B, |u|) + 1
  have hsum0 : 0 ≤ ∑ u ∈ B, |u| :=
    Finset.sum_nonneg fun u _ => abs_nonneg u
  have hT0T : T0 ≤ T := by
    dsimp only [T]
    linarith
  obtain ⟨tau, htauIcc, hzeta⟩ := hHardy T hT0T
  have hTpos : 0 < T := lt_of_lt_of_le hT0 hT0T
  have htau : 0 < tau := lt_of_lt_of_le hTpos htauIcc.1
  have htauNot : tau ∉ B := by
    intro htauB
    have habs : |tau| ≤ ∑ u ∈ B, |u| :=
      Finset.single_le_sum (fun u _ => abs_nonneg u) htauB
    have htauLe : tau ≤ ∑ u ∈ B, |u| :=
      (le_abs_self tau).trans habs
    dsimp only [T] at htauIcc
    have hTtau : T0 + (∑ u ∈ B, |u|) + 1 ≤ tau := htauIcc.1
    linarith
  have htauSmall : ‖r tau‖ < 1 := by
    by_contra hnot
    have htauB : tau ∈ B := by
      simp only [B, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
      exact hnot
    exact htauNot htauB
  have hrhoRe : (linePt tau).re = 1 / 2 := by simp [linePt]
  have hrhoIm : 0 < (linePt tau).im := by simpa [linePt] using htau
  obtain ⟨m, hm, hmres⟩ :=
    woldNatAbelContinuation_forced_residue_at_criticalLine_zero
      hrhoRe hrhoIm hzeta hF hEq
  have hreseq : r tau = -(m : ℂ) :=
    tendsto_nhds_unique (hres tau htau) hmres
  have hnorm : ‖r tau‖ = (m : ℝ) := by
    rw [hreseq, norm_neg, Complex.norm_natCast]
  rw [hnorm] at htauSmall
  have hmreal : (1 : ℝ) ≤ m := by exact_mod_cast hm
  exact (not_lt_of_ge hmreal) htauSmall

/-- **Infinite-variation T2 no-go.**  No admissible continuation of the literal natural Wold Abel
germ has a summable radial residue profile. -/
theorem not_woldNatAbelSummableRadialResidueProfile
    {F : ℂ → ℂ}
    (hF : AnalyticOnNhd ℂ F (xiHeatCassiniWoldResidualODESector 1))
    (hEq : Set.EqOn F (fun s : ℂ => abelDirichlet woldNatDifferenceCoeff s)
      {s : ℂ | s ∈ xiHeatCassiniWoldResidualODESector 1 ∧ 0 < s.re}) :
    ¬ WoldNatAbelSummableRadialResidueProfile F := by
  rintro ⟨r, hrSum, hrRes⟩
  exact (woldNatAbelRadialResidueProfile_not_tendsto_cofinite_zero hF hEq hrRes)
    hrSum.tendsto_cofinite_zero

end

end RHTower
