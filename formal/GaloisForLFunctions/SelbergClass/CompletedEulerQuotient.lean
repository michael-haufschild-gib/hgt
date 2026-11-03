import GaloisForLFunctions.SelbergClass.SubcriticalEulerRigidity

/-!
# The entire completed Euler quotient

A subcritical Euler-log discrepancy identifies the quotient of two full
Selberg functions without dividing by their common zeros. Multiplying by
their Gamma quotient and using the actual functional equations extends
this quotient to a nowhere-vanishing entire function. No equality of the
Gamma presentations is required.
-/

noncomputable section
open Complex Filter Set Topology

namespace GaloisForLFunctions.SelbergClass

/-- The completed quotient in the right half-plane. -/
def rightCompletedEulerQuotient (F G : RHTower.SelbergClass) (s : ℂ) : ℂ :=
  F.gammaData.gammaFactor s / G.gammaData.gammaFactor s * eulerQuotient F G s

theorem rightCompletedEulerQuotient_analyticOnNhd (F G : RHTower.SelbergClass) {σ : ℝ}
    (hσ0 : 0 ≤ σ)
    (hb : LSeriesSummable (fun n => F.eulerLogCoeff n - G.eulerLogCoeff n) σ) :
    AnalyticOnNhd ℂ (rightCompletedEulerQuotient F G) {s : ℂ | σ < s.re} := by
  intro s hs
  have hs0 := lt_of_le_of_lt hσ0 hs
  exact ((gammaFactor_analytic_ne_zero F.gammaData hs0).1.div
    (gammaFactor_analytic_ne_zero G.gammaData hs0).1
    (gammaFactor_analytic_ne_zero G.gammaData hs0).2).mul
      (eulerQuotient_analyticOnNhd F G hb s hs)

theorem rightCompletedEulerQuotient_ne_zero (F G : RHTower.SelbergClass) {s : ℂ}
    (hs : 0 < s.re) : rightCompletedEulerQuotient F G s ≠ 0 :=
  mul_ne_zero (div_ne_zero (gammaFactor_analytic_ne_zero F.gammaData hs).2
    (gammaFactor_analytic_ne_zero G.gammaData hs).2) (Complex.exp_ne_zero _)

theorem rightCompletedEulerQuotient_reflection (F G : RHTower.SelbergClass) {σ : ℝ}
    (hσ0 : 0 ≤ σ)
    (hb : LSeriesSummable (fun n => F.eulerLogCoeff n - G.eulerLogCoeff n) σ)
    {s : ℂ} (hs : σ < s.re) (hs' : s.re < 1 - σ) :
    rightCompletedEulerQuotient F G s =
      F.gammaData.rootNumber / G.gammaData.rootNumber *
        star (rightCompletedEulerQuotient F G (1 - star s)) := by
  apply completedQuotient_reflection F G hσ0
    (rightCompletedEulerQuotient_analyticOnNhd F G hσ0 hb) _ hs hs'
  intro z hz hz1
  have hne := (gammaFactor_analytic_ne_zero G.gammaData (lt_of_le_of_lt hσ0 hz)).2
  have hv := eulerQuotient_mul_value_of_summable F G (by linarith) hb hz hz1
  dsimp only [rightCompletedEulerQuotient]
  rw [← hv]
  field_simp

/-- The right completed quotient glued to its functional-equation reflection. -/
def completedEulerQuotient (F G : RHTower.SelbergClass) (s : ℂ) : ℂ :=
  if 1 / 2 ≤ s.re then rightCompletedEulerQuotient F G s else
    F.gammaData.rootNumber / G.gammaData.rootNumber *
      star (rightCompletedEulerQuotient F G (1 - star s))

/-- On the right half-plane the gluing agrees with the Gamma-corrected Euler quotient. -/
theorem completedEulerQuotient_eq_right (F G : RHTower.SelbergClass) {s : ℂ}
    (hs : 1 / 2 ≤ s.re) :
    completedEulerQuotient F G s = rightCompletedEulerQuotient F G s := if_pos hs

/-- The completed quotient has no zeros, independently of its analytic continuation. -/
theorem completedEulerQuotient_ne_zero (F G : RHTower.SelbergClass) (s : ℂ) :
    completedEulerQuotient F G s ≠ 0 := by
  have hphase : ‖F.gammaData.rootNumber / G.gammaData.rootNumber‖ = 1 := by
    rw [norm_div, F.gammaData.rootNumber_norm, G.gammaData.rootNumber_norm, div_one]
  have hphase0 : F.gammaData.rootNumber / G.gammaData.rootNumber ≠ 0 := by
    apply norm_ne_zero_iff.mp
    rw [hphase]
    exact one_ne_zero
  dsimp only [completedEulerQuotient]
  split_ifs with hs
  · exact rightCompletedEulerQuotient_ne_zero F G (by linarith)
  · apply mul_ne_zero hphase0
    exact star_ne_zero.mpr (rightCompletedEulerQuotient_ne_zero F G
      (by simpa using (by linarith : 0 < 1 - s.re)))

/-- A subcritical Euler discrepancy makes the completed quotient entire, even
when the two Gamma products, exponential parameters and root numbers differ. -/
theorem completedEulerQuotient_analyticOnNhd (F G : RHTower.SelbergClass) {σ : ℝ}
    (hσ : σ < 1 / 2)
    (hb : LSeriesSummable (fun n => F.eulerLogCoeff n - G.eulerLogCoeff n) σ) :
    AnalyticOnNhd ℂ (completedEulerQuotient F G) univ := by
  let τ := max σ 0
  have hτ : τ < 1 / 2 := max_lt hσ (by norm_num)
  have hτ0 : 0 ≤ τ := le_max_right σ 0
  have hbτ : LSeriesSummable (fun n => F.eulerLogCoeff n - G.eulerLogCoeff n) τ :=
    hb.of_re_le_re (by simpa only [ofReal_re] using le_max_left σ 0)
  have hR := rightCompletedEulerQuotient_analyticOnNhd F G hτ0 hbτ
  have hright : ∀ s : ℂ, τ < s.re →
      completedEulerQuotient F G s = rightCompletedEulerQuotient F G s := by
    intro s hs
    dsimp only [completedEulerQuotient]
    split_ifs with h
    · rfl
    · exact (rightCompletedEulerQuotient_reflection F G hτ0 hbτ hs (by linarith)).symm
  have hleft : ∀ s : ℂ, s.re < 1 - τ → completedEulerQuotient F G s =
      F.gammaData.rootNumber / G.gammaData.rootNumber *
        star (rightCompletedEulerQuotient F G (1 - star s)) := by
    intro s hs
    dsimp only [completedEulerQuotient]
    split_ifs with h
    · exact rightCompletedEulerQuotient_reflection F G hτ0 hbτ (by linarith) hs
    · rfl
  apply analyticOnNhd_univ_iff_differentiable.mpr
  intro s
  by_cases hs : τ < s.re
  · have hopen : IsOpen {z : ℂ | τ < z.re} := isOpen_lt continuous_const continuous_re
    apply (hR s hs).differentiableAt.congr_of_eventuallyEq
    filter_upwards [hopen.mem_nhds hs] with z hz
    exact hright z hz
  · have hs' : s.re < 1 - τ := by linarith
    have href : τ < (1 - star s).re := by simpa using (by linarith : τ < 1 - s.re)
    have ha : AnalyticAt ℂ (fun z => F.gammaData.rootNumber / G.gammaData.rootNumber *
        star (rightCompletedEulerQuotient F G (1 - star z))) s :=
      analyticAt_const.mul (RHTower.analyticAt_selbergConjugateReflection (hR _ href))
    have hopen : IsOpen {z : ℂ | z.re < 1 - τ} := isOpen_lt continuous_re continuous_const
    apply ha.differentiableAt.congr_of_eventuallyEq
    filter_upwards [hopen.mem_nhds hs'] with z hz
    exact hleft z hz

end GaloisForLFunctions.SelbergClass
