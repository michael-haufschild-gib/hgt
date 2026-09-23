import GaloisForLFunctions.RHTower.XiMassSharpSpacelikeConeSummability

/-!
# Timelike-glancing residual criterion for the Xi-mass route

The sharp-spacelike component is uniformly bounded, so it can be removed from the exact finite
centered-atom criterion without changing its logical strength.  This module proves the resulting
residual line bound is equivalent to RH.  It also proves that, for every slope `alpha > 1`, one can
choose a legal fixed mass for which the entire RH-bearing residual lies in

`log n < alpha * u`.

Thus the unresolved source is localizable to an arbitrarily thin outer neighborhood of the true
timelike cone; no spacelike contour or summation debt remains.
-/

open Complex Real MeasureTheory Set Filter Topology

namespace RHTower

noncomputable section

/-- Uniform line bound for the exact complementary timelike-plus-glancing finite sum. -/
def XiMassCriticalCenteredTimelikeGlancingConeLineBound
    (a sigma d alpha : ℝ) : Prop :=
  ∃ C : ℝ, ∀ u : ℝ, 0 ≤ u →
    ‖xiMassCriticalCenteredTimelikeGlancingConeSum a sigma d alpha u‖ ≤ C

/-- Removing the uniformly bounded sharp-spacelike component preserves the finite-cone line-bound
problem exactly. -/
theorem xiMassCriticalCenteredAtomConeLineBound_iff_timelikeGlancing
    {a sigma d alpha : ℝ} (ha : 1 / 2 < a) (hsigma : 0 < sigma)
    (hsharp : xiMassSpacelikeSharpSlope a < alpha) :
    XiMassCriticalCenteredAtomConeLineBound a sigma d ↔
      XiMassCriticalCenteredTimelikeGlancingConeLineBound a sigma d alpha := by
  let B : ℝ := ∑' n : ℕ, xiMassSharpSpacelikeCenteredMajorant a alpha n
  have hspace : ∀ u : ℝ, 0 ≤ u →
      ‖xiMassCriticalCenteredSharpSpacelikeConeSum a sigma d alpha u‖ ≤ B :=
    fun u hu => by
      simpa only [B] using
        norm_xiMassCriticalCenteredSharpSpacelikeConeSum_le_tsum
          ha hsigma hsharp hu
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨C + B, fun u hu => ?_⟩
    have hpartition :=
      xiMassCriticalCenteredAtomConeSum_eq_sharpSpacelike_add_timelikeGlancing
        a sigma d alpha u
    have hsolve :
        xiMassCriticalCenteredTimelikeGlancingConeSum a sigma d alpha u =
          xiMassCriticalCenteredAtomConeSum a sigma d u -
            xiMassCriticalCenteredSharpSpacelikeConeSum a sigma d alpha u := by
      calc
        xiMassCriticalCenteredTimelikeGlancingConeSum a sigma d alpha u =
            (xiMassCriticalCenteredSharpSpacelikeConeSum a sigma d alpha u +
              xiMassCriticalCenteredTimelikeGlancingConeSum a sigma d alpha u) -
                xiMassCriticalCenteredSharpSpacelikeConeSum a sigma d alpha u := by ring
        _ = _ := by rw [← hpartition]
    rw [hsolve]
    exact (norm_sub_le _ _).trans (add_le_add (hC u hu) (hspace u hu))
  · rintro ⟨C, hC⟩
    refine ⟨B + C, fun u hu => ?_⟩
    rw [xiMassCriticalCenteredAtomConeSum_eq_sharpSpacelike_add_timelikeGlancing]
    exact (norm_add_le _ _).trans (add_le_add (hspace u hu) (hC u hu))

/-- **Exact residual RH criterion.**  For every legal strict-spacelike cutoff, RH is equivalent to
uniform boundedness of only the complementary finite sum `log n < alpha*u`. -/
theorem riemannHypothesis_iff_xiMassCriticalCenteredTimelikeGlancingConeLineBound
    {a c sigma d alpha : ℝ} (hhalf : 1 / 2 < c) (hca : c < a)
    (hsigma : 0 < sigma) (hdhalf : 1 / 2 < d) (hda : d < a)
    (hsharp : xiMassSpacelikeSharpSlope a < alpha) :
    RiemannHypothesis ↔
      XiMassCriticalCenteredTimelikeGlancingConeLineBound a sigma d alpha := by
  have ha : 1 / 2 < a := lt_trans hdhalf hda
  exact (riemannHypothesis_iff_xiMassCriticalCenteredAtomConeLineBound
    hhalf hca hsigma hdhalf hda).trans
      (xiMassCriticalCenteredAtomConeLineBound_iff_timelikeGlancing
        ha hsigma hsharp)

/-- Every slope strictly above the physical light slope `1` is above the sharp spacelike threshold
for some fixed legal mass. -/
theorem exists_mass_with_xiMassSpacelikeSharpSlope_lt
    {alpha : ℝ} (halpha : 1 < alpha) :
    ∃ a : ℝ, 1 / 2 < a ∧ xiMassSpacelikeSharpSlope a < alpha := by
  let k := Real.sqrt (alpha ^ (2 : ℕ) - 1)
  let a := alpha / k
  have halpha0 : 0 < alpha := lt_trans (by norm_num) halpha
  have hk : 0 < k := by
    dsimp only [k]
    rw [Real.sqrt_pos]
    nlinarith
  have hkSq : k ^ (2 : ℕ) = alpha ^ (2 : ℕ) - 1 := by
    dsimp only [k]
    rw [Real.sq_sqrt]
    nlinarith
  have ha0 : 0 < a := by
    dsimp only [a]
    positivity
  have hhalf : 1 / 2 < a := by
    dsimp only [a]
    rw [lt_div_iff₀ hk]
    nlinarith [sq_nonneg (2 * alpha + k)]
  have hj : 0 < Real.sqrt (a ^ (2 : ℕ) - 1 / 4) :=
    xiMassSpacelikeSharpSlope_denominator_pos hhalf
  have hjSq : Real.sqrt (a ^ (2 : ℕ) - 1 / 4) ^ (2 : ℕ) = a ^ (2 : ℕ) - 1 / 4 := by
    rw [Real.sq_sqrt]
    nlinarith [sq_pos_of_pos ha0]
  have hka : k * a = alpha := by
    dsimp only [a]
    field_simp [hk.ne']
  have hkaSq := congrArg (fun x : ℝ => x ^ (2 : ℕ)) hka
  have hlinear : a < alpha * Real.sqrt (a ^ (2 : ℕ) - 1 / 4) := by
    have hleft : 0 < a := ha0
    have hright : 0 < alpha * Real.sqrt (a ^ (2 : ℕ) - 1 / 4) := mul_pos halpha0 hj
    have hsquare : a ^ (2 : ℕ) <
        (alpha * Real.sqrt (a ^ (2 : ℕ) - 1 / 4)) ^ (2 : ℕ) := by
      rw [mul_pow, hjSq]
      nlinarith [sq_pos_of_pos halpha0]
    nlinarith [sq_nonneg (a + alpha * Real.sqrt (a ^ (2 : ℕ) - 1 / 4))]
  refine ⟨a, hhalf, ?_⟩
  rw [xiMassSpacelikeSharpSlope, div_lt_iff₀ hj]
  exact hlinear

/-- **Arbitrarily sharp causal localization.**  For every `alpha>1` and every positive vertical
damping, legal fixed mass/cone parameters exist for which RH is equivalent to the residual finite
sum supported on `log n < alpha*u`. -/
theorem exists_xiMassTimelikeGlancingResidualCriterion
    {sigma alpha : ℝ} (hsigma : 0 < sigma) (halpha : 1 < alpha) :
    ∃ a c d : ℝ,
      1 / 2 < c ∧ c < a ∧ 1 / 2 < d ∧ d < a ∧
      xiMassSpacelikeSharpSlope a < alpha ∧
      (RiemannHypothesis ↔
        XiMassCriticalCenteredTimelikeGlancingConeLineBound
          a sigma d alpha) := by
  rcases exists_mass_with_xiMassSpacelikeSharpSlope_lt halpha with
    ⟨a, ha, hsharp⟩
  let c : ℝ := (1 / 2 + a) / 2
  let d : ℝ := (1 / 2 + a) / 2
  have hcHalf : 1 / 2 < c := by dsimp only [c]; linarith
  have hca : c < a := by dsimp only [c]; linarith
  have hdHalf : 1 / 2 < d := by dsimp only [d]; linarith
  have hda : d < a := by dsimp only [d]; linarith
  refine ⟨a, c, d, hcHalf, hca, hdHalf, hda, hsharp, ?_⟩
  exact riemannHypothesis_iff_xiMassCriticalCenteredTimelikeGlancingConeLineBound
    hcHalf hca hsigma hdHalf hda hsharp

end

end RHTower
