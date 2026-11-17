import GaloisForLFunctions.ExclusionOfTheCriticalState.WeilsFormOnProbesIsTheCaratheodoryKernelOfXi
import GaloisForLFunctions.ArchimedeanTateDomination.FirstFoldStageDomination
import GaloisForLFunctions.RHTower.WeilMarkovThinNonnegativeOddPositivity
import GaloisForLFunctions.RHTower.WeilMarkovOddSectorTrivialZeroSquares
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.ConfiningHalfLineWeakEquation

/-!
# The collar is coercive and prime-blind

The collar is the terminal window `[−A, 0]` of the half line, `A < log 2`. No translate by `log n`,
`n ≥ 2`, keeps it on itself, and windows up to `2·enlargedWeilFloorAperture > log 2` carry the
strict Weil floor `1/8000` (ArchimedeanTateDomination).

* **Coercivity** (`collar_fullEnergy_ge`). On `C²` tests of `[−A, 0]`,
  `A ≤ 2·enlargedWeilFloorAperture`, the confined form satisfies
  `Q_R(G) ≥ ‖G‖²/8000 + a(R) W₈(G)` at every ratio. The windows include the collar
  (`log_two_lt_two_mul_enlargedWeilFloorAperture`).
* **Prime-blindness** (`collar_fullEnergy_eq_arch_add_pole`). For `A < log 2` the prime sum of a
  collar test vanishes: `Q_R = arch + pole + a(R) W₈` on the collar. Collar positivity is a property
  of the Gamma factor and the pole alone; every prime side shares it.
* **The collar equation of the critical state** (`criticalState_collar_equation`). Against a
  collar test only the backward prime translates of the state enter:
  `Γ(F, G) + pole(F, G) + a W₈(F, G) = Σ_n Λ(n) n^{−½} ∫ F(t) G(t + log n) dt`. The right side
  reads `F` only on `u ≤ −log 2 + A < 0`, outside the collar: on the collar, the archimedean,
  polar and confinement response of the state is the backward prime wave of its far part.
-/

noncomputable section
open MeasureTheory Set Filter Topology Zeta23
open _root_.RHTower

namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri HTGeometry
  CriticalArithmeticCorrelationTheory CohomologyOfWindowsOfSpecZ SpacingScaleHarmonicAnalysis
  ArithmeticIncidencePositivity

/-- The floor windows contain the collar: `log 2 < 2·enlargedWeilFloorAperture`. -/
theorem log_two_lt_two_mul_enlargedWeilFloorAperture :
    Real.log 2 < 2 * enlargedWeilFloorAperture := by
  have h := enlargedWeilFloorAperture_bounds.1
  have h2 := Real.log_two_lt_d9
  linarith

/-- On `C²` compactly supported half-line tests the bare form is Weil's form. -/
theorem fullEnergy_eq_weilQuad_add {G : ℝ → ℝ} (hG : ContDiff ℝ 2 G) (hGc : HasCompactSupport G)
    (hGs : ∀ u, 0 ≤ u → G u = 0) (R : ℝ) :
    criticalHalfLineFullEnergy R G =
      weilQuad G + criticalAliasCoefficient R * ∫ u, G u ^ 2 * Real.exp (-(8 * u)) := by
  have hM := markovEnergy_ofReal_eq_archForm_sub_primeSum hG hGc
  have hP := re_weilPoleTerm_ofReal_eq_two_mul_cosh_sq_sub_sinh_sq hG.continuous hGc
  have hW : weilQuad G = markovEnergy (fun u => (G u : ℂ)) +
      (weilPoleTerm (EF.weilTest (fun u => (G u : ℂ)) (fun u => (G u : ℂ)))).re := by
    unfold weilQuad markovEnergy
    rw [Complex.sub_re]
    ring
  unfold criticalHalfLineFullEnergy
  rw [halfLineExpMass_eq_full hGs, hW, hM, hP]

/-- A window test vanishes on `[0, ∞)`: it is continuous and zero to the right of `0`. -/
theorem windowTest_vanish_nonneg {A : ℝ} {G : ℝ → ℝ} (hG : IsWindowTest A G) :
    ∀ u, 0 ≤ u → G u = 0 := by
  intro u hu
  rcases hu.lt_or_eq with h | h
  · exact hG.vanish u fun hm => absurd hm.2 (not_le.mpr h)
  · subst h
    have hlim : Tendsto G (𝓝[>] 0) (𝓝 (G 0)) :=
      hG.continuous.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have hz : G =ᶠ[𝓝[>] 0] fun _ => 0 :=
      eventually_nhdsWithin_of_forall fun x hx =>
        hG.vanish x fun hm => absurd hm.2 (not_le.mpr hx)
    exact tendsto_nhds_unique (hlim.congr' hz) tendsto_const_nhds

/-- **Collar coercivity.** On the floor windows the confined form dominates `‖G‖²/8000` plus the
confinement. -/
theorem collar_fullEnergy_ge {A R : ℝ} (hA : A ≤ 2 * enlargedWeilFloorAperture) {G : ℝ → ℝ}
    (hG : IsWindowTest A G) :
    (1 / 8000 : ℝ) * (∫ u, G u ^ 2) +
        criticalAliasCoefficient R * (∫ u, G u ^ 2 * Real.exp (-(8 * u))) ≤
      criticalHalfLineFullEnergy R G := by
  rw [fullEnergy_eq_weilQuad_add hG.contDiff hG.hasCompactSupport (windowTest_vanish_nonneg hG)]
  have := ArchimedeanTateDomination.weilQuad_ge_one_div_eightThousand_of_le_two_mul_enlargedAperture
    hA hG
  linarith

/-- The collar prime sum vanishes. -/
theorem collar_primeSum_eq_zero {A : ℝ} (hA : A < Real.log 2) {G : ℝ → ℝ}
    (hG : IsWindowTest A G) : primeSum G = 0 :=
  primeSum_eq_zero_of_width_lt (x₀ := -A) (w := A) (fun x hx => hG.vanish x (by
    simpa using hx)) hA

/-- **Prime-blindness.** On the collar the confined form is archimedean plus polar plus
confinement. -/
theorem collar_fullEnergy_eq_arch_add_pole {A : ℝ} (hA : A < Real.log 2) {G : ℝ → ℝ}
    (hG : IsWindowTest A G) (R : ℝ) :
    criticalHalfLineFullEnergy R G = archForm G +
      (2 * coshHalfMoment G ^ 2 - 2 * sinhHalfMoment G ^ 2) +
        criticalAliasCoefficient R * (∫ u in Iio 0, G u ^ 2 * Real.exp (-(8 * u))) := by
  unfold criticalHalfLineFullEnergy
  rw [collar_primeSum_eq_zero hA hG, sub_zero]

/-! ### The collar equation of the state -/

theorem vonMangoldtAtom_eq_zero_of_lt_two {n : ℕ} (hn : n < 2) : vonMangoldtAtom n = 0 := by
  unfold vonMangoldtAtom
  rw [if_neg (by omega)]

/-- A collar test meets a half-line profile only through backward translates. -/
theorem primePairTerm_collar_left {A : ℝ} (hA : A < Real.log 2) {F G : ℝ → ℝ}
    (hF : ∀ u, 0 ≤ u → F u = 0) (hG : IsWindowTest A G) (n : ℕ) :
    primePairTerm F G n = vonMangoldtAtom n * ∫ t, F t * G (t + Real.log n) := by
  unfold primePairTerm
  rcases lt_or_ge n 2 with hn | hn
  · rw [vonMangoldtAtom_eq_zero_of_lt_two hn, zero_mul, zero_mul]
  · have hlog : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) (by exact_mod_cast hn)
    have h0 : (fun t => F t * G (t - Real.log n)) = fun _ => 0 := by
      funext t
      by_cases ht : 0 ≤ t
      · rw [hF t ht, zero_mul]
      · rw [hG.vanish (t - Real.log n) fun hm => by linarith [hm.1], mul_zero]
    rw [h0, integral_zero, zero_add]

/-- The transposed prime term of a collar test is the same backward translate. -/
theorem primePairTerm_collar_right {A : ℝ} (hA : A < Real.log 2) {F G : ℝ → ℝ}
    (hF : ∀ u, 0 ≤ u → F u = 0) (hG : IsWindowTest A G) (n : ℕ) :
    primePairTerm G F n = vonMangoldtAtom n * ∫ t, F t * G (t + Real.log n) := by
  unfold primePairTerm
  rcases lt_or_ge n 2 with hn | hn
  · rw [vonMangoldtAtom_eq_zero_of_lt_two hn, zero_mul, zero_mul]
  · have hlog : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) (by exact_mod_cast hn)
    have h0 : (fun t => G t * F (t + Real.log n)) = fun _ => 0 := by
      funext t
      by_cases ht : t ∈ Icc (-A) 0
      · rw [hF (t + Real.log n) (by linarith [ht.1]), mul_zero]
      · rw [hG.vanish t ht, zero_mul]
    have hs : (∫ t, G t * F (t - Real.log n)) = ∫ t, F t * G (t + Real.log n) := by
      have h := integral_add_right_eq_self (μ := volume)
        (fun t => G t * F (t - Real.log n)) (Real.log n)
      simp only [add_sub_cancel_right] at h
      rw [← h]
      exact integral_congr_ae (Eventually.of_forall fun t => mul_comm _ _)
    rw [h0, integral_zero, add_zero, hs]

/-- **The collar equation of the critical state.** Against a collar test, the Gamma, pole and
confinement pairings of the state equal its backward prime wave. -/
theorem criticalState_collar_equation {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) {A : ℝ} (hA : A < Real.log 2)
    {G : ℝ → ℝ} (hG : IsWindowTest A G) :
    gammaMixedForm F G +
        (2 * coshHalfMoment F * coshHalfMoment G - 2 * sinhHalfMoment F * sinhHalfMoment G) +
          criticalAliasCoefficient W₀ * (∫ u in Iio 0, F u * G u * Real.exp (-(8 * u))) =
      ∑' n : ℕ, vonMangoldtAtom n * ∫ t, F t * G (t + Real.log n) := by
  have hdF := criticalHalfLineEnergyDomain_of_groundState hF
  have hdG := criticalHalfLineEnergyDomain_of_compact_negative hG.contDiff hG.hasCompactSupport
    (windowTest_vanish_nonneg hG)
  have hweak := criticalHalfLineMixedEnergy_groundState_eq_zero hW ht hF hdG
  rw [criticalHalfLineMixedEnergy_eq_bare_add] at hweak
  unfold bareMixedEnergy primeMixedForm at hweak
  simp_rw [primePairTerm_collar_left hA hF.2.2.2.2.2.1 hG,
    primePairTerm_collar_right hA hF.2.2.2.2.2.1 hG] at hweak
  linarith

#print axioms collar_fullEnergy_ge
#print axioms criticalState_collar_equation

end GaloisForLFunctions.ExclusionOfTheCriticalState
