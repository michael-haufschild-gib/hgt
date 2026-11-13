import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.SoftLogarithmicSublevelCompactness
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.ConfiningLogarithmicLimit

/-!
# Compact soft logarithmic minimizing profiles

Compactness of unit Rayleigh sublevels produces a strongly convergent
minimizing sequence. The uniform confinement limit places the entire
family of sufficiently confined, rescaled minimizers in one such sublevel.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set Topology
open _root_.RHTower
namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
open HTGeometry CriticalArithmeticCorrelationTheory ArithmeticCastelnuovoSeveri


private theorem norm_L2_real_representative_eq_one {F : ℝ → ℝ}
    (hm : (∫ u, F u ^ 2) = 1)
    (v : SoninL2) (hv : (v : ℝ → ℂ) =ᵐ[volume] cx F) : ‖v‖ = 1 := by
  have hn : ‖v‖ ^ 2 = 1 := by
    calc
      _ = ∫ u, ‖v u‖ ^ 2 := _root_.RHTower.norm_sq_eq_integral v
      _ = ∫ u, F u ^ 2 := by
        apply integral_congr_ae
        filter_upwards [hv] with u hu
        rw [hu]
        change ‖(F u : ℂ)‖ ^ 2 = F u ^ 2
        rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
      _ = 1 := hm
  nlinarith only [hn, norm_nonneg v]

/-- The trial infimum has a unit strongly convergent minimizing sequence in one fixed sublevel. -/
theorem exists_softLogarithmic_strong_minimizingSequence :
    ∃ (U : ℕ → ℝ → ℝ) (hU : ∀ n, SoftLogarithmicHalfLineDomain (U n)) (v : SoninL2),
      (∀ n, (∫ u, U n u ^ 2) = 1) ∧
      (∀ n, softLogarithmicHalfLineEnergy (U n) ≤ softLogarithmicHalfLineGroundEnergy + 1) ∧
      ‖v‖ = 1 ∧
      Tendsto (fun n => softLogarithmicHalfLineEnergy (U n)) atTop
        (𝓝 softLogarithmicHalfLineGroundEnergy) ∧
      Tendsto (fun n => (hU n).memLp_complex.toLp (cx (U n))) atTop (𝓝 v) := by
  classical
  have hnear (n : ℕ) : ∃ F : ℝ → ℝ, SoftLogarithmicHalfLineDomain F ∧
      (∫ u, F u ^ 2) = 1 ∧ softLogarithmicHalfLineEnergy F <
        softLogarithmicHalfLineGroundEnergy + 1 / ((n : ℝ) + 1) := by
    obtain ⟨e, ⟨F, hF, hm, rfl⟩, he⟩ := exists_lt_of_csInf_lt
      softLogarithmicHalfLineEnergyRange_nonempty
      (show softLogarithmicHalfLineGroundEnergy <
        softLogarithmicHalfLineGroundEnergy + 1 / ((n : ℝ) + 1) from
          lt_add_of_pos_right _ (by positivity))
    exact ⟨F, hF, hm, he⟩
  choose U hU hm he using hnear
  let V : ℕ → SoninL2 := fun n => (hU n).memLp_complex.toLp (cx (U n))
  have hVnorm (n : ℕ) : ‖V n‖ = 1 :=
    norm_L2_real_representative_eq_one (hm n) (V n)
      (hU n).memLp_complex.coeFn_toLp
  have hbounded (n : ℕ) : softLogarithmicHalfLineEnergy (U n) ≤
      softLogarithmicHalfLineGroundEnergy + 1 := by
    have hε : 1 / ((n : ℝ) + 1) ≤ 1 := by
      apply (div_le_one (by positivity : (0 : ℝ) < (n : ℝ) + 1)).mpr
      exact le_add_of_nonneg_left (Nat.cast_nonneg n)
    linarith only [he n, hε]
  have hmem (n : ℕ) : V n ∈ closure
      (softLogarithmicRayleighSublevel (softLogarithmicHalfLineGroundEnergy + 1)) :=
    subset_closure ⟨U n, hU n, hm n, hbounded n, rfl⟩
  obtain ⟨v, _, s, hs, hconv⟩ :=
    (isCompact_closure_softLogarithmicRayleighSublevel
      (softLogarithmicHalfLineGroundEnergy + 1)).tendsto_subseq hmem
  have hεlim : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 (0 : ℝ)) :=
    tendsto_const_nhds.div_atTop
      (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  have hupper : Tendsto (fun n : ℕ =>
      softLogarithmicHalfLineGroundEnergy + 1 / ((n : ℝ) + 1)) atTop
      (𝓝 softLogarithmicHalfLineGroundEnergy) := by
    simpa only [add_zero] using hεlim.const_add softLogarithmicHalfLineGroundEnergy
  have hEnergy : Tendsto (fun n => softLogarithmicHalfLineEnergy (U n)) atTop
      (𝓝 softLogarithmicHalfLineGroundEnergy) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
      (fun n => softLogarithmicHalfLineGroundEnergy_le (hU n) (hm n)) (fun n => (he n).le)
  refine ⟨fun n => U (s n), fun n => hU (s n), v, fun n => hm (s n),
    fun n => hbounded (s n), ?_,
    hEnergy.comp hs.tendsto_atTop, hconv⟩
  have hnorm := hconv.norm
  have hn : (fun n => ‖(V ∘ s) n‖) = fun _ : ℕ => (1 : ℝ) :=
    funext fun n => hVnorm (s n)
  rw [hn] at hnorm
  exact (tendsto_nhds_unique tendsto_const_nhds hnorm).symm

#print axioms exists_softLogarithmic_strong_minimizingSequence

/-- All L² representatives of rescaled unit minimizers above a confinement strength. -/
def rescaledConfiningMinimizerFamily (A : ℝ) : Set SoninL2 :=
  {v | ∃ (a : ℝ) (F : ℝ → ℝ), A ≤ a ∧
    IsHalfLineEnergyMinimizer (confiningHalfLineRatio a) F ∧
      (v : ℝ → ℂ) =ᵐ[volume] cx (rescaledConfiningProfile a F)}

/-- Sufficiently confined rescaled minimizers form a family with compact L² closure. -/
theorem exists_isCompact_closure_rescaledConfiningMinimizerFamily :
    ∃ A : ℝ, 1 ≤ A ∧ IsCompact (closure (rescaledConfiningMinimizerFamily A)) := by
  obtain ⟨A, hA, hsmall⟩ := exists_minimizer_softLogarithmic_error_small zero_lt_one
  refine ⟨A, hA, ?_⟩
  have hsubset : rescaledConfiningMinimizerFamily A ⊆
      softLogarithmicRayleighSublevel (softLogarithmicHalfLineGroundEnergy + 1) := by
    rintro v ⟨a, F, ha, hF, hv⟩
    have ha0 := zero_lt_one.trans_le (hA.trans ha)
    have hG := hF.1.rescaled_softLogarithmic ha0
    have hm : (∫ u, rescaledConfiningProfile a F u ^ 2) = 1 := by
      rw [integral_sq_rescaledConfiningProfile ha0, hF.2.1]
    obtain ⟨_, hp, he⟩ := hsmall ha hF
    have hE : softLogarithmicHalfLineEnergy (rescaledConfiningProfile a F) ≤
        softLogarithmicHalfLineGroundEnergy + 1 := by
      linarith only [hp, he]
    refine ⟨rescaledConfiningProfile a F, hG, hm, hE, ?_⟩
    exact Lp.ext (hv.trans hG.memLp_complex.coeFn_toLp.symm)
  exact (isCompact_closure_softLogarithmicRayleighSublevel
    (softLogarithmicHalfLineGroundEnergy + 1)).of_isClosed_subset
      isClosed_closure (closure_mono hsubset)

#print axioms exists_isCompact_closure_rescaledConfiningMinimizerFamily
end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
