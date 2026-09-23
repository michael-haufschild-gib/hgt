import GaloisForLFunctions.RHTower.XiMassLevinsonSymmetricReciprocalLanding
import GaloisForLFunctions.RHTower.Sieve.VonMangoldtMomentRatioAsymptotics

/-!
# Symmetric reciprocal Levinson energy obstruction

Exact fixed-Weil normalization turns the opposite reciprocal detector pair into the zero jet.
Its short coefficient energy is therefore exactly the von Mangoldt harmonic square moment and
diverges like one half log squared.  Positive coefficient energy cannot provide the uniform
aperture budget needed by the vertical RH criterion; any successful estimate must use phase.
-/

noncomputable section

open Complex Finset Filter Topology
open scoped ArithmeticFunction

namespace RHTower.Sieve

/-- Short coefficient energy of the fixed-Weil-normalized opposite reciprocal pair. -/
def levinsonSymmetricReciprocalShortEnergy (M : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 2 M,
    ‖levinsonSymmetricReciprocalRescaledCoeff M k‖ ^ (2 : ℕ)

/-- The paired reciprocal energy is exactly the von Mangoldt harmonic square moment. -/
theorem levinsonSymmetricReciprocalShortEnergy_eq_vonMangoldtHarmonicSquareSum
    (M : ℕ) (hM : 1 < M) :
    levinsonSymmetricReciprocalShortEnergy M =
      vonMangoldtHarmonicSquareSum M := by
  rw [levinsonSymmetricReciprocalShortEnergy, vonMangoldtHarmonicSquareSum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [levinsonSymmetricReciprocalRescaledCoeff_eq_zeroJet,
    levinsonZeroJetRescaledCoeff_eq_vonMangoldt hM
      (lt_of_lt_of_le Nat.one_lt_two (Finset.mem_Icc.mp hk).1)
      (Finset.mem_Icc.mp hk).2]
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg
    (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)), div_pow,
    Real.sq_sqrt (by positivity : (0 : ℝ) ≤ k)]

/-- Sharp normalized energy law for the fixed-Weil-normalized reciprocal pair. -/
theorem tendsto_levinsonSymmetricReciprocalShortEnergy_div_logSquare :
    Tendsto (fun M : ℕ =>
      levinsonSymmetricReciprocalShortEnergy M / Real.log M ^ (2 : ℕ))
      atTop (nhds (1 / 2 : ℝ)) := by
  refine tendsto_vonMangoldtHarmonicSquareSum_div_logSquare.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with M hM
  rw [levinsonSymmetricReciprocalShortEnergy_eq_vonMangoldtHarmonicSquareSum M (by omega)]

/-- The exact paired source has divergent positive coefficient energy. -/
theorem tendsto_levinsonSymmetricReciprocalShortEnergy_atTop :
    Tendsto levinsonSymmetricReciprocalShortEnergy atTop atTop := by
  have hlog : Tendsto (fun M : ℕ => Real.log M) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlogSq : Tendsto (fun M : ℕ => Real.log M ^ (2 : ℕ)) atTop atTop := by
    simpa only [pow_two] using hlog.atTop_mul_atTop₀ hlog
  have hprod :=
    tendsto_levinsonSymmetricReciprocalShortEnergy_div_logSquare.pos_mul_atTop
      (by norm_num : (0 : ℝ) < 1 / 2) hlogSq
  refine hprod.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with M hM
  have hlogne : Real.log (M : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast hM)).ne'
  field_simp [hlogne]

/-- No aperture-independent positive `L²` budget exists for the exact paired source. -/
theorem not_exists_levinsonSymmetricReciprocalShortEnergy_uniformBound :
    ¬ ∃ C : ℝ, ∀ M : ℕ, levinsonSymmetricReciprocalShortEnergy M ≤ C := by
  rintro ⟨C, hC⟩
  have hlarge := tendsto_levinsonSymmetricReciprocalShortEnergy_atTop.eventually_gt_atTop C
  obtain ⟨M, hM⟩ := hlarge.exists
  exact (not_lt_of_ge (hC M)) hM

end RHTower.Sieve
