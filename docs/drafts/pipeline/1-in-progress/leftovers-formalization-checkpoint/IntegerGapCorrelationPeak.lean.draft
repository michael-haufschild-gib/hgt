import GaloisForLFunctions.BiScaleUncertainty.LocalCorrelationEnergyStability
import GaloisForLFunctions.BiScaleUncertainty.DistantCopyCorrelationTopology
import GaloisForLFunctions.BiScaleUncertainty.PerturbedCorrelationSamples

/-!
# Exact correlation peaks inside an integer-logarithm gap

Two narrow smooth source copies are blind at every integer logarithm but
have normalized correlation one half at any prescribed lag between log two
and log three. Their energy grows at most logarithmically in the gap radius.
The singular-energy modulus supplies the complementary lower bound.
-/

noncomputable section
open MeasureTheory Set
open scoped CompactlySupported
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm
namespace GaloisForLFunctions.BiScaleUncertainty
open FiniteHorizon
set_option autoImplicit false

/-- Correlation support radius that avoids the origin packet and both ends of the first log gap. -/
def integerLogGapRadius (T : ℝ) : ℝ :=
  min 1 (min (Real.log 2 / 2) (min ((T - Real.log 2) / 2) ((Real.log 3 - T) / 2)))

theorem integerLogGapRadius_pos {T : ℝ} (h2 : Real.log 2 < T) (h3 : T < Real.log 3) :
    0 < integerLogGapRadius T := by
  exact lt_min zero_lt_one (lt_min (half_pos (Real.log_pos (by norm_num)))
    (lt_min (half_pos (sub_pos.mpr h2)) (half_pos (sub_pos.mpr h3))))

/-- A genuine smooth integer-grid-blind source has a half peak at every lag in the first gap. -/
theorem exists_smooth_integer_gap_peak :
    ∃ C : ℝ, ∀ T : ℝ, Real.log 2 < T → T < Real.log 3 →
      ∃ E : ℝ, ∃ f : LevyEnergySource E,
        ContDiff ℝ (↑(⊤ : ℕ∞)) (f.source : ℝ → ℝ) ∧
        (∀ n : ℕ, 2 ≤ n → f.correlation (Real.log (n : ℝ)) = 0) ∧
        f.correlation T = 1 / 2 ∧ E ≤ C - Real.log (integerLogGapRadius T) := by
  obtain ⟨C, hC⟩ := exists_smooth_small_support_logarithmic_cost
  let a : ℝ := Real.log 2 / 4
  let tail : ℝ := 2 * ∫ x in Ioi a, archLevySinhWeight x
  refine ⟨C + tail, ?_⟩
  intro T h2 h3
  let ρ := integerLogGapRadius T
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hρ : 0 < ρ := integerLogGapRadius_pos h2 h3
  have hρ1 : ρ ≤ 1 := min_le_left _ _
  have hρ2 : ρ ≤ Real.log 2 / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hρlo : ρ ≤ (T - Real.log 2) / 2 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hρhi : ρ ≤ (Real.log 3 - T) / 2 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hρlog : ρ < Real.log 2 := by linarith only [hρ2, hlog2]
  have hρT : ρ < T := hρlog.trans h2
  have ha : 0 < a := div_pos hlog2 (by norm_num)
  have hlocalT : ρ + a < T := by dsimp only [a]; linarith only [hρ2, h2, hlog2]
  obtain ⟨b, hb, hbc, hbR, hbs, hbE⟩ := hC ρ hρ hρ1
  have horder : (2 : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞) :=
    WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top)
  let g := subtractCopy b (-1) T
  have hgs : ContDiff ℝ (↑(⊤ : ℕ∞)) g := contDiff_subtractCopy hb (-1) T
  have hgc : HasCompactSupport g := hasCompactSupport_subtractCopy hbc (-1) T
  have hgR : 0 < autocorr g 0 := autocorr_subtractCopy_zero_pos hb.continuous hbc hbR hbs hρT (-1)
  have hlocal : ∀ x, 0 ≤ x → x ≤ a →
      autocorr g x / autocorr g 0 = autocorr b x / autocorr b 0 := by
    intro x hx0 hxa
    exact normalized_autocorr_subtractCopy_local hb.continuous hbc ha.le hbs hlocalT
      (by rwa [abs_of_nonneg hx0]) (-1)
  have henergy := normalizedArchEnergy_abs_sub_le_of_local (hb.of_le horder) hbc hbR
    (hgs.of_le horder) hgc hgR ha hlocal
  let G : C_c(ℝ, ℝ) := ⟨⟨g, hgs.continuous⟩, hgc⟩
  refine ⟨normalizedArchEnergy g, ⟨G, hgs.of_le horder, hgR, le_rfl⟩, hgs, ?_, ?_, ?_⟩
  · intro n hn
    have hlogn : Real.log 2 ≤ Real.log (n : ℝ) :=
      Real.log_le_log (by norm_num) (by exact_mod_cast hn)
    have hx : ρ < |Real.log (n : ℝ)| := hρlog.trans_le (hlogn.trans (le_abs_self _))
    have hminus : ρ < |Real.log (n : ℝ) - T| := by
      by_cases hn2 : n = 2
      · subst n
        norm_num only [Nat.cast_ofNat]
        exact (show ρ < -(Real.log 2 - T) by linarith only [hρlo, h2]).trans_le (neg_le_abs _)
      · have hn3 : 3 ≤ n := by omega
        have hlogn3 : Real.log 3 ≤ Real.log (n : ℝ) :=
          Real.log_le_log (by norm_num) (by exact_mod_cast hn3)
        exact (show ρ < Real.log (n : ℝ) - T by
          linarith only [hρhi, h3, hlogn3]).trans_le (le_abs_self _)
    have hplus : ρ < |Real.log (n : ℝ) + T| :=
      (show ρ < Real.log (n : ℝ) + T by
        linarith only [hρlog, hlogn, h2, hlog2]).trans_le (le_abs_self _)
    change autocorr g (Real.log (n : ℝ)) / autocorr g 0 = 0
    have hz : autocorr g (Real.log (n : ℝ)) = 0 := by
      rw [autocorr_subtractCopy hb.continuous hbc, hbs _ hx, hbs _ hminus, hbs _ hplus]
      ring
    rw [hz, zero_div]
  · change normalizedSourceCorrelation (subtractCopy b (-1) T) T = 1 / 2
    rw [normalizedSourceCorrelation_subtractCopy_center hb.continuous hbc hbR hρ hbs hρT]
    norm_num [copyMixingCoefficient]
  · have hu := (abs_le.mp henergy).2
    change normalizedArchEnergy g ≤ C + tail - Real.log ρ
    change normalizedArchEnergy g - normalizedArchEnergy b ≤ tail at hu
    linarith only [hu, hbE]

/-- The exact quadratic grid admits a half-sized violation despite blindness on every integer log. -/
theorem exists_quadratic_integer_grid_blind_violation {δ : ℝ} (hδ : 0 < δ)
    (hδ1 : δ < 1 / 4) {N : ℕ} (hN : 2 ≤ N) :
    ∃ E : ℝ, ∃ f : LevyEnergySource E,
      ContDiff ℝ (↑(⊤ : ℕ∞)) (f.source : ℝ → ℝ) ∧
      (∀ n : ℕ, 2 ≤ n → f.correlation (Real.log (n : ℝ)) = 0) ∧
      f.correlation (quadraticPerturbedLogNode δ N 2) = 1 / 2 ∧
      Real.exp (-(1 / 2 : ℝ)) * (-Real.log (δ / (N : ℝ))) / 32 ≤ E := by
  have hd := quadraticPerturbedNode_displacement hδ (by norm_num : 1 ≤ (2 : ℕ)) hN
  have hphys2 : (2 : ℝ) < quadraticPerturbedNode δ N 2 := by
    norm_num only [Nat.cast_ofNat] at hd
    linarith only [hd.1]
  have hphys3 : quadraticPerturbedNode δ N 2 < (3 : ℝ) := by
    norm_num only [Nat.cast_ofNat] at hd
    linarith only [hd.2, hδ1]
  have h2 : Real.log 2 < quadraticPerturbedLogNode δ N 2 :=
    Real.log_lt_log (by norm_num) hphys2
  have h3 : quadraticPerturbedLogNode δ N 2 < Real.log 3 :=
    Real.log_lt_log (zero_lt_two.trans hphys2) hphys3
  obtain ⟨_, hpeak⟩ := exists_smooth_integer_gap_peak
  obtain ⟨E, f, hf, hz, hp, _⟩ := hpeak _ h2 h3
  exact ⟨E, f, hf, hz, hp, quadratic_correlation_half_energy_barrier f hδ hδ1
    (by norm_num : 2 ≤ (2 : ℕ)) hN (hz 2 le_rfl) hp⟩

end GaloisForLFunctions.BiScaleUncertainty
