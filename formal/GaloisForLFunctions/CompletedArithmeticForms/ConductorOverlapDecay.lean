import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheTiltedSplineHasAPolynomialConductorFloor
import GaloisForLFunctions.BiScaleUncertainty.SplineProbeFiniteShiftBounds

/-!
# Matching overlap decay of fixed completed conductors

The literal tilted-spline Fourier spectrum has eighth-power decay. Its
coprime-tail series gives a seventh-power upper bound for every fixed
conductor, matching the common lower floor. Consequently every fixed
finite conductor family has uniformly bounded energy ratios at large overlap.
-/

noncomputable section

open MeasureTheory Set Finset Filter Topology
open scoped Real

namespace GaloisForLFunctions.CompletedArithmeticForms

open CriticalArithmeticCorrelationTheory RenormalizedArithmeticPotentialTheory
  RenormalizedArithmeticPotentialTheory.CompletedShell SpacingScaleHarmonicAnalysis
  ArithmeticCastelnuovoSeveri BiScaleUncertainty.ChebyshevGauge

/-- The positive coefficient of the actual common conductor floor. -/
def tiltedConductorFloorCoefficient : ℝ :=
  2 * tiltedSplineTailConstant / (∫ u, tiltedUnitSpline u ^ 2)

theorem tiltedConductorFloorCoefficient_pos : 0 < tiltedConductorFloorCoefficient :=
  div_pos (mul_pos zero_lt_two tiltedSplineTailConstant_pos) integral_tiltedUnitSpline_sq_pos

private def spectrumDecayCoefficient : ℝ := Real.cosh 1 ^ 8 * 4 ^ 8 / (64 * π ^ 8)

private theorem spectrumDecayCoefficient_pos : 0 < spectrumDecayCoefficient := by
  unfold spectrumDecayCoefficient
  positivity

private theorem norm_tiltedSpline_transform (r : ℝ) :
    ‖Zeta23.paperFT (cx tiltedUnitSpline) (r : ℂ)‖ =
      (1 / 8 : ℝ) * ‖Zeta23.paperFT (cx splineProbe) ((r / 8 : ℝ) : ℂ)‖ := by
  have heq : cx tiltedUnitSpline =
      ArithmeticCastelnuovoSeveri.translate (1 / 2) (cx (atomDilate splineProbe (1 / 8))) := rfl
  rw [heq, paperFT_translate, paperFT_atomDilate (by norm_num : (0 : ℝ) < 1 / 8),
    norm_mul, norm_mul, Complex.norm_exp]
  have hz : ((1 / 8 : ℝ) : ℂ) * (r : ℂ) = ((r / 8 : ℝ) : ℂ) := by push_cast; ring
  rw [hz]
  norm_num [Complex.mul_re, Complex.mul_im]

private theorem tilted_spectrum_decay {t : ℝ} (ht : 0 < t) :
    shellSpectrum tiltedUnitSpline t ≤ spectrumDecayCoefficient * t ^ (-8 : ℝ) := by
  set x := π * t / 4 with hx
  have hx0 : 0 < x := by positivity
  have hn : ‖Zeta23.paperFT (cx tiltedUnitSpline) ((2 * π * t : ℝ) : ℂ)‖ ≤
      (1 / 8) * (Real.cosh 1 ^ 4 / x ^ 4) := by
    rw [norm_tiltedSpline_transform]
    refine mul_le_mul_of_nonneg_left ((norm_paperFT_splineProbe_ofReal_le _).trans ?_)
      (by norm_num)
    rw [show 2 * π * t / 8 = x by rw [hx]; ring]
    refine div_le_div_of_nonneg_left (by positivity) (by positivity) ?_
    nlinarith only [sq_nonneg x, pow_pos hx0 2, pow_pos hx0 4]
  have hsq := pow_le_pow_left₀ (norm_nonneg _) hn 2
  have hrpow : t ^ (-8 : ℝ) = 1 / t ^ 8 := by
    rw [Real.rpow_neg ht.le, one_div]
    norm_cast
  change ‖Zeta23.paperFT (fun u => (tiltedUnitSpline u : ℂ)) ((2 * π * t : ℝ) : ℂ)‖ ^ 2 ≤ _
  refine hsq.trans (le_of_eq ?_)
  rw [hrpow, hx]
  unfold spectrumDecayCoefficient
  field_simp
  <;> ring

private theorem tilted_spectrum_tail_decay {z : ℝ} (hz : 0 < z) :
    (∫ t in Ioi z, shellSpectrum tiltedUnitSpline t) ≤
      spectrumDecayCoefficient / 7 * z ^ (-7 : ℝ) := by
  have hmaj : IntegrableOn (fun t : ℝ => spectrumDecayCoefficient * t ^ (-8 : ℝ)) (Ioi z) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num) hz).const_mul _
  have hval : (∫ t in Ioi z, spectrumDecayCoefficient * t ^ (-8 : ℝ)) =
      spectrumDecayCoefficient / 7 * z ^ (-7 : ℝ) := by
    rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) hz]
    norm_num
    ring
  rw [← hval]
  exact setIntegral_mono_on
    (integrableOn_shellSpectrum_Ioi contDiff_tiltedUnitSpline hasCompactSupport_tiltedUnitSpline z)
    hmaj measurableSet_Ioi fun t ht => tilted_spectrum_decay (hz.trans ht)

private theorem sum_inverse_squares_le_two (K : ℕ) :
    (∑ n ∈ range K, 1 / ((n : ℝ) + 1) ^ 2) ≤ 2 := by
  have h (n : ℕ) : 1 / ((n : ℝ) + 1) ^ 2 ≤
      2 / ((n : ℝ) + 1) - 2 / ((n : ℝ) + 2) := by
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    rw [div_sub_div _ _ (by positivity) (by positivity),
      div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith only [hn, sq_nonneg (n : ℝ), mul_nonneg hn (sq_nonneg (n : ℝ))]
  calc
    _ ≤ ∑ n ∈ range K, (2 / ((n : ℝ) + 1) - 2 / ((n : ℝ) + 2)) :=
      sum_le_sum fun n _ => h n
    _ = 2 - 2 / ((K : ℝ) + 1) := by
      convert Finset.sum_range_sub' (fun n : ℕ => 2 / ((n : ℝ) + 1)) K using 1 <;> simp
    _ ≤ 2 := sub_le_self _ (by positivity)

private theorem hasSum_tilted_pole {c : ℝ} (hc : 0 < c) :
    HasSum (fun n : ℕ => 2 / (∫ u, tiltedUnitSpline u ^ 2) * (1 / ((n : ℝ) + 1)) *
      ∫ t in Ioi (((n : ℝ) + 1) * c), shellSpectrum tiltedUnitSpline t)
      (completedConductorEnergy tiltedUnitSpline c 1) := by
  have h := hasSum_completedConductorEnergy contDiff_tiltedUnitSpline tiltedUnitSpline_eq_zero
    integral_tiltedUnitSpline_sq_pos hc one_pos
  convert h using 1
  funext n
  simp

private def poleDecayCoefficient : ℝ :=
  4 * (spectrumDecayCoefficient / 7) / (∫ u, tiltedUnitSpline u ^ 2)

private theorem poleDecayCoefficient_pos : 0 < poleDecayCoefficient := by
  unfold poleDecayCoefficient
  have hA := spectrumDecayCoefficient_pos
  have hM := integral_tiltedUnitSpline_sq_pos
  positivity

private theorem tilted_pole_energy_upper {c : ℝ} (hc : 1 ≤ c) :
    completedConductorEnergy tiltedUnitSpline c 1 ≤ poleDecayCoefficient * c ^ (-7 : ℝ) := by
  have hc0 : 0 < c := zero_lt_one.trans_le hc
  apply le_of_tendsto' (hasSum_tilted_pole hc0).tendsto_sum_nat
  intro K
  let D := 2 * (spectrumDecayCoefficient / 7) / (∫ u, tiltedUnitSpline u ^ 2) * c ^ (-7 : ℝ)
  have hD : 0 ≤ D := by
    dsimp only [D]
    have hA := spectrumDecayCoefficient_pos
    have hM := integral_tiltedUnitSpline_sq_pos
    positivity
  have hterm (n : ℕ) : 2 / (∫ u, tiltedUnitSpline u ^ 2) * (1 / ((n : ℝ) + 1)) *
      (∫ t in Ioi (((n : ℝ) + 1) * c), shellSpectrum tiltedUnitSpline t) ≤
        D * (1 / ((n : ℝ) + 1) ^ 2) := by
    have hn : (1 : ℝ) ≤ (n : ℝ) + 1 := by have := Nat.cast_nonneg (α := ℝ) n; linarith
    have hn0 : (0 : ℝ) < (n : ℝ) + 1 := zero_lt_one.trans_le hn
    have ht := tilted_spectrum_tail_decay (mul_pos hn0 hc0)
    rw [Real.mul_rpow hn0.le hc0.le] at ht
    have hp : ((n : ℝ) + 1) ^ (-7 : ℝ) ≤ 1 / ((n : ℝ) + 1) := by
      rw [one_div, ← Real.rpow_neg_one]
      exact Real.rpow_le_rpow_of_exponent_le hn (by norm_num)
    have hA : 0 ≤ spectrumDecayCoefficient / 7 := by have := spectrumDecayCoefficient_pos; positivity
    have hM : 0 < ∫ u, tiltedUnitSpline u ^ 2 := integral_tiltedUnitSpline_sq_pos
    calc
      _ ≤ 2 / (∫ u, tiltedUnitSpline u ^ 2) * (1 / ((n : ℝ) + 1)) *
          ((spectrumDecayCoefficient / 7) * (((n : ℝ) + 1) ^ (-7 : ℝ) * c ^ (-7 : ℝ))) :=
        mul_le_mul_of_nonneg_left ht (by positivity)
      _ ≤ 2 / (∫ u, tiltedUnitSpline u ^ 2) * (1 / ((n : ℝ) + 1)) *
          ((spectrumDecayCoefficient / 7) * ((1 / ((n : ℝ) + 1)) * c ^ (-7 : ℝ))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hp (by positivity)) hA) (by positivity)
      _ = _ := by dsimp only [D]; ring
  calc
    _ ≤ ∑ n ∈ range K, D * (1 / ((n : ℝ) + 1) ^ 2) := sum_le_sum fun n _ => hterm n
    _ = D * ∑ n ∈ range K, 1 / ((n : ℝ) + 1) ^ 2 := (mul_sum _ _ _).symm
    _ ≤ D * 2 := mul_le_mul_of_nonneg_left (sum_inverse_squares_le_two K) hD
    _ = _ := by dsimp only [D, poleDecayCoefficient]; ring

private theorem tilted_conductor_le_pole {c : ℝ} (hc : 0 < c) {m : ℕ} (hm : 0 < m) :
    completedConductorEnergy tiltedUnitSpline c m ≤
      ((m : ℝ) / m.totient) * completedConductorEnergy tiltedUnitSpline (c / m) 1 := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have htot : (0 : ℝ) < m.totient := by exact_mod_cast Nat.totient_pos.mpr hm
  have hM := integral_tiltedUnitSpline_sq_pos
  have h1 := hasSum_completedConductorEnergy contDiff_tiltedUnitSpline tiltedUnitSpline_eq_zero
    hM hc hm
  have h2 := (hasSum_tilted_pole (div_pos hc hm0)).mul_left ((m : ℝ) / m.totient)
  refine hasSum_le (fun n => ?_) h1 h2
  have hT : 0 ≤ ∫ t in Ioi (((n : ℝ) + 1) * (c / m)), shellSpectrum tiltedUnitSpline t :=
    setIntegral_nonneg measurableSet_Ioi fun t _ => shellSpectrum_nonneg t
  rw [show ((n : ℝ) + 1) * c / m = ((n : ℝ) + 1) * (c / m) by ring]
  split_ifs
  · apply le_of_eq
    field_simp
  · positivity

/-- The explicit seventh-power upper coefficient of a completed conductor. -/
def tiltedConductorUpperCoefficient (m : ℕ) : ℝ := poleDecayCoefficient * (m : ℝ) ^ 8 / m.totient

theorem tiltedConductorUpperCoefficient_pos {m : ℕ} (hm : 0 < m) :
    0 < tiltedConductorUpperCoefficient m := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have htot : (0 : ℝ) < m.totient := by exact_mod_cast Nat.totient_pos.mpr hm
  unfold tiltedConductorUpperCoefficient
  exact div_pos (mul_pos poleDecayCoefficient_pos (pow_pos hm0 8)) htot

/-- Every fixed conductor has matching seventh-power overlap bounds on its literal energy. -/
theorem tiltedConductorEnergy_two_sided {m : ℕ} (hm : 0 < m) {c : ℝ} (hmc : (m : ℝ) ≤ c) :
    tiltedConductorFloorCoefficient / c ^ 7 ≤ completedConductorEnergy tiltedUnitSpline c m ∧
      completedConductorEnergy tiltedUnitSpline c m ≤ tiltedConductorUpperCoefficient m / c ^ 7 := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hc1 := hm1.trans hmc
  have hc0 : 0 < c := hm0.trans_le hmc
  refine ⟨tiltedUnitSpline_completedConductorEnergy_ge_polynomial_floor hc1 hm, ?_⟩
  have hy : 1 ≤ c / m := (le_div_iff₀ hm0).mpr (by simpa using hmc)
  have h := mul_le_mul_of_nonneg_left (tilted_pole_energy_upper hy)
    (div_nonneg hm0.le (Nat.cast_nonneg _))
  refine (tilted_conductor_le_pole hc0 hm).trans (h.trans_eq ?_)
  rw [Real.rpow_neg (div_pos hc0 hm0).le, show (c / (m : ℝ)) ^ (7 : ℝ) =
    (c / m) ^ (7 : ℕ) by norm_cast]
  unfold tiltedConductorUpperCoefficient
  field_simp
  <;> ring

private theorem tiltedConductorEnergy_ratio_le {m l : ℕ} (hm : 0 < m) (hl : 0 < l)
    {c : ℝ} (hmc : (m : ℝ) ≤ c) (hlc : (l : ℝ) ≤ c) :
    completedConductorEnergy tiltedUnitSpline c m / completedConductorEnergy tiltedUnitSpline c l ≤
      tiltedConductorUpperCoefficient m / tiltedConductorFloorCoefficient := by
  have hc : 0 < c := (show (0 : ℝ) < m by exact_mod_cast hm).trans_le hmc
  have hfloor := (tiltedConductorEnergy_two_sided hl hlc).1
  have hlow : 0 < tiltedConductorFloorCoefficient / c ^ 7 :=
    div_pos tiltedConductorFloorCoefficient_pos (pow_pos hc 7)
  have hE := hlow.trans_le hfloor
  calc
    _ ≤ (tiltedConductorUpperCoefficient m / c ^ 7) /
        completedConductorEnergy tiltedUnitSpline c l :=
      div_le_div_of_nonneg_right (tiltedConductorEnergy_two_sided hm hmc).2 hE.le
    _ ≤ (tiltedConductorUpperCoefficient m / c ^ 7) / (tiltedConductorFloorCoefficient / c ^ 7) :=
      div_le_div_of_nonneg_left (by have := tiltedConductorUpperCoefficient_pos hm; positivity) hlow hfloor
    _ = _ := by field_simp

/-- One finite constant bounds every energy ratio in a fixed finite positive-conductor family. -/
theorem exists_finite_conductor_energy_ratio_bound (S : Finset ℕ) (hS : ∀ m ∈ S, 0 < m) :
    ∃ R : ℝ, 0 < R ∧ ∀ c : ℝ, (∀ m ∈ S, (m : ℝ) ≤ c) → ∀ m ∈ S, ∀ l ∈ S,
      completedConductorEnergy tiltedUnitSpline c m / completedConductorEnergy tiltedUnitSpline c l ≤ R := by
  let R := (∑ m ∈ S, tiltedConductorUpperCoefficient m) / tiltedConductorFloorCoefficient + 1
  have hs : 0 ≤ ∑ m ∈ S, tiltedConductorUpperCoefficient m :=
    sum_nonneg fun m hm => (tiltedConductorUpperCoefficient_pos (hS m hm)).le
  refine ⟨R, by dsimp only [R]; have := tiltedConductorFloorCoefficient_pos; positivity, ?_⟩
  intro c hc m hm l hl
  refine (tiltedConductorEnergy_ratio_le (hS m hm) (hS l hl) (hc m hm) (hc l hl)).trans ?_
  have hsum : tiltedConductorUpperCoefficient m ≤ ∑ j ∈ S, tiltedConductorUpperCoefficient j :=
    single_le_sum (fun j hj => (tiltedConductorUpperCoefficient_pos (hS j hj)).le) hm
  have h := div_le_div_of_nonneg_right hsum tiltedConductorFloorCoefficient_pos.le
  dsimp only [R]
  linarith only [h]

#print axioms tiltedConductorEnergy_two_sided
#print axioms exists_finite_conductor_energy_ratio_bound

end GaloisForLFunctions.CompletedArithmeticForms
