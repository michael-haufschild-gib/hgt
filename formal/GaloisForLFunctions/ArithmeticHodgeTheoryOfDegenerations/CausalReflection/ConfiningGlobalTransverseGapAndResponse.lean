import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.ConfiningHalfLineGroundEnergyCurvature
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.ConfiningHalfLineGroundStateRigidity
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.CriticalHalfLineEnergyBranch
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.CriticalHalfLineGroundEnergyDerivative
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# Global transverse spectral gap and Lipschitz parameter response at every positive ratio

At every positive confinement ratio `R > 0`, subtracting the attained floor
`criticalHalfLineGroundEnergy R` times ordinary square mass produces a nonnegative
quadratic form `confiningShiftedEnergy R` whose kernel is the unique minimizing line.
Compactness on the actual Gamma domain and uniqueness up to sign yield a strictly
positive eighth-exponential spectral gap on the ordinary-`L²` orthogonal complement.

From this global transverse gap follow:
1. Quadratic tangent control and continuous differentiability of
   `criticalHalfLineGroundEnergy` (`R > 0`) and `confiningHalfLineGroundEnergy` (`t > 0`)
   everywhere on `(0, ∞)`, with no finite-threshold hypothesis.
2. Optimal local Lipschitz stability (`O(|a(S) - a(R)|²)` in squared eighth-exponential
   norm) of the sign-aligned minimizer, its eighth-exponential mass, its polar source
   pairing, and the ground-energy derivatives (`C^{1,1}_loc` regularity on `(0, ∞)`).
-/

noncomputable section
open MeasureTheory Set Filter Topology Zeta23
open _root_.RHTower

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
open CriticalArithmeticCorrelationTheory ArithmeticCastelnuovoSeveri
  ArithmeticPositivityTheory SpacingScaleHarmonicAnalysis WindowTowerOfSpecZ
  CohomologyOfWindowsOfSpecZ

/-- The half-line energy shifted by its attained unit-mass variational floor. -/
def confiningShiftedEnergy (R : ℝ) (G : ℝ → ℝ) : ℝ :=
  criticalHalfLineFullEnergy R G - criticalHalfLineGroundEnergy R * (∫ u, G u ^ 2)

theorem confiningShiftedEnergy_nonneg {R : ℝ} (hR : 0 < R) {G : ℝ → ℝ}
    (hG : CriticalHalfLineEnergyDomain G) :
    0 ≤ confiningShiftedEnergy R G :=
  sub_nonneg.mpr (criticalHalfLineGroundEnergy_mul_mass_le_all hR hG)

theorem confiningShiftedEnergy_const_mul (R c : ℝ) (G : ℝ → ℝ) :
    confiningShiftedEnergy R (fun u => c * G u) = c ^ 2 * confiningShiftedEnergy R G := by
  unfold confiningShiftedEnergy
  simp_rw [criticalHalfLineFullEnergy_const_mul, mul_pow, integral_const_mul]
  ring

theorem IsHalfLineEnergyMinimizer.shiftedEnergy_eq_zero {R : ℝ} {F : ℝ → ℝ}
    (hF : IsHalfLineEnergyMinimizer R F) :
    confiningShiftedEnergy R F = 0 := by
  unfold confiningShiftedEnergy
  rw [hF.2.1, hF.2.2, mul_one, sub_self]

private theorem pair_integrable_domain {F G : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) (hG : CriticalHalfLineEnergyDomain G) :
    Integrable (fun u => F u * G u) :=
  HTGeometry.integrable_mul_of_sq_integrable hF.meas.aestronglyMeasurable
    hG.meas.aestronglyMeasurable hF.sq hG.sq

theorem IsHalfLineEnergyMinimizer.neutralPart_orthogonal {R : ℝ} {F G : ℝ → ℝ}
    (hF : IsHalfLineEnergyMinimizer R F) (hG : CriticalHalfLineEnergyDomain G) :
    (∫ u, F u * criticalHalfLineNeutralPart F G u) = 0 := by
  have heq : (fun u => F u * criticalHalfLineNeutralPart F G u) =
      fun u => F u * G u - (∫ v, F v * G v) * F u ^ 2 := by
    funext u
    dsimp only [criticalHalfLineNeutralPart]
    ring
  rw [heq, integral_sub (pair_integrable_domain hF.1 hG) (hF.1.sq.const_mul _),
    integral_const_mul, hF.2.1, mul_one, sub_self]

theorem IsHalfLineEnergyMinimizer.neutralPart_square_mass {R : ℝ} {F G : ℝ → ℝ}
    (hF : IsHalfLineEnergyMinimizer R F) (hG : CriticalHalfLineEnergyDomain G)
    (hm : (∫ u, G u ^ 2) = 1) :
    (∫ u, criticalHalfLineNeutralPart F G u ^ 2) = 1 - (∫ u, F u * G u) ^ 2 := by
  have hpair := pair_integrable_domain hF.1 hG
  have heq : (fun u => criticalHalfLineNeutralPart F G u ^ 2) =
      fun u => (G u ^ 2 - (2 * (∫ v, F v * G v)) * (F u * G u)) +
        (∫ v, F v * G v) ^ 2 * F u ^ 2 := by
    funext u
    dsimp only [criticalHalfLineNeutralPart]
    ring
  have hdiff : Integrable (fun u => G u ^ 2 -
      (2 * (∫ v, F v * G v)) * (F u * G u)) := hG.sq.sub (hpair.const_mul _)
  rw [heq, integral_add hdiff (hF.1.sq.const_mul _),
    integral_sub hG.sq (hpair.const_mul _), integral_const_mul, integral_const_mul,
    hm, hF.2.1]
  ring

theorem IsHalfLineEnergyMinimizer.exponential_mass_neutral_decomposition {R : ℝ} {F G : ℝ → ℝ}
    (hF : IsHalfLineEnergyMinimizer R F) (hG : CriticalHalfLineEnergyDomain G) :
    (∫ u, G u ^ 2 * Real.exp (-(8 * u))) =
      (∫ u, criticalHalfLineNeutralPart F G u ^ 2 * Real.exp (-(8 * u))) +
        2 * (∫ v, F v * G v) * criticalHalfLineExponentialPair (criticalHalfLineNeutralPart F G) F +
        (∫ v, F v * G v) ^ 2 * (∫ u, F u ^ 2 * Real.exp (-(8 * u))) := by
  have h := criticalHalfLine_exponential_mass_add_const_mul (hF.1.neutralPart hG) hF.1
    (∫ v, F v * G v)
  have heq (u : ℝ) : criticalHalfLineNeutralPart F G u + (∫ v, F v * G v) * F u = G u :=
    sub_add_cancel _ _
  simpa only [heq] using h

/-- Projecting out a normalized confining minimizer preserves the shifted energy. -/
theorem IsHalfLineEnergyMinimizer.shiftedEnergy_neutralPart
    {R : ℝ} (hR : 0 < R) {F G : ℝ → ℝ}
    (hF : IsHalfLineEnergyMinimizer R F) (hG : CriticalHalfLineEnergyDomain G) :
    confiningShiftedEnergy R (criticalHalfLineNeutralPart F G) = confiningShiftedEnergy R G := by
  let c : ℝ := -(∫ v, F v * G v)
  have he := criticalHalfLineFullEnergy_add_const_mul R hG hF.1 c
  have hm := criticalHalfLine_square_mass_add_const_mul hG hF.1 c
  have hsymm : criticalHalfLineMixedEnergy R G F = criticalHalfLineMixedEnergy R F G :=
    criticalHalfLineMixedEnergy_symm R hG hF.1
  have hcomm : (∫ u, G u * F u) = ∫ u, F u * G u :=
    integral_congr_ae (Eventually.of_forall fun u => mul_comm _ _)
  rw [hsymm, hF.weakEquation hR hG, hF.2.2] at he
  rw [hcomm, hF.2.1] at hm
  have hfun : (fun u => G u + c * F u) = criticalHalfLineNeutralPart F G := by
    funext u
    dsimp only [criticalHalfLineNeutralPart, c]
    ring
  have hm' : (∫ u, criticalHalfLineNeutralPart F G u ^ 2) =
      ((∫ u, G u ^ 2) + 2 * c * ∫ u, F u * G u) + c ^ 2 * 1 := by
    simpa only [← congrFun hfun] using hm
  rw [hfun] at he
  unfold confiningShiftedEnergy
  rw [he, hm']
  dsimp only [c]
  ring

/-- The shifted energy controls the eighth-exponential mass up to an ordinary `L²` remainder. -/
theorem confiningShiftedEnergy_coercive_remainder {R : ℝ} (hR : 0 < R) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ {G : ℝ → ℝ}, CriticalHalfLineEnergyDomain G →
      (criticalAliasCoefficient R / 2) * (∫ u, G u ^ 2 * Real.exp (-(8 * u))) ≤
        confiningShiftedEnergy R G + B * ∫ u, G u ^ 2 := by
  obtain ⟨B₀, hB₀, hgard⟩ := criticalHalfLineFullEnergy_coercive_remainder hR
  refine ⟨B₀ + |criticalHalfLineGroundEnergy R|, add_nonneg hB₀ (abs_nonneg _), ?_⟩
  intro G hG
  have hm : 0 ≤ ∫ u, G u ^ 2 := integral_nonneg fun u => sq_nonneg _
  have habs := mul_le_mul_of_nonneg_right (le_abs_self (criticalHalfLineGroundEnergy R)) hm
  have hg := hgard hG
  unfold confiningShiftedEnergy
  nlinarith only [hg, habs]

private theorem tendsto_pair_diff_domain {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F)
    {U V : ℕ → ℝ → ℝ} (hU : ∀ n, CriticalHalfLineEnergyDomain (U n))
    (hV : ∀ n, CriticalHalfLineEnergyDomain (V n))
    (hd : Tendsto (fun n => ∫ u, (U n u - V n u) ^ 2) atTop (𝓝 0)) :
    Tendsto (fun n => (∫ u, F u * U n u) - ∫ u, F u * V n u) atTop (𝓝 0) := by
  have hdiff (n : ℕ) : CriticalHalfLineEnergyDomain (fun u => U n u - V n u) := by
    simpa only [neg_one_mul, sub_eq_add_neg] using (hU n).add_const_mul (hV n) (-1)
  have hs : Tendsto (fun n => Real.sqrt ((∫ u, F u ^ 2) *
      ∫ u, (U n u - V n u) ^ 2)) atTop (𝓝 0) := by
    simpa only [mul_zero, Real.sqrt_zero] using (hd.const_mul (∫ u, F u ^ 2)).sqrt
  have hp : Tendsto (fun n => ∫ u, F u * (U n u - V n u)) atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun n => ?_) hs
    simpa only [Real.norm_eq_abs] using HTGeometry.abs_integral_mul_le_sqrt
      hF.meas.aestronglyMeasurable (hdiff n).meas.aestronglyMeasurable
      hF.sq (hdiff n).sq
  have he (n : ℕ) : (∫ u, F u * (U n u - V n u)) =
      (∫ u, F u * U n u) - ∫ u, F u * V n u := by
    simp_rw [mul_sub]
    exact integral_sub (pair_integrable_domain hF (hU n)) (pair_integrable_domain hF (hV n))
  simpa only [he] using hp

/-- At every positive confinement ratio `R > 0`, the shifted energy has a strictly positive
ordinary `L²` spectral gap transverse to the unique minimizing line. -/
theorem IsHalfLineEnergyMinimizer.transverse_L2_gap
    {R : ℝ} (hR : 0 < R) {F : ℝ → ℝ} (hF : IsHalfLineEnergyMinimizer R F) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ {G : ℝ → ℝ}, CriticalHalfLineEnergyDomain G →
      (∫ u, F u * G u) = 0 → δ * (∫ u, G u ^ 2) ≤ confiningShiftedEnergy R G := by
  by_contra hnot
  push Not at hnot
  let e : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hepos (n : ℕ) : 0 < e n := by dsimp only [e]; positivity
  have hele (n : ℕ) : e n ≤ 1 := by
    dsimp only [e]
    exact div_le_one_of_le₀ (by linarith only [Nat.cast_nonneg (α := ℝ) n]) (by positivity)
  have helim : Tendsto e atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hnormalized (n : ℕ) : ∃ G : ℝ → ℝ, CriticalHalfLineEnergyDomain G ∧
      (∫ u, G u ^ 2) = 1 ∧ (∫ u, F u * G u) = 0 ∧
      confiningShiftedEnergy R G < e n := by
    obtain ⟨G, hdG, horth, hE⟩ := hnot (e n) (hepos n)
    have hE0 := confiningShiftedEnergy_nonneg hR hdG
    let m : ℝ := ∫ u, G u ^ 2
    have hm : 0 < m := by
      by_contra hn
      have hmn : m = 0 := le_antisymm (not_lt.mp hn) (integral_nonneg fun u => sq_nonneg _)
      change confiningShiftedEnergy R G < e n * m at hE
      rw [hmn, mul_zero] at hE
      exact (not_lt_of_ge hE0) hE
    let c : ℝ := (Real.sqrt m)⁻¹
    have hc : 0 < c := inv_pos.mpr (Real.sqrt_pos.mpr hm)
    have hcm : c ^ 2 * m = 1 := by
      calc
        _ = c ^ 2 * (Real.sqrt m) ^ 2 := by rw [Real.sq_sqrt hm.le]
        _ = 1 := by
          dsimp only [c]
          rw [inv_pow, inv_mul_cancel₀ (pow_ne_zero 2 (Real.sqrt_pos.mpr hm).ne')]
    refine ⟨fun u => c * G u, hdG.const_mul c, ?_, ?_, ?_⟩
    · simp_rw [mul_pow]
      rw [integral_const_mul]
      exact hcm
    · have heq : (fun u => F u * (c * G u)) = fun u => c * (F u * G u) :=
        funext fun u => by ring
      rw [heq, integral_const_mul, horth, mul_zero]
    · rw [confiningShiftedEnergy_const_mul]
      have hh := mul_lt_mul_of_pos_left hE (sq_pos_of_pos hc)
      have heq : c ^ 2 * (e n * m) = e n := by rw [mul_left_comm, hcm, mul_one]
      exact hh.trans_eq heq
  choose G hdG hnG hoG heG using hnormalized
  obtain ⟨B, hB, hgarding⟩ := confiningShiftedEnergy_coercive_remainder hR
  have ha := criticalAliasCoefficient_positive hR
  let M : ℝ := (1 + B) / (criticalAliasCoefficient R / 2)
  have hM : 0 ≤ M := div_nonneg (by linarith only [hB]) (half_pos ha).le
  have hG8 (n : ℕ) : (∫ u, G n u ^ 2 * Real.exp (-(8 * u))) ≤ M := by
    apply (le_div_iff₀ (half_pos ha)).mpr
    have h := hgarding (hdG n)
    rw [hnG n, mul_one] at h
    nlinarith only [h, (heG n).le, hele n]
  have hrec (n : ℕ) := exists_window_energy_recovery hR (hdG n) (hnG n).le (hepos n)
  choose A H hA hHwin hnH hdH hH8 heH using hrec
  have hDH (n : ℕ) := criticalHalfLineEnergyDomain_of_window (hHwin n)
  have hdiff (n : ℕ) : CriticalHalfLineEnergyDomain (fun u => H n u - G n u) := by
    simpa only [neg_one_mul, sub_eq_add_neg] using (hDH n).add_const_mul (hdG n) (-1)
  have herr : Tendsto (fun n => ∫ u, (H n u - G n u) ^ 2) atTop (𝓝 0) :=
    squeeze_zero (fun n => integral_nonneg fun u => sq_nonneg _) (fun n => (hdH n).le) helim
  have hmasslim : Tendsto (fun n => ∫ u, H n u ^ 2) atTop (𝓝 1) := by
    have h := HTGeometry.tendsto_integral_sq_add_of_tendsto_zero
      (Eventually.of_forall fun n => (hdG n).meas.aestronglyMeasurable)
      (Eventually.of_forall fun n => (hdiff n).meas.aestronglyMeasurable)
      (Eventually.of_forall fun n => (hdG n).sq)
      (Eventually.of_forall fun n => (hdiff n).sq)
      (show Tendsto (fun n => ∫ u, G n u ^ 2) atTop (𝓝 1) by
        simpa only [hnG] using (tendsto_const_nhds (x := (1 : ℝ)))) herr
    exact h.congr fun n => integral_congr_ae (Eventually.of_forall fun u => by congr 1; ring)
  let lamR : ℝ := criticalHalfLineGroundEnergy R
  have hEs_upper (n : ℕ) : criticalHalfLineFullEnergy R (H n) ≤ lamR + 2 * e n := by
    have hh := heH n
    have hq := heG n
    unfold confiningShiftedEnergy at hq
    rw [hnG n, mul_one] at hq
    linarith only [hh, hq]
  have hEs_lower (n : ℕ) : lamR * (∫ u, H n u ^ 2) ≤ criticalHalfLineFullEnergy R (H n) :=
    criticalHalfLineGroundEnergy_mul_mass_le_all hR (hDH n)
  have hElim : Tendsto (fun n => criticalHalfLineFullEnergy R (H n)) atTop (𝓝 lamR) := by
    have hlow_lim : Tendsto (fun n => lamR * ∫ u, H n u ^ 2) atTop (𝓝 lamR) := by
      simpa only [mul_one] using hmasslim.const_mul lamR
    have hup_lim : Tendsto (fun n => lamR + 2 * e n) atTop (𝓝 lamR) := by
      simpa only [mul_zero, add_zero] using (helim.const_mul 2).const_add lamR
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlow_lim hup_lim hEs_lower hEs_upper
  obtain ⟨K, s, hs, hDK, hnormK, hEK, _, hL2, _⟩ :=
    exists_domain_limit_of_smooth_energy_limit hR hDH
      (fun n => (hHwin n).contDiff) (fun n => (hHwin n).hasCompactSupport)
      (fun n => (hnH n).trans (hnG n).le) hmasslim
      (mul_nonneg (by norm_num) hM)
      (fun n => (hH8 n).trans (mul_le_mul_of_nonneg_left (hG8 n) (by norm_num)))
      (B := lamR + 2) (fun n => (hEs_upper n).trans (by linarith only [hele n])) hElim
  have hKmin : IsHalfLineEnergyMinimizer R K :=
    ⟨hDK, hnormK, le_antisymm hEK (criticalHalfLineGroundEnergy_le hR hDK hnormK)⟩
  have hpair0 := tendsto_pair_diff_domain hF.1 hDH hdG herr
  simp only [hoG, sub_zero] at hpair0
  have hpair := tendsto_pair_diff_domain hF.1 (fun n => hDH (s n)) (fun _ => hDK) hL2
  have hpairlim := hpair.add_const (∫ u, F u * K u)
  simp only [sub_add_cancel, zero_add] at hpairlim
  have horth : (∫ u, F u * K u) = 0 :=
    tendsto_nhds_unique hpairlim (hpair0.comp hs.tendsto_atTop)
  rcases halfLineEnergyMinimizer_unique_up_to_sign hR hKmin hF with heq | heq
  · have hm : (∫ u, F u * K u) = ∫ u, F u ^ 2 := by
      apply integral_congr_ae
      filter_upwards [heq] with u hu
      rw [hu, pow_two]
    rw [horth, hF.2.1] at hm
    norm_num at hm
  · have hm : (∫ u, F u * K u) = -(∫ u, F u ^ 2) := by
      rw [← integral_neg]
      apply integral_congr_ae
      filter_upwards [heq] with u hu
      rw [hu]
      ring
    rw [horth, hF.2.1] at hm
    norm_num at hm

/-- At every positive confinement ratio `R > 0`, the shifted energy controls the full
eighth-exponential mass on the ordinary-`L²` orthogonal complement of its minimizer. -/
theorem IsHalfLineEnergyMinimizer.transverse_exponential_gap
    {R : ℝ} (hR : 0 < R) {F : ℝ → ℝ} (hF : IsHalfLineEnergyMinimizer R F) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ {G : ℝ → ℝ}, CriticalHalfLineEnergyDomain G →
      (∫ u, F u * G u) = 0 → γ * (∫ u, G u ^ 2 * Real.exp (-(8 * u))) ≤
        confiningShiftedEnergy R G := by
  obtain ⟨δ, hδ, hgap⟩ := hF.transverse_L2_gap hR
  obtain ⟨B, hB, hgard⟩ := confiningShiftedEnergy_coercive_remainder hR
  have ha := criticalAliasCoefficient_positive hR
  have hden : 0 < δ + B := add_pos_of_pos_of_nonneg hδ hB
  refine ⟨δ * (criticalAliasCoefficient R / 2) / (δ + B), by positivity, ?_⟩
  intro G hG ho
  have hg := mul_le_mul_of_nonneg_left (hgard hG) hδ.le
  have hl := mul_le_mul_of_nonneg_left (hgap hG ho) hB
  calc
    _ = (δ * (criticalAliasCoefficient R / 2) *
        (∫ u, G u ^ 2 * Real.exp (-(8 * u)))) / (δ + B) := by ring
    _ ≤ _ := (div_le_iff₀ hden).mpr (by nlinarith only [hg, hl])

/-- At every positive confinement ratio `R > 0`, the shifted energy dominates a positive
multiple of the eighth-exponential norm of the neutral component `G - (∫ F G) F`. -/
theorem IsHalfLineEnergyMinimizer.controls_neutralPart
    {R : ℝ} (hR : 0 < R) {F : ℝ → ℝ} (hF : IsHalfLineEnergyMinimizer R F) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ {G : ℝ → ℝ}, CriticalHalfLineEnergyDomain G →
      γ * (∫ u, criticalHalfLineNeutralPart F G u ^ 2 * Real.exp (-(8 * u))) ≤
        confiningShiftedEnergy R G := by
  obtain ⟨γ, hγ, hgap⟩ := hF.transverse_exponential_gap hR
  refine ⟨γ, hγ, ?_⟩
  intro G hG
  have h := hgap (hF.1.neutralPart hG) (hF.neutralPart_orthogonal hG)
  rwa [hF.shiftedEnergy_neutralPart hR hG] at h

private theorem shifted_tangent_algebra {ES lamR Q η w m n q c γ : ℝ}
    (hγ : 0 < γ) (hw : 0 ≤ w) (hm : 0 ≤ m) (hn : 0 ≤ n)
    (hmn : m ≤ n) (hmass : m = 1 - c ^ 2)
    (hQ : γ * n ≤ Q) (he : ES = lamR + Q + η * (n + 2 * c * q + (1 - m) * w))
    (hsmall : |η| * (1 + w) ≤ γ / 2)
    (hpos : 0 ≤ n + 2 * (2 * η * c / γ) * q + (2 * η * c / γ) ^ 2 * w) :
    lamR + η * w - (2 * w / γ) * η ^ 2 ≤ ES := by
  have hc : c ^ 2 ≤ 1 := by linarith only [hmass, hm]
  have hC : 0 ≤ 2 * w / γ := by positivity
  have hy := mul_nonneg (half_pos hγ).le hpos
  have hid : γ / 2 * (n + 2 * (2 * η * c / γ) * q + (2 * η * c / γ) ^ 2 * w) =
      γ / 2 * n + 2 * η * c * q + (2 * w / γ) * η ^ 2 * c ^ 2 := by
    field_simp [hγ.ne']
  rw [hid] at hy
  have h1 := mul_le_mul_of_nonneg_right (neg_abs_le η) hn
  have h2 := mul_le_mul_of_nonneg_right (le_abs_self η) (mul_nonneg hw hm)
  have h3 := mul_le_mul_of_nonneg_left hmn (mul_nonneg (abs_nonneg η) hw)
  have h4 := mul_le_mul_of_nonneg_right hsmall hn
  have h5 := mul_le_mul_of_nonneg_left hc (mul_nonneg hC (sq_nonneg η))
  nlinarith only [he, hQ, hy, h1, h2, h3, h4, h5]

/-- Quadratic tangent approximation of `criticalHalfLineGroundEnergy` around any `R > 0`. -/
theorem IsHalfLineEnergyMinimizer.quadratic_tangent
    {R : ℝ} (hR : 0 < R) {F : ℝ → ℝ} (hF : IsHalfLineEnergyMinimizer R F) :
    ∃ δ C : ℝ, 0 < δ ∧ 0 ≤ C ∧ ∀ S : ℝ, 0 < S →
      |criticalAliasCoefficient S - criticalAliasCoefficient R| ≤ δ →
      |criticalHalfLineGroundEnergy S - criticalHalfLineGroundEnergy R -
        (criticalAliasCoefficient S - criticalAliasCoefficient R) *
          (∫ u, F u ^ 2 * Real.exp (-(8 * u)))| ≤
            C * (criticalAliasCoefficient S - criticalAliasCoefficient R) ^ 2 := by
  obtain ⟨γ, hγ, hgap⟩ := hF.controls_neutralPart hR
  let w : ℝ := ∫ u, F u ^ 2 * Real.exp (-(8 * u))
  have hw : 0 ≤ w := integral_nonneg fun u => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le
  have hC : 0 ≤ 2 * w / γ := div_nonneg (mul_nonneg (by norm_num) hw) hγ.le
  refine ⟨γ / (2 * (1 + w)), 2 * w / γ, by positivity, hC, ?_⟩
  intro S hS hsmall
  let η : ℝ := criticalAliasCoefficient S - criticalAliasCoefficient R
  have hnonempty : ({e : ℝ | ∃ G : ℝ → ℝ, CriticalHalfLineEnergyDomain G ∧
      (∫ u, G u ^ 2) = 1 ∧ criticalHalfLineFullEnergy S G = e} : Set ℝ).Nonempty :=
    ⟨criticalHalfLineFullEnergy S F, F, hF.1, hF.2.1, rfl⟩
  have hlower : criticalHalfLineGroundEnergy R + η * w - (2 * w / γ) * η ^ 2 ≤
      criticalHalfLineGroundEnergy S := by
    apply le_csInf hnonempty
    rintro _ ⟨G, hG, hm, rfl⟩
    let c : ℝ := ∫ u, F u * G u
    let N : ℝ → ℝ := criticalHalfLineNeutralPart F G
    let m : ℝ := ∫ u, N u ^ 2
    let n : ℝ := ∫ u, N u ^ 2 * Real.exp (-(8 * u))
    let q : ℝ := criticalHalfLineExponentialPair N F
    have hdN : CriticalHalfLineEnergyDomain N := hF.1.neutralPart hG
    have hm0 : 0 ≤ m := integral_nonneg fun u => sq_nonneg _
    have hn0 : 0 ≤ n := integral_nonneg fun u => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le
    have hmn : m ≤ n := hdN.square_mass_le_exponential_mass
    have hmass : m = 1 - c ^ 2 := hF.neutralPart_square_mass hG hm
    have hc' : c ^ 2 = 1 - m := by linarith only [hmass]
    have hQ : γ * n ≤ confiningShiftedEnergy R G := hgap hG
    have hdecomp : (∫ u, G u ^ 2 * Real.exp (-(8 * u))) = n + 2 * c * q + c ^ 2 * w :=
      hF.exponential_mass_neutral_decomposition hG
    have he0 := criticalHalfLineFullEnergy_change_ratio S R hG
    rw [hdecomp, hc'] at he0
    have he : criticalHalfLineFullEnergy S G =
        criticalHalfLineGroundEnergy R + confiningShiftedEnergy R G +
          η * (n + 2 * c * q + (1 - m) * w) := by
      unfold confiningShiftedEnergy
      rw [hm, mul_one]
      dsimp only [η]
      linarith only [he0]
    change |η| ≤ γ / (2 * (1 + w)) at hsmall
    have hsmall' : |η| * (1 + w) ≤ γ / 2 := by
      have h := (le_div_iff₀ (by positivity : 0 < 2 * (1 + w))).mp hsmall
      linarith only [h]
    have hpos : 0 ≤ ∫ u, (N u + (2 * η * c / γ) * F u) ^ 2 * Real.exp (-(8 * u)) :=
      integral_nonneg fun u => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le
    rw [criticalHalfLine_exponential_mass_add_const_mul hdN hF.1] at hpos
    change 0 ≤ n + 2 * (2 * η * c / γ) * q + (2 * η * c / γ) ^ 2 * w at hpos
    exact shifted_tangent_algebra hγ hw hm0 hn0 hmn hmass hQ he hsmall' hpos
  have hupper : criticalHalfLineGroundEnergy S ≤ criticalHalfLineGroundEnergy R + η * w := by
    have h := criticalHalfLineGroundEnergy_le hS hF.1 hF.2.1
    rwa [criticalHalfLineFullEnergy_change_ratio S R hF.1, hF.2.2] at h
  have herr := mul_nonneg hC (sq_nonneg η)
  exact abs_le.mpr ⟨by linarith only [hlower], by linarith only [hupper, herr]⟩

/-- At every positive confinement ratio `R > 0`, `criticalHalfLineGroundEnergy` is
differentiable with derivative `-(a(R) / R) * ∫ F_R² e^{-8u}`. -/
theorem IsHalfLineEnergyMinimizer.hasDerivAt_criticalHalfLineGroundEnergy
    {R : ℝ} (hR : 0 < R) {F : ℝ → ℝ} (hF : IsHalfLineEnergyMinimizer R F) :
    HasDerivAt criticalHalfLineGroundEnergy
      (-(criticalAliasCoefficient R) *
        (∫ u, F u ^ 2 * Real.exp (-(8 * u))) / R) R := by
  obtain ⟨δ, C, hδ, _, hbound⟩ := hF.quadratic_tangent hR
  have ha := hasDerivAt_criticalAliasCoefficient hR
  have hlim : Tendsto
      (fun S => |criticalAliasCoefficient S - criticalAliasCoefficient R|) (𝓝 R) (𝓝 0) := by
    simpa only [sub_self, abs_zero] using
      (ha.continuousAt.tendsto.sub_const (criticalAliasCoefficient R)).abs
  have hnear : ∀ᶠ S in 𝓝 R, |criticalAliasCoefficient S - criticalAliasCoefficient R| ≤ δ :=
    (hlim.eventually (gt_mem_nhds hδ)).mono fun _ h => h.le
  have hquadratic : ∀ᶠ S in 𝓝 R,
      ‖criticalHalfLineGroundEnergy S - criticalHalfLineGroundEnergy R -
        (∫ u, F u ^ 2 * Real.exp (-(8 * u))) *
          (criticalAliasCoefficient S - criticalAliasCoefficient R)‖ ≤
      C * ‖criticalAliasCoefficient S - criticalAliasCoefficient R‖ ^ 2 := by
    filter_upwards [hnear, (lt_mem_nhds hR : ∀ᶠ S in 𝓝 R, 0 < S)] with S hη hS
    simpa only [Real.norm_eq_abs, sq_abs, mul_comm] using hbound S hS hη
  have h := HTGeometry.hasDerivAt_of_quadratic_comparison ha hquadratic
  convert h using 1
  ring

/-- At every positive confinement strength `t > 0`, `confiningHalfLineGroundEnergy` is
differentiable with strictly positive derivative `a(1) * ∫ F_{t⁻¹}² e^{-8u}`. -/
theorem hasDerivAt_confiningHalfLineGroundEnergy_of_minimizer
    {t : ℝ} (ht : 0 < t) {F : ℝ → ℝ} (hF : IsHalfLineEnergyMinimizer t⁻¹ F) :
    HasDerivAt confiningHalfLineGroundEnergy
      (criticalAliasCoefficient 1 * ∫ u, F u ^ 2 * Real.exp (-(8 * u))) t := by
  have hd := hF.hasDerivAt_criticalHalfLineGroundEnergy (inv_pos.mpr ht)
  have hcomp := hd.comp t (hasDerivAt_inv ht.ne')
  change HasDerivAt confiningHalfLineGroundEnergy _ t at hcomp
  refine hcomp.congr_deriv ?_
  rw [criticalAliasCoefficient_inv]
  field_simp [ht.ne']

/-- Response constant `(1 + 3w + √(2J))(1 + 6(1 + w)w/γ)` of the Lipschitz stability estimate,
where `J = ∫ (e^{-|u|} polarSourceProfile u)²` is the fixed polar weight mass. -/
def confiningResponseConstant (γ w : ℝ) : ℝ :=
  (1 + 3 * w + Real.sqrt (2 * ∫ u, (Real.exp (-|u|) * polarSourceProfile u) ^ 2)) *
    (1 + 6 * (1 + w) * w / γ)

theorem confiningResponseConstant_nonneg {γ w : ℝ} (hγ : 0 < γ) (hw : 0 ≤ w) :
    0 ≤ confiningResponseConstant γ w := by
  unfold confiningResponseConstant
  positivity

theorem confiningResponseConstant_mono {γ w w' : ℝ} (hγ : 0 < γ) (hw : 0 ≤ w) (hww : w ≤ w') :
    confiningResponseConstant γ w ≤ confiningResponseConstant γ w' := by
  unfold confiningResponseConstant
  have hJ := Real.sqrt_nonneg (2 * ∫ u, (Real.exp (-|u|) * polarSourceProfile u) ^ 2)
  have hprod : (1 + w) * w ≤ (1 + w') * w' := by nlinarith only [hw, hww]
  have h2 : 1 + 6 * (1 + w) * w / γ ≤ 1 + 6 * (1 + w') * w' / γ := by
    have h := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hprod (by norm_num : (0 : ℝ) ≤ 6))
      hγ.le
    rw [mul_assoc 6 (1 + w), mul_assoc 6 (1 + w')]
    linarith only [h]
  have h2pos : 0 ≤ 1 + 6 * (1 + w) * w / γ := by positivity
  exact mul_le_mul (by linarith only [hww]) h2 h2pos (by linarith only [hJ, hw, hww])

/-- Quantitative Lipschitz response around a ratio `R` from an explicit neutral-part control
constant `γ` of the minimizer `F`: the admissible radius `γ / (8w(1 + w))` and the response
constant depend only on `γ` and on the exponential mass `w` of `F`. -/
theorem IsHalfLineEnergyMinimizer.minimizer_lipschitz_stability_of_control
    {R : ℝ} {F : ℝ → ℝ} (hF : IsHalfLineEnergyMinimizer R F) {γ : ℝ} (hγ : 0 < γ)
    (hgap : ∀ {G : ℝ → ℝ}, CriticalHalfLineEnergyDomain G →
      γ * (∫ u, criticalHalfLineNeutralPart F G u ^ 2 * Real.exp (-(8 * u))) ≤
        confiningShiftedEnergy R G)
    {S : ℝ} (hS : 0 < S)
    (hsmall : |criticalAliasCoefficient S - criticalAliasCoefficient R| ≤
      γ / (8 * (∫ u, F u ^ 2 * Real.exp (-(8 * u))) *
        (1 + ∫ u, F u ^ 2 * Real.exp (-(8 * u)))))
    {H : ℝ → ℝ} (hH : IsHalfLineEnergyMinimizer S H) :
    ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧
      (∫ u, (H u - σ * F u) ^ 2 * Real.exp (-(8 * u))) ≤
        confiningResponseConstant γ (∫ u, F u ^ 2 * Real.exp (-(8 * u))) ^ 2 *
          (criticalAliasCoefficient S - criticalAliasCoefficient R) ^ 2 ∧
      |(∫ u, H u ^ 2 * Real.exp (-(8 * u))) - (∫ u, F u ^ 2 * Real.exp (-(8 * u)))| ≤
        confiningResponseConstant γ (∫ u, F u ^ 2 * Real.exp (-(8 * u))) *
          |criticalAliasCoefficient S - criticalAliasCoefficient R| ∧
      |(∫ u, H u * polarSourceProfile u) - σ * (∫ u, F u * polarSourceProfile u)| ≤
        confiningResponseConstant γ (∫ u, F u ^ 2 * Real.exp (-(8 * u))) *
          |criticalAliasCoefficient S - criticalAliasCoefficient R| := by
  let w : ℝ := ∫ u, F u ^ 2 * Real.exp (-(8 * u))
  have hw1 : 1 ≤ w := one_le_exponential_square_of_domain hF.1 hF.2.1
  have hw : 0 < w := zero_lt_one.trans_le hw1
  let J : ℝ := ∫ u, (Real.exp (-|u|) * polarSourceProfile u) ^ 2
  have hJ : 0 ≤ J := integral_nonneg fun u => sq_nonneg _
  let K0 : ℝ := 6 * (1 + w) * w / γ
  have hK0 : 0 < K0 := by dsimp only [K0]; positivity
  let L : ℝ := (1 + 3 * w + Real.sqrt (2 * J)) * (1 + K0)
  let η : ℝ := criticalAliasCoefficient S - criticalAliasCoefficient R
  let c : ℝ := ∫ u, F u * H u
  let N : ℝ → ℝ := criticalHalfLineNeutralPart F H
  let m : ℝ := ∫ u, N u ^ 2
  let n : ℝ := ∫ u, N u ^ 2 * Real.exp (-(8 * u))
  let v : ℝ := ∫ u, H u ^ 2 * Real.exp (-(8 * u))
  have hdN : CriticalHalfLineEnergyDomain N := hF.1.neutralPart hH.1
  have hm0 : 0 ≤ m := integral_nonneg fun u => sq_nonneg _
  have hn0 : 0 ≤ n := integral_nonneg fun u => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le
  have hv0 : 0 ≤ v := integral_nonneg fun u => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le
  have hmn : m ≤ n := hdN.square_mass_le_exponential_mass
  have hmass : m = 1 - c ^ 2 := hF.neutralPart_square_mass hH.1 hH.2.1
  have hc : c ^ 2 ≤ 1 := by linarith only [hmass, hm0]
  -- Symmetric variational comparison: Q_R(H) ≤ η * (w - v).
  have hQR : γ * n ≤ confiningShiftedEnergy R H := hgap hH.1
  have hER_H : criticalHalfLineFullEnergy R H = criticalHalfLineGroundEnergy S - η * v := by
    have h := criticalHalfLineFullEnergy_change_ratio S R hH.1
    rw [hH.2.2] at h
    dsimp only [η, v] at h ⊢
    linarith only [h]
  have hlamS_le : criticalHalfLineGroundEnergy S ≤ criticalHalfLineGroundEnergy R + η * w := by
    have h := criticalHalfLineGroundEnergy_le hS hF.1 hF.2.1
    rwa [criticalHalfLineFullEnergy_change_ratio S R hF.1, hF.2.2] at h
  have hsymm : confiningShiftedEnergy R H ≤ η * (w - v) := by
    unfold confiningShiftedEnergy
    rw [hH.2.1, mul_one, hER_H]
    linarith only [hlamS_le]
  -- Crude preliminary bound showing n ≤ 1 on the neighborhood.
  have hrepr (u : ℝ) : N u + c * F u = H u := sub_add_cancel _ _
  have hweighted := criticalHalfLine_exponential_mass_add_const_mul_le hdN hF.1 c
  simp only [hrepr] at hweighted
  change v ≤ 2 * n + 2 * c ^ 2 * w at hweighted
  have hcw := mul_le_mul_of_nonneg_right hc hw.le
  have hvbound : v ≤ 2 * n + 2 * w := by linarith only [hweighted, hcw]
  have hηw := mul_le_mul_of_nonneg_right (le_abs_self η) hw.le
  have hηv := mul_le_mul_of_nonneg_right (neg_abs_le η) hv0
  have hvabs := mul_le_mul_of_nonneg_left hvbound (abs_nonneg η)
  have hcrude : γ * n ≤ |η| * (3 * w + 2 * n) := by
    nlinarith only [hQR, hsymm, hηw, hηv, hvabs]
  change |η| ≤ γ / (8 * w * (1 + w)) at hsmall
  have hsmall_prod : |η| * (8 * w * (1 + w)) ≤ γ :=
    (le_div_iff₀ (by positivity : 0 < 8 * w * (1 + w))).mp hsmall
  have hsmall_4 : |η| ≤ γ / 4 := by
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 4)).mpr
    have h8 : 4 ≤ 8 * w * (1 + w) := by nlinarith only [hw1]
    nlinarith only [hsmall_prod, mul_le_mul_of_nonneg_left h8 (abs_nonneg η)]
  have hn1 : n ≤ 1 := by
    have hsn := mul_le_mul_of_nonneg_right hsmall_4 hn0
    have h6 : 6 * w * |η| ≤ γ := by
      have h68 : 6 * w ≤ 8 * w * (1 + w) := by nlinarith only [hw1]
      nlinarith only [hsmall_prod, mul_le_mul_of_nonneg_right h68 (abs_nonneg η)]
    have hγn : γ * n ≤ γ := by linarith only [hcrude, hsn, h6]
    exact (mul_le_iff_le_one_right hγ).mp hγn
  -- Sign alignment with quadratic scalar residual (c - σ)² ≤ n².
  have hsign : ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ (c - σ) ^ 2 ≤ n ^ 2 := by
    by_cases hcp : 0 ≤ c
    · refine ⟨1, Or.inl rfl, ?_⟩
      have hc1 : c ≤ 1 := by nlinarith only [hc, sq_nonneg (c - 1)]
      have h1mc : 1 - c ≤ m := by nlinarith only [hmass, mul_nonneg hcp (sub_nonneg.mpr hc1)]
      have hle : 1 - c ≤ n := h1mc.trans hmn
      have hpos1 : 0 ≤ 1 - c := sub_nonneg.mpr hc1
      nlinarith only [mul_le_mul hle hle hpos1 hn0]
    · refine ⟨-1, Or.inr rfl, ?_⟩
      have hc1 : -1 ≤ c := by nlinarith only [hc, sq_nonneg (c + 1)]
      have h1pc : 1 + c ≤ m := by
        nlinarith only [hmass, mul_nonneg (neg_nonneg.mpr (le_of_not_ge hcp))
          (show 0 ≤ 1 + c by linarith only [hc1])]
      have hle : 1 + c ≤ n := h1pc.trans hmn
      have hpos1 : 0 ≤ 1 + c := by linarith only [hc1]
      nlinarith only [mul_le_mul hle hle hpos1 hn0]
  obtain ⟨σ, hσ, hσsq⟩ := hsign
  have hσ2 : σ ^ 2 = 1 := by rcases hσ with rfl | rfl <;> norm_num
  have hσn : (c - σ) ^ 2 ≤ n := hσsq.trans (by nlinarith only [hn0, hn1])
  let D : ℝ → ℝ := fun u => H u - σ * F u
  have hD : CriticalHalfLineEnergyDomain D := by
    simpa only [D, neg_mul, sub_eq_add_neg] using hH.1.add_const_mul hF.1 (-σ)
  let d : ℝ := ∫ u, D u ^ 2 * Real.exp (-(8 * u))
  have hd0 : 0 ≤ d := integral_nonneg fun u => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le
  have hdist := criticalHalfLine_exponential_mass_add_const_mul_le hdN hF.1 (c - σ)
  have heqD (u : ℝ) : N u + (c - σ) * F u = D u := by
    dsimp only [N, D, criticalHalfLineNeutralPart, c]
    ring
  simp only [heqD] at hdist
  change d ≤ 2 * n + 2 * (c - σ) ^ 2 * w at hdist
  have hd_le_n : d ≤ 2 * (1 + w) * n := by
    nlinarith only [hdist, mul_le_mul_of_nonneg_right hσn hw.le]
  -- Exact expansion v - w = d + 2 * σ * qD eliminates square roots via quadratic positivity.
  let qD : ℝ := criticalHalfLineExponentialPair D F
  have hvw : v - w = d + 2 * σ * qD := by
    have hexp := criticalHalfLine_exponential_mass_add_const_mul hD hF.1 σ
    have hsumD (u : ℝ) : D u + σ * F u = H u := sub_add_cancel _ _
    simp only [hsumD, hσ2, one_mul] at hexp
    change v = d + 2 * σ * qD + w at hexp
    linarith only [hexp]
  have hsq_cancel : 0 ≤ ∫ u, (D u + (4 * (1 + w) * σ * η / γ) * F u) ^ 2 * Real.exp (-(8 * u)) :=
    integral_nonneg fun u => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le
  rw [criticalHalfLine_exponential_mass_add_const_mul hD hF.1] at hsq_cancel
  change 0 ≤ d + 2 * (4 * (1 + w) * σ * η / γ) * qD +
    (4 * (1 + w) * σ * η / γ) ^ 2 * w at hsq_cancel
  have hscale : 0 < γ / (4 * (1 + w)) := by positivity
  have hmul_sq := mul_nonneg hscale.le hsq_cancel
  have hid_sq : γ / (4 * (1 + w)) *
      (d + 2 * (4 * (1 + w) * σ * η / γ) * qD + (4 * (1 + w) * σ * η / γ) ^ 2 * w) =
      γ / (4 * (1 + w)) * d + 2 * σ * η * qD + (4 * (1 + w) * w / γ) * η ^ 2 := by
    have h1w : 1 + w ≠ 0 := by linarith only [hw1]
    field_simp [hγ.ne', h1w]
    rw [hσ2]
    ring
  rw [hid_sq] at hmul_sq
  have hηd : -η * d ≤ |η| * d := by
    simpa only [neg_mul] using mul_le_mul_of_nonneg_right (neg_le_abs η) hd0
  have hsmall_d : |η| ≤ γ / (8 * (1 + w)) := by
    apply (le_div_iff₀ (by positivity : 0 < 8 * (1 + w))).mpr
    have h8w : 8 * (1 + w) ≤ 8 * w * (1 + w) := by nlinarith only [hw1, mul_nonneg hw.le (by linarith only [hw1] : 0 ≤ 1 + w)]
    nlinarith only [hsmall_prod, mul_le_mul_of_nonneg_right h8w (abs_nonneg η)]
  have hsmall_d_mul := mul_le_mul_of_nonneg_right hsmall_d hd0
  have hγ_step : γ / (2 * (1 + w)) * d ≤ γ * n := by
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (by positivity : 0 < 2 * (1 + w))).mpr
    have h := mul_le_mul_of_nonneg_left hd_le_n hγ.le
    linarith only [h]
  have hcomb : γ / (8 * (1 + w)) * d ≤ (4 * (1 + w) * w / γ) * η ^ 2 := by
    have hsymm' : γ * n ≤ -η * d - 2 * σ * η * qD := by
      have h1 : η * (w - v) = -η * d - 2 * σ * η * qD := by rw [← neg_sub v w, hvw]; ring
      linarith only [hQR, hsymm, h1]
    have hquarter : γ / (2 * (1 + w)) * d - γ / (4 * (1 + w)) * d -
        γ / (8 * (1 + w)) * d = γ / (8 * (1 + w)) * d := by
      have h1w : 1 + w ≠ 0 := by linarith only [hw1]
      field_simp [h1w]
      ring
    linarith only [hγ_step, hsymm', hηd, hmul_sq, hsmall_d_mul, hquarter]
  have hd_lip : d ≤ K0 ^ 2 * η ^ 2 := by
    have hd32 : d ≤ (32 * (1 + w) ^ 2 * w / γ ^ 2) * η ^ 2 := by
      have hpos8 : 0 < 8 * (1 + w) / γ := by positivity
      have hm8 := mul_le_mul_of_nonneg_left hcomb hpos8.le
      have hlhs : 8 * (1 + w) / γ * (γ / (8 * (1 + w)) * d) = d := by
        have h1w : 1 + w ≠ 0 := by linarith only [hw1]
        field_simp [hγ.ne', h1w]
      have hrhs : 8 * (1 + w) / γ * ((4 * (1 + w) * w / γ) * η ^ 2) =
          (32 * (1 + w) ^ 2 * w / γ ^ 2) * η ^ 2 := by ring
      rwa [hlhs, hrhs] at hm8
    have h32_36 : 32 * (1 + w) ^ 2 * w / γ ^ 2 ≤ K0 ^ 2 := by
      dsimp only [K0]
      have hsub : 36 * (1 + w) ^ 2 * w ^ 2 - 32 * (1 + w) ^ 2 * w =
          (1 + w) ^ 2 * w * (36 * w - 32) := by ring
      have hnum : 32 * (1 + w) ^ 2 * w ≤ (6 * (1 + w) * w) ^ 2 := by
        have hp : 0 ≤ (1 + w) ^ 2 * w := by positivity
        have hw36 : 0 ≤ 36 * w - 32 := by linarith only [hw1]
        nlinarith only [mul_nonneg hp hw36]
      rw [div_pow]
      exact div_le_div_of_nonneg_right hnum (sq_nonneg γ)
    exact hd32.trans (mul_le_mul_of_nonneg_right h32_36 (sq_nonneg η))
  -- Deduce |v - w| ≤ L * |η| and polar difference ≤ L * |η|.
  have hd_le_L2 : d ≤ L ^ 2 * η ^ 2 := by
    have hK_le_L : K0 ≤ L := by
      dsimp only [L]
      have h1 : 1 ≤ 1 + 3 * w + Real.sqrt (2 * J) := by
        linarith only [hw.le, Real.sqrt_nonneg (2 * J)]
      nlinarith only [h1, hK0.le]
    have hK2 : K0 ^ 2 ≤ L ^ 2 := pow_le_pow_left₀ hK0.le hK_le_L 2
    exact hd_lip.trans (mul_le_mul_of_nonneg_right hK2 (sq_nonneg η))
  -- Bound |2 * σ * qD| using quadratic completion at scale t = K0 * |η| (or η = 0 directly).
  have hvw_lip : |v - w| ≤ L * |η| := by
    by_cases hη0 : η = 0
    · have hd_zero : d = 0 := by
        rw [hη0, zero_pow two_ne_zero, mul_zero] at hd_lip
        exact le_antisymm hd_lip hd0
      have hq_pos (t : ℝ) : 0 ≤ 2 * t * qD + t ^ 2 * w := by
        have hp : 0 ≤ ∫ u, (D u + t * F u) ^ 2 * Real.exp (-(8 * u)) :=
          integral_nonneg fun u => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le
        rw [criticalHalfLine_exponential_mass_add_const_mul hD hF.1] at hp
        change 0 ≤ d + 2 * t * qD + t ^ 2 * w at hp
        rwa [hd_zero, zero_add] at hp
      have hq0 : qD = 0 := by
        by_contra hqne
        have hp := hq_pos (-qD / w)
        have hid : 2 * (-qD / w) * qD + (-qD / w) ^ 2 * w = -(qD ^ 2 / w) := by
          field_simp [hw.ne']
          ring
        rw [hid] at hp
        have hpos_sq : 0 < qD ^ 2 / w := div_pos (sq_pos_of_ne_zero hqne) hw
        linarith only [hp, hpos_sq]
      rw [hvw, hd_zero, hq0, hη0]
      simp
    · have hηpos : 0 < |η| := abs_pos.mpr hη0
      let t : ℝ := K0 * |η|
      have ht : 0 < t := mul_pos hK0 hηpos
      have hp1 : 0 ≤ d + 2 * t * (σ * qD) + t ^ 2 * w := by
        have hp : 0 ≤ ∫ u, (D u + (t * σ) * F u) ^ 2 * Real.exp (-(8 * u)) :=
          integral_nonneg fun u => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le
        rw [criticalHalfLine_exponential_mass_add_const_mul hD hF.1] at hp
        have hs2 : (t * σ) ^ 2 = t ^ 2 := by rw [mul_pow, hσ2, mul_one]
        change 0 ≤ d + 2 * (t * σ) * qD + (t * σ) ^ 2 * w at hp
        rw [hs2] at hp
        linarith only [hp]
      have hp2 : 0 ≤ d - 2 * t * (σ * qD) + t ^ 2 * w := by
        have hp : 0 ≤ ∫ u, (D u + (-(t * σ)) * F u) ^ 2 * Real.exp (-(8 * u)) :=
          integral_nonneg fun u => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le
        rw [criticalHalfLine_exponential_mass_add_const_mul hD hF.1] at hp
        have hs2 : (-(t * σ)) ^ 2 = t ^ 2 := by rw [neg_sq, mul_pow, hσ2, mul_one]
        change 0 ≤ d + 2 * (-(t * σ)) * qD + (-(t * σ)) ^ 2 * w at hp
        rw [hs2] at hp
        linarith only [hp]
      have hd_t : d ≤ t ^ 2 := by
        dsimp only [t]
        rw [mul_pow, sq_abs]
        exact hd_lip
      have h2q : 2 * |σ * qD| ≤ (1 + w) * t := by
        have habs : 2 * t * |σ * qD| ≤ d + t ^ 2 * w := by
          rcases le_total 0 (σ * qD) with hge | hle
          · rw [abs_of_nonneg hge]; linarith only [hp2]
          · rw [abs_of_nonpos hle]; linarith only [hp1]
        have hdt : d + t ^ 2 * w ≤ t * ((1 + w) * t) := by nlinarith only [hd_t]
        have hle := habs.trans hdt
        have hmul : t * (2 * |σ * qD|) ≤ t * ((1 + w) * t) := by linarith only [hle]
        exact le_of_mul_le_mul_left hmul ht
      have hd_bound : d ≤ t := by
        have ht1 : t ≤ 1 := by
          dsimp only [t, K0]
          rw [div_mul_eq_mul_div]
          apply (div_le_one hγ).mpr
          have h68 : 6 * (1 + w) * w ≤ 8 * w * (1 + w) := by nlinarith only [hw1]
          nlinarith only [hsmall_prod, mul_le_mul_of_nonneg_right h68 (abs_nonneg η)]
        nlinarith only [hd_t, mul_le_mul_of_nonneg_left ht1 ht.le]
      have hvabs' : |v - w| ≤ d + 2 * |σ * qD| := by
        rw [hvw]
        calc |d + 2 * σ * qD| ≤ |d| + |2 * (σ * qD)| := by
              rw [show 2 * σ * qD = 2 * (σ * qD) by ring]; exact abs_add_le _ _
          _ = d + 2 * |σ * qD| := by rw [abs_of_nonneg hd0, abs_mul, abs_of_pos two_pos]
      have hsum_t : d + 2 * |σ * qD| ≤ (2 + w) * K0 * |η| := by
        dsimp only [t] at hd_bound h2q
        linarith only [hd_bound, h2q]
      have hL_dom : (2 + w) * K0 ≤ L := by
        dsimp only [L]
        have h2w : 2 + w ≤ 1 + 3 * w + Real.sqrt (2 * J) := by
          linarith only [hw1, Real.sqrt_nonneg (2 * J)]
        have hm := mul_le_mul_of_nonneg_right h2w hK0.le
        linarith only [hm, hw1, Real.sqrt_nonneg (2 * J)]
      exact hvabs'.trans (hsum_t.trans (mul_le_mul_of_nonneg_right hL_dom (abs_nonneg η)))
  -- Polar difference bound from d ≤ K0² η².
  have hpolar_lip : |(∫ u, H u * polarSourceProfile u) -
      σ * (∫ u, F u * polarSourceProfile u)| ≤ L * |η| := by
    have hs := exponentialSourceMass_le_of_support (Y := 0) le_rfl
      hD.meas.aestronglyMeasurable hD.sq hD.exponential
      (Eventually.of_forall fun u hu => hD.support u hu.le)
    have hs' : exponentialSourceMass D ≤ (∫ u, D u ^ 2) + d := by
      simpa only [mul_zero, neg_zero, Real.exp_zero, one_mul] using hs.2
    have hsource : exponentialSourceMass D ≤ 2 * d := by
      linarith only [hs', hD.square_mass_le_exponential_mass]
    have hcs := (sq_integral_mul_polarSourceProfile_le hD.weighted).trans
      (mul_le_mul_of_nonneg_right hsource hJ)
    have hp : (∫ u, D u * polarSourceProfile u) =
        (∫ u, H u * polarSourceProfile u) - σ * (∫ u, F u * polarSourceProfile u) := by
      have heq : (fun u => D u * polarSourceProfile u) =
          fun u => H u * polarSourceProfile u - σ * (F u * polarSourceProfile u) := by
        funext u
        dsimp only [D]
        ring
      rw [heq, integral_sub (integrable_mul_polarSourceProfile hH.1.weighted)
        ((integrable_mul_polarSourceProfile hF.1.weighted).const_mul σ), integral_const_mul]
    rw [hp] at hcs
    have hsq_bound : ((∫ u, H u * polarSourceProfile u) -
        σ * (∫ u, F u * polarSourceProfile u)) ^ 2 ≤
          (Real.sqrt (2 * J) * K0 * |η|) ^ 2 := by
      calc _ ≤ 2 * d * J := hcs
        _ = (2 * J) * d := by ring
        _ ≤ (2 * J) * (K0 ^ 2 * η ^ 2) :=
            mul_le_mul_of_nonneg_left hd_lip (by positivity)
        _ = (Real.sqrt (2 * J) * K0 * |η|) ^ 2 := by
            rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity : 0 ≤ 2 * J), sq_abs]
            ring
    have habs_le : |(∫ u, H u * polarSourceProfile u) -
        σ * (∫ u, F u * polarSourceProfile u)| ≤ Real.sqrt (2 * J) * K0 * |η| := by
      have hnonneg : 0 ≤ Real.sqrt (2 * J) * K0 * |η| := by positivity
      nlinarith only [sq_abs ((∫ u, H u * polarSourceProfile u) -
        σ * (∫ u, F u * polarSourceProfile u)), hsq_bound, hnonneg,
        abs_nonneg ((∫ u, H u * polarSourceProfile u) - σ * (∫ u, F u * polarSourceProfile u))]
    have hL_dom2 : Real.sqrt (2 * J) * K0 ≤ L := by
      dsimp only [L]
      have h1 : Real.sqrt (2 * J) ≤ 1 + 3 * w + Real.sqrt (2 * J) := by
        linarith only [hw.le]
      nlinarith only [h1, hK0.le, Real.sqrt_nonneg (2 * J)]
    exact habs_le.trans (mul_le_mul_of_nonneg_right hL_dom2 (abs_nonneg η))
  exact ⟨σ, hσ, hd_le_L2, hvw_lip, hpolar_lip⟩

/-- Optimal local Lipschitz response of the sign-aligned minimizer (squared distance
`O(|a(S) - a(R)|²)` in `L²(e^{-8u})`), its eighth-exponential mass, and its polar pairing
around any positive confinement ratio `R > 0`. -/
theorem IsHalfLineEnergyMinimizer.minimizer_lipschitz_stability
    {R : ℝ} (hR : 0 < R) {F : ℝ → ℝ} (hF : IsHalfLineEnergyMinimizer R F) :
    ∃ δ L : ℝ, 0 < δ ∧ 0 ≤ L ∧ ∀ S : ℝ, 0 < S →
      |criticalAliasCoefficient S - criticalAliasCoefficient R| ≤ δ →
      ∀ H : ℝ → ℝ, IsHalfLineEnergyMinimizer S H →
        ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧
          (∫ u, (H u - σ * F u) ^ 2 * Real.exp (-(8 * u))) ≤
            L ^ 2 * (criticalAliasCoefficient S - criticalAliasCoefficient R) ^ 2 ∧
          |(∫ u, H u ^ 2 * Real.exp (-(8 * u))) -
            (∫ u, F u ^ 2 * Real.exp (-(8 * u)))| ≤
              L * |criticalAliasCoefficient S - criticalAliasCoefficient R| ∧
          |(∫ u, H u * polarSourceProfile u) -
            σ * (∫ u, F u * polarSourceProfile u)| ≤
              L * |criticalAliasCoefficient S - criticalAliasCoefficient R| := by
  obtain ⟨γ, hγ, hgap⟩ := hF.controls_neutralPart hR
  have hw1 : 1 ≤ ∫ u, F u ^ 2 * Real.exp (-(8 * u)) :=
    one_le_exponential_square_of_domain hF.1 hF.2.1
  exact ⟨_, _, div_pos hγ (mul_pos (mul_pos (by norm_num) (by linarith only [hw1]))
      (by linarith only [hw1])),
    confiningResponseConstant_nonneg hγ (by linarith only [hw1]),
    fun S hS hsmall H hH => hF.minimizer_lipschitz_stability_of_control hγ hgap hS hsmall hH⟩

/-- The confining ground energy `μ(t) = λ(t⁻¹)` is continuously differentiable on `(0, ∞)`. -/
theorem contDiffOn_one_confiningHalfLineGroundEnergy :
    ContDiffOn ℝ 1 confiningHalfLineGroundEnergy (Ioi 0) := by
  rw [show (1 : WithTop ℕ∞) = 0 + 1 from rfl, contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi]
  refine ⟨fun t ht => ?_, by simp, contDiffOn_zero.mpr ?_⟩
  · obtain ⟨F, hF⟩ := exists_criticalHalfLineGroundEnergy_minimizer (inv_pos.mpr ht)
    exact (hasDerivAt_confiningHalfLineGroundEnergy_of_minimizer ht hF).differentiableAt.differentiableWithinAt
  · rw [isOpen_Ioi.continuousOn_iff]
    intro t ht
    obtain ⟨F, hF⟩ := exists_criticalHalfLineGroundEnergy_minimizer (inv_pos.mpr ht)
    obtain ⟨δ, L, hδ, hL, hlip⟩ := hF.minimizer_lipschitz_stability (inv_pos.mpr ht)
    rw [Metric.continuousAt_iff]
    intro ε hε
    have ha1 := criticalAliasCoefficient_positive zero_lt_one
    let r : ℝ := min (t / 2) (min (δ / criticalAliasCoefficient 1)
      (ε / (2 * (criticalAliasCoefficient 1 ^ 2 * L + 1))))
    have hr : 0 < r := lt_min (half_pos ht) (lt_min (div_pos hδ ha1) (by positivity))
    refine ⟨r, hr, ?_⟩
    intro s hs
    rw [Real.dist_eq] at hs ⊢
    have ht' : 0 < t := ht
    have hs_pos : 0 < s := by
      have hrt : r ≤ t / 2 := min_le_left _ _
      linarith only [(abs_lt.mp hs).1, hrt, ht']
    obtain ⟨H, hH⟩ := exists_criticalHalfLineGroundEnergy_minimizer (inv_pos.mpr hs_pos)
    have hds := (hasDerivAt_confiningHalfLineGroundEnergy_of_minimizer hs_pos hH).deriv
    have hdt := (hasDerivAt_confiningHalfLineGroundEnergy_of_minimizer ht' hF).deriv
    rw [hds, hdt, ← mul_sub, abs_mul, abs_of_pos ha1]
    have hη_eq : criticalAliasCoefficient s⁻¹ - criticalAliasCoefficient t⁻¹ =
        criticalAliasCoefficient 1 * (s - t) := by
      rw [criticalAliasCoefficient_inv, criticalAliasCoefficient_inv]
      ring
    have hη_small : |criticalAliasCoefficient s⁻¹ - criticalAliasCoefficient t⁻¹| ≤ δ := by
      rw [hη_eq, abs_mul, abs_of_pos ha1]
      have hrδ : r ≤ δ / criticalAliasCoefficient 1 :=
        (min_le_right _ _).trans (min_le_left _ _)
      have hlt := hs.trans_le hrδ
      linarith only [((lt_div_iff₀ ha1).mp hlt).le]
    obtain ⟨_, _, _, hvw, _⟩ := hlip s⁻¹ (inv_pos.mpr hs_pos) hη_small H hH
    rw [hη_eq, abs_mul, abs_of_pos ha1] at hvw
    have hrε : r ≤ ε / (2 * (criticalAliasCoefficient 1 ^ 2 * L + 1)) :=
      (min_le_right _ _).trans (min_le_right _ _)
    have hstep1 : criticalAliasCoefficient 1 *
        |(∫ u, H u ^ 2 * Real.exp (-(8 * u))) - (∫ u, F u ^ 2 * Real.exp (-(8 * u)))| ≤
          criticalAliasCoefficient 1 ^ 2 * L * |s - t| := by
      have hm := mul_le_mul_of_nonneg_left hvw ha1.le
      linarith only [hm, show criticalAliasCoefficient 1 *
        (L * (criticalAliasCoefficient 1 * |s - t|)) =
          criticalAliasCoefficient 1 ^ 2 * L * |s - t| by ring]
    have hden_pos : 0 < 2 * (criticalAliasCoefficient 1 ^ 2 * L + 1) := by positivity
    have hstep2 : (criticalAliasCoefficient 1 ^ 2 * L + 1) * |s - t| < ε / 2 := by
      have hlt := hs.trans_le hrε
      have hm := (lt_div_iff₀ hden_pos).mp hlt
      linarith only [hm]
    have hnonneg : 0 ≤ |s - t| := abs_nonneg _
    nlinarith only [hstep1, hstep2, hnonneg, hε]

/-- Locally uniform neutral-part control. Near every positive ratio `R`, every minimizer `H` at a
nearby ratio `S` has exponential mass at most `w_R + 1` and neutral-part control `γ / 8`, where
`γ` controls the minimizer `F` at `R`. A test orthogonal to `H` is almost orthogonal to `F`,
because `H` and `±F` are `O(|a(S) - a(R)|)`-close in `L²(e^{-8u})`, and the ratio change
perturbs the shifted energy by `O(|a(S) - a(R)|)` times the exponential mass. -/
theorem IsHalfLineEnergyMinimizer.uniform_neutral_control
    {R : ℝ} (hR : 0 < R) {F : ℝ → ℝ} (hF : IsHalfLineEnergyMinimizer R F) :
    ∃ ρ γ : ℝ, 0 < ρ ∧ 0 < γ ∧ ∀ S : ℝ, 0 < S →
      |criticalAliasCoefficient S - criticalAliasCoefficient R| ≤ ρ →
      ∀ H : ℝ → ℝ, IsHalfLineEnergyMinimizer S H →
        (∫ u, H u ^ 2 * Real.exp (-(8 * u))) ≤ (∫ u, F u ^ 2 * Real.exp (-(8 * u))) + 1 ∧
        ∀ {G : ℝ → ℝ}, CriticalHalfLineEnergyDomain G →
          γ * (∫ u, criticalHalfLineNeutralPart H G u ^ 2 * Real.exp (-(8 * u))) ≤
            confiningShiftedEnergy S G := by
  obtain ⟨γ, hγ, hgap⟩ := hF.controls_neutralPart hR
  obtain ⟨w, hw⟩ : ∃ w, (∫ u, F u ^ 2 * Real.exp (-(8 * u))) = w := ⟨_, rfl⟩
  have hw1 : 1 ≤ w := hw ▸ one_le_exponential_square_of_domain hF.1 hF.2.1
  have hw0 : 0 < w := zero_lt_one.trans_le hw1
  have hL : 0 ≤ confiningResponseConstant γ w := confiningResponseConstant_nonneg hγ hw0.le
  have hρ1 : 0 < γ / (8 * w * (1 + w)) :=
    div_pos hγ (mul_pos (mul_pos (by norm_num) hw0) (by linarith only [hw0]))
  have hρ2 : 0 < 1 / (2 * (w + 1) * (confiningResponseConstant γ w + 1)) :=
    div_pos one_pos (mul_pos (mul_pos two_pos (by linarith only [hw0])) (by linarith only [hL]))
  have hρ3 : 0 < γ / (8 * (w + 2)) := div_pos hγ (mul_pos (by norm_num) (by linarith only [hw0]))
  refine ⟨min (γ / (8 * w * (1 + w)))
      (min (1 / (2 * (w + 1) * (confiningResponseConstant γ w + 1))) (γ / (8 * (w + 2)))),
    γ / 8, lt_min hρ1 (lt_min hρ2 hρ3), by positivity, ?_⟩
  intro S hS hsmall H hH
  rw [hw]
  obtain ⟨η, hη⟩ : ∃ η, criticalAliasCoefficient S - criticalAliasCoefficient R = η := ⟨_, rfl⟩
  rw [hη] at hsmall
  have hη1 : |η| ≤ γ / (8 * w * (1 + w)) := hsmall.trans (min_le_left _ _)
  have hη2 : |η| ≤ 1 / (2 * (w + 1) * (confiningResponseConstant γ w + 1)) :=
    hsmall.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hη3 : |η| ≤ γ / (8 * (w + 2)) :=
    hsmall.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨σ, hσ, hd, hv, -⟩ := hF.minimizer_lipschitz_stability_of_control hγ hgap hS
    (by rw [hη, hw]; exact hη1) hH
  rw [hw, hη] at hd hv
  obtain ⟨v, hvv⟩ : ∃ v, (∫ u, H u ^ 2 * Real.exp (-(8 * u))) = v := ⟨_, rfl⟩
  rw [hvv] at hv ⊢
  have hv1 : 1 ≤ v := hvv ▸ one_le_exponential_square_of_domain hH.1 hH.2.1
  -- `L |η| ≤ 1 / (2(w + 1))`
  have hx : 2 * (w + 1) * (confiningResponseConstant γ w * |η|) ≤ 1 := by
    have h := (le_div_iff₀ (mul_pos (mul_pos two_pos (by linarith only [hw0]))
      (by linarith only [hL]))).mp hη2
    have hpos : 0 ≤ |η| * (2 * (w + 1)) := mul_nonneg (abs_nonneg η) (by linarith only [hw0])
    linarith only [h, hpos]
  have hLη0 : 0 ≤ confiningResponseConstant γ w * |η| := mul_nonneg hL (abs_nonneg η)
  have hvw : v ≤ w + 1 := by
    have h1 := (abs_le.mp hv).2
    nlinarith only [h1, hx, hLη0, hw0]
  refine ⟨hvw, ?_⟩
  have hlamS_le : criticalHalfLineGroundEnergy S ≤ criticalHalfLineGroundEnergy R + η * w := by
    have h := criticalHalfLineGroundEnergy_le hS hF.1 hF.2.1
    rwa [criticalHalfLineFullEnergy_change_ratio S R hF.1, hF.2.2, hη, hw] at h
  have hlamR_le : criticalHalfLineGroundEnergy R ≤ criticalHalfLineGroundEnergy S - η * v := by
    have h := criticalHalfLineGroundEnergy_le hR hH.1 hH.2.1
    rw [criticalHalfLineFullEnergy_change_ratio R S hH.1, hH.2.2, hvv] at h
    have h' : criticalAliasCoefficient R - criticalAliasCoefficient S = -η := by
      rw [← hη]; ring
    rw [h'] at h
    linarith only [h]
  have hlam_abs : |criticalHalfLineGroundEnergy S - criticalHalfLineGroundEnergy R| ≤
      |η| * (w + 1) := by
    have h1 := mul_le_mul_of_nonneg_right (le_abs_self η) hw0.le
    have h2 := mul_le_mul_of_nonneg_right (neg_abs_le η) (zero_le_one.trans hv1)
    have h3 := mul_le_mul_of_nonneg_left hvw (abs_nonneg η)
    have h4 := abs_nonneg η
    refine abs_le.mpr ⟨?_, ?_⟩ <;> nlinarith only [hlamS_le, hlamR_le, h1, h2, h3, h4]
  have hσ2 : σ ^ 2 = 1 := by rcases hσ with rfl | rfl <;> norm_num
  have hD : CriticalHalfLineEnergyDomain (fun u => H u - σ * F u) := by
    simpa only [neg_mul, sub_eq_add_neg] using hH.1.add_const_mul hF.1 (-σ)
  have hDsq : (∫ u, (H u - σ * F u) ^ 2) ≤ confiningResponseConstant γ w ^ 2 * η ^ 2 :=
    hD.square_mass_le_exponential_mass.trans hd
  have hLη2 : confiningResponseConstant γ w ^ 2 * η ^ 2 * w ≤ 1 / 4 := by
    have hx2 : (2 * (w + 1) * (confiningResponseConstant γ w * |η|)) ^ 2 ≤ 1 := by
      have h2 : 0 ≤ 2 * (w + 1) * (confiningResponseConstant γ w * |η|) :=
        mul_nonneg (by linarith only [hw0]) hLη0
      calc _ ≤ (1 : ℝ) ^ 2 := pow_le_pow_left₀ h2 hx 2
        _ = 1 := one_pow 2
    have hsq : confiningResponseConstant γ w ^ 2 * η ^ 2 =
        (confiningResponseConstant γ w * |η|) ^ 2 := by rw [mul_pow, sq_abs]
    rw [hsq]
    nlinarith only [hx2, mul_nonneg (sq_nonneg (confiningResponseConstant γ w * |η|))
      (show (0 : ℝ) ≤ w ^ 2 + w + 1 by nlinarith only [hw0])]
  -- Transfer of the gap to tests orthogonal to `H`.
  have key : ∀ {G : ℝ → ℝ}, CriticalHalfLineEnergyDomain G → (∫ u, H u * G u) = 0 →
      γ / 8 * (∫ u, G u ^ 2 * Real.exp (-(8 * u))) ≤ confiningShiftedEnergy S G := by
    intro G hG horth
    have hm0 : 0 ≤ ∫ u, G u ^ 2 := integral_nonneg fun u => sq_nonneg _
    have hmg : (∫ u, G u ^ 2) ≤ ∫ u, G u ^ 2 * Real.exp (-(8 * u)) :=
      hG.square_mass_le_exponential_mass
    have hDG : (∫ u, (H u - σ * F u) * G u) = -(σ * ∫ u, F u * G u) := by
      have heq : (fun u => (H u - σ * F u) * G u) = fun u => H u * G u - σ * (F u * G u) := by
        funext u; ring
      rw [heq, integral_sub (pair_integrable_domain hH.1 hG)
        ((pair_integrable_domain hF.1 hG).const_mul σ), integral_const_mul, horth]
      ring
    have hcs : (∫ u, (H u - σ * F u) * G u) ^ 2 ≤ (∫ u, (H u - σ * F u) ^ 2) * ∫ u, G u ^ 2 := by
      have h := HTGeometry.abs_integral_mul_le_sqrt hD.meas.aestronglyMeasurable
        hG.meas.aestronglyMeasurable hD.sq hG.sq
      have hnn : 0 ≤ (∫ u, (H u - σ * F u) ^ 2) * ∫ u, G u ^ 2 :=
        mul_nonneg (integral_nonneg fun u => sq_nonneg _) hm0
      calc _ = |∫ u, (H u - σ * F u) * G u| ^ 2 := (sq_abs _).symm
        _ ≤ Real.sqrt ((∫ u, (H u - σ * F u) ^ 2) * ∫ u, G u ^ 2) ^ 2 :=
          pow_le_pow_left₀ (abs_nonneg _) h 2
        _ = _ := Real.sq_sqrt hnn
    have hc2 : (∫ u, F u * G u) ^ 2 ≤
        confiningResponseConstant γ w ^ 2 * η ^ 2 * ∫ u, G u ^ 2 * Real.exp (-(8 * u)) := by
      have h1 : (∫ u, F u * G u) ^ 2 = (∫ u, (H u - σ * F u) * G u) ^ 2 := by
        rw [hDG, neg_sq, mul_pow, hσ2, one_mul]
      rw [h1]
      exact hcs.trans (mul_le_mul hDsq hmg hm0 (by positivity))
    have hsplit := criticalHalfLine_exponential_mass_add_const_mul_le (hF.1.neutralPart hG) hF.1
      (∫ v, F v * G v)
    have hrepr (u : ℝ) : criticalHalfLineNeutralPart F G u + (∫ v, F v * G v) * F u = G u :=
      sub_add_cancel _ _
    simp only [hrepr] at hsplit
    rw [hw] at hsplit
    have hg0 : 0 ≤ ∫ u, G u ^ 2 * Real.exp (-(8 * u)) := hm0.trans hmg
    have hc2w : (∫ u, F u * G u) ^ 2 * w ≤ (∫ u, G u ^ 2 * Real.exp (-(8 * u))) / 4 := by
      calc (∫ u, F u * G u) ^ 2 * w ≤ confiningResponseConstant γ w ^ 2 * η ^ 2 *
            (∫ u, G u ^ 2 * Real.exp (-(8 * u))) * w := mul_le_mul_of_nonneg_right hc2 hw0.le
        _ = (confiningResponseConstant γ w ^ 2 * η ^ 2 * w) *
            ∫ u, G u ^ 2 * Real.exp (-(8 * u)) := by ring
        _ ≤ (1 / 4) * ∫ u, G u ^ 2 * Real.exp (-(8 * u)) := mul_le_mul_of_nonneg_right hLη2 hg0
        _ = _ := by ring
    have hQR : γ / 4 * (∫ u, G u ^ 2 * Real.exp (-(8 * u))) ≤ confiningShiftedEnergy R G := by
      have hnF : (∫ u, G u ^ 2 * Real.exp (-(8 * u))) / 4 ≤
          ∫ u, criticalHalfLineNeutralPart F G u ^ 2 * Real.exp (-(8 * u)) := by
        linarith only [hsplit, hc2w]
      have h := mul_le_mul_of_nonneg_left hnF hγ.le
      linarith only [h, hgap hG]
    have hQS : confiningShiftedEnergy S G = confiningShiftedEnergy R G +
        η * (∫ u, G u ^ 2 * Real.exp (-(8 * u))) -
          (criticalHalfLineGroundEnergy S - criticalHalfLineGroundEnergy R) * ∫ u, G u ^ 2 := by
      unfold confiningShiftedEnergy
      rw [criticalHalfLineFullEnergy_change_ratio S R hG, hη]
      ring
    have hterm : (criticalHalfLineGroundEnergy S - criticalHalfLineGroundEnergy R) *
        (∫ u, G u ^ 2) ≤ |η| * (w + 1) * ∫ u, G u ^ 2 * Real.exp (-(8 * u)) := by
      calc _ ≤ |criticalHalfLineGroundEnergy S - criticalHalfLineGroundEnergy R| *
            ∫ u, G u ^ 2 := mul_le_mul_of_nonneg_right (le_abs_self _) hm0
        _ ≤ |η| * (w + 1) * ∫ u, G u ^ 2 := mul_le_mul_of_nonneg_right hlam_abs hm0
        _ ≤ _ := mul_le_mul_of_nonneg_left hmg
            (mul_nonneg (abs_nonneg η) (by linarith only [hw0]))
    have hηg : -(|η| * ∫ u, G u ^ 2 * Real.exp (-(8 * u))) ≤
        η * ∫ u, G u ^ 2 * Real.exp (-(8 * u)) := by
      simpa only [neg_mul] using mul_le_mul_of_nonneg_right (neg_abs_le η) hg0
    have hsmall3 : |η| * (w + 2) * (∫ u, G u ^ 2 * Real.exp (-(8 * u))) ≤
        γ / 8 * ∫ u, G u ^ 2 * Real.exp (-(8 * u)) := by
      refine mul_le_mul_of_nonneg_right ?_ hg0
      have h := (le_div_iff₀ (by linarith only [hw0] : (0 : ℝ) < 8 * (w + 2))).mp hη3
      linarith only [h]
    linarith only [hQS, hQR, hterm, hηg, hsmall3]
  intro G hG
  have h := key (hH.1.neutralPart hG) (hH.neutralPart_orthogonal hG)
  rwa [hH.shiftedEnergy_neutralPart hS hG] at h

/-- The coupling slope `μ'(t) = a(1) W₈(F_{t⁻¹})` is locally Lipschitz on `(0, ∞)`, so the
confining ground energy `μ` is `C^{1,1}_loc`. Around `t`, the minimizers at all nearby
reciprocal ratios share one neutral-part control constant and one exponential-mass bound, so the
quantitative response estimate centred at each of them has a common radius and constant. -/
theorem locallyLipschitzOn_deriv_confiningHalfLineGroundEnergy :
    LocallyLipschitzOn (Ioi 0) (deriv confiningHalfLineGroundEnergy) := by
  intro t ht
  have ht' : (0 : ℝ) < t := ht
  obtain ⟨F, hF⟩ := exists_criticalHalfLineGroundEnergy_minimizer (inv_pos.mpr ht')
  obtain ⟨ρ, γ, hρ, hγ, hunif⟩ := hF.uniform_neutral_control (inv_pos.mpr ht')
  obtain ⟨w, hw⟩ : ∃ w, (∫ u, F u ^ 2 * Real.exp (-(8 * u))) = w := ⟨_, rfl⟩
  have hw1 : 1 ≤ w := hw ▸ one_le_exponential_square_of_domain hF.1 hF.2.1
  have hK := criticalAliasCoefficient_positive zero_lt_one
  have hL₀ : 0 ≤ confiningResponseConstant γ (w + 1) :=
    confiningResponseConstant_nonneg hγ (by linarith only [hw1])
  obtain ⟨r, hr_def⟩ : ∃ r, min (ρ / 2) (γ / (16 * (w + 1) * (w + 2))) = r := ⟨_, rfl⟩
  have hr : 0 < r := hr_def ▸ lt_min (half_pos hρ)
    (div_pos hγ (mul_pos (mul_pos (by norm_num) (by linarith only [hw1])) (by linarith only [hw1])))
  have hrρ : r ≤ ρ / 2 := hr_def ▸ min_le_left _ _
  have hrγ : r ≤ γ / (16 * (w + 1) * (w + 2)) := hr_def ▸ min_le_right _ _
  obtain ⟨r', hr'_def⟩ : ∃ r', min (t / 2) (r / criticalAliasCoefficient 1) = r' := ⟨_, rfl⟩
  have hr' : 0 < r' := hr'_def ▸ lt_min (half_pos ht') (div_pos hr hK)
  have hr't : r' ≤ t / 2 := hr'_def ▸ min_le_left _ _
  have hr'r : r' ≤ r / criticalAliasCoefficient 1 := hr'_def ▸ min_le_right _ _
  have hKr' : criticalAliasCoefficient 1 * r' ≤ r := by
    have h := mul_le_mul_of_nonneg_left hr'r hK.le
    rwa [mul_div_cancel₀ r hK.ne'] at h
  refine ⟨Real.toNNReal (criticalAliasCoefficient 1 ^ 2 * confiningResponseConstant γ (w + 1)),
    Ioo (t - r') (t + r'),
    mem_nhdsWithin_of_mem_nhds (Ioo_mem_nhds (by linarith only [hr']) (by linarith only [hr'])),
    ?_⟩
  apply lipschitzOnWith_iff_dist_le_mul.mpr
  intro s hs s' hs'
  have hs0 : 0 < s := by linarith only [hs.1, hr't, ht']
  have hs'0 : 0 < s' := by linarith only [hs'.1, hr't, ht']
  have hcoord (x : ℝ) : criticalAliasCoefficient x⁻¹ - criticalAliasCoefficient t⁻¹ =
      criticalAliasCoefficient 1 * (x - t) := by
    rw [criticalAliasCoefficient_inv, criticalAliasCoefficient_inv]; ring
  have hst : |s - t| ≤ r' := abs_le.mpr ⟨by linarith only [hs.1], by linarith only [hs.2]⟩
  have hs't : |s' - t| ≤ r' := abs_le.mpr ⟨by linarith only [hs'.1], by linarith only [hs'.2]⟩
  have hsR : |criticalAliasCoefficient s⁻¹ - criticalAliasCoefficient t⁻¹| ≤ ρ := by
    rw [hcoord, abs_mul, abs_of_pos hK]
    have h := mul_le_mul_of_nonneg_left hst hK.le
    linarith only [h, hKr', hrρ, hρ]
  obtain ⟨H, hH⟩ := exists_criticalHalfLineGroundEnergy_minimizer (inv_pos.mpr hs0)
  obtain ⟨H', hH'⟩ := exists_criticalHalfLineGroundEnergy_minimizer (inv_pos.mpr hs'0)
  obtain ⟨hvH, hgapH⟩ := hunif s⁻¹ (inv_pos.mpr hs0) hsR H hH
  rw [hw] at hvH
  obtain ⟨v, hvv⟩ : ∃ v, (∫ u, H u ^ 2 * Real.exp (-(8 * u))) = v := ⟨_, rfl⟩
  rw [hvv] at hvH
  have hv1 : 1 ≤ v := hvv ▸ one_le_exponential_square_of_domain hH.1 hH.2.1
  have hss' : criticalAliasCoefficient s'⁻¹ - criticalAliasCoefficient s⁻¹ =
      criticalAliasCoefficient 1 * (s' - s) := by
    rw [criticalAliasCoefficient_inv, criticalAliasCoefficient_inv]; ring
  have hdist : |s' - s| ≤ 2 * r' := by
    have h := abs_sub_le s' t s
    rw [abs_sub_comm t s] at h
    linarith only [h, hst, hs't]
  have hsmall : |criticalAliasCoefficient s'⁻¹ - criticalAliasCoefficient s⁻¹| ≤
      γ / (8 * (∫ u, H u ^ 2 * Real.exp (-(8 * u))) *
        (1 + ∫ u, H u ^ 2 * Real.exp (-(8 * u)))) := by
    rw [hvv, hss', abs_mul, abs_of_pos hK]
    have h1 : criticalAliasCoefficient 1 * |s' - s| ≤ 2 * r := by
      have h := mul_le_mul_of_nonneg_left hdist hK.le
      linarith only [h, hKr']
    have hvpos : 0 < 8 * v * (1 + v) := by positivity
    have hwpos : 0 < 16 * (w + 1) * (w + 2) := by positivity
    have hvle : 8 * v * (1 + v) ≤ 8 * (w + 1) * (w + 2) := by nlinarith only [hvH, hv1]
    have h2 : γ / (8 * (w + 1) * (w + 2)) ≤ γ / (8 * v * (1 + v)) :=
      div_le_div_of_nonneg_left hγ.le hvpos hvle
    have h3 : 2 * r ≤ γ / (8 * (w + 1) * (w + 2)) := by
      have h := mul_le_mul_of_nonneg_left hrγ (by norm_num : (0 : ℝ) ≤ 2)
      have heq : 2 * (γ / (16 * (w + 1) * (w + 2))) = γ / (8 * (w + 1) * (w + 2)) := by
        field_simp; ring
      linarith only [h, heq]
    linarith only [h1, h2, h3]
  obtain ⟨σ, -, -, hvlip, -⟩ :=
    hH.minimizer_lipschitz_stability_of_control hγ hgapH (inv_pos.mpr hs'0) hsmall hH'
  rw [hvv, hss', abs_mul, abs_of_pos hK] at hvlip
  have hLmono := confiningResponseConstant_mono hγ (zero_le_one.trans hv1) hvH
  have hds := (hasDerivAt_confiningHalfLineGroundEnergy_of_minimizer hs0 hH).deriv
  have hds' := (hasDerivAt_confiningHalfLineGroundEnergy_of_minimizer hs'0 hH').deriv
  rw [hvv] at hds
  rw [Real.dist_eq, Real.dist_eq, hds, hds', Real.coe_toNNReal _ (by positivity), ← mul_sub,
    abs_mul, abs_of_pos hK, abs_sub_comm, abs_sub_comm s s']
  have hstep := mul_le_mul_of_nonneg_left
    (hvlip.trans (mul_le_mul_of_nonneg_right hLmono
      (mul_nonneg hK.le (abs_nonneg _)))) hK.le
  calc _ ≤ _ := hstep
    _ = _ := by ring

#print axioms IsHalfLineEnergyMinimizer.controls_neutralPart
#print axioms IsHalfLineEnergyMinimizer.hasDerivAt_criticalHalfLineGroundEnergy
#print axioms hasDerivAt_confiningHalfLineGroundEnergy_of_minimizer
#print axioms IsHalfLineEnergyMinimizer.minimizer_lipschitz_stability
#print axioms contDiffOn_one_confiningHalfLineGroundEnergy
#print axioms IsHalfLineEnergyMinimizer.minimizer_lipschitz_stability_of_control
#print axioms IsHalfLineEnergyMinimizer.uniform_neutral_control
#print axioms locallyLipschitzOn_deriv_confiningHalfLineGroundEnergy

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
