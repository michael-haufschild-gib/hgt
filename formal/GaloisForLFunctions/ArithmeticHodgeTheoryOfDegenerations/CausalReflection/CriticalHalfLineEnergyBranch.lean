import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.CriticalHalfLineGroundEnergy
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.CriticalHalfLineVariationalCompactness

/-!
# Minimizers of the full half-line energy

Smooth recovery and variational compactness attain the normalized floor
inside the actual Gamma domain.
-/

noncomputable section
open MeasureTheory Set Filter Topology Zeta23
open _root_.RHTower
namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
open CriticalArithmeticCorrelationTheory ArithmeticCastelnuovoSeveri
  ArithmeticPositivityTheory WindowTowerOfSpecZ

/-- A normalized profile attaining the actual full-domain variational floor. -/
def IsHalfLineEnergyMinimizer (R : ℝ) (H : ℝ → ℝ) : Prop :=
  CriticalHalfLineEnergyDomain H ∧ (∫ u, H u ^ 2) = 1 ∧
    criticalHalfLineFullEnergy R H = criticalHalfLineGroundEnergy R

/-- A critical state supplies a unit profile; positive confinement then attains every variational floor. -/
theorem exists_criticalHalfLineGroundEnergy_minimizer {W₀ R : ℝ} (hR : 0 < R)
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) :
    ∃ H : ℝ → ℝ, IsHalfLineEnergyMinimizer R H := by
  let λ : ℝ := criticalHalfLineGroundEnergy R
  let e : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hepos (n : ℕ) : 0 < e n := by dsimp only [e]; positivity
  have hele (n : ℕ) : e n ≤ 1 := by
    dsimp only [e]
    exact div_le_one_of_le₀ (by linarith only [Nat.cast_nonneg (α := ℝ) n]) (by positivity)
  have helim : Tendsto e atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hdF := criticalHalfLineEnergyDomain_of_groundState hF
  have hnonempty : ({b : ℝ | ∃ G : ℝ → ℝ, CriticalHalfLineEnergyDomain G ∧
      (∫ u, G u ^ 2) = 1 ∧ criticalHalfLineFullEnergy R G = b} : Set ℝ).Nonempty :=
    ⟨criticalHalfLineFullEnergy R F, F, hdF, hF.2.2.2.1, rfl⟩
  have hchoose (n : ℕ) : ∃ G : ℝ → ℝ, CriticalHalfLineEnergyDomain G ∧
      (∫ u, G u ^ 2) = 1 ∧ criticalHalfLineFullEnergy R G < λ + e n := by
    obtain ⟨b, ⟨G, hG, hm, rfl⟩, hb⟩ := exists_lt_of_csInf_lt hnonempty
      (show criticalHalfLineGroundEnergy R < λ + e n from lt_add_of_pos_right λ (hepos n))
    exact ⟨G, hG, hm, hb⟩
  choose G hDG hmG heG using hchoose
  obtain ⟨B, hB, hgard⟩ := criticalHalfLineFullEnergy_coercive_remainder hR
  have ha := criticalAliasCoefficient_positive hR
  let M : ℝ := (|λ| + 1 + B) / (criticalAliasCoefficient R / 2)
  have hM : 0 ≤ M := div_nonneg
    (add_nonneg (add_nonneg (abs_nonneg _) zero_le_one) hB) (half_pos ha).le
  have hG8 (n : ℕ) : (∫ u, G n u ^ 2 * Real.exp (-(8 * u))) ≤ M := by
    apply (le_div_iff₀ (half_pos ha)).mpr
    have h := hgard (hDG n)
    rw [hmG n, mul_one] at h
    linarith only [h, heG n, hele n, le_abs_self λ]
  have hrec (n : ℕ) := exists_window_energy_recovery hR (hDG n) (hmG n).le (hepos n)
  choose A H hA hHwin hmH hdH hH8 heH using hrec
  have hDH (n : ℕ) := criticalHalfLineEnergyDomain_of_window (hHwin n)
  have hdiff (n : ℕ) : CriticalHalfLineEnergyDomain (fun u => H n u - G n u) := by
    simpa only [neg_one_mul, sub_eq_add_neg] using (hDH n).add_const_mul (hDG n) (-1)
  have herr : Tendsto (fun n => ∫ u, (H n u - G n u) ^ 2) atTop (𝓝 0) :=
    squeeze_zero (fun n => integral_nonneg fun u => sq_nonneg _) (fun n => (hdH n).le) helim
  have hmasslim : Tendsto (fun n => ∫ u, H n u ^ 2) atTop (𝓝 1) := by
    have h := HTGeometry.tendsto_integral_sq_add_of_tendsto_zero
      (Eventually.of_forall fun n => (hDG n).meas.aestronglyMeasurable)
      (Eventually.of_forall fun n => (hdiff n).meas.aestronglyMeasurable)
      (Eventually.of_forall fun n => (hDG n).sq)
      (Eventually.of_forall fun n => (hdiff n).sq)
      (show Tendsto (fun n => ∫ u, G n u ^ 2) atTop (𝓝 1) by
        simpa only [hmG] using (tendsto_const_nhds (x := (1 : ℝ)))) herr
    exact h.congr fun n => integral_congr_ae (Eventually.of_forall fun u => by congr 1; ring)
  have hupper (n : ℕ) : criticalHalfLineFullEnergy R (H n) ≤ λ + 2 * e n := by
    have h := heH n
    linarith only [h, heG n]
  have hmasspos : ∀ᶠ n in atTop, 0 < ∫ u, H n u ^ 2 :=
    hmasslim.eventually (gt_mem_nhds zero_lt_one)
  have hupperlim : Tendsto (fun n => λ + 2 * e n - λ * (∫ u, H n u ^ 2))
      atTop (𝓝 0) := by
    simpa only [mul_zero, add_zero, mul_one, sub_self] using
      (((tendsto_const_nhds (x := λ)).add (helim.const_mul 2)).sub (hmasslim.const_mul λ))
  have hdiffE : Tendsto (fun n => criticalHalfLineFullEnergy R (H n) - λ * (∫ u, H n u ^ 2))
      atTop (𝓝 0) := by
    apply squeeze_zero' ?_ (Eventually.of_forall fun n => sub_le_sub_right (hupper n) _) hupperlim
    filter_upwards [hmasspos] with n hn
    exact sub_nonneg.mpr (criticalHalfLineGroundEnergy_mul_mass_le hR (hDH n) hn)
  have hElim : Tendsto (fun n => criticalHalfLineFullEnergy R (H n)) atTop (𝓝 λ) := by
    simpa only [sub_add_cancel, mul_one, zero_add] using hdiffE.add (hmasslim.const_mul λ)
  obtain ⟨K, _, _, hDK, hmK, heK, _⟩ := exists_domain_limit_of_smooth_energy_limit hR hDH
    (fun n => (hHwin n).contDiff) (fun n => (hHwin n).hasCompactSupport)
    (fun n => (hmH n).trans (hmG n).le) hmasslim (mul_nonneg (by norm_num) hM)
    (fun n => (hH8 n).trans (mul_le_mul_of_nonneg_left (hG8 n) (by norm_num)))
    (B := |λ| + 2) (fun n => (hupper n).trans (by linarith only [hele n, le_abs_self λ])) hElim
  exact ⟨K, hDK, hmK, le_antisymm heK (criticalHalfLineGroundEnergy_le hR hDK hmK)⟩

/-- Two profiles attaining the homogeneous floor generate a line of attaining profiles. -/
theorem criticalHalfLine_minimizing_add_const_mul
    {W₀ R : ℝ} (hW : 0 < W₀) (hR : 0 < R)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {H K : ℝ → ℝ} (hH : CriticalHalfLineEnergyDomain H) (hK : CriticalHalfLineEnergyDomain K)
    (heH : criticalHalfLineFullEnergy R H = criticalHalfLineGroundEnergy R * (∫ u, H u ^ 2))
    (heK : criticalHalfLineFullEnergy R K = criticalHalfLineGroundEnergy R * (∫ u, K u ^ 2))
    (c : ℝ) :
    criticalHalfLineFullEnergy R (fun u => H u + c * K u) =
      criticalHalfLineGroundEnergy R * (∫ u, (H u + c * K u) ^ 2) := by
  have hp := criticalHalfLineGroundEnergy_mul_mass_le_all hW hR ht (hH.add_const_mul hK 1)
  have hm := criticalHalfLineGroundEnergy_mul_mass_le_all hW hR ht (hH.add_const_mul hK (-1))
  rw [criticalHalfLineFullEnergy_add_const_mul R hH hK,
    criticalHalfLine_square_mass_add_const_mul hH hK, heH, heK] at hp hm
  have hcross : criticalHalfLineMixedEnergy R H K =
      criticalHalfLineGroundEnergy R * (∫ u, H u * K u) := by
    nlinarith only [hp, hm]
  rw [criticalHalfLineFullEnergy_add_const_mul R hH hK,
    criticalHalfLine_square_mass_add_const_mul hH hK, heH, heK, hcross]
  ring

theorem criticalHalfLine_minimizing_const_mul {R : ℝ} {H : ℝ → ℝ}
    (heH : criticalHalfLineFullEnergy R H = criticalHalfLineGroundEnergy R * (∫ u, H u ^ 2))
    (c : ℝ) :
    criticalHalfLineFullEnergy R (fun u => c * H u) =
      criticalHalfLineGroundEnergy R * (∫ u, (c * H u) ^ 2) := by
  rw [criticalHalfLineFullEnergy_const_mul, HTGeometry.integral_sq_const_mul, heH]
  ring

/-- Near the threshold, an attaining profile orthogonal to the critical state must vanish. -/
theorem criticalHalfLine_minimizing_neutral_eq_zero
    {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ R : ℝ, 0 < R →
      |criticalAliasCoefficient R - criticalAliasCoefficient W₀| ≤ δ →
      ∀ G : ℝ → ℝ, CriticalHalfLineEnergyDomain G → (∫ u, F u * G u) = 0 →
        criticalHalfLineFullEnergy R G = criticalHalfLineGroundEnergy R * (∫ u, G u ^ 2) →
          G =ᵐ[volume] 0 := by
  obtain ⟨γ, hγ, hgap⟩ := criticalHalfLineFullEnergy_transverse_exponential_gap hW ht hF
  let w : ℝ := ∫ u, F u ^ 2 * Real.exp (-(8 * u))
  have hw : 0 ≤ w := integral_nonneg fun u => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le
  refine ⟨γ / (2 * (1 + w)), by positivity, ?_⟩
  intro R hR hsmall G hG ho heG
  let η : ℝ := criticalAliasCoefficient R - criticalAliasCoefficient W₀
  change |η| ≤ γ / (2 * (1 + w)) at hsmall
  have hsmall' : |η| * (1 + w) ≤ γ / 2 := by
    have h := (le_div_iff₀ (by positivity : 0 < 2 * (1 + w))).mp hsmall
    linarith only [h]
  have hηw : 0 ≤ |η| * w := mul_nonneg (abs_nonneg _) hw
  have hcoef : 0 < γ - |η| := by linarith only [hsmall', hηw, hγ]
  have hupper := criticalHalfLineGroundEnergy_le_critical_tangent hW hR ht hF
  have hupper' := mul_le_mul_of_nonneg_right (le_abs_self η) hw
  have hsep : criticalHalfLineGroundEnergy R < γ - |η| := by
    change criticalHalfLineGroundEnergy R ≤ η * w at hupper
    linarith only [hupper, hupper', hsmall', hγ]
  let m : ℝ := ∫ u, G u ^ 2
  let n : ℝ := ∫ u, G u ^ 2 * Real.exp (-(8 * u))
  have hm : 0 ≤ m := integral_nonneg fun u => sq_nonneg _
  have hn : 0 ≤ n := integral_nonneg fun u => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le
  have hmn : m ≤ n := hG.square_mass_le_exponential_mass
  have heg := hgap hG ho
  have hηn := mul_le_mul_of_nonneg_right (neg_abs_le η) hn
  have he := criticalHalfLineFullEnergy_change_ratio R W₀ hG
  have hflo : (γ - |η|) * n ≤ criticalHalfLineFullEnergy R G := by
    change γ * n ≤ criticalHalfLineFullEnergy W₀ G at heg
    change criticalHalfLineFullEnergy R G = criticalHalfLineFullEnergy W₀ G + η * n at he
    nlinarith only [heg, hηn, he]
  have hmass := (mul_le_mul_of_nonneg_left hmn hcoef.le).trans hflo
  rw [heG] at hmass
  change (γ - |η|) * m ≤ criticalHalfLineGroundEnergy R * m at hmass
  have hprod : (γ - |η| - criticalHalfLineGroundEnergy R) * m ≤ 0 := by
    nlinarith only [hmass]
  have hm0 : m = 0 := le_antisymm
    ((mul_le_mul_left (sub_pos.mpr hsep)).mp (by simpa only [mul_zero] using hprod)) hm
  have hae := (integral_eq_zero_iff_of_nonneg_ae
    (Eventually.of_forall fun u => sq_nonneg (G u)) hG.sq).mp hm0
  filter_upwards [hae] with u hu
  change G u ^ 2 = 0 at hu
  change G u = 0
  nlinarith only [hu]

#print axioms exists_criticalHalfLineGroundEnergy_minimizer

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
