import GaloisForLFunctions.BezoutValuationIncidence.TheVaughanEmptyLegReadsTheZeroAbscissa
import GaloisForLFunctions.RHTower.MertensFrontierOneSidedOmega

/-!
Exact endpoint Vaughan power bounds constrain zeros on the corresponding
boundary line. Mertens frontier oscillation bounds their order and the
remaining analytic factor; square-root endpoint rates force simple critical zeros.
-/

open Finset Filter RHTower
open GaloisForLFunctions.TransHorizonIncidenceMechanics
open scoped BigOperators Topology
noncomputable section
namespace GaloisForLFunctions.BezoutValuationIncidence
set_option autoImplicit false

private theorem mertens_subpowers_of_moebius_power {C β : ℝ}
    (hC : 0 ≤ C) (hβ : 0 ≤ β)
    (hM : ∀ n : ℕ, 1 ≤ n →
      |∑ d ∈ Icc 1 n, moebiusReal d| ≤ C * (n : ℝ) ^ β) :
    ∀ δ : ℝ, 0 < δ → ∃ K : ℝ, 0 ≤ K ∧ ∀ n : ℕ,
      ‖mobiusMertensPartialSum n‖ ≤ K * ((n : ℝ) + 1) ^ (β + δ) := by
  intro δ hδ
  refine ⟨C, hC, fun n => ?_⟩
  rw [norm_mobiusMertensPartialSum_eq_abs_sum]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [Icc_eq_empty (by norm_num), sum_empty, abs_zero]
    positivity
  · refine (hM n hn).trans (mul_le_mul_of_nonneg_left ?_ hC)
    exact (Real.rpow_le_rpow (Nat.cast_nonneg n)
      (by linarith : (n : ℝ) ≤ (n : ℝ) + 1) hβ).trans
      (Real.rpow_le_rpow_of_exponent_le (by linarith [Nat.cast_nonneg n])
        (by linarith only [hδ]))

private theorem abs_mertensReal_le_of_moebius_power {C β : ℝ}
    (hC : 0 ≤ C) (hβ : 0 ≤ β)
    (hM : ∀ n : ℕ, 1 ≤ n →
      |∑ d ∈ Icc 1 n, moebiusReal d| ≤ C * (n : ℝ) ^ β)
    {x : ℝ} (hx : 1 ≤ x) : |mertensFunctionReal x| ≤ C * x ^ β := by
  change |∑ d ∈ Icc 1 ⌊x⌋₊, moebiusReal d| ≤ C * x ^ β
  rcases Nat.eq_zero_or_pos ⌊x⌋₊ with hzero | hpos
  · rw [hzero, Icc_eq_empty (by norm_num), sum_empty, abs_zero]
    exact mul_nonneg hC (Real.rpow_nonneg (zero_le_one.trans hx) β)
  · exact (hM _ hpos).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Nat.cast_nonneg _) (Nat.floor_le (zero_le_one.trans hx)) hβ) hC)

/-- An attained Möbius power bound caps boundary zero orders and bounds their local factors. -/
theorem boundary_zeta_order_and_factor_bound_of_moebius_power {C β : ℝ}
    (hC : 0 ≤ C) (hβ : 0 ≤ β) (hβ1 : β < 1)
    (hM : ∀ n : ℕ, 1 ≤ n →
      |∑ d ∈ Icc 1 n, moebiusReal d| ≤ C * (n : ℝ) ^ β)
    {ρ : ℂ} (hρ : ρ.re = β) :
    (analyticOrderAt riemannZeta ρ).toNat ≤ 1 ∧
      ∀ p : ℂ → ℂ, ContinuousAt p ρ →
        (∀ᶠ z in 𝓝 ρ, riemannZeta z =
          (z - ρ) ^ (analyticOrderAt riemannZeta ρ).toNat • p z) →
        (analyticOrderAt riemannZeta ρ).toNat = 1 →
        1 ≤ 4 * C * polylogConst 0 * ‖ρ‖ * ‖p ρ‖ := by
  have hβhalf : 1 / 2 ≤ β := half_le_zetaZeroAbscissa.trans
    (zetaZeroAbscissa_le_of_moebius_power_bound hC hβ hM)
  have hone (x : ℝ) (hx : 1 ≤ x) :
      (1 : ℝ) * mertensFunctionReal x ≤ C * x ^ β * (1 + Real.log x) ^ (0 : ℝ) + 0 := by
    simpa only [one_mul, Real.rpow_zero, mul_one, add_zero] using
      (le_abs_self (mertensFunctionReal x)).trans (abs_mertensReal_le_of_moebius_power hC hβ hM hx)
  have h := natCast_order_le_of_mertens_oneSided hβhalf hβ1
    (by norm_num : (0 : ℝ) ≤ 0) hC (le_refl (0 : ℝ)) (by norm_num : |(1 : ℝ)| = 1)
    (mertens_subpowers_of_moebius_power hC hβ hM) hone hρ
  refine ⟨?_, fun p hp hfac hn => ?_⟩
  · have hc' : ((analyticOrderAt riemannZeta ρ).toNat : ℝ) ≤ 1 := by
      simpa only [zero_add] using h.1
    exact_mod_cast hc'
  · have hpbound := h.2 p hp hfac (by simp only [hn, Nat.cast_one, zero_add])
    norm_num only [zero_add, Real.rpow_one] at hpbound
    exact hpbound.trans_eq (by ring)

/-- Every zero on the boundary of an attained positive Vaughan tail rate is simple. -/
theorem analyticOrderAt_eq_one_of_vaughan_tail_rate {ε η : ℝ}
    (hε : 0 < ε) (hη : 0 < η) (hrate : η ∈ pmPronicVaughanTailPowerRates ε)
    {ρ : ℂ} (hρ : ρ.re = 1 - η) (hz : riemannZeta ρ = 0) :
    analyticOrderAt riemannZeta ρ = 1 := by
  have hη1 : η < 1 := hrate.2.1
  obtain ⟨C, hC, hM⟩ := (mem_pmPronicVaughanTailPowerRates_iff_moebius_power hε hη hη1).mp hrate
  have hβ0 : 0 ≤ 1 - η := (sub_pos.mpr hη1).le
  have hβ1 : 1 - η < 1 := by linarith only [hη]
  have hcap := (boundary_zeta_order_and_factor_bound_of_moebius_power hC hβ0 hβ1 hM hρ).1
  have hρpos : 0 < ρ.re := by rw [hρ]; exact sub_pos.mpr hη1
  have hρlt : ρ.re < 1 := by rw [hρ]; exact hβ1
  have hρne1 : ρ ≠ 1 := by
    intro h
    rw [h, Complex.one_re] at hρlt
    exact (lt_irrefl (1 : ℝ)) hρlt
  have hfinite : analyticOrderAt riemannZeta ρ ≠ ⊤ := by
    rw [← xi_analyticOrderAt_eq_riemannZeta_of_mem_strip ⟨hρpos, hρlt⟩]
    exact xi_orderAt_ne_top ρ
  have hnonzero : analyticOrderAt riemannZeta ρ ≠ 0 := by
    rw [Ne, analyticOrderAt_eq_zero]
    rintro (h | h)
    exacts [h (analyticOn_riemannZeta ρ hρne1), h hz]
  have hpositive : 1 ≤ (analyticOrderAt riemannZeta ρ).toNat := by
    rw [Nat.one_le_iff_ne_zero]
    intro h
    exact hnonzero ((ENat.toNat_eq_zero.mp h).resolve_right hfinite)
  have hn : (analyticOrderAt riemannZeta ρ).toNat = 1 := le_antisymm hcap hpositive
  calc
    analyticOrderAt riemannZeta ρ = ((analyticOrderAt riemannZeta ρ).toNat : ℕ∞) :=
      (ENat.coe_toNat hfinite).symm
    _ = 1 := by rw [hn]; rfl

/-- Endpoint tail attainment implies RH and simplicity on the critical line. -/
theorem riemannHypothesis_and_simple_zeros_of_vaughan_half_tail_rate {ε : ℝ}
    (hε : 0 < ε) (hrate : (1 / 2 : ℝ) ∈ pmPronicVaughanTailPowerRates ε) :
    RiemannHypothesis ∧ ∀ ρ : ℂ, ρ.re = 1 / 2 → riemannZeta ρ = 0 →
      analyticOrderAt riemannZeta ρ = 1 := by
  have hupper := pmPronicVaughanTailPowerRates_le hε.le hrate
  have hΘ : zetaZeroAbscissa = 1 / 2 := le_antisymm
    (by linarith only [hupper]) half_le_zetaZeroAbscissa
  refine ⟨zetaZeroAbscissa_eq_half_iff_riemannHypothesis.mp hΘ, fun ρ hρ hz => ?_⟩
  exact analyticOrderAt_eq_one_of_vaughan_tail_rate hε (by norm_num) hrate
    (by linarith only [hρ]) hz

/-- The endpoint square-cutoff energy rate has the same RH and simplicity consequence. -/
theorem riemannHypothesis_and_simple_zeros_of_vaughan_square_energy_endpoint {ε : ℝ}
    (hε : 0 < ε) (hrate : (2 : ℝ) ∈ pmPronicVaughanSquareEnergyPowerRates ε) :
    RiemannHypothesis ∧ ∀ ρ : ℂ, ρ.re = 1 / 2 → riemannZeta ρ = 0 →
      analyticOrderAt riemannZeta ρ = 1 := by
  apply riemannHypothesis_and_simple_zeros_of_vaughan_half_tail_rate hε
  have h := (mem_pmPronicVaughanSquareEnergyPowerRates_iff hε).mp hrate
  norm_num only at h
  exact h

/-- The endpoint square-horizon energy rate also forces RH and simple critical zeros. -/
theorem riemannHypothesis_and_simple_zeros_of_vaughan_horizon_energy_endpoint {ε : ℝ}
    (hε : 0 < ε) (hrate : (1 : ℝ) ∈ pmPronicVaughanHorizonEnergyPowerRates ε) :
    RiemannHypothesis ∧ ∀ ρ : ℂ, ρ.re = 1 / 2 → riemannZeta ρ = 0 →
      analyticOrderAt riemannZeta ρ = 1 := by
  apply riemannHypothesis_and_simple_zeros_of_vaughan_square_energy_endpoint hε
  simpa only [mul_one] using mem_pmPronicVaughanHorizonEnergyPowerRates_iff.mp hrate

/-- An attained tail rate gives a common lower bound on the local factor at each boundary zero. -/
theorem exists_boundary_factor_bound_of_vaughan_tail_rate {ε η : ℝ}
    (hε : 0 < ε) (hη : 0 < η) (hrate : η ∈ pmPronicVaughanTailPowerRates ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ρ : ℂ, ρ.re = 1 - η → riemannZeta ρ = 0 →
      ∀ p : ℂ → ℂ, ContinuousAt p ρ →
        (∀ᶠ z in 𝓝 ρ, riemannZeta z = (z - ρ) • p z) →
        1 ≤ 4 * C * polylogConst 0 * ‖ρ‖ * ‖p ρ‖ := by
  have hη1 := hrate.2.1
  obtain ⟨C, hC, hM⟩ := (mem_pmPronicVaughanTailPowerRates_iff_moebius_power hε hη hη1).mp hrate
  refine ⟨C, hC, fun ρ hρ hz p hp hfac => ?_⟩
  have horder := analyticOrderAt_eq_one_of_vaughan_tail_rate hε hη hrate hρ hz
  have hn : (analyticOrderAt riemannZeta ρ).toNat = 1 := by rw [horder]; rfl
  exact (boundary_zeta_order_and_factor_bound_of_moebius_power hC
    (sub_pos.mpr hη1).le (by linarith only [hη]) hM hρ).2 p hp
    (by simpa only [hn, pow_one] using hfac) hn

#print axioms boundary_zeta_order_and_factor_bound_of_moebius_power
#print axioms analyticOrderAt_eq_one_of_vaughan_tail_rate
#print axioms riemannHypothesis_and_simple_zeros_of_vaughan_half_tail_rate
#print axioms riemannHypothesis_and_simple_zeros_of_vaughan_square_energy_endpoint
#print axioms riemannHypothesis_and_simple_zeros_of_vaughan_horizon_energy_endpoint
#print axioms exists_boundary_factor_bound_of_vaughan_tail_rate
end GaloisForLFunctions.BezoutValuationIncidence
