import GaloisForLFunctions.BezoutValuationIncidence.ReadoutEnergyUncertaintyPrinciple
import GaloisForLFunctions.RHTower.CausalMobiusThetaHistoryLocalization

/-!
# The readout is the log-harmonic sum of the row; the Möbius row's energy floor

Exchanging the sums and using `Σ_{e ∣ d} Λ(e) = log d`, the von Mangoldt readout of a row is its
log-harmonic sum:

`R(c) = Σ_{2 ≤ e ≤ N} Λ(e) Y_c(e) = Σ_{d ≤ N} c(d) log d / d`.

In these terms the uncertainty principle says `κ (Σ_d c(d) log d / d)² ≤ (log N - κ) Q^{ec}(c)`, and RH
is the unboundedness of the ratio. For the truncated Möbius row `μ_N`,
`Σ_{d ≤ N} μ(d) log d / d → -1`, so the readout of `-μ_N` tends to `1`. Hence, unconditionally, the
energy-centered pronic energy of the Möbius row is eventually at least `κ/(4 log N)`, and its
Báez-Duarte residual `(1 + Σ_d μ(d) log d/d)² + Q^{ec}(μ_N)` is at least `κ/log N` for every `N ≥ 2`.
-/

open Finset Filter Topology RHTower ArithmeticFunction GaloisForLFunctions.BiScaleUncertainty
open scoped BigOperators

namespace GaloisForLFunctions.BezoutValuationIncidence
noncomputable section
set_option autoImplicit false

/-- **The readout is the log-harmonic sum.** `Σ_e Λ(e) Y_c(e) = Σ_{d ≤ N} c(d) log d / d`. -/
theorem vonMangoldtReadout_eq_log_harmonic (N : ℕ) (c : ℕ → ℝ) :
    vonMangoldtReadout N c = ∑ d ∈ Icc 1 N, c d * Real.log d / d := by
  unfold vonMangoldtReadout selbergMultiplesCoord
  simp_rw [mul_sum]
  rw [sum_comm' (t' := Icc 1 N) (s' := fun d => (Icc 2 N).filter (fun e => e ∣ d))]
  · refine sum_congr rfl fun d hd => ?_
    have hd1 := (mem_Icc.mp hd).1
    have hdiv : (Icc 2 N).filter (fun e => e ∣ d) = d.divisors.erase 1 := by
      ext e
      simp only [mem_filter, mem_Icc, mem_erase, Nat.mem_divisors]
      constructor
      · rintro ⟨⟨h2, hN⟩, hed⟩
        exact ⟨by omega, hed, by omega⟩
      · rintro ⟨h1, hed, -⟩
        have hle := Nat.le_of_dvd (by omega) hed
        have hpos := Nat.pos_of_dvd_of_pos hed (by omega)
        exact ⟨⟨by omega, le_trans hle (mem_Icc.mp hd).2⟩, hed⟩
    rw [hdiv, ← sum_mul, sum_erase _ vonMangoldt_apply_one, vonMangoldt_sum]
    ring
  · intro e d
    simp only [mem_filter, mem_Icc]
    tauto

/-- The energy-centered pronic energy is even in the row. -/
theorem sieveEnergyCenteredPronicGramForm_neg (N : ℕ) (c : ℕ → ℝ) :
    sieveEnergyCenteredPronicGramForm N (fun d => -c d) = sieveEnergyCenteredPronicGramForm N c := by
  have h := sieveEnergyCenteredPronicGramForm_smul N (-1) c
  simp only [neg_one_mul, neg_one_sq, one_mul] at h
  exact h

/-- **The Möbius row's energy floor.** Eventually `Q^{ec}(μ_N) ≥ κ/(4 log N)`. -/
theorem exists_mobius_centered_energy_floor :
    ∃ κ : ℝ, 0 < κ ∧ ∀ᶠ N : ℕ in atTop,
      κ / (4 * Real.log N) ≤
        sieveEnergyCenteredPronicGramForm N (fun d => ((moebius d : ℤ) : ℝ)) := by
  obtain ⟨κ, hκ, hunc⟩ := exists_readout_energy_uncertainty
  refine ⟨κ, hκ, ?_⟩
  have hlim := tendsto_sum_moebius_log_div
  -- eventually the readout of `-μ_N` exceeds one half
  have hev : ∀ᶠ N : ℕ in atTop,
      ∑ d ∈ Icc 1 N, ((moebius d : ℤ) : ℝ) * Real.log d / d < -1 / 2 :=
    hlim.eventually (gt_mem_nhds (by norm_num))
  filter_upwards [hev, eventually_ge_atTop 2] with N hN hN2
  have hlog : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have h := hunc N hN2 (fun d => -((moebius d : ℤ) : ℝ))
  rw [sieveEnergyCenteredPronicGramForm_neg, vonMangoldtReadout_eq_log_harmonic] at h
  have hR : (1 / 2 : ℝ) < ∑ d ∈ Icc 1 N, -((moebius d : ℤ) : ℝ) * Real.log d / d := by
    have : ∑ d ∈ Icc 1 N, -((moebius d : ℤ) : ℝ) * Real.log d / d =
        -∑ d ∈ Icc 1 N, ((moebius d : ℤ) : ℝ) * Real.log d / d := by
      rw [← sum_neg_distrib]
      exact sum_congr rfl fun d _ => by ring
    rw [this]
    linarith
  have hQ := sieveEnergyCenteredPronicGramForm_nonneg' N (fun d => ((moebius d : ℤ) : ℝ))
  set R := ∑ d ∈ Icc 1 N, -((moebius d : ℤ) : ℝ) * Real.log d / d
  set Q := sieveEnergyCenteredPronicGramForm N (fun d => ((moebius d : ℤ) : ℝ))
  have hR2 : (1 : ℝ) / 4 < R ^ 2 := by nlinarith
  have h1 : κ * (1 / 4) < κ * R ^ 2 := mul_lt_mul_of_pos_left hR2 hκ
  have h2 : (Real.log N - κ) * Q ≤ Real.log N * Q := by nlinarith
  rw [div_le_iff₀ (by positivity)]
  linarith

/-- **The Möbius row's Báez-Duarte residual floor**, for every `N ≥ 2`. -/
theorem exists_mobius_residual_floor :
    ∃ κ : ℝ, 0 < κ ∧ ∀ N : ℕ, 2 ≤ N →
      κ / Real.log N ≤ (1 + ∑ d ∈ Icc 1 N, ((moebius d : ℤ) : ℝ) * Real.log d / d) ^ 2 +
        sieveEnergyCenteredPronicGramForm N (fun d => ((moebius d : ℤ) : ℝ)) := by
  obtain ⟨κ, hκ, hfloor⟩ := exists_readout_centered_energy_floor
  refine ⟨κ, hκ, fun N hN => ?_⟩
  have h := hfloor N hN (fun d => -((moebius d : ℤ) : ℝ))
  rw [sieveEnergyCenteredPronicGramForm_neg, vonMangoldtReadout_eq_log_harmonic] at h
  have : 1 - ∑ d ∈ Icc 1 N, -((moebius d : ℤ) : ℝ) * Real.log d / d =
      1 + ∑ d ∈ Icc 1 N, ((moebius d : ℤ) : ℝ) * Real.log d / d := by
    rw [sub_eq_add_neg, ← sum_neg_distrib]
    congr 1
    exact sum_congr rfl fun d _ => by ring
  rwa [this] at h

end

end GaloisForLFunctions.BezoutValuationIncidence
