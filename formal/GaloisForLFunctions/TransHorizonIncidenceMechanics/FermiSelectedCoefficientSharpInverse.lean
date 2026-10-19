import GaloisForLFunctions.TransHorizonIncidenceMechanics.FermiSelectedCoefficientTransportAndRecovery
import Mathlib.Data.Nat.Log

/-!
# Sharp inverse energy for selected Fermi coefficients

Finite dyadic packets have an alias residual only at their terminal boundary.
Their residual energy tends to zero while coefficient energy stays positive,
forcing the universal inverse constant to be exactly `3/2`.
-/

open Finset
open scoped BigOperators

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

private def packetSupport (K : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (K + 2)).image (fun j : ℕ => 2 ^ j)

private def packet (K d : ℕ) : ℝ :=
  if d ∈ packetSupport K then
    if d = 2 then 3 else (2 / 3 : ℝ) ^ (Nat.log 2 d - 2)
  else 0

private theorem power_mem (K j : ℕ) (hj : j ∈ Finset.Icc 1 (K + 2)) :
    2 ^ j ∈ packetSupport K :=
  Finset.mem_image.mpr ⟨j, hj, rfl⟩

private theorem packet_power (K j : ℕ) (hj : j ∈ Finset.Icc 1 (K + 2)) :
    packet K (2 ^ j) = if j = 1 then 3 else (2 / 3 : ℝ) ^ (j - 2) := by
  have heq : 2 ^ j = 2 ↔ j = 1 := by
    constructor
    · intro h
      apply Nat.pow_right_injective (by omega : 2 ≤ 2)
      simpa using h
    · rintro rfl
      norm_num
  simp only [packet, if_pos (power_mem K j hj), heq, Nat.log_pow (by omega : 1 < 2)]

private theorem packet_two (K : ℕ) : packet K 2 = 3 := by
  simpa using packet_power K 1 (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)

private theorem packet_outside (K d : ℕ) (hd : d ∉ packetSupport K) :
    packet K d = 0 := by
  simp [packet, hd]

private theorem double_power (j : ℕ) : 2 * 2 ^ j = 2 ^ (j + 1) := by
  rw [pow_succ]
  omega

private theorem two_dvd_power {j : ℕ} (hj : 1 ≤ j) : 2 ∣ 2 ^ j := by
  refine ⟨2 ^ (j - 1), ?_⟩
  rw [double_power, show j - 1 + 1 = j by omega]

private theorem four_dvd_power {j : ℕ} (hj : 2 ≤ j) : 4 ∣ 2 ^ j := by
  refine ⟨2 ^ (j - 2), ?_⟩
  calc
    2 ^ j = 2 ^ ((j - 2) + 2) := by congr 1; omega
    _ = 4 * 2 ^ (j - 2) := by rw [pow_add]; ring

private theorem even_half_mem (K d : ℕ) (hd : 2 ∣ d)
    (h : 2 * d ∈ packetSupport K) : d ∈ packetSupport K := by
  obtain ⟨j, hj, heq⟩ := Finset.mem_image.mp h
  have hjb := Finset.mem_Icc.mp hj
  have hj2 : 2 ≤ j := by
    by_contra hn
    have hj1 : j = 1 := by omega
    rw [hj1] at heq
    norm_num at heq
    have hd1 : d = 1 := by omega
    rw [hd1] at hd
    norm_num at hd
  have hh : 2 ^ j = 2 * 2 ^ (j - 1) := by
    rw [double_power, show j - 1 + 1 = j by omega]
  have he : 2 ^ (j - 1) = d := by omega
  exact Finset.mem_image.mpr ⟨j - 1, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, he⟩

private theorem packet_residual (K d : ℕ) :
    (if 2 ∣ d then
      (if 4 ∣ d then 2 else 1) * packet K d -
        3 * (if 2 * d ≤ 2 ^ (K + 2) then packet K (2 * d) else 0)
    else packet K d) =
      if d = 2 ^ (K + 2) then 2 * (2 / 3 : ℝ) ^ K else 0 := by
  by_cases hd : d ∈ packetSupport K
  · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hd
    have hjb := Finset.mem_Icc.mp hj
    rw [if_pos (two_dvd_power hjb.1), packet_power K j hj]
    by_cases ht : j = K + 2
    · subst j
      have hpos : 0 < (2 : ℕ) ^ (K + 2) := by positivity
      have hcut : ¬2 * 2 ^ (K + 2) ≤ 2 ^ (K + 2) := by omega
      rw [if_pos (four_dvd_power (by omega)), if_neg hcut, if_pos rfl,
        if_neg (by omega : K + 2 ≠ 1)]
      simp
    · have hn : 2 ^ j ≠ 2 ^ (K + 2) := fun h =>
        ht (Nat.pow_right_injective (by omega : 2 ≤ 2) h)
      have hjnext : j + 1 ∈ Finset.Icc 1 (K + 2) :=
        Finset.mem_Icc.mpr ⟨by omega, by omega⟩
      have hcut : 2 * 2 ^ j ≤ 2 ^ (K + 2) := by
        rw [double_power]
        exact Nat.pow_le_pow_right (by omega) (Finset.mem_Icc.mp hjnext).2
      rw [if_neg hn, if_pos hcut, double_power, packet_power K (j + 1) hjnext]
      by_cases hj1 : j = 1
      · subst j
        norm_num
      · rw [if_neg hj1, if_neg (by omega : j + 1 ≠ 1),
          if_pos (four_dvd_power (by omega)),
          show j + 1 - 2 = (j - 2) + 1 by omega, pow_succ]
        ring
  · have hn : d ≠ 2 ^ (K + 2) := by
      intro h
      subst d
      exact hd (power_mem K (K + 2) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩))
    rw [if_neg hn, packet_outside K d hd]
    by_cases hd2 : 2 ∣ d
    · have hdouble : 2 * d ∉ packetSupport K := fun h => hd (even_half_mem K d hd2 h)
      rw [if_pos hd2, packet_outside K (2 * d) hdouble]
      simp
    · simp [hd2]

private theorem packet_energy_floor (K : ℕ) :
    9 ≤ ∑ d ∈ Finset.Icc 1 (2 ^ (K + 2)), packet K d ^ 2 := by
  have htwo : 2 ≤ (2 : ℕ) ^ (K + 2) := by
    have := Nat.pow_le_pow_right (by omega : 0 < 2) (show 1 ≤ K + 2 by omega)
    simpa using this
  have h := Finset.single_le_sum (fun d _ => sq_nonneg (packet K d))
    (Finset.mem_Icc.mpr ⟨(by omega : 1 ≤ 2), htwo⟩)
  rw [packet_two] at h
  norm_num at h
  exact h

private theorem packet_decay (K : ℕ) :
    0 ≤ (2 / 3 : ℝ) ^ K ∧ (2 / 3 : ℝ) ^ K ≤ 1 ∧
      (2 / 3 : ℝ) ^ K * ((K : ℝ) + 2) ≤ 2 := by
  induction K with
  | zero => norm_num
  | succ K ih =>
    rw [pow_succ]
    push_cast
    obtain ⟨h0, h1, h2⟩ := ih
    constructor
    · nlinarith
    constructor
    · nlinarith
    · nlinarith

private theorem packet_sharp_constant (C : ℝ)
    (hC : ∀ K : ℕ, ∃ A B : ℝ, 9 ≤ A ∧ 0 ≤ B ∧
      3 * B - 2 * A = 4 * ((2 / 3 : ℝ) ^ K) ^ 2 ∧ A ≤ C * B) :
    3 / 2 ≤ C := by
  have hpos : 0 < C := by
    obtain ⟨A, B, hA, hB, _, hAB⟩ := hC 0
    by_contra hn
    have hc : C ≤ 0 := by linarith
    nlinarith [mul_le_mul_of_nonneg_right hc hB]
  by_contra hn
  have hdelta : 0 < 9 * (3 - 2 * C) := by linarith
  obtain ⟨K, hK⟩ := exists_nat_gt (8 * C / (9 * (3 - 2 * C)))
  have hlarge : 8 * C < (K : ℝ) * (9 * (3 - 2 * C)) :=
    (div_lt_iff₀ hdelta).mp hK
  obtain ⟨A, B, hA, hB, hslack, hAB⟩ := hC K
  obtain ⟨hq0, hq1, hdecay⟩ := packet_decay K
  have hsq : ((2 / 3 : ℝ) ^ K) ^ 2 ≤ (2 / 3 : ℝ) ^ K := by nlinarith
  have hAB' : (3 - 2 * C) * A ≤ C * (4 * ((2 / 3 : ℝ) ^ K) ^ 2) := by
    nlinarith
  have hfloor := mul_le_mul_of_nonneg_left hA (show 0 ≤ 3 - 2 * C by linarith)
  have hsmall : 9 * (3 - 2 * C) ≤ 4 * C * (2 / 3 : ℝ) ^ K := by
    nlinarith [mul_le_mul_of_nonneg_left hsq (show 0 ≤ 4 * C by positivity)]
  have hk0 : 0 ≤ (K : ℝ) := Nat.cast_nonneg K
  have hprod := mul_le_mul_of_nonneg_right hsmall (show 0 ≤ (K : ℝ) + 2 by positivity)
  have hdec := mul_le_mul_of_nonneg_left hdecay (show 0 ≤ 4 * C by positivity)
  nlinarith

private theorem packet_residual_energy (K : ℕ) :
    (∑ d ∈ Finset.Icc 1 (2 ^ (K + 2)),
      fermiAliasResidual (2 ^ (K + 2)) (packet K) d ^ 2) =
        4 * ((2 / 3 : ℝ) ^ K) ^ 2 := by
  have hr (d : ℕ) : fermiAliasResidual (2 ^ (K + 2)) (packet K) d =
      if d = 2 ^ (K + 2) then 2 * (2 / 3 : ℝ) ^ K else 0 :=
    packet_residual K d
  have hmem : 2 ^ (K + 2) ∈ Finset.Icc 1 (2 ^ (K + 2)) :=
    Finset.mem_Icc.mpr ⟨by
      have hp : 0 < (2 : ℕ) ^ (K + 2) := by positivity
      omega, le_refl _⟩
  calc
    (∑ d ∈ Finset.Icc 1 (2 ^ (K + 2)),
        fermiAliasResidual (2 ^ (K + 2)) (packet K) d ^ 2) =
        fermiAliasResidual (2 ^ (K + 2)) (packet K) (2 ^ (K + 2)) ^ 2 := by
      apply Finset.sum_eq_single (2 ^ (K + 2))
      · intro d _ hd
        rw [hr d, if_neg hd]
        norm_num
      · intro hn
        exact (hn hmem).elim
    _ = 4 * ((2 / 3 : ℝ) ^ K) ^ 2 := by
      rw [hr, if_pos rfl]
      ring

/-- The best uniform inverse coefficient-energy constant is exactly `3/2`. -/
theorem fermiSelectedCoefficient_inverse_constant_iff (C : ℝ) :
    (∀ (N : ℕ) (c : ℕ → ℝ),
      (∑ d ∈ Finset.Icc 1 N, c d ^ 2) ≤
        C * ∑ d ∈ Finset.Icc 1 N, fermiSelectedCoefficient N c d ^ 2) ↔
      3 / 2 ≤ C := by
  constructor
  · intro hC
    apply packet_sharp_constant C
    intro K
    refine ⟨∑ d ∈ Finset.Icc 1 (2 ^ (K + 2)), packet K d ^ 2,
      ∑ d ∈ Finset.Icc 1 (2 ^ (K + 2)),
        fermiSelectedCoefficient (2 ^ (K + 2)) (packet K) d ^ 2,
      packet_energy_floor K, Finset.sum_nonneg (fun _ _ => sq_nonneg _), ?_,
      hC (2 ^ (K + 2)) (packet K)⟩
    rw [fermiSelectedCoefficient_energy_slack, packet_residual_energy]
  · intro hC N c
    have h := fermiSelectedCoefficient_energy_bound N c
    have hn : 0 ≤ ∑ d ∈ Finset.Icc 1 N, fermiSelectedCoefficient N c d ^ 2 :=
      Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    exact h.trans (mul_le_mul_of_nonneg_right hC hn)

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
