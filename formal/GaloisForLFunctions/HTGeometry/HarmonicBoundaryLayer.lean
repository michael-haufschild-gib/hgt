import Mathlib

/-!
# Uniform harmonic bounds at a quotient boundary

A sequence tending to zero contributes an arbitrarily small multiple of harmonic
mass, plus a fixed constant, when sampled at complementary integer quotients.
The estimate holds on every subset of a shorter horizon.
-/

noncomputable section

open Filter Topology Finset

namespace GaloisForLFunctions.HTGeometry

/-- Quotient sampling of a vanishing sequence is uniformly negligible relative
to harmonic mass, up to a fixed boundary constant. -/
theorem exists_harmonicBoundaryLayer_bound {f : ℕ → ℝ}
    (hf : Tendsto f atTop (𝓝 0)) {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (A B : ℕ) (S : Finset ℕ), S ⊆ Icc 1 A → A ≤ B →
      |∑ k ∈ S, f (B / k) / (k : ℝ)| ≤ η * (∑ k ∈ S, 1 / (k : ℝ)) + C := by
  obtain ⟨K, hKrange⟩ := hf.abs.bddAbove_range
  have hK : ∀ n, |f n| ≤ K := fun n => hKrange ⟨n, rfl⟩
  have hK0 : 0 ≤ K := (abs_nonneg (f 0)).trans (hK 0)
  obtain ⟨Y, hY⟩ := Metric.tendsto_atTop.mp hf η hη
  refine ⟨K * Y, mul_nonneg hK0 (Nat.cast_nonneg Y), fun A B S hS hAB => ?_⟩
  rcases Nat.eq_zero_or_pos B with rfl | hB
  · have hA : A = 0 := by omega
    have hS0 : S = ∅ := by simpa [hA] using hS
    simp only [hS0, sum_empty, abs_zero, mul_zero, zero_add]
    exact mul_nonneg hK0 (Nat.cast_nonneg Y)
  have hBR : (0 : ℝ) < B := by exact_mod_cast hB
  have hterm : ∀ k ∈ S, |f (B / k) / (k : ℝ)| ≤
      η * (1 / (k : ℝ)) + K * ((Y : ℝ) / B) := by
    intro k hk
    have hkpos : 0 < k := (mem_Icc.mp (hS hk)).1
    have hkR : (0 : ℝ) < k := by exact_mod_cast hkpos
    rw [abs_div, abs_of_pos hkR, div_eq_mul_one_div]
    by_cases hq : Y ≤ B / k
    · have hsmall : |f (B / k)| ≤ η := by
        simpa only [Real.dist_eq, sub_zero] using (hY (B / k) hq).le
      exact (mul_le_mul_of_nonneg_right hsmall (by positivity)).trans
        (le_add_of_nonneg_right (mul_nonneg hK0 (by positivity)))
    · have hlt : B < Y * k := by
        simpa only [Nat.mul_comm] using
          (Nat.div_lt_iff_lt_mul hkpos).mp (show B / k < Y by omega)
      have hinv : 1 / (k : ℝ) ≤ (Y : ℝ) / B := by
        rw [div_le_div_iff₀ hkR hBR]
        simpa only [one_mul] using (show (B : ℝ) ≤ (Y : ℝ) * k by exact_mod_cast hlt.le)
      exact (mul_le_mul (hK _) hinv (by positivity) hK0).trans
        (le_add_of_nonneg_left (mul_nonneg hη.le (by positivity)))
  have hcard : (S.card : ℝ) ≤ (B : ℝ) := by
    have hcardNat : S.card ≤ B :=
      (card_le_card hS).trans (by simpa only [Nat.card_Icc, Nat.add_sub_cancel] using hAB)
    exact_mod_cast hcardNat
  have htail : (S.card : ℝ) * (K * ((Y : ℝ) / B)) ≤ K * Y := by
    calc
      (S.card : ℝ) * (K * ((Y : ℝ) / B)) ≤
        (B : ℝ) * (K * ((Y : ℝ) / B)) :=
        mul_le_mul_of_nonneg_right hcard (mul_nonneg hK0 (by positivity))
      _ = K * Y := by field_simp [hBR.ne']
  calc
    |∑ k ∈ S, f (B / k) / (k : ℝ)| ≤
      ∑ k ∈ S, |f (B / k) / (k : ℝ)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ S, (η * (1 / (k : ℝ)) + K * ((Y : ℝ) / B)) := sum_le_sum hterm
    _ = η * (∑ k ∈ S, 1 / (k : ℝ)) + (S.card : ℝ) * (K * ((Y : ℝ) / B)) := by
      rw [sum_add_distrib, ← mul_sum, sum_const, nsmul_eq_mul]
    _ ≤ _ := add_le_add le_rfl htail

end GaloisForLFunctions.HTGeometry
