import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralFilling.ReplicaOrders.NearHilbertWindow
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.Detuning.AllHeights.Growth

/-! # Doubly exponential record length for the half-order gate test -/
open Filter Set MeasureTheory
namespace GaloisForLFunctions.HTGeometry.SpectralFilling.ReplicaOrders
open SpectralJets SpectralJets.AllHeights
noncomputable section

/-- The half-dimension order has polynomial height. The derivative bound
therefore controls its dephasing time by two to a polynomial in dimension. -/
theorem windowLength_bound : ∃ c : ℕ, ∀ k : ℕ, windowLength k ≤ (2:ℝ)^((2^(k+3):ℕ)^c) := by
  let h (k : ℕ) := 2^(k+1)
  let q (k : ℕ) := 2*h k
  have hh : PolynomialInDimension h := PolynomialInDimension.dim.mono (fun k =>
    Nat.pow_le_pow_right (by decide) (by omega : k+1 ≤ k+3))
  have hq : PolynomialInDimension q := (PolynomialInDimension.const 2).mul hh
  have ha := (LogPolynomialInDimension.const 4).mul (LogPolynomialInDimension.natCast hh)
  have hb := inverse_height_log_polynomial q (LogPolynomialInDimension.natCast hq)
  apply LogPolynomialInDimension.bound
  apply (ha.mul hb).mono
  · intro k
    exact div_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)) (effectiveGap_pos k (q k)).le
  · intro k
    change 4*Real.sqrt (h k:ℝ)/effectiveGap k (q k) ≤ (4*(h k:ℝ))*(heightMargin k (q k))⁻¹
    have h₁ : 1 ≤ (h k:ℝ) := by exact_mod_cast (Nat.one_le_two_pow : 1 ≤ 2^(k+1))
    have hs := (Real.sqrt_le_iff).mpr ⟨(Nat.cast_nonneg (h k)),
      by nlinarith only [h₁,mul_nonneg (sub_nonneg.mpr h₁) (Nat.cast_nonneg (h k))]⟩
    rw [div_eq_mul_inv]
    exact mul_le_mul (mul_le_mul_of_nonneg_left hs (by norm_num))
      (inv_anti₀ (heightMargin_pos k (q k)) (le_max_right ..))
      (inv_nonneg.mpr (effectiveGap_pos k (q k)).le) (by positivity)

/-- On one frozen Gaussian chain, each sufficiently large prefix has an
absolute record length valid for every origin and every error through 39/80. -/
theorem gaussian_absolute_nearHilbert_window :
    ∃ c : ℕ, ∃ b ∈ Ioo (0:ℝ) 1, ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop,
      let K := k+3
      let D : ℕ := 2^K
      let u := pathPauliDisorderShell ω (k+1)
      let H : selfAdjoint (SharpOccupation.Register K) := ⟨pathHamiltonian u,isSelfAdjoint_pathHamiltonian u⟩
      ∀ ε : ℝ, ε ≤ 39/80 → ∀ o : ℝ, ∀ T ≥ (2:ℝ)^(D^c), ∀ j ≤ nearHilbertContinuousCircuitBudget K,
        SharpOccupation.visitFraction H j ε o (o+T) < b^D := by
  obtain ⟨c,hc⟩ := windowLength_bound
  obtain ⟨b,hb,h⟩ := gaussian_nearHilbert_window
  refine ⟨c,b,hb,?_⟩
  filter_upwards [h] with ω hw
  filter_upwards [hw] with k hk
  intro K D u H ε hε o T hT
  exact hk ε hε o T ((hc k).trans hT)

#print axioms gaussian_absolute_nearHilbert_window
end
end GaloisForLFunctions.HTGeometry.SpectralFilling.ReplicaOrders
