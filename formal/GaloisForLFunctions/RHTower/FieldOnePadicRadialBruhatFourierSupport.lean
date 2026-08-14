import GaloisForLFunctions.RHTower.FieldOnePadicRadialBruhatClassification

/-!
# Fourier support of radial p-adic Bruhat vectors with a Sonin gap

The finite shell classification implies that the Fourier transform of every
radial Bruhat function vanishing on `pℤ_p` is supported in `p⁻¹ℤ_p`.
-/

namespace GaloisForLFunctions.RHTower

noncomputable section

open MeasureTheory Set Topology TopologicalSpace
open scoped BigOperators ENNReal NNReal ComplexConjugate

variable (p : ℕ) [Fact p.Prime]

theorem fieldOnePadicSoninBallSet_mono
    {m n : ℤ} (hmn : m ≤ n) :
    fieldOnePadicSoninBallSet p m ⊆
      fieldOnePadicSoninBallSet p n := by
  intro x hx
  rcases eq_or_ne x 0 with rfl | hx0
  · change ((((fieldOnePadicPrimeUnit p) ^ n : ℚ_[p]ˣ) : ℚ_[p]) * 0) ∈
      fieldOnePadicUnitBall p
    refine ⟨(0 : ℤ_[p]), ?_⟩
    simp
  · have hv :=
      (fieldOnePadicSoninBallSet_mem_iff_valuation p m hx0).mp hx
    exact (fieldOnePadicSoninBallSet_mem_iff_valuation p n hx0).mpr (by omega)

theorem fieldOnePadicBruhatFourierLinear_soninShell
    (n : ℤ) :
    fieldOnePadicBruhatFourierLinear p
        (fieldOnePadicSoninShell p n) =
      ((p : ℂ) ^ n) • fieldOnePadicSoninBall p (-n) -
        ((p : ℂ) ^ (n - 1)) •
          fieldOnePadicSoninBall p (1 - n) := by
  rw [fieldOnePadicSoninShell, map_sub,
    fieldOnePadicBruhatFourierLinear_soninBall,
    fieldOnePadicBruhatFourierLinear_soninBall]
  congr 2
  ring

theorem fieldOnePadicBruhatFourier_soninShell_eq_zero_outside_outer
    (n : ℕ) {x : ℚ_[p]}
    (hx : x ∉ fieldOnePadicSoninOuterFourierBall p) :
    (fieldOnePadicBruhatFourierLinear p
      (fieldOnePadicSoninShell p (n : ℤ))).1 x = 0 := by
  have hneg : x ∉ fieldOnePadicSoninBallSet p (-(n : ℤ)) := by
    intro h
    exact hx (fieldOnePadicSoninBallSet_mono p (by omega) h)
  have hone : x ∉ fieldOnePadicSoninBallSet p (1 - (n : ℤ)) := by
    intro h
    exact hx (fieldOnePadicSoninBallSet_mono p (by omega) h)
  rw [fieldOnePadicBruhatFourierLinear_soninShell]
  change (p : ℂ) ^ (n : ℤ) *
      (fieldOnePadicSoninBall p (-(n : ℤ))).1 x -
    (p : ℂ) ^ ((n : ℤ) - 1) *
      (fieldOnePadicSoninBall p (1 - (n : ℤ))).1 x = 0
  rw [fieldOnePadicSoninBall_apply_eq_indicator,
    fieldOnePadicSoninBall_apply_eq_indicator]
  simp [hneg, hone]

theorem fieldOnePadicRadialBruhat_fourier_eq_zero_outside_outer
    (f : compactlySupportedLocallyConstant ℚ_[p])
    (hunit : ∀ u : ℤ_[p]ˣ, ∀ x : ℚ_[p],
      f.1 ((((u : ℤ_[p]) : ℚ_[p])) * x) = f.1 x)
    (hgap : ∀ x ∈ fieldOnePadicSoninInnerBall p, f.1 x = 0)
    {x : ℚ_[p]} (hx : x ∉ fieldOnePadicSoninOuterFourierBall p) :
    (fieldOnePadicBruhatFourierLinear p f).1 x = 0 := by
  obtain ⟨N, hN⟩ := fieldOnePadicRadialBruhat_eq_shellSum p f hunit hgap
  rw [hN]
  change fieldOnePadicBruhatEvalLinear p x
    (fieldOnePadicBruhatFourierLinear p
      (∑ n ∈ Finset.range (N + 1),
        (fieldOnePadicRadialShellCoefficient p f n) •
          fieldOnePadicSoninShell p (n : ℤ))) = 0
  simp only [map_sum, map_smul, fieldOnePadicBruhatEvalLinear_apply,
    smul_eq_mul]
  apply Finset.sum_eq_zero
  intro n hn
  rw [fieldOnePadicBruhatFourier_soninShell_eq_zero_outside_outer p n hx]
  ring

end

end GaloisForLFunctions.RHTower
