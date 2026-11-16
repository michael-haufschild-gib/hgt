import GaloisForLFunctions.HTGeometry.HardyBoundary.DirichletBoundaryCyclicity

/-!
# Repeated boundary zeros preserve polynomial Dirichlet density

The harmonic-kernel approximation to one extends to every power of `1 - X`.
The induction uses bounded multiplication by each fixed polynomial: first
approximate one by a multiple of the old power, then approximate one by a
multiple of `1 - X` finely enough for that fixed multiplier. Consequently each
ideal `(1 - X)^m` is dense in polynomial Dirichlet energy, despite its prescribed
boundary zero of arbitrary multiplicity.
-/

open Polynomial Filter
open scoped Topology

namespace HTGeometry.DirichletBoundaryCyclicity
noncomputable section

private theorem exists_boundary_approximant (ε : ℝ) (hε : 0 < ε) :
    ∃ p : Polynomial ℝ, coefficientEnergy (1 - (1 - X) * p) < ε := by
  obtain ⟨N, hN⟩ := (approximant_energy_tendsto.eventually (gt_mem_nhds hε)).exists
  exact ⟨approximant N, hN⟩

private theorem exists_boundary_power_approximant (m : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ p : Polynomial ℝ, coefficientEnergy (1 - (1 - X)^m * p) < ε := by
  induction m generalizing ε with
  | zero =>
      refine ⟨1, ?_⟩
      simpa only [pow_zero, one_mul, sub_self, coefficientEnergy_zero] using hε
  | succ m ih =>
      obtain ⟨p, hp⟩ := ih (ε / 4) (by positivity)
      obtain ⟨C, hC, hmult⟩ := exists_coefficientEnergy_multiplier_bound ((1 - X)^m * p)
      have hC1 : 0 < C + 1 := by linarith only [hC]
      obtain ⟨q, hq⟩ := exists_boundary_approximant (ε / (4 * (C + 1))) (by positivity)
      have heq : (C + 1) * (ε / (4 * (C + 1))) = ε / 4 := by field_simp
      have hsmall : coefficientEnergy (((1 - X)^m * p) * (1 - (1 - X) * q)) < ε / 4 := by
        have hlarge := mul_lt_mul_of_pos_left hq hC1
        rw [heq] at hlarge
        have hstep : C * coefficientEnergy (1 - (1 - X) * q) ≤
            (C + 1) * coefficientEnergy (1 - (1 - X) * q) :=
          mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one)
            (coefficientEnergy_nonneg _)
        exact ((hmult _).trans hstep).trans_lt hlarge
      refine ⟨p * q, ?_⟩
      have he : 1 - (1 - X)^(m + 1) * (p * q) =
          (1 - (1 - X)^m * p) + ((1 - X)^m * p) * (1 - (1 - X) * q) := by
        rw [pow_succ]
        ring
      rw [he]
      have hadd := coefficientEnergy_add_le (1 - (1 - X)^m * p)
        (((1 - X)^m * p) * (1 - (1 - X) * q))
      linarith only [hadd, hp, hsmall]

/-- Polynomial factors whose multiples by `(1 - X)^m` converge to one. -/
def boundaryPowerApproximant (m N : ℕ) : Polynomial ℝ :=
  (exists_boundary_power_approximant m (N + 1 : ℝ)⁻¹ (by positivity)).choose

theorem boundaryPowerApproximant_error_lt (m N : ℕ) :
    coefficientEnergy (1 - (1 - X)^m * boundaryPowerApproximant m N) < (N + 1 : ℝ)⁻¹ :=
  (exists_boundary_power_approximant m (N + 1 : ℝ)⁻¹ (by positivity)).choose_spec

/-- Every boundary multiplicity admits a sequence of polynomial approximants to one. -/
theorem boundary_power_cyclicity (m : ℕ) :
    Tendsto (fun N => coefficientEnergy (1 - (1 - X)^m * boundaryPowerApproximant m N))
      atTop (𝓝 0) := by
  apply squeeze_zero (fun _ => coefficientEnergy_nonneg _)
    (fun N => (boundaryPowerApproximant_error_lt m N).le)
  exact tendsto_inv_atTop_zero.comp
    (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)

/-- Every positive power enforces the boundary zero on every approximating polynomial. -/
theorem boundaryPowerApproximant_eval_one (m N : ℕ) :
    ((1 - X)^(m + 1) * boundaryPowerApproximant (m + 1) N).eval 1 = 0 := by
  simp

/-- Multiples with arbitrarily high prescribed boundary multiplicity approximate every polynomial. -/
theorem boundary_power_dense (m : ℕ) (p : Polynomial ℝ) :
    ∃ q : ℕ → Polynomial ℝ,
      Tendsto (fun N => coefficientEnergy (p - (1 - X)^m * q N)) atTop (𝓝 0) := by
  obtain ⟨C, hC, hmult⟩ := exists_coefficientEnergy_multiplier_bound p
  refine ⟨fun N => p * boundaryPowerApproximant m N, ?_⟩
  have hbound (N : ℕ) :
      coefficientEnergy (p - (1 - X)^m * (p * boundaryPowerApproximant m N)) ≤
        C * coefficientEnergy (1 - (1 - X)^m * boundaryPowerApproximant m N) := by
    have he : p - (1 - X)^m * (p * boundaryPowerApproximant m N) =
        p * (1 - (1 - X)^m * boundaryPowerApproximant m N) := by ring
    rw [he]
    exact hmult _
  apply squeeze_zero (fun _ => coefficientEnergy_nonneg _) hbound
  simpa only [mul_zero] using Filter.Tendsto.const_mul C (boundary_power_cyclicity m)

#print axioms boundary_power_cyclicity
#print axioms boundary_power_dense

end
end HTGeometry.DirichletBoundaryCyclicity
