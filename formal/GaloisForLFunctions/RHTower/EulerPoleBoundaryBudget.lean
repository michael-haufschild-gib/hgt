import GaloisForLFunctions.RHTower.XiThetaSquareRateLaplace

/-!
# The four-unit Euler-pole boundary profile

The existing causal Laplace infrastructure already contains the incoming boundary channel left by
the finite-prime completed logarithmic source.  In the project Fourier normalization, choosing the
rate `x = (2π)⁻¹` gives the causal exponential `exp (-t/2)`.  Multiplicity two therefore produces
the Euler-pole profile `2 exp (-t/2)`, whose squared `L²` norm is exactly four.

This module formalizes the incoming budget only.  It does not assert that the all-prime
Euler--Gamma continuation transports this vector contractively to the transverse-divisor channel;
that is the RH-bearing analytic theorem.
-/

open Complex Real MeasureTheory

noncomputable section

namespace RHTower

private lemma eulerPoleRate_pos : 0 < (2 * Real.pi)⁻¹ := by
  positivity

/-- The incoming Euler-pole boundary channel as a canonical `L²(ℝ)` vector. -/
def eulerPoleBoundaryProfileL2 : Lp ℂ 2 (volume : Measure ℝ) :=
  (2 : ℂ) • causalLaplaceWeightL2 ((2 * Real.pi)⁻¹) eulerPoleRate_pos

/-- The pointwise causal representative `2 exp (-t/2)` on the positive half-line. -/
def eulerPoleBoundaryProfile (t : ℝ) : ℂ :=
  Set.Ioi (0 : ℝ) |>.indicator
    (fun y => (2 : ℂ) * Complex.exp (-(y / 2 : ℝ))) t

/-- The canonical `L²` vector is represented almost everywhere by the expected Euler-pole
exponential. -/
theorem eulerPoleBoundaryProfileL2_ae :
    (fun t : ℝ => eulerPoleBoundaryProfileL2 t) =ᵐ[volume]
      eulerPoleBoundaryProfile := by
  filter_upwards [Lp.coeFn_smul (2 : ℂ)
      (causalLaplaceWeightL2 ((2 * Real.pi)⁻¹) eulerPoleRate_pos),
    causalLaplaceWeightL2_ae ((2 * Real.pi)⁻¹) eulerPoleRate_pos] with t hsmul ht
  rw [eulerPoleBoundaryProfileL2, hsmul, Pi.smul_apply, ht]
  by_cases hpos : 0 < t
  · rw [eulerPoleBoundaryProfile,
      Set.indicator_of_mem (show t ∈ Set.Ioi (0 : ℝ) from hpos),
      causalLaplaceWeightFun_of_pos hpos]
    rw [smul_eq_mul]
    congr 1
    congr 1
    field_simp [Real.pi_ne_zero]
  · rw [eulerPoleBoundaryProfile,
      Set.indicator_of_notMem (show t ∉ Set.Ioi (0 : ℝ) by simpa using hpos)]
    unfold causalLaplaceWeightFun causalFourierExponential
    rw [Set.indicator_of_notMem (show t ∉ Set.Ioi (0 : ℝ) by simpa using hpos),
      mul_zero, smul_zero]

/-- The unit-amplitude rate-`1/2` causal exponential has squared norm one in the existing Fourier
normalization. -/
theorem norm_causalLaplaceWeightL2_eulerPole_sq :
    ‖causalLaplaceWeightL2 ((2 * Real.pi)⁻¹) eulerPoleRate_pos‖ ^ 2 = 1 := by
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ),
    inner_causalLaplaceWeightL2 eulerPoleRate_pos eulerPoleRate_pos]
  push_cast
  field_simp [Real.pi_ne_zero]
  norm_num

/-- **Exact four-unit incoming budget.** The Euler-pole channel `2 exp (-t/2)` has squared
`L²(ℝ)` norm exactly `4`. -/
theorem norm_eulerPoleBoundaryProfileL2_sq :
    ‖eulerPoleBoundaryProfileL2‖ ^ 2 = 4 := by
  rw [eulerPoleBoundaryProfileL2, norm_smul]
  rw [show ‖(2 : ℂ)‖ = 2 by norm_num]
  have hsq := norm_causalLaplaceWeightL2_eulerPole_sq
  nlinarith

end RHTower
