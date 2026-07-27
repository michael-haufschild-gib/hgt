import GaloisForLFunctions.HTGeometry.CoshHalfPowerLowerBound
import GaloisForLFunctions.RHTower.SquarefreePartitionPole

/-!
# The critical Gamma--Sonin constant and its super-four bound

The time-one Gamma cyclic covariance `φ(h) = (cosh h)^(-1/2)` is the characteristic function of a
probability measure with continuous density, whose value at zero is the Fourier inversion integral

```text
ρ_Γ(0) = (1/2π) ∫_ℝ (cosh t)^(-1/2) dt = Γ(1/4)/(2 √π Γ(3/4)).
```

Sewing it to the squarefree Dirichlet pole `1/ζ(2)` against the centred pole profile produces the
residue--density constant

```text
C_Γ = 2 √2 ρ_Γ(0) π / ζ(2) = 6 √2 Γ(1/4)/(π^(3/2) Γ(3/4)),
```

and the elementary envelope `cosh t ≤ (e^t+1)/2` forces `C_Γ ≥ 48 arsinh 1/π² > 4`: the archimedean
excess over the four-unit source budget is strict.
-/

open MeasureTheory

namespace RHTower

noncomputable section

/-- Spectral density at zero of the time-one Gamma cyclic measure, i.e. Fourier inversion of the
covariance `φ(h) = (cosh h)^(-1/2)`. -/
def gammaCyclicDensityZero : ℝ :=
  (1 / (2 * Real.pi)) * ∫ t : ℝ, (Real.cosh t) ^ (-(1 / 2) : ℝ)

/-- **The archimedean density at zero.** `ρ_Γ(0) = Γ(1/4)/(2 √π Γ(3/4))`. -/
theorem gammaCyclicDensityZero_eq :
    gammaCyclicDensityZero
      = Real.Gamma (1 / 4) / (2 * Real.sqrt Real.pi * Real.Gamma (3 / 4)) := by
  have hval := HTGeometry.integral_cosh_rpow_neg (by norm_num : (0 : ℝ) < 1 / 2)
  norm_num at hval
  have hsp : Real.sqrt Real.pi * Real.sqrt Real.pi = Real.pi :=
    Real.mul_self_sqrt Real.pi_pos.le
  have hGne : Real.Gamma (3 / 4 : ℝ) ≠ 0 := ne_of_gt (Real.Gamma_pos_of_pos (by norm_num))
  have halg : ∀ S G A : ℝ, 0 < S → G ≠ 0 →
      (1 / (2 * (S * S))) * (S * A / G) = A / (2 * S * G) := by
    intro S G A hS hG
    have hSne : S ≠ 0 := ne_of_gt hS
    field_simp
  rw [gammaCyclicDensityZero, hval]
  calc (1 / (2 * Real.pi)) * (Real.sqrt Real.pi * Real.Gamma (1 / 4) / Real.Gamma (3 / 4))
      = (1 / (2 * (Real.sqrt Real.pi * Real.sqrt Real.pi))) *
          (Real.sqrt Real.pi * Real.Gamma (1 / 4) / Real.Gamma (3 / 4)) := by rw [hsp]
    _ = Real.Gamma (1 / 4) / (2 * Real.sqrt Real.pi * Real.Gamma (3 / 4)) :=
        halg _ _ _ (Real.sqrt_pos.mpr Real.pi_pos) hGne

/-- The critical Gamma--Sonin constant `C_Γ = 6 √2 Γ(1/4)/(π^(3/2) Γ(3/4))`. -/
def gammaCriticalConstant : ℝ :=
  6 * Real.sqrt 2 * Real.Gamma (1 / 4) / (Real.pi * Real.sqrt Real.pi * Real.Gamma (3 / 4))

/-- **Residue--density--profile form of the critical constant.**  `C_Γ` is the product of the
squarefree pole residue `1/ζ(2)`, the archimedean spectral density at zero, and the universal
centred-pole profile `2 √2 π`. -/
theorem gammaCriticalConstant_eq_residueDensityProfile :
    gammaCriticalConstant
      = 2 * Real.sqrt 2 * gammaCyclicDensityZero * Real.pi / (riemannZeta 2).re := by
  have hsp : Real.sqrt Real.pi * Real.sqrt Real.pi = Real.pi :=
    Real.mul_self_sqrt Real.pi_pos.le
  have hGne : Real.Gamma (3 / 4 : ℝ) ≠ 0 := ne_of_gt (Real.Gamma_pos_of_pos (by norm_num))
  have halg : ∀ S G A R : ℝ, 0 < S → G ≠ 0 →
      6 * R * A / (S * S * S * G)
        = 2 * R * (A / (2 * S * G)) * (S * S) / ((S * S) ^ 2 / 6) := by
    intro S G A R hS hG
    have hSne : S ≠ 0 := ne_of_gt hS
    field_simp
  rw [gammaCriticalConstant, gammaCyclicDensityZero_eq, re_riemannZeta_two]
  calc 6 * Real.sqrt 2 * Real.Gamma (1 / 4) /
        (Real.pi * Real.sqrt Real.pi * Real.Gamma (3 / 4))
      = 6 * Real.sqrt 2 * Real.Gamma (1 / 4) /
          (Real.sqrt Real.pi * Real.sqrt Real.pi * Real.sqrt Real.pi *
            Real.Gamma (3 / 4)) := by rw [hsp]
    _ = 2 * Real.sqrt 2 * (Real.Gamma (1 / 4) / (2 * Real.sqrt Real.pi * Real.Gamma (3 / 4))) *
          (Real.sqrt Real.pi * Real.sqrt Real.pi) /
          ((Real.sqrt Real.pi * Real.sqrt Real.pi) ^ 2 / 6) :=
        halg _ _ _ _ (Real.sqrt_pos.mpr Real.pi_pos) hGne
    _ = 2 * Real.sqrt 2 * (Real.Gamma (1 / 4) / (2 * Real.sqrt Real.pi * Real.Gamma (3 / 4))) *
          Real.pi / (Real.pi ^ 2 / 6) := by rw [hsp]

/-- **The critical constant is strictly larger than four.**  The envelope `cosh t ≤ (e^t+1)/2`
gives `C_Γ ≥ 48 arsinh 1/π²`, and `12 arsinh 1 > 21/2 > π²`. -/
theorem four_lt_gammaCriticalConstant : 4 < gammaCriticalConstant := by
  have hA : (7 : ℝ) / 8 < Real.arsinh 1 := HTGeometry.seven_div_eight_lt_arsinh_one
  have hq := HTGeometry.four_sqrt_two_mul_arsinh_one_le_gammaQuotient
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  have hsp : (0 : ℝ) < Real.sqrt Real.pi := Real.sqrt_pos.mpr hπ
  have hspsq : Real.sqrt Real.pi * Real.sqrt Real.pi = Real.pi := Real.mul_self_sqrt hπ.le
  have hG : (0 : ℝ) < Real.Gamma (3 / 4) := Real.Gamma_pos_of_pos (by norm_num)
  have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hGa : 4 * Real.sqrt 2 * Real.arsinh 1 * Real.Gamma (3 / 4)
      ≤ Real.sqrt Real.pi * Real.Gamma (1 / 4) := (le_div_iff₀ hG).mp hq
  have hpisq : Real.pi ^ 2 < 9.9225 := by nlinarith [Real.pi_lt_d2, hπ]
  have hkey : 4 * Real.pi ^ 2 * Real.Gamma (3 / 4)
      < 48 * Real.arsinh 1 * Real.Gamma (3 / 4) := by
    have h1 : Real.pi ^ 2 < 12 * Real.arsinh 1 := by linarith
    nlinarith [h1, hG]
  have hmul := mul_le_mul_of_nonneg_left hGa (by positivity : (0 : ℝ) ≤ 6 * Real.sqrt 2)
  have h2 : 48 * Real.arsinh 1 * Real.Gamma (3 / 4)
      ≤ 6 * Real.sqrt 2 * (Real.sqrt Real.pi * Real.Gamma (1 / 4)) := by
    calc 48 * Real.arsinh 1 * Real.Gamma (3 / 4)
        = 6 * Real.sqrt 2 * (4 * Real.sqrt 2 * Real.arsinh 1 * Real.Gamma (3 / 4)) := by
          linear_combination (-24 * Real.arsinh 1 * Real.Gamma (3 / 4)) * hs2
      _ ≤ _ := hmul
  rw [gammaCriticalConstant, lt_div_iff₀ (by positivity)]
  have hgoal : 4 * (Real.pi * Real.sqrt Real.pi * Real.Gamma (3 / 4)) * Real.sqrt Real.pi
      < 6 * Real.sqrt 2 * Real.Gamma (1 / 4) * Real.sqrt Real.pi := by
    calc 4 * (Real.pi * Real.sqrt Real.pi * Real.Gamma (3 / 4)) * Real.sqrt Real.pi
        = 4 * Real.pi ^ 2 * Real.Gamma (3 / 4) := by
          linear_combination (4 * Real.pi * Real.Gamma (3 / 4)) * hspsq
      _ < 48 * Real.arsinh 1 * Real.Gamma (3 / 4) := hkey
      _ ≤ 6 * Real.sqrt 2 * (Real.sqrt Real.pi * Real.Gamma (1 / 4)) := h2
      _ = 6 * Real.sqrt 2 * Real.Gamma (1 / 4) * Real.sqrt Real.pi := by ring
  exact lt_of_mul_lt_mul_right hgoal hsp.le

/-- The critical constant is positive. -/
theorem gammaCriticalConstant_pos : 0 < gammaCriticalConstant :=
  lt_trans (by norm_num) four_lt_gammaCriticalConstant

end

end RHTower
