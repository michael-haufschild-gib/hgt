import GaloisForLFunctions.RHTower.ZetaCarrier
import GaloisForLFunctions.RHTower.ExteriorParity

/-!
# The archimedean × prime cross-term: the FE-conspiracy cocycle is purely archimedean

The functional equation of the completed zeta function is the statement that the two factor defects
multiply to one,

`ρ_∞(s) · ρ_ζ(s) = 1`,  `ρ_∞(s) = Γ_ℝ(1−s)/Γ_ℝ(s)`,  `ρ_ζ(s) = ζ(1−s)/ζ(s)`.

The archimedean defect is built from `π` and `Γ` alone — no integer prime occurs in it — and it is
**not** a horizontal gauge: it is a nonconstant function, so the reflection cannot be realized inside
the archimedean factor as a module automorphism.  The prime lane therefore carries the reflection
with no defect of its own, and the whole obstruction sits in `ρ_∞`.

The prime-side statement that the reflection acts there by inversion, with the resulting sign a
parity of the exterior power, is the pre-existing `exteriorPower_map_neg_id`.

## Main results

* `zetaChi_mul_zetaRho` — the cocycle relation `ρ_∞ · ρ_ζ = 1`;
* `zetaChi_eq_pi_cpow_mul_gamma_ratio` — `ρ_∞` is `π^{s−1/2} Γ((1−s)/2)/Γ(s/2)`: purely archimedean;
* `zetaChi_half`, `zetaChi_two` — two exact values;
* `zetaChi_not_constant` — `ρ_∞` is nonconstant, hence not a horizontal gauge.
-/

noncomputable section

namespace RHTower

open Complex

/-- The prime-lane functional-equation defect `ρ_ζ(s) = ζ(1−s)/ζ(s)`. -/
def zetaRho (s : ℂ) : ℂ := riemannZeta (1 - s) / riemannZeta s

/-- **The FE-conspiracy cocycle relation.**  The archimedean and prime defects multiply to one; this
is exactly the functional equation of the completed zeta function. -/
theorem zetaChi_mul_zetaRho {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1)
    (hG : Gammaℝ (1 - s) ≠ 0) (hz : riemannZeta s ≠ 0) :
    zetaChi s * zetaRho s = 1 := by
  have hfe := zeta_eq_zetaChi_mul h0 h1 hG
  rw [zetaRho, mul_div_assoc']
  rw [div_eq_one_iff_eq hz]
  exact hfe.symm

/-- **The archimedean defect is purely archimedean.**  It is `π^{s−1/2}` times a ratio of `Γ`
values: no integer prime occurs in it. -/
theorem zetaChi_eq_pi_cpow_mul_gamma_ratio (s : ℂ) :
    zetaChi s
      = (Real.pi : ℂ) ^ (s - 1 / 2) * Complex.Gamma ((1 - s) / 2) / Complex.Gamma (s / 2) := by
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hp : (Real.pi : ℂ) ^ (-(1 - s) / 2) / (Real.pi : ℂ) ^ (-s / 2)
      = (Real.pi : ℂ) ^ (s - 1 / 2) := by
    rw [← Complex.cpow_sub _ _ hpi]
    congr 1
    ring
  show Gammaℝ (1 - s) / Gammaℝ s = _
  calc Gammaℝ (1 - s) / Gammaℝ s
      = ((Real.pi : ℂ) ^ (-(1 - s) / 2) * Complex.Gamma ((1 - s) / 2)) /
        ((Real.pi : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2)) := by
        rw [Gammaℝ_def, Gammaℝ_def]
    _ = ((Real.pi : ℂ) ^ (-(1 - s) / 2) / (Real.pi : ℂ) ^ (-s / 2)) *
        (Complex.Gamma ((1 - s) / 2) / Complex.Gamma (s / 2)) :=
        (div_mul_div_comm _ _ _ _).symm
    _ = (Real.pi : ℂ) ^ (s - 1 / 2) * (Complex.Gamma ((1 - s) / 2) / Complex.Gamma (s / 2)) := by
        rw [hp]
    _ = (Real.pi : ℂ) ^ (s - 1 / 2) * Complex.Gamma ((1 - s) / 2) / Complex.Gamma (s / 2) := by
        rw [mul_div_assoc]

/-- The archimedean defect is `1` at the centre. -/
theorem zetaChi_half : zetaChi (1 / 2 : ℂ) = 1 := by
  have hne : Gammaℝ (1 / 2 : ℂ) ≠ 0 := by
    refine Gammaℝ_ne_zero_of_re_pos ?_
    norm_num
  show Gammaℝ (1 - 1 / 2 : ℂ) / Gammaℝ (1 / 2 : ℂ) = 1
  rw [show (1 : ℂ) - 1 / 2 = 1 / 2 by ring]
  exact div_self hne

/-- The value of `Γ_ℝ` at `-1`. -/
theorem Gammaℝ_neg_one : Gammaℝ (-1 : ℂ) = -2 * (Real.pi : ℂ) := by
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have h := Gammaℝ_add_two (s := (-1 : ℂ)) (by norm_num)
  rw [show (-1 : ℂ) + 2 = 1 by ring, Gammaℝ_one] at h
  field_simp at h
  linear_combination h

/-- The value of `Γ_ℝ` at `2`. -/
theorem Gammaℝ_two : Gammaℝ (2 : ℂ) = (Real.pi : ℂ)⁻¹ := by
  rw [Gammaℝ_def]
  rw [show (2 : ℂ) / 2 = 1 by norm_num, Complex.Gamma_one, mul_one,
    show -(2 : ℂ) / 2 = -1 by norm_num, Complex.cpow_neg_one]

/-- The archimedean defect at `s = 2`. -/
theorem zetaChi_two : zetaChi (2 : ℂ) = -2 * (Real.pi : ℂ) ^ 2 := by
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  show Gammaℝ (1 - 2 : ℂ) / Gammaℝ (2 : ℂ) = _
  rw [show (1 : ℂ) - 2 = -1 by ring, Gammaℝ_neg_one, Gammaℝ_two]
  field_simp

/-- **The archimedean defect is not a horizontal gauge.**  It is nonconstant, so the reflection
cannot be realized as an automorphism inside the archimedean factor: the whole functional-equation
obstruction is carried by `ρ_∞`. -/
theorem zetaChi_not_constant : ¬ ∃ c : ℂ, ∀ s : ℂ, zetaChi s = c := by
  rintro ⟨c, hc⟩
  have h1 : c = 1 := by rw [← hc (1 / 2 : ℂ), zetaChi_half]
  have h2 : c = -2 * (Real.pi : ℂ) ^ 2 := by rw [← hc (2 : ℂ), zetaChi_two]
  rw [h1] at h2
  have hcast : ((1 : ℝ) : ℂ) = ((-2 * Real.pi ^ 2 : ℝ) : ℂ) := by
    push_cast
    exact h2
  have hreal : (1 : ℝ) = -2 * Real.pi ^ 2 := by exact_mod_cast hcast
  nlinarith [Real.pi_pos]

end RHTower
