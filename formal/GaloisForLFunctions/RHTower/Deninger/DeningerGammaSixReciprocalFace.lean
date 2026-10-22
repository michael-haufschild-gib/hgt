import GaloisForLFunctions.RHTower.Deninger.DeningerGammaSixResidueLanding

/-!
# The functional-equation mate cancels the pole but not the phase

In the critical strip the archimedean ratio `G(s) = A(s)/A(1-s)` satisfies `G(s)/ζ(1-s) = 1/ζ(s)`,
because `A(s)ζ(s)` is the completed Xi function and Xi is invariant under `s ↦ 1-s`.  Subtracting
the two multipliers therefore removes every nontrivial-divisor pole before a zero is selected, and
the paired six-tail face is the finite Stokes remainder `P₆(s) - G(s)P₆(1-s)`.

The place-marked regulators of the same polygon sum to zero, because `log 6 = log 2 + log 3`.

* `deningerXi_eq_completed` : `Ξ = ½s(s-1)Λ` on the critical strip.
* `deningerXi_one_sub` : **the functional equation `Ξ(1-s) = Ξ(s)`.**
* `deningerArchimedeanRatio_div` : **`(15)`: `G(s)/ζ(1-s) = 1/ζ(s)`.**
* `deningerSixTail_reciprocal_face` : **`(16)`: the paired multiplier is the finite remainder.**
* `deningerSixPlaceRegulator_sum_zero` : **`(19)`: the place-marked regulators cancel.**
-/

namespace GaloisForLFunctions

open Complex

noncomputable section

theorem deningerGammaR_ne_zero {s : ℂ} (h0 : 0 < s.re) : Gammaℝ s ≠ 0 := by
  rw [Gammaℝ_def]
  refine mul_ne_zero ?_ ?_
  · refine Complex.cpow_ne_zero_iff.2 (Or.inl ?_)
    exact_mod_cast Real.pi_ne_zero
  · refine Complex.Gamma_ne_zero fun m => ?_
    intro hcontra
    have hre : (s / 2).re = -(m : ℝ) := by rw [hcontra]; simp
    have : s.re / 2 = -(m : ℝ) := by simpa using hre
    have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith

/-- On the right half plane the factored Xi is `½s(s-1)` times the completed zeta. -/
theorem deningerXi_eq_completed {s : ℂ} (h0 : 0 < s.re) :
    deningerXi s = (1 / 2 : ℂ) * s * (s - 1) * completedRiemannZeta s := by
  have hs : s ≠ 0 := by
    intro h
    rw [h] at h0
    simp at h0
  have hG : Gammaℝ s ≠ 0 := deningerGammaR_ne_zero h0
  have hzeta : riemannZeta s = completedRiemannZeta s / Gammaℝ s :=
    riemannZeta_def_of_ne_zero hs
  have hA : deningerArchimedeanFactor s = (1 / 2 : ℂ) * s * (s - 1) * Gammaℝ s := by
    rw [deningerArchimedeanFactor, Gammaℝ_def]
    ring
  rw [deningerXi, hA, hzeta]
  field_simp

/-- **The functional equation `Ξ(1-s) = Ξ(s)` on the critical strip.** -/
theorem deningerXi_one_sub {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) :
    deningerXi (1 - s) = deningerXi s := by
  have h0' : 0 < (1 - s).re := by
    rw [Complex.sub_re, Complex.one_re]
    linarith
  rw [deningerXi_eq_completed h0', deningerXi_eq_completed h0, completedRiemannZeta_one_sub]
  ring

/-- The archimedean ratio `G(s) = A(s)/A(1-s)` of `(14)`. -/
def deningerArchimedeanRatio (s : ℂ) : ℂ :=
  deningerArchimedeanFactor s / deningerArchimedeanFactor (1 - s)

/-- **`(15)`: `G(s)/ζ(1-s) = 1/ζ(s)`.** -/
theorem deningerArchimedeanRatio_div {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1)
    (hz : riemannZeta s ≠ 0) (hz' : riemannZeta (1 - s) ≠ 0) :
    deningerArchimedeanRatio s / riemannZeta (1 - s) = (riemannZeta s)⁻¹ := by
  have h0' : 0 < (1 - s).re := by
    rw [Complex.sub_re, Complex.one_re]
    linarith
  have h1' : (1 - s).re < 1 := by
    rw [Complex.sub_re, Complex.one_re]
    linarith
  have hA : deningerArchimedeanFactor s ≠ 0 := deningerArchimedeanFactor_ne_zero h0 h1
  have hA' : deningerArchimedeanFactor (1 - s) ≠ 0 :=
    deningerArchimedeanFactor_ne_zero h0' h1'
  have hfe : deningerArchimedeanFactor s * riemannZeta s
      = deningerArchimedeanFactor (1 - s) * riemannZeta (1 - s) := by
    have := deningerXi_one_sub h0 h1
    rw [deningerXi, deningerXi] at this
    exact this.symm
  rw [deningerArchimedeanRatio, div_div, ← hfe, div_mul_eq_div_div, div_self hA, one_div]

/-- **`(16)`: the paired six-tail multiplier is the finite Stokes remainder.**  Every
nontrivial-divisor pole cancels before a zero is selected. -/
theorem deningerSixTail_reciprocal_face {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1)
    (hz : riemannZeta s ≠ 0) (hz' : riemannZeta (1 - s) ≠ 0) :
    deningerSixTailMultiplier s
        - deningerArchimedeanRatio s * deningerSixTailMultiplier (1 - s)
      = deningerSixTailCorrection s
        - deningerArchimedeanRatio s * deningerSixTailCorrection (1 - s) := by
  have hkey := deningerArchimedeanRatio_div h0 h1 hz hz'
  rw [deningerSixTailMultiplier, deningerSixTailMultiplier, mul_add]
  have hpole : deningerArchimedeanRatio s * (riemannZeta (1 - s))⁻¹
      = (riemannZeta s)⁻¹ := by
    rw [← hkey, div_eq_mul_inv]
  rw [← hpole]
  ring

/-! ## The place-marked regulators -/

/-- The three placewise Kummer regulators of `(19)`. -/
def deningerSixPlaceRegulator (m : ℕ) : ℝ × ℝ × ℝ :=
  (2 * m * Real.log 6, -(2 * m * Real.log 2), -(2 * m * Real.log 3))

/-- **`(19)`: the place-marked regulators sum to zero**, because `log 6 = log 2 + log 3`. -/
theorem deningerSixPlaceRegulator_sum_zero (m : ℕ) :
    (deningerSixPlaceRegulator m).1 + (deningerSixPlaceRegulator m).2.1
      + (deningerSixPlaceRegulator m).2.2 = 0 := by
  have hlog : Real.log 6 = Real.log 2 + Real.log 3 := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]
    norm_num
  rw [deningerSixPlaceRegulator, hlog]
  ring

end

end GaloisForLFunctions
