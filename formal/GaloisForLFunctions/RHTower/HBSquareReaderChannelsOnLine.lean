import GaloisForLFunctions.RHTower.EisensteinLineRealness
import GaloisForLFunctions.RHTower.HardyTheorem

/-!
# The Weyl channels of the square reader on the critical line

The principal square of the centre reader `E*(·, ρ)` has the three Weyl channels

  `Λ(2ρ)² y^{2ρ} + 2Λ(2ρ)Λ(2ρ−1) y + Λ(2ρ−1)² y^{2−2ρ}`,   `Λ = π^{−s/2}Γ(s/2)ζ(s)`.

For a zero with `Re ρ < ½` the lower coefficient `Λ(2ρ−1)` cannot vanish since `Re(2ρ−1) < 0`.
It cannot vanish on the line either: for `ρ = ½ + iγ` one has `Λ(2ρ) = Λ(1+2iγ) ≠ 0` and
`Λ(2ρ−1) = Λ(2iγ) = conj Λ(1+2iγ) ≠ 0`.  Hardy's theorem supplies zeros on the line, so no law
can force `Λ(2ρ−1) = 0` at every zero of `ξ`; any cancellation law for these channels must be
sensitive to the real growth rates `2σ, 1, 2−2σ`, which coincide exactly on the line.  There the
principal square is the nonnegative real perfect square `y·(2·Re(Λ(1+2iγ)·y^{iγ}))²`.
-/

open Complex

namespace RHTower

noncomputable section

/-- `Λ(1 + 2it) ≠ 0` for every real `t ≠ 0`. -/
theorem eisLineLambda_ne_zero {t : ℝ} (ht : t ≠ 0) : eisLineLambda t ≠ 0 := by
  unfold eisLineLambda reflectedCompletedLambda
  apply mul_ne_zero
  · apply Gammaℝ_ne_zero_of_im_ne_zero
    simp [ht]
  · apply riemannZeta_ne_zero_of_one_le_re
    simp

/-- On the line `Re ρ = ½` both Weyl coefficients `Λ(2ρ)` and `Λ(2ρ−1)` are nonzero. -/
theorem lambda_channels_ne_zero_of_re_half {ρ : ℂ} (hre : ρ.re = 1 / 2) (him : ρ.im ≠ 0) :
    reflectedCompletedLambda (2 * ρ) ≠ 0 ∧ reflectedCompletedLambda (2 * ρ - 1) ≠ 0 := by
  have h1 : 2 * ρ = 1 + 2 * ((ρ.im : ℂ) * I) := by
    apply Complex.ext <;> simp [hre]
  have h2 : 2 * ρ - 1 = 2 * ((ρ.im : ℂ) * I) := by
    apply Complex.ext <;> simp [hre]
  refine ⟨?_, ?_⟩
  · rw [h1]
    exact eisLineLambda_ne_zero him
  · rw [h2, reflectedCompletedLambda_two_mul_I_eq_conj him]
    intro h
    apply eisLineLambda_ne_zero him
    have := congrArg (starRingEnd ℂ) h
    rwa [Complex.conj_conj, map_zero] at this

/-- **No law can force `Λ(2ρ−1) = 0` at every zero of `ξ`:** Hardy's theorem gives a zero on the
line, where `Λ(2ρ−1) = conj Λ(1+2iγ) ≠ 0`. -/
theorem not_forall_xi_zero_lambda_lower_eq_zero :
    ¬ ∀ ρ : ℂ, xi ρ = 0 → reflectedCompletedLambda (2 * ρ - 1) = 0 := by
  intro h
  obtain ⟨t, ht1, ht0⟩ := exists_Xi_zero_gt 1
  have hxi : xi (1 / 2 + (t : ℂ) * I) = 0 := by
    rw [xi_eq_XiC_comp]
    have e : ((1 / 2 + (t : ℂ) * I - 1 / 2) * -I) = (t : ℂ) := by
      ring_nf
      simp [Complex.I_sq]
    rw [e, XiC_ofReal, ht0]
    simp
  have hre : (1 / 2 + (t : ℂ) * I).re = 1 / 2 := by simp
  have him : (1 / 2 + (t : ℂ) * I).im ≠ 0 := by
    simp
    linarith
  exact (lambda_channels_ne_zero_of_re_half hre him).2 (h _ hxi)

/-- Likewise no law can force `Λ(2ρ) = 0` at every zero of `ξ`. -/
theorem not_forall_xi_zero_lambda_upper_eq_zero :
    ¬ ∀ ρ : ℂ, xi ρ = 0 → reflectedCompletedLambda (2 * ρ) = 0 := by
  intro h
  obtain ⟨t, ht1, ht0⟩ := exists_Xi_zero_gt 1
  have hxi : xi (1 / 2 + (t : ℂ) * I) = 0 := by
    rw [xi_eq_XiC_comp]
    have e : ((1 / 2 + (t : ℂ) * I - 1 / 2) * -I) = (t : ℂ) := by
      ring_nf
      simp [Complex.I_sq]
    rw [e, XiC_ofReal, ht0]
    simp
  have hre : (1 / 2 + (t : ℂ) * I).re = 1 / 2 := by simp
  have him : (1 / 2 + (t : ℂ) * I).im ≠ 0 := by
    simp
    linarith
  exact (lambda_channels_ne_zero_of_re_half hre him).1 (h _ hxi)

/-- **On the line the principal square is a nonnegative real perfect square:** for
`ρ = ½ + iγ` and `y > 0`,
`Λ(2ρ)² y^{2ρ} + 2Λ(2ρ)Λ(2ρ−1) y + Λ(2ρ−1)² y^{2−2ρ} = y·(2·Re(Λ(1+2iγ)·y^{iγ}))²`. -/
theorem principal_square_channels_on_line {γ : ℝ} (hγ : γ ≠ 0) {y : ℝ} (hy : 0 < y) :
    reflectedCompletedLambda (2 * (1 / 2 + (γ : ℂ) * I)) ^ 2 *
        (y : ℂ) ^ (2 * (1 / 2 + (γ : ℂ) * I)) +
      2 * reflectedCompletedLambda (2 * (1 / 2 + (γ : ℂ) * I)) *
        reflectedCompletedLambda (2 * (1 / 2 + (γ : ℂ) * I) - 1) * (y : ℂ) +
      reflectedCompletedLambda (2 * (1 / 2 + (γ : ℂ) * I) - 1) ^ 2 *
        (y : ℂ) ^ (2 - 2 * (1 / 2 + (γ : ℂ) * I)) =
      ((y * (2 * (eisLineLambda γ * (y : ℂ) ^ ((γ : ℂ) * I)).re) ^ 2 : ℝ) : ℂ) := by
  have h1 : 2 * (1 / 2 + (γ : ℂ) * I) = 1 + 2 * ((γ : ℂ) * I) := by ring
  have h2 : 2 * (1 / 2 + (γ : ℂ) * I) - 1 = 2 * ((γ : ℂ) * I) := by ring
  have h3 : 2 - 2 * (1 / 2 + (γ : ℂ) * I) = 1 + 2 * (-((γ : ℂ) * I)) := by ring
  rw [h2, h3, h1, reflectedCompletedLambda_two_mul_I_eq_conj hγ]
  have hAe : reflectedCompletedLambda (1 + 2 * ((γ : ℂ) * I)) = eisLineLambda γ := rfl
  rw [hAe]
  set A := eisLineLambda γ with hA
  set w := (y : ℂ) ^ ((γ : ℂ) * I) with hw
  have hy0 : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  have hp1 : (y : ℂ) ^ (1 + 2 * ((γ : ℂ) * I)) = (y : ℂ) * w ^ 2 := by
    rw [Complex.cpow_add _ _ hy0, Complex.cpow_one]
    congr 1
    have := Complex.cpow_nat_mul (y : ℂ) 2 ((γ : ℂ) * I)
    rw [Nat.cast_ofNat] at this
    exact this
  have hconj : (starRingEnd ℂ) w = (y : ℂ) ^ (-((γ : ℂ) * I)) := by
    rw [hw, conj_cpow_of_pos hy]
    congr 1
    rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
    ring
  have hp2 : (y : ℂ) ^ (1 + 2 * (-((γ : ℂ) * I))) = (y : ℂ) * ((starRingEnd ℂ) w) ^ 2 := by
    rw [Complex.cpow_add _ _ hy0, Complex.cpow_one, hconj]
    congr 1
    have := Complex.cpow_nat_mul (y : ℂ) 2 (-((γ : ℂ) * I))
    rw [Nat.cast_ofNat] at this
    exact this
  rw [hp1, hp2]
  have hww : w * (starRingEnd ℂ) w = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hw, Complex.norm_cpow_eq_rpow_re_of_pos hy]
    simp
  have hsq : A ^ 2 * ((y : ℂ) * w ^ 2) + 2 * A * (starRingEnd ℂ) A * (y : ℂ) +
      ((starRingEnd ℂ) A) ^ 2 * ((y : ℂ) * ((starRingEnd ℂ) w) ^ 2) =
      (y : ℂ) * (A * w + (starRingEnd ℂ) (A * w)) ^ 2 := by
    rw [map_mul]
    linear_combination (-(2 * A * (starRingEnd ℂ) A * (y : ℂ))) * hww
  rw [hsq, Complex.add_conj]
  push_cast
  ring

end

end RHTower
