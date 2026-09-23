import GaloisForLFunctions.RHTower.LevinsonDetectorLine
import GaloisForLFunctions.RHTower.HardyZPhaseAsymptotic

/-!
# The completed zeta on the critical line is a positive multiple of Hardy's `Z`

`gammaHardyPhase` is by definition the conjugate unit vector of `Γ_ℝ` on the critical line, and the
corpus identifies it with `exp(−iθ)`.  Conjugating gives the polar form
`Γ_ℝ(½+iτ) = ‖Γ_ℝ(½+iτ)‖·exp(iθ(τ))`, and multiplying by the branch-free representation
`ζ(½+iτ) = exp(−iθ(τ))·Z(τ)` the two phases cancel:

```text
Λ(½+iτ) = ‖Γ_ℝ(½+iτ)‖ · Z(τ).
```

This is what converts Levinson's detector identity `Y·Λ = 2·Re[Γ_ℝ·G]` into a polar representation
of `Z` itself, whose phase is `θ + (phase of G)`.
-/

open Complex


noncomputable section

namespace RHTower

/-- **The archimedean factor in polar form on the critical line.**  `gammaHardyPhase` is the
conjugate unit vector of `Γ_ℝ` and equals `exp(−iθ)`, so `Γ_ℝ(½+iτ) = ‖Γ_ℝ(½+iτ)‖·exp(iθ(τ))`. -/
theorem Gammaℝ_line_eq_norm_mul_exp_theta (τ : ℝ) :
    Complex.Gammaℝ (linePt τ)
      = ((‖Complex.Gammaℝ (linePt τ)‖ : ℝ) : ℂ) * Complex.exp (I * (gammaHardyTheta τ : ℂ)) := by
  have hne : Complex.Gammaℝ (linePt τ) ≠ 0 :=
    Complex.Gammaℝ_ne_zero_of_re_pos (linePt_re_pos τ)
  have hnorm : ((‖Complex.Gammaℝ (linePt τ)‖ : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hne)
  have hphase := gammaHardyPhase_eq_exp_neg_theta τ
  rw [gammaHardyPhase, div_eq_iff hnorm] at hphase
  have hconj : (starRingEnd ℂ) (Complex.Gammaℝ (linePt τ))
      = ((‖Complex.Gammaℝ (linePt τ)‖ : ℝ) : ℂ) * Complex.exp (-I * (gammaHardyTheta τ : ℂ)) := by
    rw [hphase]; ring
  have hback := congrArg (starRingEnd ℂ) hconj
  rw [Complex.conj_conj, map_mul, Complex.conj_ofReal, ← Complex.exp_conj] at hback
  have hcc : (starRingEnd ℂ) (-I * (gammaHardyTheta τ : ℂ)) = I * (gammaHardyTheta τ : ℂ) := by
    rw [map_mul, map_neg, Complex.conj_I, Complex.conj_ofReal]
    ring
  conv_lhs => rw [hback, hcc]

/-- **The completed zeta on the critical line is a positive multiple of Hardy's `Z`.** -/
theorem completedRiemannZeta_line_eq_norm_mul_hardyZ (τ : ℝ) :
    completedRiemannZeta (linePt τ)
      = ((‖Complex.Gammaℝ (linePt τ)‖ * hardyZ τ : ℝ) : ℂ) := by
  have h1 := completedRiemannZeta_eq_Gammaℝ_mul_levinsonDetectorFE (linePt_re_pos τ)
  have h2 := riemannZeta_line_eq_exp_neg_theta_mul_hardyZ τ
  have h3 := Gammaℝ_line_eq_norm_mul_exp_theta τ
  conv_lhs => rw [h1, h2, h3]
  push_cast
  rw [show ((‖Complex.Gammaℝ (linePt τ)‖ : ℝ) : ℂ) * Complex.exp (I * (gammaHardyTheta τ : ℂ))
        * (Complex.exp (-I * (gammaHardyTheta τ : ℂ)) * (hardyZ τ : ℂ))
      = ((‖Complex.Gammaℝ (linePt τ)‖ : ℝ) : ℂ) * (hardyZ τ : ℂ)
        * (Complex.exp (I * (gammaHardyTheta τ : ℂ))
          * Complex.exp (-I * (gammaHardyTheta τ : ℂ))) by ring,
    ← Complex.exp_add]
  simp

end RHTower

end
