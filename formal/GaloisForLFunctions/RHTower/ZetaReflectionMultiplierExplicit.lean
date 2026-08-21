import GaloisForLFunctions.RHTower.ReflectionCocycleClass

/-!
# The reflection multiplier in explicit `π`-and-`Γ` coordinates

The functional equation of `ζ` can be written `ζ(s) = G(s) ζ(1-s)` with

`G(s) = (π^((s-1)/2) Γ((1-s)/2)) / (π^(-s/2) Γ(s/2))`,

which is exactly the ratio `Γ_ℝ(1-s)/Γ_ℝ(s)` of archimedean factors.

`G` is not nonvanishing on all of `ℂ`.  `Γ_ℝ` vanishes on the nonpositive even integers — the
points where the underlying `Γ` has a pole — and there the reflection identity carries no
information about zeros.  Concretely `ζ(-2) = 0` while `ζ(3) ≠ 0`, so the zero locus of `ζ` is
*not* invariant under `s ↦ 1 - s` on the whole plane.  Invariance holds exactly where both
archimedean factors are regular, in particular throughout the open critical strip.
-/

open Complex Real

noncomputable section

namespace RHTower

/-- The archimedean reflection multiplier in explicit coordinates. -/
def reflectionMultiplier (s : ℂ) : ℂ :=
  ((π : ℂ) ^ ((s - 1) / 2) * Complex.Gamma ((1 - s) / 2)) /
    ((π : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2))

/-- The explicit multiplier is the ratio of the two archimedean factors. -/
theorem reflectionMultiplier_eq_Gammaℝ_ratio (s : ℂ) :
    reflectionMultiplier s = Complex.Gammaℝ (1 - s) / Complex.Gammaℝ s := by
  rw [reflectionMultiplier, Complex.Gammaℝ_def, Complex.Gammaℝ_def,
    show -(1 - s) / 2 = (s - 1) / 2 by ring]

/-- **The functional equation in the explicit multiplier form.**  Valid wherever both archimedean
factors are regular, in particular on the open critical strip. -/
theorem riemannZeta_eq_reflectionMultiplier_mul {s : ℂ}
    (hΓs : Complex.Gammaℝ s ≠ 0) (hΓ1 : Complex.Gammaℝ (1 - s) ≠ 0) :
    riemannZeta s = reflectionMultiplier s * riemannZeta (1 - s) := by
  rw [reflectionMultiplier_eq_Gammaℝ_ratio,
    riemannZeta_one_sub_eq_gammaRatio_mul_of_Gammaℝ_ne_zero hΓs hΓ1]
  field_simp

/-- On the open critical strip the multiplier is a ratio of two nonzero numbers. -/
theorem reflectionMultiplier_ne_zero {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) :
    reflectionMultiplier s ≠ 0 := by
  have h1re : 0 < (1 - s).re := by rw [Complex.sub_re, Complex.one_re]; linarith
  rw [reflectionMultiplier_eq_Gammaℝ_ratio]
  exact div_ne_zero (Complex.Gammaℝ_ne_zero_of_re_pos h1re)
    (Complex.Gammaℝ_ne_zero_of_re_pos h0)

/-- The archimedean factor vanishes at `-2`: the underlying `Γ` has a pole there. -/
theorem Gammaℝ_neg_two_eq_zero : Complex.Gammaℝ (-2) = 0 :=
  Complex.Gammaℝ_eq_zero_iff.mpr ⟨1, by norm_num⟩

theorem riemannZeta_neg_two_eq_zero : riemannZeta (-2) = 0 := by
  have h := riemannZeta_neg_two_mul_nat_add_one 0
  norm_num at h
  exact h

theorem riemannZeta_three_ne_zero : riemannZeta 3 ≠ 0 := by
  refine riemannZeta_ne_zero_of_one_lt_re ?_
  norm_num

/-- **The zero locus of `ζ` is not globally invariant under reflection.**  At `s = -2` the value
`ζ(s)` vanishes while `ζ(1-s) = ζ(3)` does not, so the appendix-style claim that the reflection
identity forces `ζ(s) = 0 ↔ ζ(1-s) = 0` for *all* `s ∈ ℂ` is false.  The obstruction is exactly
the vanishing of `Γ_ℝ` on the nonpositive even integers. -/
theorem not_forall_riemannZeta_eq_zero_iff_one_sub :
    ¬ ∀ s : ℂ, riemannZeta s = 0 ↔ riemannZeta (1 - s) = 0 := by
  intro h
  have h3 : riemannZeta (1 - (-2 : ℂ)) = 0 := (h (-2)).mp riemannZeta_neg_two_eq_zero
  rw [show (1 : ℂ) - (-2 : ℂ) = 3 by norm_num] at h3
  exact riemannZeta_three_ne_zero h3

end RHTower
