import GaloisForLFunctions.RHTower.RiemannXiZerosInfinite
import GaloisForLFunctions.RHTower.FractionalPartZeta

/-!
# The completed Xi function has no zero on the positive real ray

On the positive real axis the archimedean factor `Gammaℝ` is nonvanishing, so a zero of the
completed function would be a zero of `ζ`.  There are none: the Euler product excludes `σ > 1`, the
alternating-eta comparison excludes `0 < σ < 1`, and the value `ξ(1) = 1/2` handles the remaining
point, where `ζ` itself has its pole and the completed function is regular.

This is the real-axis regularity that a Landau argument needs: the abscissa of a nonnegative
carrier lies on the real axis, and a pole of the transform there must be excluded before the
argument can place the singularity at a nonreal point.
-/

open Complex

noncomputable section

namespace GaloisForLFunctions.RHTower

open _root_.RHTower

/-- **The completed factor is nonvanishing on the positive real ray.** -/
theorem completedRiemannZeta_ne_zero_of_ofReal_pos {σ : ℝ} (h0 : 0 < σ) (h1 : σ ≠ 1) :
    completedRiemannZeta ((σ : ℝ) : ℂ) ≠ 0 := by
  have hs0 : (((σ : ℝ) : ℂ)) ≠ 0 := by
    intro hcon
    have := congrArg Complex.re hcon
    simp at this
    linarith
  have hre : (((σ : ℝ) : ℂ)).re = σ := Complex.ofReal_re σ
  have hG : Gammaℝ ((σ : ℝ) : ℂ) ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by rw [hre]; exact h0)
  have hzeta : riemannZeta ((σ : ℝ) : ℂ) ≠ 0 := by
    rcases lt_trichotomy σ 1 with hlt | heq | hgt
    · exact _root_.RHTower.riemannZeta_ne_zero_of_ofReal_mem_Ioo h0 hlt
    · exact absurd heq h1
    · exact riemannZeta_ne_zero_of_one_lt_re (by rw [hre]; exact hgt)
  intro hcon
  apply hzeta
  rw [riemannZeta_def_of_ne_zero hs0, hcon, zero_div]

/-- **`ξ` has no zero on the positive real ray.** -/
theorem riemannXi_ne_zero_of_ofReal_pos {σ : ℝ} (h0 : 0 < σ) :
    _root_.RHTower.riemannXi ((σ : ℝ) : ℂ) ≠ 0 := by
  rcases eq_or_ne σ 1 with heq | hne
  · subst heq
    rw [show (((1 : ℝ) : ℂ)) = 1 by norm_num, _root_.RHTower.riemannXi_one]
    norm_num
  · have hs0 : (((σ : ℝ) : ℂ)) ≠ 0 := by
      intro hcon
      have := congrArg Complex.re hcon
      simp at this
      linarith
    have hs1 : (((σ : ℝ) : ℂ)) ≠ 1 := by
      intro hcon
      apply hne
      have := congrArg Complex.re hcon
      simpa using this
    rw [_root_.RHTower.riemannXi_eq_mul_completedRiemannZeta hs0 hs1]
    have hsub : (((σ : ℝ) : ℂ)) - 1 ≠ 0 := sub_ne_zero.mpr hs1
    have hlam : completedRiemannZeta ((σ : ℝ) : ℂ) ≠ 0 :=
      completedRiemannZeta_ne_zero_of_ofReal_pos h0 hne
    intro hcon
    rw [div_eq_zero_iff] at hcon
    rcases hcon with hcon | hcon
    · rcases mul_eq_zero.mp hcon with hcon' | hcon'
      · rcases mul_eq_zero.mp hcon' with h | h
        · exact hs0 h
        · exact hsub h
      · exact hlam hcon'
    · norm_num at hcon

end GaloisForLFunctions.RHTower
