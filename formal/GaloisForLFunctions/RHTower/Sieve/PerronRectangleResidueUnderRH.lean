import GaloisForLFunctions.RHTower.Sieve.PerronIntegrandResidue
import GaloisForLFunctions.PNTPlus.Rectangle

/-!
# The rectangle integral of the Perron integrand

Under the Riemann hypothesis `ζ` has no zero right of the critical line, so the Perron integrand is
holomorphic on a rectangle straddling `s = 1` except at that point, where its residue is `x`.  The
rectangle residue theorem then evaluates the contour integral exactly.
-/

namespace RHTower.Sieve

open Complex Filter Asymptotics Topology

noncomputable section

/-- Under the Riemann hypothesis `ζ` has no zero strictly right of the critical line. -/
theorem riemannZeta_ne_zero_of_rh (hRH : RiemannHypothesis) {s : ℂ} (hs : 1 / 2 < s.re)
    (hs1 : s ≠ 1) : riemannZeta s ≠ 0 := by
  intro hz
  have htriv : ¬ ∃ n : ℕ, s = -2 * ((n : ℂ) + 1) := by
    rintro ⟨n, rfl⟩
    have hre : ((-2 * ((n : ℂ) + 1)).re) = -2 * ((n : ℝ) + 1) := by
      simp [Complex.mul_re]
    rw [hre] at hs
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have := hRH s hz htriv hs1
  linarith

/-- **The rectangle integral of the Perron integrand.** -/
theorem rectangleIntegral_perron_eq (hRH : RiemannHypothesis) {x : ℝ} (hx : 0 < x)
    {σ₁ σ₀ T : ℝ} (hσ₁ : 1 / 2 < σ₁) (hσ₁1 : σ₁ < 1) (hσ₀ : 1 < σ₀) (hT : 0 < T) :
    RectangleIntegral' (fun s : ℂ => (-deriv riemannZeta s / riemannZeta s) * ((x : ℂ) ^ s / s))
      ((σ₁ : ℂ) - Complex.I * (T : ℂ)) ((σ₀ : ℂ) + Complex.I * (T : ℂ)) = (x : ℂ) := by
  have hzre : ((σ₁ : ℂ) - Complex.I * (T : ℂ)).re = σ₁ := by simp
  have hzim : ((σ₁ : ℂ) - Complex.I * (T : ℂ)).im = -T := by simp
  have hwre : ((σ₀ : ℂ) + Complex.I * (T : ℂ)).re = σ₀ := by simp
  have hwim : ((σ₀ : ℂ) + Complex.I * (T : ℂ)).im = T := by simp
  refine ResidueTheoremOnRectangleWithSimplePole' (p := 1) (A := (x : ℂ))
    (by rw [hzre, hwre]; linarith) (by rw [hzim, hwim]; linarith) ?_ ?_
    (perron_integrand_residue hx)
  · rw [rectangle_mem_nhds_iff, hzre, hzim, hwre, hwim]
    constructor
    · rw [Set.uIoo_of_le (by linarith : σ₁ ≤ σ₀)]
      exact ⟨by simpa using hσ₁1, by simpa using hσ₀⟩
    · rw [Set.uIoo_of_le (by linarith : -T ≤ T)]
      refine ⟨by simpa using (by linarith : -T < (0:ℝ)), by simpa using hT⟩
  · intro s hs
    have hs1 : s ≠ 1 := hs.2
    have hsre : 1 / 2 < s.re := by
      have := hs.1.1
      rw [hzre, hwre, Set.uIcc_of_le (by linarith)] at this
      linarith [this.1]
    have hzne : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_rh hRH hsre hs1
    have hs0 : s ≠ 0 := by
      intro h
      rw [h] at hsre
      simp at hsre
      linarith
    have hxne : ((x : ℝ) : ℂ) ≠ 0 := by simpa using hx.ne'
    refine DifferentiableWithinAt.mul ?_ ?_
    · exact ((differentiableAt_deriv_riemannZeta hs1).neg.div
        (differentiableAt_riemannZeta hs1) hzne).differentiableWithinAt
    · exact ((differentiableAt_id.const_cpow (Or.inl hxne)).div
        differentiableAt_id hs0).differentiableWithinAt

end

end RHTower.Sieve
