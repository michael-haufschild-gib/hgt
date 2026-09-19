import GaloisForLFunctions.RHTower.EisensteinResonantStateNorm

/-!
# The Eisenstein transform of a truncated resonant state is a Cauchy kernel

For a resonant parameter `u` (`Λ(1+2u) = 0`, `Re u < 0`) the Maass–Selberg pairing of the
truncation `Λ^Y E_u` with the truncated line model `Λ^Y E_{it}` is

`⟨Λ^Y E_u, Λ^Y E_{it}⟩ = −Λ(2u)·( Λ(1+2it)·Y^{it−u}/(u − it) + Λ(2it)·Y^{−u−it}/(u + it) )`.

As a function of the spectral parameter `t` this is a Cauchy (Poisson) kernel with poles at
`t = ∓iu`, i.e. at distance `|Re u| = (1 − σ)/2` from the real axis when `1 + 2u = σ + iγ`.  This
is the structural reason why the Hecke moments of truncated resonant states are the moments of the
Breit–Wigner profile of the resonance: the resonant state is the Cauchy wave packet of the
Eisenstein continuum centred at the resonance.
-/

open Complex

namespace RHTower

noncomputable section

/-- **The Eisenstein transform of a truncated resonant state.** -/
theorem truncatedPairing_resonant_line {u : ℂ} (hu : u ∈ eisensteinLineDomain) (hre : u.re < 0)
    (hA : msA u = 0) {t : ℝ} (ht : 0 < t) {Y : ℝ} (hY : 1 ≤ Y) :
    truncatedPairing Y u ((t : ℂ) * I) =
      -(msB u) * (msA ((t : ℂ) * I) * (Y : ℂ) ^ ((t : ℂ) * I - u) / (u - (t : ℂ) * I) +
        msB ((t : ℂ) * I) * (Y : ℂ) ^ (-u - (t : ℂ) * I) / (u + (t : ℂ) * I)) := by
  have hne1 : u - (t : ℂ) * I ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hne2 : u + (t : ℂ) * I ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have h := maassSelberg_lineModel hu (I_mul_mem_eisensteinLineDomain ht) hY
  rw [msRight, hA] at h
  have hprod : (u - (t : ℂ) * I) * (u + (t : ℂ) * I) ≠ 0 := mul_ne_zero hne1 hne2
  apply mul_left_cancel₀ hprod
  rw [h]
  field_simp
  ring

end

end RHTower
