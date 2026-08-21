/-
# Chen--Gupta--Li Lemma 4.5 Fourier-series summability

Supplies absolute summability of the one-coordinate frequency series. This
licenses the Fubini/product assembly of CGL's three Poisson expansions.
-/

import GaloisForLFunctions.RHTower.ChenGuptaLiLemma45CharacterPoisson

open scoped BigOperators FourierTransform

noncomputable section

namespace RHTower

/-- The unweighted Fourier series on one affine residue lattice. -/
def cglLemma45AffineFourierCore (f : SchwartzMap ℝ ℂ) (N : CGLPositiveLength)
    (Q : CGLPositiveModulus) (a : ZMod Q.value) (m : ℤ) : ℂ :=
  ZMod.stdAddChar (a * (m : ZMod Q.value)) *
    ((cglAffineFourierScale N Q : ℂ) *
      𝓕 (f : ℝ → ℂ) (cglAffineFourierScale N Q * (m : ℝ)))

/-- The affine Schwartz Fourier series is summable on the integer frequency
lattice. -/
theorem cglLemma45AffineFourierCore_summable (f : SchwartzMap ℝ ℂ)
    (N : CGLPositiveLength) (Q : CGLPositiveModulus) (a : ZMod Q.value) :
    Summable (cglLemma45AffineFourierCore f N Q a) := by
  refine (cglSchwartz_summable_fourier_int (cglAffineResidueSchwartz f N Q a)).congr ?_
  intro m
  calc
    𝓕 (cglAffineResidueSchwartz f N Q a : ℝ → ℂ) (m : ℝ) =
        Complex.exp ((↑(2 * Real.pi * ((a.val : ℝ) / Q.value) * (m : ℝ)) : ℂ) * Complex.I) *
          ((cglAffineFourierScale N Q : ℂ) *
            𝓕 (f : ℝ → ℂ) (cglAffineFourierScale N Q * (m : ℝ))) :=
      cglAffineResidueSchwartz_fourier f N Q a (m : ℝ)
    _ = cglLemma45AffineFourierCore f N Q a m := by
      rw [cglAffineFourierPhase_eq_stdAddChar_mul]
      rfl

/-- The full character-pair frequency series is absolutely summable. -/
theorem cglLemma45CharacterPairFourierTerm_summable_norm
    (w : CGLRealSmoothBump) (N : CGLPositiveLength)
    (Q : CGLPositiveModulus) (χ ψ : DirichletCharacter ℂ Q.value) (t : ℝ)
    (a : ZMod Q.value) :
    Summable fun m : ℤ => ‖cglLemma45CharacterPairFourierTerm w N Q χ ψ t a m‖ := by
  have h := cglLemma45AffineFourierCore_summable (cglSmoothBumpHt w.toCGLSmoothBump t) N Q a
  exact (h.mul_left (χ a * (starRingEnd ℂ) (ψ a))).norm

end RHTower
