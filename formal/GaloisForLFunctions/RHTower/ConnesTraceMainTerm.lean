import GaloisForLFunctions.RHTower.ConnesTwistedChartFourier

/-!
# §VII (31): the main term of the trace formula

§VII (31) of

  A. Connes, *Trace formula in noncommutative geometry and the zeros of the Riemann zeta
  function*, arXiv:math/9811068.

The constant term of the cut-off trace is

  `∑_{q ∈ O_S^*} ∫ ĝ_q(u) du = ∑_q g_q(0) = ∑_q f(q) = h(1)`,                 (31)

the first equality being Fourier inversion at the origin, the second the value of the twisted
chart at the origin (`connesTwistedChart_zero`), and the third Connes' defining property (14) of
the lift `f` of `h`.

Everything here is unconditional at the archimedean place; the only structure used is that the
twisted chart is Schwartz, which is Connes' `g_q ∈ C_c^∞(A_S)`.
-/

open MeasureTheory Real
open scoped SchwartzMap Real FourierTransform

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- The inverse Fourier transform at the origin is the total mass. -/
theorem connes_fourierInv_zero (w : ℝ → ℂ) : 𝓕⁻ w 0 = ∫ v : ℝ, w v := by
  rw [Real.fourierInv_eq']
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  simp

/-- **Fourier inversion at the origin.**  The total mass of the transform of a Schwartz function is
its value at the origin. -/
theorem connes_integral_fourier_eq_zero_value (g : 𝓢(ℝ, ℂ)) :
    (∫ u : ℝ, 𝓕 ((g : 𝓢(ℝ, ℂ)) : ℝ → ℂ) u) = g 0 := by
  have hFint : Integrable (𝓕 ((g : 𝓢(ℝ, ℂ)) : ℝ → ℂ)) := by
    have h : Integrable ((SchwartzMap.fourierTransformCLM ℂ g : 𝓢(ℝ, ℂ)) : ℝ → ℂ) :=
      (SchwartzMap.fourierTransformCLM ℂ g).integrable
    rwa [SchwartzMap.fourierTransformCLM_apply, SchwartzMap.fourier_coe] at h
  have hinv : 𝓕⁻ (𝓕 ((g : 𝓢(ℝ, ℂ)) : ℝ → ℂ)) = ((g : 𝓢(ℝ, ℂ)) : ℝ → ℂ) :=
    g.continuous.fourierInv_fourier_eq g.integrable hFint
  have h0 : 𝓕⁻ (𝓕 ((g : 𝓢(ℝ, ℂ)) : ℝ → ℂ)) 0 = g 0 := congrFun hinv 0
  rw [← h0, connes_fourierInv_zero]

/-- **§VII (31), one lattice element.**  If the twisted chart at `q` is Schwartz, the total mass of
its transform is `f(q)`. -/
theorem connes_mainTerm_eq (f : ℝ → ℂ) (q : ℝ) (G : 𝓢(ℝ, ℂ))
    (hG : ∀ u : ℝ, (G : ℝ → ℂ) u = connesTwistedChart f q u) :
    (∫ u : ℝ, 𝓕 ((G : 𝓢(ℝ, ℂ)) : ℝ → ℂ) u) = f q := by
  rw [connes_integral_fourier_eq_zero_value G, hG 0, connesTwistedChart_zero]

/-- **§VII (31).**  Summed over the lattice, the constant term is `∑_q f(q)`, which by Connes'
(14) is `h(1)`. -/
theorem connes_mainTerm_tsum (f : ℝ → ℂ) {ι : Type*} (qs : ι → ℝ) (G : ι → 𝓢(ℝ, ℂ))
    (hG : ∀ (i : ι) (u : ℝ), (G i : ℝ → ℂ) u = connesTwistedChart f (qs i) u) :
    (∑' i : ι, ∫ u : ℝ, 𝓕 ((G i : 𝓢(ℝ, ℂ)) : ℝ → ℂ) u) = ∑' i : ι, f (qs i) :=
  tsum_congr fun i => connes_mainTerm_eq f (qs i) (G i) (hG i)

end

end GaloisForLFunctions.RHTower
