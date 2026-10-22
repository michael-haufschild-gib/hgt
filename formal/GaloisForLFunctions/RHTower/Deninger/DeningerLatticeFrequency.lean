import GaloisForLFunctions.RHTower.Deninger.DeningerPaleyWiener
import GaloisForLFunctions.RHTower.Deninger.DeningerGreenSumSource

/-!
# Periodization kills the lattice frequencies

A cochain with vanishing `L`-periodization is a periodization defect, `h = Δ_L g`, and translation
multiplies the Fourier–Laplace transform by a character:

`(τ_L g)^(z) = e^{izL} ĝ(z)`,  so  `ĥ(z) = (1 - e^{izL}) ĝ(z)`.

At the lattice frequencies `zL ∈ 2πℤ` the character is `1`, so `ĥ` vanishes there.  This is the
Fourier-coefficient identity in the only form the tomography theorem uses, and it needs no
interchange of sum and integral and no tiling of the line.

* `deningerFourierLaplace_shift` : **translation multiplies `ĥ` by `e^{izL}`.**
* `deningerFourierLaplace_defect` : `ĥ = (1 - e^{izL})ĝ` for a defect.
* `deningerFourierLaplace_vanishes_at_lattice` : **`ĥ(2πk/L) = 0` when `Per_L h = 0`.**
-/

namespace RHTower

open MeasureTheory SchwartzMap

noncomputable section

/-- **Translation multiplies the Fourier–Laplace transform by a character.** -/
theorem deningerFourierLaplace_shift (g : 𝓢(ℝ, ℂ)) (L : ℝ) (z : ℂ) :
    deningerFourierLaplace (deningerExpShift L g) z
      = Complex.exp (Complex.I * z * (L : ℂ)) * deningerFourierLaplace g z := by
  have hker : ∀ u : ℝ, deningerLaplaceKernel z (u - L)
      = Complex.exp (Complex.I * z * (L : ℂ)) * deningerLaplaceKernel z u := by
    intro u
    rw [deningerLaplaceKernel, deningerLaplaceKernel, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hshift := integral_add_right_eq_self (μ := (volume : Measure ℝ))
    (fun u : ℝ => (g : ℝ → ℂ) u * deningerLaplaceKernel z (u - L)) L
  rw [deningerFourierLaplace, deningerFourierLaplace]
  have hleft : (∫ t : ℝ, ((deningerExpShift L g : 𝓢(ℝ, ℂ)) : ℝ → ℂ) t
      * deningerLaplaceKernel z t)
      = ∫ t : ℝ, (g : ℝ → ℂ) (t + L) * deningerLaplaceKernel z ((t + L) - L) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    show ((deningerExpShift L g : 𝓢(ℝ, ℂ)) : ℝ → ℂ) t * deningerLaplaceKernel z t
      = (g : ℝ → ℂ) (t + L) * deningerLaplaceKernel z ((t + L) - L)
    rw [deningerExpShift_apply]
    congr 2
    ring
  rw [hleft, hshift, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  show (g : ℝ → ℂ) u * deningerLaplaceKernel z (u - L)
    = Complex.exp (Complex.I * z * (L : ℂ)) * ((g : ℝ → ℂ) u * deningerLaplaceKernel z u)
  rw [hker u]
  ring

/-- The transform of a periodization defect. -/
theorem deningerFourierLaplace_defect {g : 𝓢(ℝ, ℂ)} (hg : g ∈ DeningerExpSchwartz) (L : ℝ)
    (z : ℂ) :
    deningerFourierLaplace
        (((deningerPeriodizationDefect L ⟨g, hg⟩ : DeningerExpSchwartz) : 𝓢(ℝ, ℂ))) z
      = (1 - Complex.exp (Complex.I * z * (L : ℂ))) * deningerFourierLaplace g z := by
  have hgi := deningerFourierLaplace_integrable hg z 0
  have hsi := deningerFourierLaplace_integrable (deningerExpShift_mem hg L) z 0
  have hg' : Integrable fun t : ℝ => (g : ℝ → ℂ) t * deningerLaplaceKernel z t := by
    refine hgi.congr (Filter.Eventually.of_forall fun t => ?_)
    simp
  have hs' : Integrable fun t : ℝ =>
      ((deningerExpShift L g : 𝓢(ℝ, ℂ)) : ℝ → ℂ) t * deningerLaplaceKernel z t := by
    refine hsi.congr (Filter.Eventually.of_forall fun t => ?_)
    simp
  have hpt : ∀ t : ℝ,
      (((deningerPeriodizationDefect L ⟨g, hg⟩ : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) : ℝ → ℂ) t
          * deningerLaplaceKernel z t
        = (g : ℝ → ℂ) t * deningerLaplaceKernel z t
          - ((deningerExpShift L g : 𝓢(ℝ, ℂ)) : ℝ → ℂ) t * deningerLaplaceKernel z t := by
    intro t
    rw [deningerPeriodizationDefect_apply, deningerExpShift_apply]
    ring
  rw [deningerFourierLaplace, integral_congr_ae (Filter.Eventually.of_forall hpt),
    integral_sub hg' hs']
  have hshift := deningerFourierLaplace_shift g L z
  rw [deningerFourierLaplace, deningerFourierLaplace] at hshift
  rw [hshift, deningerFourierLaplace]
  ring

/-- **The transform vanishes at the lattice frequencies of a vanishing periodization.** -/
theorem deningerFourierLaplace_vanishes_at_lattice {h : 𝓢(ℝ, ℂ)}
    (hh : h ∈ DeningerExpSchwartz) {L : ℝ} (hL : 0 < L)
    (hper : ∀ t : ℝ, deningerPeriodizationSum h L t = 0) (k : ℤ) :
    deningerFourierLaplace h (((2 * Real.pi * (k : ℝ) / L : ℝ) : ℂ)) = 0 := by
  have hmem : (⟨h, hh⟩ : DeningerExpSchwartz)
      ∈ Set.range (deningerPeriodizationDefect L) := by
    rw [deningerPeriodization_range_eq_kernel hL]
    exact hper
  obtain ⟨g, hg⟩ := hmem
  have hcoe : (((deningerPeriodizationDefect L g : DeningerExpSchwartz) : 𝓢(ℝ, ℂ))) = h :=
    congrArg Subtype.val hg
  have hchar : Complex.exp (Complex.I * ((2 * Real.pi * (k : ℝ) / L : ℝ) : ℂ) * (L : ℂ)) = 1 := by
    have hLne : ((L : ℝ) : ℂ) ≠ 0 := by
      simpa using ne_of_gt hL
    have harg : Complex.I * ((2 * Real.pi * (k : ℝ) / L : ℝ) : ℂ) * (L : ℂ)
        = (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
      push_cast
      field_simp
    rw [harg]
    exact Complex.exp_int_mul_two_pi_mul_I k
  have hdef := deningerFourierLaplace_defect g.2 L (((2 * Real.pi * (k : ℝ) / L : ℝ) : ℂ))
  have hgsub : (⟨(g : 𝓢(ℝ, ℂ)), g.2⟩ : DeningerExpSchwartz) = g := rfl
  rw [hgsub, hcoe, hchar] at hdef
  rw [hdef]
  ring

end

end RHTower
