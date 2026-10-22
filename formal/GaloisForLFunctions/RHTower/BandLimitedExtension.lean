import GaloisForLFunctions.RHTower.ProlateL2Regularity
import GaloisForLFunctions.RHTower.CCM.CCMEndpointResponseIdentity
import GaloisForLFunctions.RHTower.SlepianKernelFourier
import GaloisForLFunctions.HTGeometry.CompactFourierEntire

/-!
# The band transform is band-limited: Paley–Wiener for prolate eigenfunctions

The sinc kernel is the inverse transform of the frequency window, so the band transform of any
continuous test function is an integral over the *window* of its own spectrum:

```text
(B_c Phi)(x) = (c/2 pi) ∫_(-1)^(1 : ℕ) F(-c t) exp (i c x t) dt,      F(omega) = ∫_(-1)^(1 : ℕ) Phi(y) e^(i omega y) dy.
```

Only the exponential depends on `x`, and its frequency variable runs over a compact interval, so the
right-hand side extends to an *entire* function of `x` of exponential type `|c|` — the band transform
is band-limited, in the Paley–Wiener sense.

An `L²` eigenfunction of the band operator is `1/nu` times its own band transform, so the same holds
for it: **the prolate eigenfunctions are restrictions of entire functions of exponential type `c`**.
That structure is what any sharp two-sided estimate of the band leakage has to exploit — the leakage
compares the eigenfunction's mass inside the band with the mass its entire extension is forced to have
outside, and the exponential type is the only thing that controls the comparison.
-/

noncomputable section

attribute [local instance] MeasureTheory.Measure.Subtype.measureSpace

namespace GaloisForLFunctions.RHTower

open MeasureTheory Set intervalIntegral

open _root_.RHTower

/-! ## A complex rectangle Fubini -/

/-- The interchange of two interval integrals of a continuous complex integrand on a rectangle. -/
theorem swap_interval_integral_complex {F : ℝ → ℝ → ℂ}
    (hF : Continuous fun z : ℝ × ℝ => F z.1 z.2)
    {a b u v : ℝ} (hab : a ≤ b) (huv : u ≤ v) :
    (∫ y in a..b, ∫ t in u..v, F y t) = ∫ t in u..v, ∫ y in a..b, F y t := by
  have hcompact : IsCompact (Icc a b ×ˢ Icc u v) := isCompact_Icc.prod isCompact_Icc
  have hFu : Continuous (Function.uncurry F) := hF
  have hint0 : IntegrableOn (Function.uncurry F) (Icc a b ×ˢ Icc u v)
      ((volume : Measure ℝ).prod (volume : Measure ℝ)) :=
    (hFu.continuousOn).integrableOn_compact hcompact
  have hsub : Ioc a b ×ˢ Ioc u v ⊆ Icc a b ×ˢ Icc u v := by
    intro z hz
    exact ⟨Ioc_subset_Icc_self hz.1, Ioc_subset_Icc_self hz.2⟩
  have hint : Integrable (Function.uncurry F)
      ((volume.restrict (Ioc a b)).prod (volume.restrict (Ioc u v))) := by
    rw [Measure.prod_restrict]
    exact hint0.mono_set hsub
  simp only [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le huv]
  exact integral_integral_swap hint

/-! ## The spectrum on the window -/

/-- The band moment as a compact Fourier transform: the corpus's finite-Fourier moment *is* the
compact Fourier transform of the amplitude at a real frequency. -/
theorem bandFourier_eq_compactFourier (ω : ℝ) (Φ : ℝ → ℝ) :
    bandFourier ω Φ
      = HTGeometry.compactFourier (fun y => ((Φ y : ℝ) : ℂ)) (-1) 1 ((ω : ℝ) : ℂ) := rfl

/-- The spectrum of a test function, read on the window in normalized coordinates. -/
def bandSpectrum (c : ℝ) (Φ : ℝ → ℝ) (t : ℝ) : ℂ := bandFourier (-(c * t)) Φ

theorem continuous_bandSpectrum (c : ℝ) {Φ : ℝ → ℝ} (hΦ : Continuous Φ) :
    Continuous (bandSpectrum c Φ) := by
  have hcont : Continuous fun y : ℝ => ((Φ y : ℝ) : ℂ) := Complex.continuous_ofReal.comp hΦ
  have hentire := HTGeometry.differentiable_compactFourier hcont (-1) 1
  have hinner : Continuous fun t : ℝ => (((-(c * t) : ℝ) : ℂ)) := by fun_prop
  have hcomp := hentire.continuous.comp hinner
  refine hcomp.congr fun t => ?_
  simp only [Function.comp_apply, bandSpectrum, bandFourier_eq_compactFourier]

/-! ## The window representation of the band transform -/

/-- **The band transform is an integral over the frequency window.**  Inserting the inverse-window
representation of the sinc kernel and interchanging the two compact integrals leaves the `x`-dependence
in a single exponential. -/
theorem bandTransform_eq_windowIntegral {c : ℝ} (hc : c ≠ 0) {Φ : ℝ → ℝ} (hΦ : Continuous Φ)
    (x : ℝ) :
    ((bandTransform c Φ x : ℝ) : ℂ)
      = ((c : ℂ) / (2 * (Real.pi : ℂ)))
          * ∫ t in (-1 : ℝ)..1, bandSpectrum c Φ t
              * Complex.exp (Complex.I * (((c : ℂ) * (x : ℂ)) * (t : ℂ))) := by
  have hle : (-1 : ℝ) ≤ 1 := by norm_num
  -- move the cast inside the integral
  have hcast : ((bandTransform c Φ x : ℝ) : ℂ)
      = ∫ y in (-1 : ℝ)..1, ((sincKernelSmooth c x y : ℝ) : ℂ) * ((Φ y : ℝ) : ℂ) := by
    rw [bandTransform, ← intervalIntegral.integral_ofReal]
    refine intervalIntegral.integral_congr fun y _ => ?_
    push_cast
    ring
  -- the sinc kernel is the inverse transform of the window
  have hsinc : ∀ y : ℝ, ((sincKernelSmooth c x y : ℝ) : ℂ)
      = ((c : ℂ) / (2 * (Real.pi : ℂ)))
          * ∫ t in (-1 : ℝ)..1,
              Complex.exp (Complex.I * ((c * (x - y) : ℝ) : ℂ) * (t : ℂ)) := by
    intro y
    rw [sincKernelSmooth]
    exact sincSmooth_eq_integral c (x - y) hc
  -- pull the constant out, and the amplitude into the frequency integral
  have hstep : (∫ y in (-1 : ℝ)..1, ((sincKernelSmooth c x y : ℝ) : ℂ) * ((Φ y : ℝ) : ℂ))
      = ((c : ℂ) / (2 * (Real.pi : ℂ))) * ∫ y in (-1 : ℝ)..1, ∫ t in (-1 : ℝ)..1,
          ((Φ y : ℝ) : ℂ) * Complex.exp (Complex.I * ((c * (x - y) : ℝ) : ℂ) * (t : ℂ)) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun y _ => ?_
    rw [hsinc y, show (((c : ℂ) / (2 * (Real.pi : ℂ)))
        * ∫ t in (-1 : ℝ)..1, Complex.exp (Complex.I * ((c * (x - y) : ℝ) : ℂ) * (t : ℂ)))
          * ((Φ y : ℝ) : ℂ)
        = ((c : ℂ) / (2 * (Real.pi : ℂ)))
          * ((∫ t in (-1 : ℝ)..1, Complex.exp (Complex.I * ((c * (x - y) : ℝ) : ℂ) * (t : ℂ)))
              * ((Φ y : ℝ) : ℂ)) from by ring, ← intervalIntegral.integral_mul_const]
    congr 1
    refine intervalIntegral.integral_congr fun t _ => ?_
    ring
  -- interchange the two compact integrals
  have hswap : (∫ y in (-1 : ℝ)..1, ∫ t in (-1 : ℝ)..1,
      ((Φ y : ℝ) : ℂ) * Complex.exp (Complex.I * ((c * (x - y) : ℝ) : ℂ) * (t : ℂ)))
      = ∫ t in (-1 : ℝ)..1, ∫ y in (-1 : ℝ)..1,
          ((Φ y : ℝ) : ℂ) * Complex.exp (Complex.I * ((c * (x - y) : ℝ) : ℂ) * (t : ℂ)) := by
    refine swap_interval_integral_complex ?_ hle hle
    have h1 : Continuous fun z : ℝ × ℝ => ((Φ z.1 : ℝ) : ℂ) :=
      Complex.continuous_ofReal.comp (hΦ.comp continuous_fst)
    have h2 : Continuous fun z : ℝ × ℝ =>
        Complex.exp (Complex.I * ((c * (x - z.1) : ℝ) : ℂ) * (z.2 : ℂ)) := by
      fun_prop
    exact h1.mul h2
  -- the inner integral is the spectrum times the surviving exponential
  have hinner : ∀ t : ℝ, (∫ y in (-1 : ℝ)..1,
      ((Φ y : ℝ) : ℂ) * Complex.exp (Complex.I * ((c * (x - y) : ℝ) : ℂ) * (t : ℂ)))
      = bandSpectrum c Φ t * Complex.exp (Complex.I * (((c : ℂ) * (x : ℂ)) * (t : ℂ))) := by
    intro t
    rw [bandSpectrum, bandFourier, ← intervalIntegral.integral_mul_const]
    refine intervalIntegral.integral_congr fun y _ => ?_
    have hsplit : Complex.exp (Complex.I * ((c * (x - y) : ℝ) : ℂ) * (t : ℂ))
        = Complex.exp (Complex.I * (((-(c * t) : ℝ) : ℂ) * (y : ℂ)))
          * Complex.exp (Complex.I * (((c : ℂ) * (x : ℂ)) * (t : ℂ))) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [hsplit]
    ring
  rw [hcast, hstep, hswap]
  congr 1
  refine intervalIntegral.integral_congr fun t _ => ?_
  exact hinner t

/-! ## The entire extension -/

/-- The entire extension of the band transform: the window integral read at a complex point. -/
def bandTransformEntire (c : ℝ) (Φ : ℝ → ℝ) (z : ℂ) : ℂ :=
  ((c : ℂ) / (2 * (Real.pi : ℂ)))
    * HTGeometry.compactFourier (bandSpectrum c Φ) (-1) 1 ((c : ℂ) * z)

theorem bandTransformEntire_ofReal {c : ℝ} (hc : c ≠ 0) {Φ : ℝ → ℝ} (hΦ : Continuous Φ) (x : ℝ) :
    bandTransformEntire c Φ ((x : ℝ) : ℂ) = ((bandTransform c Φ x : ℝ) : ℂ) := by
  rw [bandTransformEntire, HTGeometry.compactFourier, bandTransform_eq_windowIntegral hc hΦ x]

/-- **The band transform is band-limited.**  Its window representation is entire in the space
variable. -/
theorem differentiable_bandTransformEntire (c : ℝ) {Φ : ℝ → ℝ} (hΦ : Continuous Φ) :
    Differentiable ℂ (bandTransformEntire c Φ) := by
  have hentire := HTGeometry.differentiable_compactFourier (continuous_bandSpectrum c hΦ) (-1) 1
  have hinner : Differentiable ℂ fun z : ℂ => (c : ℂ) * z := by fun_prop
  exact (hentire.comp hinner).const_mul _

/-- **The exponential type of the band transform is `|c|`.** -/
theorem norm_bandTransformEntire_le {c : ℝ} {Φ : ℝ → ℝ} {M : ℝ}
    (hM : ∀ t ∈ Set.uIoc (-1 : ℝ) 1, ‖bandSpectrum c Φ t‖ ≤ M) (z : ℂ) :
    ‖bandTransformEntire c Φ z‖
      ≤ ‖(c : ℂ) / (2 * (Real.pi : ℂ))‖ * (M * Real.exp (|c| * |z.im|) * 2) := by
  have hbound := HTGeometry.norm_compactFourier_le (f := bandSpectrum c Φ) (M := M)
    (by norm_num : (-1 : ℝ) ≤ 1) hM ((c : ℂ) * z)
  have hmax : max |(-1 : ℝ)| |(1 : ℝ)| = 1 := by norm_num
  have him : ((c : ℂ) * z).im = c * z.im := by
    simp [Complex.mul_im]
  have habs : |((c : ℂ) * z).im| = |c| * |z.im| := by
    rw [him, abs_mul]
  rw [hmax, habs, one_mul] at hbound
  have hval : ((1 : ℝ) - -1) = 2 := by norm_num
  rw [hval] at hbound
  rw [bandTransformEntire, norm_mul]
  exact mul_le_mul_of_nonneg_left hbound (norm_nonneg _)

/-! ## Paley–Wiener for the eigenfunctions -/

/-- **The prolate eigenfunctions are entire of exponential type `c`.**  An `L²` eigenfunction is
`1/nu` times its own band transform, and the band transform is band-limited. -/
theorem exists_entire_extension_eigenExtension {c ν : ℝ} (hc : c ≠ 0) (hν : ν ≠ 0)
    {ψ : RealIntervalL2 (-1 : ℝ) 1} (heig : bandOperatorL2 c ψ = ν • ψ) :
    ∃ F : ℂ → ℂ, Differentiable ℂ F
      ∧ (∀ x : ℝ, F ((x : ℝ) : ℂ) = ((eigenExtension c ν ψ x : ℝ) : ℂ))
      ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, ‖F z‖ ≤ C * Real.exp (|c| * |z.im|) := by
  have hΦcont : Continuous (eigenExtension c ν ψ) := continuous_eigenExtension c ν ψ
  refine ⟨fun z => ((ν : ℂ))⁻¹ * bandTransformEntire c (eigenExtension c ν ψ) z, ?_, ?_, ?_⟩
  · exact (differentiable_bandTransformEntire c hΦcont).const_mul _
  · intro x
    show ((ν : ℝ) : ℂ)⁻¹ * bandTransformEntire c (eigenExtension c ν ψ) ((x : ℝ) : ℂ)
        = ((eigenExtension c ν ψ x : ℝ) : ℂ)
    rw [bandTransformEntire_ofReal hc hΦcont x, bandTransform_eigenExtension hν heig x]
    have hνne : ((ν : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hν
    push_cast
    field_simp
  · -- the spectrum is bounded on the window, so the extension has exponential type `|c|`
    obtain ⟨M, hM⟩ := (isCompact_uIcc (a := (-1 : ℝ)) (b := 1)).exists_bound_of_continuousOn
      (continuous_bandSpectrum c hΦcont).continuousOn
    have hMuIoc : ∀ t ∈ Set.uIoc (-1 : ℝ) 1, ‖bandSpectrum c (eigenExtension c ν ψ) t‖ ≤ M :=
      fun t ht => hM t (Set.uIoc_subset_uIcc ht)
    have hMnonneg : 0 ≤ M := by
      have h0 : (0 : ℝ) ∈ Set.uIcc (-1 : ℝ) 1 := by
        rw [Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
        exact ⟨by norm_num, by norm_num⟩
      exact le_trans (norm_nonneg _) (hM 0 h0)
    refine ⟨‖((ν : ℝ) : ℂ)⁻¹‖ * (‖(c : ℂ) / (2 * (Real.pi : ℂ))‖ * (M * 2)), by positivity,
      fun z => ?_⟩
    have hb := norm_bandTransformEntire_le hMuIoc z
    rw [norm_mul]
    have hmono : ‖((ν : ℝ) : ℂ)⁻¹‖ * ‖bandTransformEntire c (eigenExtension c ν ψ) z‖
        ≤ ‖((ν : ℝ) : ℂ)⁻¹‖
          * (‖(c : ℂ) / (2 * (Real.pi : ℂ))‖ * (M * Real.exp (|c| * |z.im|) * 2)) :=
      mul_le_mul_of_nonneg_left hb (norm_nonneg _)
    refine hmono.trans ?_
    have hval : ‖((ν : ℝ) : ℂ)⁻¹‖
          * (‖(c : ℂ) / (2 * (Real.pi : ℂ))‖ * (M * Real.exp (|c| * |z.im|) * 2))
        = ‖((ν : ℝ) : ℂ)⁻¹‖ * (‖(c : ℂ) / (2 * (Real.pi : ℂ))‖ * (M * 2))
            * Real.exp (|c| * |z.im|) := by ring
    rw [hval]

end GaloisForLFunctions.RHTower

end
