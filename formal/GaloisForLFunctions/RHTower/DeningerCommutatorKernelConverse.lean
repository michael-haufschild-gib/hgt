import GaloisForLFunctions.RHTower.DeningerEvenPreimageDecay
import GaloisForLFunctions.RHTower.DeningerFourierBoundedDerivs
import GaloisForLFunctions.RHTower.DeningerL1FourierDistribution
import GaloisForLFunctions.RHTower.DeningerSchwartzOfDecay
import GaloisForLFunctions.RHTower.DeningerCommutatorBoundaryKernel

/-!
# The kernel of the commutator consists of Schwartz preimages

If `𝔖_μ h = 0` then the two even extensions are a Fourier pair of integrable densities.  The
opposite collar supplies every moment, so the transform is smooth with all derivatives bounded; the
Möbius side supplies rapid decay.  Landau interpolation then upgrades the pair to a Schwartz
function.

This is the load-bearing step `(23)`--`(24)` of the exact-kernel theorem: the singular radial
preimage is repaired by the Fourier moments of the opposite collar, and no regularity at the origin
is assumed anywhere.

* `deningerOpen_null_empty` : an open null set of the line is empty.
* `deningerAeBound_on_open` : an almost-everywhere bound on continuous data is a pointwise bound.
* `deningerEvenPreimage_ae_fourier` : **`E f_h = ℱ(E f_{Jh})` almost everywhere.**
* `deningerCommutatorKernel_schwartz` : **a kernel element has a Schwartz preimage.**
-/

namespace RHTower

open MeasureTheory SchwartzMap FourierTransform

open scoped ContDiff

noncomputable section

/-! ## From almost-everywhere bounds to pointwise bounds -/

/-- An open null set of the line is empty. -/
theorem deningerOpen_null_empty {s : Set ℝ} (hs : IsOpen s) (h0 : volume s = 0) : s = ∅ := by
  by_contra hne
  have hnonempty : s.Nonempty := Set.nonempty_iff_ne_empty.mpr hne
  have hpos := hs.measure_pos volume hnonempty
  rw [h0] at hpos
  exact lt_irrefl 0 hpos

/-- **An almost-everywhere bound between continuous functions holds pointwise on any open set.** -/
theorem deningerAeBound_on_open {u b : ℝ → ℝ} {s : Set ℝ} (hsopen : IsOpen s)
    (hu : Continuous u) (hb : Continuous b)
    (hae : ∀ᵐ x : ℝ, x ∈ s → u x ≤ b x) : ∀ x ∈ s, u x ≤ b x := by
  intro x hx
  by_contra hcon0
  have hcon : b x < u x := not_le.mp hcon0
  have hopen : IsOpen (s ∩ {y : ℝ | b y < u y}) := hsopen.inter (isOpen_lt hb hu)
  have hcompl : volume {y : ℝ | y ∈ s → u y ≤ b y}ᶜ = 0 := mem_ae_iff.mp hae
  have hsub : (s ∩ {y : ℝ | b y < u y}) ⊆ {y : ℝ | y ∈ s → u y ≤ b y}ᶜ := by
    intro y hy hcon2
    exact absurd (hcon2 hy.1) (not_le.mpr hy.2)
  have hempty := deningerOpen_null_empty hopen (measure_mono_null hsub hcompl)
  have hmem : x ∈ s ∩ {y : ℝ | b y < u y} := ⟨hx, hcon⟩
  rw [hempty] at hmem
  exact hmem

/-- **The two-sided power decay transfers to a continuous representative.** -/
theorem deningerAbsDecay_of_ae {u F : ℝ → ℂ} (hu : Continuous u) (hae : F =ᵐ[volume] u)
    {C : ℝ} {B : ℕ}
    (hF : ∀ x : ℝ, 1 ≤ |x| → ‖F x‖ ≤ C / |x| ^ B) :
    ∀ x : ℝ, 1 < |x| → ‖u x‖ ≤ C / |x| ^ B := by
  have hmaxpos : ∀ y : ℝ, (0 : ℝ) < (max |y| 1) ^ B := by
    intro y
    have h1 : (1 : ℝ) ≤ max |y| 1 := le_max_right _ _
    positivity
  have hbcont : Continuous fun y : ℝ => C / (max |y| 1) ^ B := by
    refine Continuous.div continuous_const ?_ fun y => ne_of_gt (hmaxpos y)
    exact (continuous_abs.max continuous_const).pow B
  have hsopen : IsOpen {y : ℝ | 1 < |y|} := isOpen_lt continuous_const continuous_abs
  have hae' : ∀ᵐ y : ℝ, y ∈ {y : ℝ | 1 < |y|} → ‖u y‖ ≤ C / (max |y| 1) ^ B := by
    filter_upwards [hae] with y hy hys
    have hy1 : (1 : ℝ) ≤ |y| := le_of_lt hys
    have hmax : max |y| 1 = |y| := max_eq_left hy1
    rw [hmax, ← hy]
    exact hF y hy1
  have hpt := deningerAeBound_on_open hsopen hu.norm hbcont hae'
  intro x hx
  have hbound := hpt x hx
  have hmax : max |x| 1 = |x| := max_eq_left (le_of_lt hx)
  rwa [hmax] at hbound

/-! ## The Fourier pair -/

/-- **The kernel equation is a pointwise Fourier identity.**  For `h` in the kernel, the even
extension of the preimage is the Fourier transform of the even extension of the opposite collar's
preimage, almost everywhere. -/
theorem deningerEvenPreimage_ae_fourier {h : DeningerExpSchwartz}
    (hker : deningerMobiusCommutator h = 0) :
    deningerEvenPreimage ((h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ))
      =ᵐ[volume]
        𝓕 (deningerEvenPreimage
          ((deningerCollarExchange h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ))) := by
  have hFint : Integrable (deningerEvenPreimage ((h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ))) :=
    deningerEvenPreimage_integrable h.2
  have hGint : Integrable (deningerEvenPreimage
      ((deningerCollarExchange h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ))) :=
    deningerEvenPreimage_integrable (deningerCollarExchange h).2
  have hinv : 𝓕⁻ (deningerEvenPreimage
      ((deningerCollarExchange h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)))
      = 𝓕 (deningerEvenPreimage
        ((deningerCollarExchange h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ))) := by
    rw [Real.fourierInv_eq_fourier_comp_neg]
    congr 1
    funext x
    exact deningerEvenPreimage_even _ x
  have hcomm : 𝓕 (deningerL1Distribution hFint) = deningerL1Distribution hGint := by
    have hz := hker
    rw [deningerMobiusCommutator, deningerPreimageDistribution, deningerPreimageDistribution,
      sub_eq_zero] at hz
    exact hz
  have hback : deningerL1Distribution hFint = 𝓕⁻ (deningerL1Distribution hGint) := by
    rw [← hcomm, fourierInv_fourier_eq]
  have hGcont : Continuous (𝓕 (deningerEvenPreimage
      ((deningerCollarExchange h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)))) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ (E := ℝ)).continuous₂ hGint
  refine deningerDensity_ae_eq hFint.locallyIntegrable hGcont.locallyIntegrable fun g => ?_
  have hleft : (∫ x : ℝ, g x • deningerEvenPreimage
      ((h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) x)
      = deningerL1Distribution hFint g := (deningerL1Distribution_apply hFint g).symm
  rw [hleft, hback, deningerL1Distribution_fourierInv_apply, hinv]

/-! ## The Schwartz preimage -/

/-- **Every element of the kernel of the commutator has a Schwartz preimage.**  The opposite collar
supplies the Fourier moments, which give smoothness with bounded derivatives; the Möbius side
supplies the rapid decay; Landau interpolation combines them. -/
theorem deningerCommutatorKernel_schwartz {h : DeningerExpSchwartz}
    (hker : deningerMobiusCommutator h = 0) :
    ∃ f : 𝓢(ℝ, ℂ),
      deningerEvenPreimage ((h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) =ᵐ[volume] (f : ℝ → ℂ) := by
  set G : ℝ → ℂ := deningerEvenPreimage
    ((deningerCollarExchange h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) with hGdef
  have hGint : Integrable G := deningerEvenPreimage_integrable (deningerCollarExchange h).2
  have hmom : ∀ n : ℕ, Integrable fun v : ℝ => ‖v‖ ^ n * ‖G v‖ :=
    fun n => deningerEvenPreimage_norm_moment (deningerCollarExchange h).2 n
  have hae : deningerEvenPreimage ((h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) =ᵐ[volume] 𝓕 G :=
    deningerEvenPreimage_ae_fourier hker
  have hsmooth : ContDiff ℝ ∞ (𝓕 G) := deningerFourier_contDiff hmom
  have hbd : ∀ r : ℕ, ∃ M : ℝ, ∀ x : ℝ, ‖iteratedDeriv r (𝓕 G) x‖ ≤ M :=
    fun r => deningerFourier_iteratedDeriv_bound hmom hGint.aestronglyMeasurable r
  have hGcont : Continuous (𝓕 G) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ (E := ℝ)).continuous₂ hGint
  have habs : ∀ B : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 1 < |x| → ‖(𝓕 G) x‖ ≤ C / |x| ^ B := by
    intro B
    obtain ⟨C, hCnn, hC⟩ := deningerEvenPreimage_decay h.2 B
    exact ⟨C, hCnn, deningerAbsDecay_of_ae hGcont hae hC⟩
  have hR : ∀ B : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 1 ≤ x → ‖(𝓕 G) x‖ ≤ C / x ^ B := by
    intro B
    obtain ⟨C, hCnn, hC⟩ := habs B
    refine ⟨max C ‖(𝓕 G) 1‖, le_trans hCnn (le_max_left _ _), fun x hx => ?_⟩
    rcases eq_or_lt_of_le hx with heq | hlt
    · rw [← heq, one_pow, div_one]
      exact le_max_right _ _
    · have habsx : |x| = x := abs_of_nonneg (le_trans zero_le_one hx)
      have hxlt : 1 < |x| := by rwa [habsx]
      have hb := hC x hxlt
      rw [habsx] at hb
      refine le_trans hb ?_
      exact (div_le_div_iff_of_pos_right (by positivity)).mpr (le_max_left _ _)
  have hL : ∀ B : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 1 ≤ x → ‖(𝓕 G) (-x)‖ ≤ C / x ^ B := by
    intro B
    obtain ⟨C, hCnn, hC⟩ := habs B
    refine ⟨max C ‖(𝓕 G) (-1)‖, le_trans hCnn (le_max_left _ _), fun x hx => ?_⟩
    rcases eq_or_lt_of_le hx with heq | hlt
    · rw [← heq, one_pow, div_one]
      exact le_max_right _ _
    · have habsx : |(-x)| = x := by
        rw [abs_neg, abs_of_nonneg (le_trans zero_le_one hx)]
      have hxlt : 1 < |(-x)| := by rwa [habsx]
      have hb := hC (-x) hxlt
      rw [habsx] at hb
      refine le_trans hb ?_
      exact (div_le_div_iff_of_pos_right (by positivity)).mpr (le_max_left _ _)
  exact ⟨deningerSchwartzOfDecay (𝓕 G) hsmooth hbd hR hL, hae⟩

end

end RHTower
