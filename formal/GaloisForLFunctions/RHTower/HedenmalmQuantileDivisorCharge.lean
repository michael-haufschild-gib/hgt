import GaloisForLFunctions.RHTower.HedenmalmQuantileRootMode
import GaloisForLFunctions.HTGeometry.LogarithmicResidueQuantization

/-!
# The boundary flux is the modular divisor charge

For a zero `ρ` of multiplicity `m` of a meromorphic function, the residue at `ρ` of the centered
logarithmic derivative `-(s - 1/2) f'(s)/f(s)` is `-(ρ - 1/2) m`, whose real part is the modular
divisor charge

`Q_ρ = m (1/2 - Re ρ)`.

In the centered spectral coordinate `z = -i(ρ - 1/2)` the imaginary part of `z` is exactly
`Q_ρ / m`, so the universal rank-two boundary flux of a root mode at `z` equals that charge up to
the explicit factor `m |z|²`.  The critical line is exactly the equality of the incoming and
outgoing boundary intensities.
-/

open MeasureTheory Set Filter Topology Complex

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry

namespace HedenmalmQuantile

/-! ### The centered spectral coordinate -/

/-- The centered spectral coordinate `z = -i(ρ - 1/2)` of a critical-strip parameter. -/
def centeredParameter (rho : ℂ) : ℂ := -Complex.I * (rho - 1 / 2)

@[simp] theorem centeredParameter_im (rho : ℂ) :
    (centeredParameter rho).im = 1 / 2 - rho.re := by
  rw [centeredParameter]
  simp [Complex.mul_im]

/-- The modular divisor charge `Q_ρ = m (1/2 - Re ρ)`. -/
def divisorCharge (m : ℕ) (rho : ℂ) : ℝ := (m : ℝ) * (1 / 2 - rho.re)

/-! ### The charge is the centered logarithmic residue -/

/-- **The centered logarithmic residue.**  The residue of `-(s - 1/2) f'/f` at a zero of order `n`
is `-(ρ - 1/2) n`. -/
theorem centeredLogDeriv_residue {f : ℂ → ℂ} {rho : ℂ} {n : ℤ}
    (hf : MeromorphicAt f rho) (horder : meromorphicOrderAt f rho = n) :
    Tendsto (fun s => (s - rho) * (-(s - 1 / 2) * logDeriv f s)) (𝓝[≠] rho)
      (𝓝 (-(rho - 1 / 2) * (n : ℂ))) := by
  have hres := logDeriv_residue_of_meromorphicOrder hf horder
  have hfac : Tendsto (fun s : ℂ => -(s - 1 / 2)) (𝓝[≠] rho) (𝓝 (-(rho - 1 / 2))) :=
    ((continuous_id.sub continuous_const).neg.tendsto rho).mono_left nhdsWithin_le_nhds
  have := hfac.mul hres
  refine this.congr fun s => ?_
  ring

/-- **The real part of the centered logarithmic residue is the modular divisor charge.** -/
theorem re_centeredLogDeriv_residue (m : ℕ) (rho : ℂ) :
    (-(rho - 1 / 2) * (m : ℂ)).re = divisorCharge m rho := by
  rw [divisorCharge]
  simp [Complex.mul_re, Complex.sub_re, Complex.sub_im]
  ring

/-! ### The flux law in divisor form -/

theorem neg_inv_im (z : ℂ) : (-z⁻¹).im = z.im / ‖z‖ ^ (2 : ℕ) := by
  rw [Complex.neg_im, Complex.inv_im, ← Complex.normSq_eq_norm_sq]
  ring

/-- **The spectral flux of a root mode is the modular divisor charge.**  In the centered
coordinate `z = -i(ρ-1/2)`, the imaginary part of the spectral value `λ = -1/z` times `m |z|²` is
exactly the charge `Q_ρ`. -/
theorem im_spectralValue_mul (m : ℕ) {rho : ℂ} (hz : centeredParameter rho ≠ 0) :
    (-(centeredParameter rho)⁻¹).im * ((m : ℝ) * ‖centeredParameter rho‖ ^ (2 : ℕ))
      = divisorCharge m rho := by
  have hnorm : ‖centeredParameter rho‖ ^ (2 : ℕ) ≠ 0 := by
    have : ‖centeredParameter rho‖ ≠ 0 := norm_ne_zero_iff.mpr hz
    positivity
  rw [neg_inv_im, divisorCharge, centeredParameter_im]
  field_simp

variable (S : PositiveDensitySource)

/-- **The divisor charge read off a root mode.**  Combining the spectral flux law with the
centered coordinate turns the universal boundary form into the modular divisor charge. -/
theorem inner_pinnedBoundaryCLM_divisorCharge (m : ℕ) {rho : ℂ}
    (hz : centeredParameter rho ≠ 0) {g : H}
    (h : IsQuantileRootMode S (-(centeredParameter rho)⁻¹) g) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ t, ‖metricSymbol S t‖ ≤ C) :
    ((m : ℝ) * ‖centeredParameter rho‖ ^ (2 : ℕ) : ℂ) * inner ℂ (pinnedBoundaryCLM g) g
      = 2 * ((divisorCharge m rho : ℝ) : ℂ) * inner ℂ (metricOperator S hC0 hC g) g := by
  rw [inner_pinnedBoundaryCLM_rootMode S h hC0 hC, ← im_spectralValue_mul m hz]
  push_cast
  ring

/-- **The critical-line criterion.**  The boundary flux vanishes exactly when the incoming and
outgoing boundary intensities agree. -/
theorem inner_pinnedBoundaryCLM_eq_zero_iff_amplitudes (g : H) :
    (inner ℂ (pinnedBoundaryCLM g) g : ℂ) = 0
      ↔ ‖pinnedInAmplitude g‖ = ‖pinnedOutAmplitude g‖ := by
  rw [inner_pinnedBoundaryCLM_eq_amplitudes]
  constructor
  · intro hzero
    have : ((‖pinnedInAmplitude g‖ : ℂ)) ^ (2 : ℕ) = ((‖pinnedOutAmplitude g‖ : ℂ)) ^ (2 : ℕ) :=
      sub_eq_zero.mp hzero
    have hreal : ‖pinnedInAmplitude g‖ ^ (2 : ℕ) = ‖pinnedOutAmplitude g‖ ^ (2 : ℕ) := by
      exact_mod_cast this
    have := abs_eq_abs.mpr (sq_eq_sq_iff_eq_or_eq_neg.mp hreal)
    rw [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (norm_nonneg _)] at this
    exact this
  · intro heq
    rw [heq]
    ring

end HedenmalmQuantile

end

end RHTower
