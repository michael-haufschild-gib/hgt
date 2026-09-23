import GaloisForLFunctions.HTGeometry.KleinGordonShiftedEquationOfMotion

/-!
# The generator against the inverse square frequency

The strong form of the Klein–Gordon equation used by the mild theory reads

`⟨D⟩⁻²ü = −u + ⟨D⟩⁻²(Wu)`,

so the potential enters with a minus sign relative to the frequency: the natural frequency of a real
diagonal potential `p` is `Ω² = ⟨ξ⟩² − p`. Against `⟨D⟩⁻²` the generator of that frequency collapses,

`⟨D⟩⁻²(Ω²χ z) = z − ⟨D⟩⁻²(p z)`   for band-limited `z`,

which is exactly the right-hand side of the equation. This is the algebraic step that will turn the
two equations of motion into a strong solution.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

section RealPotential

variable {p : E → ℝ} {b : ℝ}

/-- The complex symbol of a real diagonal potential. -/
def kgRealPotSymbol (p : E → ℝ) (ξ : E) : ℂ := ((p ξ : ℝ) : ℂ)

omit [NormedAddCommGroup E] [BorelSpace E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
theorem measurable_kgRealPotSymbol (hp : Measurable p) : Measurable (kgRealPotSymbol p) :=
  Complex.continuous_ofReal.measurable.comp hp

omit [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
theorem norm_kgRealPotSymbol_le (hpb : ∀ ξ : E, |p ξ| ≤ b) (ξ : E) :
    ‖kgRealPotSymbol p ξ‖ ≤ b := by
  rw [kgRealPotSymbol, Complex.norm_real, Real.norm_eq_abs]
  exact hpb ξ

omit [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
theorem starRingEnd_kgRealPotSymbol (p : E → ℝ) (ξ : E) :
    (starRingEnd ℂ) (kgRealPotSymbol p ξ) = kgRealPotSymbol p ξ := Complex.conj_ofReal _

omit [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- The shifted frequency of a real potential uses the negated symbol. -/
theorem abs_neg_pot_le (hpb : ∀ ξ : E, |p ξ| ≤ b) (ξ : E) : |(-(p ξ))| ≤ b := by
  rw [abs_neg]
  exact hpb ξ

omit [MeasurableSpace E] [BorelSpace E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- **The generator of the shifted frequency, against the inverse square frequency, collapses.** -/
theorem kgFreqInvSq_kgShiftedFreqSqLow (hb1 : b < 1) (hpb : ∀ ξ : E, |p ξ| ≤ b) (R : ℝ) (ξ : E) :
    kgFreqInv ξ * (kgFreqInv ξ
        * (kgShiftedFreqSqLow (fun ζ : E => -(p ζ)) R ξ * kgLowPass R ξ))
      = kgLowPass R ξ - kgFreqInv ξ * (kgFreqInv ξ * (kgRealPotSymbol p ξ * kgLowPass R ξ)) := by
  have hfreq := kgFreq_pos ξ
  have hsq := kgShiftedFreq_sq (v := fun ζ : E => -(p ζ)) hb1 (abs_neg_pot_le hpb) ξ
  have hne : (kgFreq ξ : ℂ) ≠ 0 := by
    simpa using (ne_of_gt hfreq)
  have hinv : kgFreqInv ξ = ((kgFreq ξ : ℝ) : ℂ)⁻¹ := by
    rw [kgFreqInv, Complex.ofReal_inv]
  have hgen : kgShiftedFreqSqLow (fun ζ : E => -(p ζ)) R ξ
      = (((kgFreq ξ ^ (2 : ℕ) : ℝ) : ℂ) - kgRealPotSymbol p ξ) * kgLowPass R ξ := by
    rw [kgShiftedFreqSqLow, hsq, kgRealPotSymbol]
    push_cast
    ring
  have hchi : kgLowPass R ξ * kgLowPass R ξ = kgLowPass R ξ := by
    rw [kgLowPass]
    split <;> simp
  rw [hgen, hinv]
  have hfsq : ((kgFreq ξ : ℝ) : ℂ)⁻¹ * (((kgFreq ξ : ℝ) : ℂ)⁻¹ * ((kgFreq ξ ^ (2 : ℕ) : ℝ) : ℂ)) = 1 := by
    push_cast
    field_simp
  calc ((kgFreq ξ : ℝ) : ℂ)⁻¹ * (((kgFreq ξ : ℝ) : ℂ)⁻¹
        * ((((kgFreq ξ ^ (2 : ℕ) : ℝ) : ℂ) - kgRealPotSymbol p ξ) * kgLowPass R ξ * kgLowPass R ξ))
      = (((kgFreq ξ : ℝ) : ℂ)⁻¹ * (((kgFreq ξ : ℝ) : ℂ)⁻¹ * ((kgFreq ξ ^ (2 : ℕ) : ℝ) : ℂ)))
          * (kgLowPass R ξ * kgLowPass R ξ)
        - ((kgFreq ξ : ℝ) : ℂ)⁻¹ * (((kgFreq ξ : ℝ) : ℂ)⁻¹
            * (kgRealPotSymbol p ξ * (kgLowPass R ξ * kgLowPass R ξ))) := by ring
    _ = kgLowPass R ξ - ((kgFreq ξ : ℝ) : ℂ)⁻¹ * (((kgFreq ξ : ℝ) : ℂ)⁻¹
          * (kgRealPotSymbol p ξ * kgLowPass R ξ)) := by
        rw [hfsq, hchi, one_mul]

end RealPotential

end GaloisForLFunctions.HTGeometry
