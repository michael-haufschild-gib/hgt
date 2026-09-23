import GaloisForLFunctions.HTGeometry.WienerSynthesisSpace

/-!
# The Laplacian of a synthesis

Summing the second directional derivatives over an orthonormal basis turns the factor
`(2πi⟪ξ,eᵢ⟫)²` into `-4π²‖ξ‖²`, by the Parseval identity of the basis. So the Laplacian of a
synthesis is the synthesis of `-4π²‖ξ‖²` times the density — and since the Klein–Gordon frequency
satisfies `⟨ξ⟩² = 1 + ‖ξ‖²`, the combination `(2π)⁻²Δ - 1` is the synthesis of `-⟨ξ⟩²`.

That is the spatial half of the field equation; the temporal half was the oscillator equation, and
the two now meet on the same multiplier.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory

open scoped RealInnerProductSpace FourierTransform

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {ι : Type*} [Fintype ι]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- **Parseval for an orthonormal basis**, in real form. -/
theorem sum_sq_real_inner (b : OrthonormalBasis ι ℝ E) (ξ : E) :
    ∑ i, (⟪ξ, b i⟫ : ℝ) ^ (2 : ℕ) = ‖ξ‖ ^ (2 : ℕ) := by
  have h := b.sum_sq_norm_inner_left ξ
  rw [← h]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Real.norm_eq_abs, sq_abs]

/-- The integrand of a second directional derivative is integrable. -/
theorem integrable_dirSq {f : E → ℂ} (hmeas : AEStronglyMeasurable f (volume : Measure E))
    (h2 : Integrable (fun ξ : E => kgFreq ξ ^ (2 : ℕ) * ‖f ξ‖) (volume : Measure E)) (x v : E) :
    Integrable
      (fun ξ : E => (2 * Real.pi * Complex.I * ((⟪ξ, v⟫ : ℝ) : ℂ)) ^ (2 : ℕ) * kgChar x ξ * f ξ)
      (volume : Measure E) := by
  have hinnerCont : Continuous fun ξ : E => ((⟪ξ, v⟫ : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (continuous_inner.comp (continuous_id.prodMk continuous_const))
  refine Integrable.mono' (h2.const_mul ((2 * Real.pi * ‖v‖) ^ (2 : ℕ)))
    (((((continuous_const.mul hinnerCont).pow 2).mul
      (continuous_kgChar' x)).aestronglyMeasurable).mul hmeas) ?_
  filter_upwards with ξ
  rw [norm_mul, norm_mul, norm_kgChar, mul_one, norm_pow, norm_two_pi_I_inner]
  have hinner := norm_inner_le_kgFreq v ξ
  have hf : (0 : ℝ) ≤ ‖f ξ‖ := norm_nonneg _
  have hpipos : (0 : ℝ) < 2 * Real.pi := by positivity
  have hsq : (2 * Real.pi * |(⟪ξ, v⟫ : ℝ)|) ^ (2 : ℕ) ≤ (2 * Real.pi * (‖v‖ * kgFreq ξ)) ^ (2 : ℕ) := by
    have hnn : (0 : ℝ) ≤ 2 * Real.pi * |(⟪ξ, v⟫ : ℝ)| := by positivity
    have hmono : 2 * Real.pi * |(⟪ξ, v⟫ : ℝ)| ≤ 2 * Real.pi * (‖v‖ * kgFreq ξ) :=
      mul_le_mul_of_nonneg_left hinner hpipos.le
    exact pow_le_pow_left₀ hnn hmono 2
  nlinarith [hsq, hf]

/-- **The Laplacian of a synthesis is the synthesis of `-4π²‖ξ‖²` times the density.** -/
theorem sum_integral_dirSq {f : E → ℂ} (hmeas : AEStronglyMeasurable f (volume : Measure E))
    (h2 : Integrable (fun ξ : E => kgFreq ξ ^ (2 : ℕ) * ‖f ξ‖) (volume : Measure E))
    (b : OrthonormalBasis ι ℝ E) (x : E) :
    ∑ i, (∫ ξ, (2 * Real.pi * Complex.I * ((⟪ξ, b i⟫ : ℝ) : ℂ)) ^ (2 : ℕ) * kgChar x ξ * f ξ)
      = ∫ ξ, ((-(4 * Real.pi ^ (2 : ℕ)) * ‖ξ‖ ^ (2 : ℕ) : ℝ) : ℂ) * kgChar x ξ * f ξ := by
  rw [← integral_finsetSum Finset.univ fun i _ => integrable_dirSq hmeas h2 x (b i)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  have hsum : ∑ i, (2 * Real.pi * Complex.I * ((⟪ξ, b i⟫ : ℝ) : ℂ)) ^ (2 : ℕ)
      = ((-(4 * Real.pi ^ (2 : ℕ)) * ‖ξ‖ ^ (2 : ℕ) : ℝ) : ℂ) := by
    have hfac : ∀ i : ι, (2 * Real.pi * Complex.I * ((⟪ξ, b i⟫ : ℝ) : ℂ)) ^ (2 : ℕ)
        = -(4 * (Real.pi : ℂ) ^ (2 : ℕ)) * (((⟪ξ, b i⟫ : ℝ) : ℂ)) ^ (2 : ℕ) := by
      intro i
      have hI : (Complex.I : ℂ) ^ (2 : ℕ) = -1 := Complex.I_sq
      ring_nf
      rw [hI]
      ring
    rw [Finset.sum_congr rfl fun i _ => hfac i, ← Finset.mul_sum]
    have hreal : ∑ i, (((⟪ξ, b i⟫ : ℝ) : ℂ)) ^ (2 : ℕ) = ((‖ξ‖ ^ (2 : ℕ) : ℝ) : ℂ) := by
      have h := sum_sq_real_inner b ξ
      have hcast : ((∑ i, (⟪ξ, b i⟫ : ℝ) ^ (2 : ℕ) : ℝ) : ℂ) = ((‖ξ‖ ^ (2 : ℕ) : ℝ) : ℂ) := by rw [h]
      rw [← hcast, Complex.ofReal_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [Complex.ofReal_pow]
    rw [hreal]
    push_cast
    ring
  show (∑ i, (2 * Real.pi * Complex.I * ((⟪ξ, b i⟫ : ℝ) : ℂ)) ^ (2 : ℕ) * kgChar x ξ * f ξ)
      = ((-(4 * Real.pi ^ (2 : ℕ)) * ‖ξ‖ ^ (2 : ℕ) : ℝ) : ℂ) * kgChar x ξ * f ξ
  rw [← Finset.sum_mul, ← Finset.sum_mul, hsum]

end GaloisForLFunctions.HTGeometry
