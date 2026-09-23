import GaloisForLFunctions.HTGeometry.TorusTrigPoincare

/-!
# Finite Fourier inversion of a torus transport derivative

A constant vector field on a torus acts diagonally on characters.  On a finite packet whose
frequencies are nonresonant with the vector field, dividing each coefficient by its nonzero
transport multiplier gives an exact inverse.  The inverse has zero Haar mean when the packet has
no zero mode, and its coefficients are uniquely determined.
-/

open Complex MeasureTheory Set

namespace GaloisForLFunctions.HTGeometry.NavierStokesFiniteTorusInverse

noncomputable section

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- Real transport frequency of an integer torus character. -/
def transportDetuning (velocity : d → ℝ) (frequency : d → ℤ) : ℝ :=
  ∑ i : d, velocity i * (frequency i : ℝ)

/-- Directional derivative along a constant vector field on the vector model of a torus. -/
def transportDerivative (velocity : d → ℝ) (F : (d → ℝ) → ℂ) : (d → ℝ) → ℂ :=
  fun x => ∑ i : d, (velocity i : ℂ) * pderiv i F x

/-- Complex Fourier multiplier of the transport derivative. -/
def transportMultiplier (velocity : d → ℝ) (frequency : d → ℤ) : ℂ :=
  2 * Real.pi * I * (transportDetuning velocity frequency : ℂ)

/-- Coefficient obtained by inverting one nonresonant transport multiplier. -/
def inverseAmplitude (velocity : d → ℝ) (amplitude : (d → ℤ) → ℂ)
    (frequency : d → ℤ) : ℂ :=
  amplitude frequency / transportMultiplier velocity frequency

/-- Squared coefficient norm of a finite Fourier packet. -/
def packetEnergy (packet : Finset (d → ℤ)) (amplitude : (d → ℤ) → ℂ) : ℝ :=
  ∑ frequency ∈ packet, ‖amplitude frequency‖ ^ (2 : ℕ)

omit [DecidableEq d] in
theorem transportDetuning_zero (velocity : d → ℝ) :
    transportDetuning velocity (0 : d → ℤ) = 0 := by
  simp [transportDetuning]

omit [DecidableEq d] in
theorem transportMultiplier_ne_zero {velocity : d → ℝ} {frequency : d → ℤ}
    (hfrequency : transportDetuning velocity frequency ≠ 0) :
    transportMultiplier velocity frequency ≠ 0 := by
  unfold transportMultiplier
  exact mul_ne_zero
    (mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)) I_ne_zero)
    (by exact_mod_cast hfrequency)

omit [DecidableEq d] in
/-- Absolute size of a transport multiplier. -/
theorem norm_transportMultiplier (velocity : d → ℝ) (frequency : d → ℤ) :
    ‖transportMultiplier velocity frequency‖ =
      2 * Real.pi * |transportDetuning velocity frequency| := by
  simp only [transportMultiplier, norm_mul, norm_ofNat, Complex.norm_real,
    norm_I, mul_one, Real.norm_eq_abs, abs_of_pos Real.pi_pos]

/-- Constant transport differentiates each character by its scalar transport multiplier. -/
theorem transportDerivative_trigLift {ι : Type*} (packet : Finset ι)
    (frequency : ι → (d → ℤ)) (amplitude : ι → ℂ) (velocity : d → ℝ) :
    transportDerivative velocity (trigLift packet frequency amplitude) =
      trigLift packet frequency
        (fun q => transportMultiplier velocity (frequency q) * amplitude q) := by
  funext x
  simp only [transportDerivative, pderiv_trigLift, trigLift]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun q hq => ?_
  simp only [transportMultiplier, transportDetuning]
  push_cast
  calc
    (∑ i : d, (velocity i : ℂ) *
        (2 * (Real.pi : ℂ) * I * (frequency q i : ℂ) * amplitude q *
          charLift (frequency q) x)) =
        ∑ i : d, (2 * (Real.pi : ℂ) * I * amplitude q * charLift (frequency q) x) *
          ((velocity i : ℂ) * (frequency q i : ℂ)) := by
            apply Finset.sum_congr rfl
            intro i _
            ring
    _ = (2 * (Real.pi : ℂ) * I * amplitude q * charLift (frequency q) x) *
          ∑ i : d, (velocity i : ℂ) * (frequency q i : ℂ) := by
            rw [Finset.mul_sum]
    _ = (2 * (Real.pi : ℂ) * I *
          ∑ i : d, (velocity i : ℂ) * (frequency q i : ℂ)) *
          amplitude q * charLift (frequency q) x := by ring

/-- Exact inverse on every finite nonresonant Fourier packet. -/
theorem transportDerivative_inverse (packet : Finset (d → ℤ))
    (amplitude : (d → ℤ) → ℂ) (velocity : d → ℝ)
    (hnonresonant : ∀ frequency ∈ packet,
      transportDetuning velocity frequency ≠ 0) :
    transportDerivative velocity
        (trigLift packet id (inverseAmplitude velocity amplitude)) =
      trigLift packet id amplitude := by
  rw [transportDerivative_trigLift]
  funext x
  simp only [trigLift, id_eq]
  refine Finset.sum_congr rfl fun frequency hfrequency => ?_
  have hmultiplier : transportMultiplier velocity frequency ≠ 0 :=
    transportMultiplier_ne_zero (hnonresonant frequency hfrequency)
  rw [inverseAmplitude]
  field_simp [hmultiplier]

omit [DecidableEq d] in
/-- Nonresonance excludes the constant Fourier mode. -/
theorem zero_not_mem_of_nonresonant {packet : Finset (d → ℤ)} {velocity : d → ℝ}
    (hnonresonant : ∀ frequency ∈ packet,
      transportDetuning velocity frequency ≠ 0) :
    (0 : d → ℤ) ∉ packet := by
  intro hzero
  exact hnonresonant 0 hzero (transportDetuning_zero velocity)

/-- The finite-packet transport inverse has zero Haar mean. -/
theorem integral_box_inverse_eq_zero (packet : Finset (d → ℤ))
    (amplitude : (d → ℤ) → ℂ) (velocity : d → ℝ)
    (hnonresonant : ∀ frequency ∈ packet,
      transportDetuning velocity frequency ≠ 0) :
    (∫ x in torusBox d, trigLift packet id (inverseAmplitude velocity amplitude) x) = 0 := by
  rw [integral_box_trigLift]
  refine Finset.sum_eq_zero fun frequency hfrequency => ?_
  have hzero : frequency = 0 := (Finset.mem_filter.mp hfrequency).2
  subst frequency
  exact absurd (Finset.mem_filter.mp hfrequency).1
    (zero_not_mem_of_nonresonant hnonresonant)

omit [DecidableEq d] in
/-- Fourier coefficients of a transport solution are uniquely forced on a nonresonant packet. -/
theorem inverseAmplitude_unique_on_packet {packet : Finset (d → ℤ)}
    {amplitude candidate : (d → ℤ) → ℂ} {velocity : d → ℝ}
    (hnonresonant : ∀ frequency ∈ packet,
      transportDetuning velocity frequency ≠ 0)
    (hsolution : ∀ frequency ∈ packet,
      transportMultiplier velocity frequency * candidate frequency = amplitude frequency) :
    ∀ frequency ∈ packet,
      candidate frequency = inverseAmplitude velocity amplitude frequency := by
  intro frequency hfrequency
  have hmultiplier : transportMultiplier velocity frequency ≠ 0 :=
    transportMultiplier_ne_zero (hnonresonant frequency hfrequency)
  apply (mul_left_cancel₀ hmultiplier)
  rw [hsolution frequency hfrequency, inverseAmplitude, mul_div_cancel₀ _ hmultiplier]

/-- Existence and coefficient uniqueness of the zero-mean finite Fourier transport inverse. -/
theorem exists_unique_inverse_on_packet (packet : Finset (d → ℤ))
    (amplitude : (d → ℤ) → ℂ) (velocity : d → ℝ)
    (hnonresonant : ∀ frequency ∈ packet,
      transportDetuning velocity frequency ≠ 0) :
    (transportDerivative velocity
        (trigLift packet id (inverseAmplitude velocity amplitude)) =
          trigLift packet id amplitude) ∧
      (∫ x in torusBox d,
        trigLift packet id (inverseAmplitude velocity amplitude) x) = 0 ∧
      ∀ candidate : (d → ℤ) → ℂ,
        (∀ frequency ∈ packet,
          transportMultiplier velocity frequency * candidate frequency = amplitude frequency) →
        ∀ frequency ∈ packet,
          candidate frequency = inverseAmplitude velocity amplitude frequency :=
  ⟨transportDerivative_inverse packet amplitude velocity hnonresonant,
    integral_box_inverse_eq_zero packet amplitude velocity hnonresonant,
    fun _ hsolution => inverseAmplitude_unique_on_packet hnonresonant hsolution⟩

omit [DecidableEq d] in
/--
Finite-packet small-divisor estimate from Lemma 8.6.  A uniform transport-frequency gap
`δ` bounds inverse coefficient energy by `(2πδ)⁻²` times source energy.
-/
theorem packetEnergy_inverse_le (packet : Finset (d → ℤ))
    (amplitude : (d → ℤ) → ℂ) (velocity : d → ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hgap : ∀ frequency ∈ packet,
      δ ≤ |transportDetuning velocity frequency|) :
    packetEnergy packet (inverseAmplitude velocity amplitude) ≤
      (2 * Real.pi * δ)⁻¹ ^ (2 : ℕ) * packetEnergy packet amplitude := by
  have hscale : 0 < 2 * Real.pi * δ := mul_pos (mul_pos (by norm_num) Real.pi_pos) hδ
  unfold packetEnergy
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun frequency hfrequency => ?_
  have hmultiplier : 0 < ‖transportMultiplier velocity frequency‖ := by
    rw [norm_transportMultiplier]
    exact mul_pos (mul_pos (by norm_num) Real.pi_pos)
      (lt_of_lt_of_le hδ (hgap frequency hfrequency))
  have hscale_le : 2 * Real.pi * δ ≤ ‖transportMultiplier velocity frequency‖ := by
    rw [norm_transportMultiplier]
    gcongr
    exact hgap frequency hfrequency
  have hinverseNorm :
      ‖inverseAmplitude velocity amplitude frequency‖ =
        ‖amplitude frequency‖ / ‖transportMultiplier velocity frequency‖ := by
    simp [inverseAmplitude]
  have hnorm :
      ‖inverseAmplitude velocity amplitude frequency‖ ≤
        (2 * Real.pi * δ)⁻¹ * ‖amplitude frequency‖ := by
    rw [hinverseNorm, inv_mul_eq_div]
    exact div_le_div_of_nonneg_left (norm_nonneg _) hscale hscale_le
  rw [← mul_pow]
  exact (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (inv_nonneg.mpr hscale.le) (norm_nonneg _))).mpr hnorm

end

end GaloisForLFunctions.HTGeometry.NavierStokesFiniteTorusInverse
