import GaloisForLFunctions.HTGeometry.SchwartzShiftedNumberBounds

/-!
# Neutral no-growth on the corpus Schwartz operators

The nonnegative-energy mechanism of Theorem 2 in arXiv:2608.21406v1 applies
to the existing number operator, oscillator Hamiltonian, and shifted number
operator on complex Schwartz space. The actual sesquilinear energy is a sum
of squared L2 norms. Every frequency with strictly positive imaginary part is
constructed explicitly, and its mode equation is equivalent to the zero state.
No spectral, boundary, or integration-by-parts premise is introduced.
-/

noncomputable section
open scoped SchwartzMap
open MeasureTheory
namespace GaloisForLFunctions

def growingFrequency (u s : ℝ) : ℂ := ⟨u, Real.exp s⟩

/-- A squared upper-half-plane frequency cannot balance a nonnegative energy. -/
theorem growingFrequency_energy_balance (u s a b c : ℝ) :
    ((a ^ 2 + c ^ 2 * b ^ 2 : ℝ) : ℂ) =
      (growingFrequency u s) ^ 2 * (b ^ 2 : ℝ) ↔ a = 0 ∧ b = 0 := by
  constructor
  · intro h
    by_cases hb : b = 0
    · subst b
      have hr := congrArg Complex.re h
      simp only [Complex.ofReal_re, zero_pow (by omega : 2 ≠ 0), mul_zero, add_zero,
        Complex.ofReal_zero, mul_zero, Complex.zero_re] at hr
      exact ⟨(sq_eq_zero_iff.mp hr), rfl⟩
    · have hi := congrArg Complex.im h
      have hr := congrArg Complex.re h
      simp only [pow_two, growingFrequency, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re,
        Complex.mul_im, mul_zero, zero_add, sub_zero] at hi hr
      have hx : u * (Real.exp s * b ^ 2) = 0 := by nlinarith [hi]
      have hpos : 0 < Real.exp s * b ^ 2 := mul_pos (Real.exp_pos s) (sq_pos_of_ne_zero hb)
      have hu : u = 0 := (mul_eq_zero.mp hx).resolve_right hpos.ne'
      subst u
      have hneg : 0 < (Real.exp s) ^ 2 * b ^ 2 := mul_pos (sq_pos_of_pos (Real.exp_pos s))
        (sq_pos_of_ne_zero hb)
      have hc : 0 ≤ c ^ 2 * b ^ 2 := mul_nonneg (sq_nonneg c) (sq_nonneg b)
      exfalso
      nlinarith [sq_nonneg a]
  · rintro ⟨rfl, rfl⟩
    simp

/-- Every nonnegative shift of the corpus number operator has no growing frequency mode. -/
theorem schwartzNumber_squaredShift_no_growing_mode (u s c : ℝ) (g : 𝓢(ℝ, ℂ)) :
    numberCLM g + ((c ^ 2 : ℝ) : ℂ) • g =
      ((growingFrequency u s) ^ 2) • g ↔ g = 0 := by
  constructor
  · intro h
    have hp := congrArg (fun f => schwartzPair (SchwartzMap.conjSLM g) f) h
    rw [schwartzPair_add_right, schwartzPair_conj_numberCLM,
      schwartzPair_smul_right, schwartzPair_smul_right, schwartzPair_conj_self] at hp
    have henergy : ((‖(annihilationCLM g).toLp 2 (volume : Measure ℝ)‖ ^ 2 +
        c ^ 2 * ‖g.toLp 2 (volume : Measure ℝ)‖ ^ 2 : ℝ) : ℂ) =
      ((growingFrequency u s) ^ 2) *
        (‖g.toLp 2 (volume : Measure ℝ)‖ ^ 2 : ℝ) := by
      simpa only [Complex.ofReal_add, Complex.ofReal_mul] using hp
    have hn := (growingFrequency_energy_balance u s
      ‖(annihilationCLM g).toLp 2 (volume : Measure ℝ)‖ ‖g.toLp 2 (volume : Measure ℝ)‖ c).mp henergy
    apply SchwartzMap.injective_toLp 2 (volume : Measure ℝ)
    have hz := (SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure ℝ)).map_zero
    rw [SchwartzMap.toLpCLM_apply] at hz
    exact (norm_eq_zero.mp hn.2).trans hz.symm
  · rintro rfl
    simp

/-- The unshifted number operator inherits the neutral no-growth conclusion. -/
theorem numberCLM_no_growing_mode (u s : ℝ) (g : 𝓢(ℝ, ℂ)) :
    numberCLM g = ((growingFrequency u s) ^ 2) • g ↔ g = 0 := by
  simpa using schwartzNumber_squaredShift_no_growing_mode u s 0 g

/-- The oscillator Hamiltonian has no upper-half-plane frequency mode. -/
theorem hamiltonianCLM_no_growing_mode (u s : ℝ) (g : 𝓢(ℝ, ℂ)) :
    hamiltonianCLM g = ((growingFrequency u s) ^ 2) • g ↔ g = 0 := by
  have h := schwartzNumber_squaredShift_no_growing_mode u s (Real.sqrt (2 * Real.pi)) g
  rw [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2 * Real.pi)] at h
  simpa only [hamiltonianCLM_apply, Complex.ofReal_mul, Complex.ofReal_ofNat] using h

/-- The coercive shifted number operator has the same frequency exclusion. -/
theorem shiftedNumberCLM_no_growing_mode (u s : ℝ) (g : 𝓢(ℝ, ℂ)) :
    shiftedNumberCLM g = ((growingFrequency u s) ^ 2) • g ↔ g = 0 := by
  have h := schwartzNumber_squaredShift_no_growing_mode u s (Real.sqrt (4 * Real.pi)) g
  rw [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 4 * Real.pi)] at h
  simpa only [shiftedNumberCLM_apply, Complex.ofReal_mul, Complex.ofReal_ofNat] using h

end GaloisForLFunctions
