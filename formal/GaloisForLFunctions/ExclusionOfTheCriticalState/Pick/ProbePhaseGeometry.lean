import GaloisForLFunctions.ExclusionOfTheCriticalState.Pick.ProbePhaseOrbit

/-!
# Projective distinguishability of Weil phase orbits

The Gram determinant of two phase translates is the product of the two
sector masses and their squared phase distance. The positive-negative mass
product is also one quarter of the difference between squared Hilbert mass
and squared Weil energy. Thus projective phase sensitivity measures mixing
of the two reflection sectors.
-/

noncomputable section
namespace GaloisForLFunctions.ExclusionOfTheCriticalState.ProbeWalk
open scoped ComplexConjugate

/-- The orbital action as a surjective complex linear isometry. -/
def phaseRotationEquiv (u : Circle) : ZeroSpace ≃ₗᵢ[ℂ] ZeroSpace where
  toLinearEquiv :=
    { toFun := phaseRotate u
      map_add' := by
        intro x y
        simp only [phaseRotate, positivePart_add, negativePart_add, smul_add]
        abel
      map_smul' := by
        intro c x
        simp only [phaseRotate, positivePart_smul, negativePart_smul, RingHom.id_apply]
        module
      invFun := phaseRotate u⁻¹
      left_inv := by
        intro x
        rw [phaseRotate_mul, inv_mul_cancel, phaseRotate_one]
      right_inv := by
        intro x
        rw [phaseRotate_mul, mul_inv_cancel, phaseRotate_one] }
  norm_map' := by
    intro x
    have h : ‖phaseRotate u x‖ ^ 2 = ‖x‖ ^ 2 := by
      rw [norm_sq_eq_re_inner (𝕜 := ℂ), norm_sq_eq_re_inner (𝕜 := ℂ), inner_phaseRotate]
    nlinarith only [h, norm_nonneg (phaseRotate u x), norm_nonneg x]

/-- A unitary circle representation on the actual Weil zero-coordinate space. -/
def phaseRepresentation : Circle →* (ZeroSpace ≃ₗᵢ[ℂ] ZeroSpace) where
  toFun := phaseRotationEquiv
  map_one' := by
    ext x
    exact phaseRotate_one x
  map_mul' := by
    intro u v
    ext x
    exact (phaseRotate_mul u v x).symm

/-- Hilbert mass in the positive reflection sector. -/
def positiveMass (x : ZeroSpace) : ℝ := ‖positivePart x‖ ^ 2

/-- Hilbert mass in the negative reflection sector. -/
def negativeMass (x : ZeroSpace) : ℝ := ‖negativePart x‖ ^ 2

/-- Signed energy of an arbitrary actual zero-coordinate vector. -/
def reflectionEnergy (x : ZeroSpace) : ℝ := (inner ℂ (zeroReflection x) x).re

theorem sector_mass_sum (x : ZeroSpace) :
    positiveMass x + negativeMass x = ‖x‖ ^ 2 := by
  have h := congrArg Complex.re (sector_inner_sum x x)
  simpa only [inner_self_eq_norm_sq_to_K, ← Complex.ofReal_pow, Complex.add_re,
    Complex.ofReal_re, positiveMass, negativeMass] using h

/-- The signed Weil energy is the exact difference of the sector masses. -/
theorem reflectionEnergy_eq_mass_difference (x : ZeroSpace) :
    reflectionEnergy x = positiveMass x - negativeMass x := by
  have h := congrArg Complex.re (sector_inner_difference x x)
  simpa only [inner_self_eq_norm_sq_to_K, ← Complex.ofReal_pow, Complex.sub_re,
    Complex.ofReal_re, reflectionEnergy, positiveMass, negativeMass] using h.symm

private theorem scalar_phase_loss (a b : ℝ) (u v : Circle) :
    (a + b) ^ 2 - Complex.normSq ((a : ℂ) + (conj (u : ℂ) * (v : ℂ)) * (b : ℂ)) =
      a * b * ‖(u : ℂ) - (v : ℂ)‖ ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_sub, Complex.normSq_add]
  simp only [Complex.normSq_mul, Complex.normSq_conj, Circle.normSq_coe, one_mul,
    Complex.normSq_ofReal, map_mul, Complex.conj_ofReal,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.conj_re, Complex.conj_im, mul_zero, zero_mul, sub_zero, add_zero]
  ring

/-- Exact projective overlap loss for all phases and all zero-coordinate vectors. -/
theorem phaseRotate_projective_loss (u v : Circle) (x : ZeroSpace) :
    ‖x‖ ^ 4 - ‖inner ℂ (phaseRotate u x) (phaseRotate v x)‖ ^ 2 =
      positiveMass x * negativeMass x * ‖(u : ℂ) - (v : ℂ)‖ ^ 2 := by
  rw [phaseRotate_overlap, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K,
    ← Complex.ofReal_pow, ← Complex.ofReal_pow, ← Complex.normSq_eq_norm_sq]
  have hpow : ‖x‖ ^ 4 = (positiveMass x + negativeMass x) ^ 2 := by
    rw [sector_mass_sum]
    ring
  rw [hpow]
  exact scalar_phase_loss (positiveMass x) (negativeMass x) u v

/-- The phase-geometry numerator is exactly the deficit of squared Weil energy. -/
theorem sector_mass_product (x : ZeroSpace) :
    4 * (positiveMass x * negativeMass x) = ‖x‖ ^ 4 - reflectionEnergy x ^ 2 := by
  rw [reflectionEnergy_eq_mass_difference]
  have h := sector_mass_sum x
  calc
    _ = (positiveMass x + negativeMass x) ^ 2 -
        (positiveMass x - negativeMass x) ^ 2 := by ring
    _ = _ := by rw [h]; ring

/-- Vanishing projective phase sensitivity is exactly concentration in one eigensector. -/
theorem sector_mass_product_zero_iff (x : ZeroSpace) :
    positiveMass x * negativeMass x = 0 ↔
      zeroReflection x = x ∨ zeroReflection x = -x := by
  rw [mul_eq_zero]
  have hp : positiveMass x = 0 ↔ zeroReflection x = -x := by
    rw [positiveMass, sq_eq_zero_iff, norm_eq_zero, positivePart, smul_eq_zero]
    simp only [one_div, inv_eq_zero, OfNat.ofNat_ne_zero, false_or]
    rw [add_comm, add_eq_zero_iff_eq_neg]
  have hn : negativeMass x = 0 ↔ zeroReflection x = x := by
    rw [negativeMass, sq_eq_zero_iff, norm_eq_zero, negativePart, smul_eq_zero]
    simp only [one_div, inv_eq_zero, OfNat.ofNat_ne_zero, false_or, sub_eq_zero]
    exact eq_comm
  rw [hp, hn, or_comm]

#print axioms phaseRotate_projective_loss
#print axioms phaseRepresentation
#print axioms sector_mass_product
#print axioms sector_mass_product_zero_iff

end GaloisForLFunctions.ExclusionOfTheCriticalState.ProbeWalk
