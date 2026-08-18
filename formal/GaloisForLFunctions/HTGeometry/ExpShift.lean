import GaloisForLFunctions.HTGeometry.RealExponentBase

/-!
# Shifting the exponents

Translating every exponent by a real number `β` multiplies the exponential polynomial by the
nowhere-zero factor `e^{-β t}`, so it changes neither the zero set nor real-valuedness, and it moves
a chosen exponent `y₀` onto the imaginary axis at `i·Im y₀` — where the Sturm operator `D² + γ²`
deletes it together with its conjugate.

This is the normalisation the descent needs: the reduction of `SturmReduction` removes the pair
`± iγ`, so the pair `β ± iγ` is removed by shifting first.
-/

open Set Filter Real

namespace GaloisForLFunctions.HTGeometry

variable (S : Finset ℂ) (C : ℂ → ℂ) (β : ℝ)

/-- The shifted support. -/
noncomputable def shiftSupport : Finset ℂ := S.image (fun y => y - ((β : ℝ) : ℂ))

/-- The shifted coefficients. -/
noncomputable def shiftCoeff : ℂ → ℂ := fun z => C (z + ((β : ℝ) : ℂ))

theorem mem_shiftSupport_iff {z : ℂ} :
    z ∈ shiftSupport S β ↔ z + ((β : ℝ) : ℂ) ∈ S := by
  rw [shiftSupport, Finset.mem_image]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using hy
  · intro hz
    exact ⟨z + ((β : ℝ) : ℂ), hz, by ring⟩

theorem shiftSupport_card : (shiftSupport S β).card = S.card := by
  rw [shiftSupport]
  refine Finset.card_image_of_injOn (fun x _ y _ hxy => ?_)
  linear_combination hxy

/-- **The shift lemma.**  Translating the exponents multiplies the polynomial by `e^{-β t}`. -/
theorem shift_expCombo (t : ℝ) :
    ∑ z ∈ shiftSupport S β, shiftCoeff C β z * Complex.exp (z * t)
      = Complex.exp (-(((β : ℝ) : ℂ) * t)) * ∑ y ∈ S, C y * Complex.exp (y * t) := by
  rw [shiftSupport, Finset.sum_image (fun x _ y _ hxy => by linear_combination hxy),
    Finset.mul_sum]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  rw [shiftCoeff]
  have hy : y - ((β : ℝ) : ℂ) + ((β : ℝ) : ℂ) = y := by ring
  rw [hy, ← mul_assoc, mul_comm (Complex.exp (-(((β : ℝ) : ℂ) * t))) (C y), mul_assoc,
    ← Complex.exp_add]
  congr 2
  ring

theorem shift_re (t : ℝ) :
    (∑ z ∈ shiftSupport S β, shiftCoeff C β z * Complex.exp (z * t)).re
      = Real.exp (-(β * t)) * (∑ y ∈ S, C y * Complex.exp (y * t)).re := by
  rw [shift_expCombo S C β t]
  have hcast : Complex.exp (-(((β : ℝ) : ℂ) * t)) = ((Real.exp (-(β * t)) : ℝ) : ℂ) := by
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  rw [hcast, Complex.re_ofReal_mul]

theorem shift_im (t : ℝ) :
    (∑ z ∈ shiftSupport S β, shiftCoeff C β z * Complex.exp (z * t)).im
      = Real.exp (-(β * t)) * (∑ y ∈ S, C y * Complex.exp (y * t)).im := by
  rw [shift_expCombo S C β t]
  have hcast : Complex.exp (-(((β : ℝ) : ℂ) * t)) = ((Real.exp (-(β * t)) : ℝ) : ℂ) := by
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  rw [hcast, Complex.im_ofReal_mul]

/-- Real-valuedness is preserved. -/
theorem shift_real (hreal : ∀ t : ℝ, (∑ y ∈ S, C y * Complex.exp (y * t)).im = 0) (t : ℝ) :
    (∑ z ∈ shiftSupport S β, shiftCoeff C β z * Complex.exp (z * t)).im = 0 := by
  rw [shift_im S C β t, hreal t, mul_zero]

/-- The zero set is preserved. -/
theorem shift_zero_iff (t : ℝ) :
    (∑ z ∈ shiftSupport S β, shiftCoeff C β z * Complex.exp (z * t)).re = 0
      ↔ (∑ y ∈ S, C y * Complex.exp (y * t)).re = 0 := by
  rw [shift_re S C β t]
  constructor
  · intro hz
    rcases mul_eq_zero.mp hz with h | h
    · exact absurd h (ne_of_gt (Real.exp_pos _))
    · exact h
  · intro hz
    rw [hz, mul_zero]

/-- Nonzero coefficients are preserved. -/
theorem shift_coeff_ne (hCne : ∀ y ∈ S, C y ≠ 0) :
    ∀ z ∈ shiftSupport S β, shiftCoeff C β z ≠ 0 := by
  intro z hz
  rw [shiftCoeff]
  exact hCne _ ((mem_shiftSupport_iff S β).mp hz)

/-- Imaginary parts are untouched by a real shift. -/
theorem shift_im_eq (z : ℂ) : z.im = (z + ((β : ℝ) : ℂ)).im := by
  simp

/-- A chosen exponent lands on the imaginary axis. -/
theorem shift_target (y₀ : ℂ) :
    y₀ - ((y₀.re : ℝ) : ℂ) = Complex.I * ((y₀.im : ℝ) : ℂ) := by
  refine Complex.ext ?_ ?_ <;> simp

/-! ## A finite set cannot fill an interval -/

theorem not_finset_covers_Icc {a b : ℝ} (hab : a < b) (Z : Finset ℝ)
    (h : ∀ x ∈ Icc a b, x ∈ Z) : False := by
  have hinf : (Icc a b).Infinite := Set.Icc_infinite hab
  have hsub : Icc a b ⊆ (Z : Set ℝ) := fun x hx => h x hx
  exact hinf (Set.Finite.subset Z.finite_toSet hsub)

end GaloisForLFunctions.HTGeometry
