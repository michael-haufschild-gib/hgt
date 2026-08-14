import GaloisForLFunctions.RHTower.FieldOnePadicRamifiedTateFunctionalEquation

/-!
# Arbitrary-test ramified local Tate pairing

The character-packet equation is extended here to every complex test on
`ZMod (p^n)`. The finite theorem is a twisted Fourier pairing: pairing the
DFT of an arbitrary test with a primitive conductor-`p^n` character equals
the inverse-character pairing of the test, multiplied by its Gauss sum.
Exact Haar quadrature then lifts that identity to literal integrals on
`ℤ_p`.

This is the arbitrary-test finite-conductor angular component of
Connes--Marcolli equation (2.258). It is derived from finite Fourier sums,
not assumed as a local functional equation.
-/

namespace GaloisForLFunctions.RHTower

noncomputable section

open MeasureTheory
open scoped BigOperators

variable (p : ℕ) [Fact p.Prime]

/-- Twisted finite Fourier pairing for every test function and every
exact-conductor angular character. -/
theorem fieldOneFinitePrimitiveAngular_dft_pairing
    (n : ℕ) (χ : FieldOnePadicPrimitiveAngularCharacter p n)
    (f : ZMod (p ^ n) → ℂ) :
    ∑ k : ZMod (p ^ n), ZMod.dft f k * χ.1 k =
      gaussSum χ.1 ZMod.stdAddChar *
        ∑ j : ZMod (p ^ n), f j * χ.1⁻¹ (-j) := by
  calc
    _ = ∑ k : ZMod (p ^ n), ∑ j : ZMod (p ^ n),
        (ZMod.stdAddChar (-(j * k)) * f j) * χ.1 k := by
      simp only [ZMod.dft_apply, smul_eq_mul]
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.sum_mul]
    _ = ∑ j : ZMod (p ^ n), ∑ k : ZMod (p ^ n),
        (ZMod.stdAddChar (-(j * k)) * f j) * χ.1 k :=
      Finset.sum_comm
    _ = ∑ j : ZMod (p ^ n), f j * ZMod.dft χ.1 j := by
      apply Finset.sum_congr rfl
      intro j _
      rw [ZMod.dft_apply, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring_nf
    _ = ∑ j : ZMod (p ^ n),
        f j * (χ.1⁻¹ (-j) * gaussSum χ.1 ZMod.stdAddChar) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [χ.2.fourierTransform_eq_inv_mul_gaussSum]
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring_nf

/-- Canonical pullback of an arbitrary finite test to `ℤ_p`. -/
def fieldOnePadicResidueLift (n : ℕ)
    (f : ZMod (p ^ n) → ℂ) : ℤ_[p] → ℂ :=
  fun u => f (PadicInt.toZModPow n u)

theorem continuous_fieldOnePadicResidueLift (n : ℕ)
    (f : ZMod (p ^ n) → ℂ) :
    Continuous (fieldOnePadicResidueLift p n f) := by
  exact (continuous_of_discreteTopology : Continuous f).comp
    (fieldOnePadicInt_toZModPow_continuous p n)

theorem integrable_fieldOnePadicResidueLift (n : ℕ)
    (f : ZMod (p ^ n) → ℂ) :
    Integrable (fieldOnePadicResidueLift p n f)
      (fieldOnePadicIntNormalizedHaar p) := by
  exact (continuous_fieldOnePadicResidueLift p n f).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

theorem fieldOnePadicResidueLift_period (n : ℕ)
    (f : ZMod (p ^ n) → ℂ) (x z : ℤ_[p]) :
    fieldOnePadicResidueLift p n f (x + (p : ℤ_[p]) ^ n * z) =
      fieldOnePadicResidueLift p n f x := by
  unfold fieldOnePadicResidueLift
  congr 1
  rw [map_add, map_mul, map_pow, map_natCast]
  have hp : ((p : ZMod (p ^ n)) ^ n) = 0 := by
    rw [← Nat.cast_pow, ZMod.natCast_self]
  rw [hp, zero_mul, add_zero]

theorem fieldOnePadicResidueLift_integral
    (n : ℕ) (f : ZMod (p ^ n) → ℂ) :
    ∫ u, fieldOnePadicResidueLift p n f u
        ∂fieldOnePadicIntNormalizedHaar p =
      (((p ^ n : ℕ) : ℂ)⁻¹) * ∑ j : ZMod (p ^ n), f j := by
  have hquad := fieldOnePadicInt_cyclicSampleSum_eq_nsmul_integral
    p n (fieldOnePadicResidueLift p n f)
    (integrable_fieldOnePadicResidueLift p n f)
    (fieldOnePadicInt_classInvariant_of_primePowerInvariant p n
      (fieldOnePadicResidueLift p n f)
      (fieldOnePadicResidueLift_period p n f))
  have hsamples :
      (∑ r : ZMod (p ^ n),
        fieldOnePadicResidueLift p n f
          (fieldOnePadicIntResidueRep p n r)) = ∑ r, f r := by
    apply Finset.sum_congr rfl
    intro r _
    unfold fieldOnePadicResidueLift
    rw [fieldOnePadicIntResidueRep_spec]
  rw [hsamples] at hquad
  rw [hquad]
  simp only [nsmul_eq_mul]
  have hN : ((p ^ n : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast pow_ne_zero n (Fact.out : Nat.Prime p).ne_zero
  field_simp

/-- Haar-integral twisted Fourier pairing for every residue-level test.
This is the arbitrary-test finite-conductor local functional equation. -/
theorem fieldOnePadicPrimitiveAngular_haarPairing
    (n : ℕ) (χ : FieldOnePadicPrimitiveAngularCharacter p n)
    (f : ZMod (p ^ n) → ℂ) :
    ∫ u,
        fieldOnePadicIntCyclicFourierIntegral p n
            (fieldOnePadicResidueLift p n f)
            (PadicInt.toZModPow n u) *
          fieldOnePadicPrimitiveAngularLift p n χ u
        ∂fieldOnePadicIntNormalizedHaar p =
      (((p ^ n : ℕ) : ℂ)⁻¹ * gaussSum χ.1 ZMod.stdAddChar) *
        ∫ u,
          fieldOnePadicResidueLift p n f u *
            χ.1⁻¹ (-(PadicInt.toZModPow n u))
          ∂fieldOnePadicIntNormalizedHaar p := by
  let N := p ^ n
  let F : ZMod N → ℂ := fun k =>
    ((N : ℕ) : ℂ)⁻¹ * ZMod.dft f k * χ.1 k
  let G : ZMod N → ℂ := fun j => f j * χ.1⁻¹ (-j)
  have hleft :
      (fun u : ℤ_[p] =>
        fieldOnePadicIntCyclicFourierIntegral p n
            (fieldOnePadicResidueLift p n f)
            (PadicInt.toZModPow n u) *
          fieldOnePadicPrimitiveAngularLift p n χ u) =
        fieldOnePadicResidueLift p n F := by
    funext u
    change fieldOnePadicIntCyclicFourierIntegral p n
        (fieldOnePadicResidueLift p n f)
          (PadicInt.toZModPow n u) *
        χ.1 (PadicInt.toZModPow n u) =
      ((N : ℕ) : ℂ)⁻¹ *
          ZMod.dft f (PadicInt.toZModPow n u) *
        χ.1 (PadicInt.toZModPow n u)
    rw [fieldOnePadicIntCyclicFourierIntegral_eq p n
      (fieldOnePadicResidueLift p n f)
      (integrable_fieldOnePadicResidueLift p n f)
      (fieldOnePadicResidueLift_period p n f)]
    unfold fieldOnePadicIntCyclicFourier
    have hsamples :
        (fun r : ZMod (p ^ n) =>
          fieldOnePadicResidueLift p n f
            (fieldOnePadicIntResidueRep p n r)) = f := by
      funext r
      unfold fieldOnePadicResidueLift
      rw [fieldOnePadicIntResidueRep_spec]
    rw [hsamples]
  have hright :
      (fun u : ℤ_[p] =>
        fieldOnePadicResidueLift p n f u *
          χ.1⁻¹ (-(PadicInt.toZModPow n u))) =
        fieldOnePadicResidueLift p n G := by
    rfl
  rw [hleft, hright,
    fieldOnePadicResidueLift_integral p n F,
    fieldOnePadicResidueLift_integral p n G]
  simp only [F, G, N]
  have hsum :
      (∑ x : ZMod (p ^ n),
        ((p ^ n : ℕ) : ℂ)⁻¹ * ZMod.dft f x * χ.1 x) =
      ((p ^ n : ℕ) : ℂ)⁻¹ *
        ∑ x : ZMod (p ^ n), ZMod.dft f x * χ.1 x := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    ring_nf
  rw [hsum]
  rw [fieldOneFinitePrimitiveAngular_dft_pairing p n χ f]
  ring_nf

end
end GaloisForLFunctions.RHTower
