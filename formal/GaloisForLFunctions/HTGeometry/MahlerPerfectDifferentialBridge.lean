import GaloisForLFunctions.HTGeometry.MahlerCommutingDerivation

/-!
# The base of the Mahler model is a differential subfield

The two-variable perfect base `F(h)` carries the derivation that differentiates the coefficients
by the Euler operator of `F` and divides by the twisting coordinate.  It is the restriction of the
commuting derivation of the ambient field, so the base is a differential subfield for the
derivation that commutes with the substitution.
-/

namespace GaloisForLFunctions.HTGeometry

open HahnSeries

open scoped RatFunc

noncomputable section

variable {k : Type*} [Field k]

theorem coeff_mahlerPEmbed_algebraMap (p : ℕ) (hp : 1 < p)
    (P : Polynomial (perfectBase (k := k) p hp)) (n : ℤ) :
    (mahlerPEmbed k p hp
        (algebraMap (Polynomial (perfectBase (k := k) p hp)) (MahlerPBase k p hp) P)).coeff n
      = if n < 0 then 0 else ((P.coeff n.natAbs : perfectBase (k := k) p hp) : HahnSeries ℚ k) := by
  rw [mahlerPEmbed, RingHom.coe_comp, Function.comp_apply, coeff_hahnMapRingHom,
    coeff_algebraMap_polynomial]
  by_cases h : n < 0
  · simp [h]
  · simp [h]

/-- The coefficient derivation of the base is the restriction of the ambient Euler derivation, on
polynomials in the twisting coordinate. -/
theorem mahlerPEmbed_twoCylDerivation_algebraMap [CharZero k] (p : ℕ) (hp : 1 < p)
    (P : Polynomial (perfectBase (k := k) p hp)) :
    letI := perfectDifferential (k := k) p hp
    mahlerPEmbed k p hp (twoCylDerivation (0 : perfectBase (k := k) p hp)
        (algebraMap (Polynomial (perfectBase (k := k) p hp)) (MahlerPBase k p hp) P))
      = mahlerAmbientDeriv (mahlerPEmbed k p hp
        (algebraMap (Polynomial (perfectBase (k := k) p hp)) (MahlerPBase k p hp) P)) := by
  letI := perfectDifferential (k := k) p hp
  rw [twoCylDerivation_algebraMap]
  simp only [map_zero, zero_mul, add_zero]
  refine HahnSeries.coeff_inj.mp (funext fun n => ?_)
  rw [coeff_mahlerPEmbed_algebraMap, coeff_mahlerAmbientDeriv, coeff_mahlerPEmbed_algebraMap]
  by_cases h : n < 0
  · simp [h]
  · rw [if_neg h, if_neg h, coeffDeriv_coeff, perfectDifferential_deriv, perfectBaseDeriv_coe]

set_option synthInstance.maxHeartbeats 400000 in
/-- **The coefficient derivation of the base is the restriction of the ambient Euler
derivation.** -/
theorem mahlerPEmbed_twoCylDerivation [CharZero k] (p : ℕ) (hp : 1 < p)
    (x : MahlerPBase k p hp) :
    letI := perfectDifferential (k := k) p hp
    mahlerPEmbed k p hp (twoCylDerivation (0 : perfectBase (k := k) p hp) x)
      = mahlerAmbientDeriv (mahlerPEmbed k p hp x) := by
  letI := perfectDifferential (k := k) p hp
  refine RatFunc.induction_on (P := fun x =>
    mahlerPEmbed k p hp (twoCylDerivation (0 : perfectBase (k := k) p hp) x)
      = mahlerAmbientDeriv (mahlerPEmbed k p hp x)) x ?_
  intro P Q hQ
  have hQne : algebraMap (Polynomial (perfectBase (k := k) p hp)) (MahlerPBase k p hp) Q ≠ 0 := by
    simpa using RatFunc.algebraMap_ne_zero hQ
  have hFq : (algebraMap (Polynomial (perfectBase (k := k) p hp)) (MahlerPBase k p hp) P /
      algebraMap (Polynomial (perfectBase (k := k) p hp)) (MahlerPBase k p hp) Q)
      * algebraMap (Polynomial (perfectBase (k := k) p hp)) (MahlerPBase k p hp) Q
      = algebraMap (Polynomial (perfectBase (k := k) p hp)) (MahlerPBase k p hp) P :=
    div_mul_cancel₀ _ hQne
  set F : MahlerPBase k p hp :=
    algebraMap (Polynomial (perfectBase (k := k) p hp)) (MahlerPBase k p hp) P /
      algebraMap (Polynomial (perfectBase (k := k) p hp)) (MahlerPBase k p hp) Q with hFdef
  have h1 := congrArg (mahlerPEmbed k p hp)
    (twoCylDerivation_leibniz (0 : perfectBase (k := k) p hp) F
      (algebraMap (Polynomial (perfectBase (k := k) p hp)) (MahlerPBase k p hp) Q))
  rw [hFq] at h1
  simp only [map_add, map_mul] at h1
  rw [mahlerPEmbed_twoCylDerivation_algebraMap, mahlerPEmbed_twoCylDerivation_algebraMap] at h1
  have h2 := mahlerAmbientDeriv_leibniz (mahlerPEmbed k p hp F)
    (mahlerPEmbed k p hp
      (algebraMap (Polynomial (perfectBase (k := k) p hp)) (MahlerPBase k p hp) Q))
  rw [← map_mul, hFq] at h2
  have hemb : mahlerPEmbed k p hp
      (algebraMap (Polynomial (perfectBase (k := k) p hp)) (MahlerPBase k p hp) Q) ≠ 0 := by
    intro h
    exact hQne ((injective_iff_map_eq_zero (mahlerPEmbed k p hp)).mp
      (mahlerPEmbed k p hp).injective _ h)
  refine mul_left_cancel₀ hemb ?_
  linear_combination h2 - h1

/-! ## The twisting coordinate through the embedding -/

theorem mahlerPEmbed_X (p : ℕ) (hp : 1 < p) :
    mahlerPEmbed k p hp (RatFunc.X : MahlerPBase k p hp) = mahlerCoord k := by
  rw [mahlerPEmbed, RingHom.coe_comp, Function.comp_apply, algebraMap_ratFuncX]
  refine HahnSeries.coeff_inj.mp (funext fun n => ?_)
  rw [coeff_hahnMapRingHom, laurentCoord, mahlerCoord]
  by_cases h : n = 1
  · subst h
    rw [HahnSeries.coeff_single_same, HahnSeries.coeff_single_same, map_one]
  · rw [HahnSeries.coeff_single_of_ne h, HahnSeries.coeff_single_of_ne h, map_zero]

theorem mahlerCoord_inv_eq (k : Type*) [Field k] :
    (mahlerCoord k)⁻¹ = mahlerCoordInv k :=
  inv_eq_of_mul_eq_one_right mahlerCoord_mul_coordInv

theorem mahlerPEmbed_X_inv (p : ℕ) (hp : 1 < p) :
    mahlerPEmbed k p hp ((RatFunc.X : MahlerPBase k p hp)⁻¹) = mahlerCoordInv k := by
  rw [map_inv₀, mahlerPEmbed_X, mahlerCoord_inv_eq]

/-- The differential structure of the two-variable perfect base for the commuting derivation. -/
@[reducible] def mahlerPBaseDifferential [CharZero k] (p : ℕ) (hp : 1 < p) :
    Differential (MahlerPBase k p hp) := by
  letI := perfectDifferential (k := k) p hp
  exact ⟨((RatFunc.X : MahlerPBase k p hp)⁻¹) •
    (twoCylinderDifferential (0 : perfectBase (k := k) p hp)).deriv⟩

theorem mahlerPBaseDifferential_deriv [CharZero k] (p : ℕ) (hp : 1 < p)
    (x : MahlerPBase k p hp) :
    letI := perfectDifferential (k := k) p hp
    (mahlerPBaseDifferential p hp).deriv x
      = (RatFunc.X : MahlerPBase k p hp)⁻¹ * twoCylDerivation (0 : perfectBase (k := k) p hp) x :=
  rfl

/-- **The base is a differential subfield for the commuting derivation.** -/
theorem mahlerPEmbed_mahlerPBaseDeriv [CharZero k] (p : ℕ) (hp : 1 < p)
    (x : MahlerPBase k p hp) :
    mahlerPEmbed k p hp ((mahlerPBaseDifferential p hp).deriv x)
      = mahlerCommDeriv (mahlerPEmbed k p hp x) := by
  rw [mahlerPBaseDifferential_deriv, map_mul, mahlerPEmbed_X_inv, mahlerPEmbed_twoCylDerivation,
    mahlerCommDeriv_apply]

end

end GaloisForLFunctions.HTGeometry
