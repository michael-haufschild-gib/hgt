import GaloisForLFunctions.HeckeLFunctions.HeckeDualClassKernelsHaveExactMellinIntegrals
import GaloisForLFunctions.HeckeLFunctions.HeckeLSeriesAreFiniteSumsOfClassThetaTransforms

/-!
# Arithmetic normalization of the Hecke reflection factors

The trace-dual norm is the reciprocal discriminant, modulus, and base norm.
Its complex power cancels the base weight against the arithmetic Poisson
scalar. Multiplication by the discriminant/conductor completion leaves
the normalized Gauss constant times the real-parity phase. The primitive
Gauss norm proves that this actual root number has absolute value one.
-/

noncomputable section
open NumberField NumberField.InfinitePlace
open scoped Classical nonZeroDivisors
namespace GaloisForLFunctions.HeckeLFunctions
open HTGeometry HTGeometry.IntegerLatticePoisson
variable {K : Type*} [Field K] [NumberField K] (𝔪 : Modulus K)
local notation "FI" => FractionalIdeal (nonZeroDivisors (𝓞 K)) K

/-- Absolute discriminant times the finite modulus norm, giving the primitive conductor scale. -/
def heckeCompletionNorm : ℕ := (NumberField.discr K).natAbs * Ideal.absNorm 𝔪.fin

theorem heckeCompletionNorm_pos : 0 < heckeCompletionNorm 𝔪 := by
  apply Nat.mul_pos
  · exact Int.natAbs_pos.mpr (NumberField.discr_ne_zero K)
  · exact Nat.pos_of_ne_zero (Ideal.absNorm_ne_zero_of_nonZeroDivisors
      ⟨𝔪.fin, mem_nonZeroDivisors_of_ne_zero 𝔪.fin_ne_bot⟩)

/-- The entire discriminant/conductor factor in the completed function. -/
def heckeCompletionFactor (s : ℂ) : ℂ := (heckeCompletionNorm 𝔪 : ℂ) ^ (s / 2)

theorem differentiable_heckeCompletionFactor : Differentiable ℂ (heckeCompletionFactor 𝔪) := by
  have hn : (heckeCompletionNorm 𝔪 : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (heckeCompletionNorm_pos 𝔪).ne'
  exact (differentiable_id.div_const 2).const_cpow (Or.inl hn)

theorem heckeCompletionFactor_ne_zero (s : ℂ) : heckeCompletionFactor 𝔪 s ≠ 0 :=
  Complex.cpow_ne_zero_iff.mpr (Or.inl (Nat.cast_ne_zero.mpr (heckeCompletionNorm_pos 𝔪).ne'))

/-- The arithmetic Gauss constant with the exact archimedean parity phase and unit normalization. -/
def heckeRootNumber (ψ : HeckeCharacter 𝔪) : ℂ :=
  heckeNormalizedGaussConstant 𝔪 ψ * (-Complex.I) ^ parityDegree (heckeCoordinateParity 𝔪 ψ)

/-- The actual primitive root number has absolute value one. -/
theorem norm_heckeRootNumber (ψ : HeckeCharacter 𝔪)
    (hψ : heckeFiniteConductor 𝔪 ψ = 𝔪.fin) : ‖heckeRootNumber 𝔪 ψ‖ = 1 := by
  rw [heckeRootNumber, norm_mul, norm_heckeNormalizedGaussConstant 𝔪 ψ hψ,
    norm_pow, norm_neg, Complex.norm_I, one_pow, one_mul]

/-- The dual fractional norm contributes the positive conductor/discriminant/base complex power. -/
theorem heckeDualMellinFactor_eq_completionNorm (ψ : HeckeCharacter 𝔪)
    {b : Ideal (𝓞 K)} (hb0 : b ≠ ⊥) (s : ℂ) :
    heckeDualMellinFactor 𝔪 hb0 ψ s =
      heckeGaussConstant 𝔪 ψ * heckeValue 𝔪 ψ b *
        ((heckeCompletionNorm 𝔪 : ℂ) ^ s * (Ideal.absNorm b : ℂ) ^ s) := by
  let δ : ℝ := heckeCompletionNorm 𝔪
  let B : ℝ := Ideal.absNorm b
  have hδ : 0 < δ := by
    dsimp only [δ]
    exact_mod_cast heckeCompletionNorm_pos 𝔪
  have hB : 0 < B := by
    dsimp only [B]
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_ne_zero_of_nonZeroDivisors
      ⟨b, mem_nonZeroDivisors_of_ne_zero hb0⟩)
  have hJ : (FractionalIdeal.absNorm (heckeDualIdealUnit 𝔪 hb0 : FI) : ℂ) =
      ((δ : ℂ) * (B : ℂ))⁻¹ := by
    change (FractionalIdeal.absNorm (FractionalIdeal.dual ℤ ℚ
      ((𝔪.fin * b : Ideal (𝓞 K)) : FI)) : ℂ) = _
    rw [absNorm_heckeDualProductIdeal]
    simp only [δ, B, heckeCompletionNorm, Rat.cast_inv, Rat.cast_mul,
      Rat.cast_natCast, Nat.cast_mul, Complex.ofReal_mul, Complex.ofReal_natCast]
  have harg : ((δ : ℂ) * (B : ℂ)).arg ≠ Real.pi := by
    rw [← Complex.ofReal_mul, Complex.arg_ofReal_of_nonneg (mul_pos hδ hB).le]
    exact Real.pi_pos.ne
  rw [heckeDualMellinFactor, hJ, Complex.inv_cpow _ _ harg, Complex.cpow_neg, inv_inv,
    Complex.mul_cpow_ofReal_nonneg hδ.le hB.le]
  simp only [δ, B, Complex.ofReal_natCast]

/-- The arithmetic Poisson scalar retains exactly the finite norm, base norm, and square-root discriminant. -/
theorem heckeThetaMellinScalar_zero_eq (ψ : HeckeCharacter 𝔪) (b : Ideal (𝓞 K)) :
    heckeThetaMellinScalar 𝔪 ψ ((𝔪.fin * b : Ideal (𝓞 K)) : FI) 0 =
      (-Complex.I) ^ parityDegree (heckeCoordinateParity 𝔪 ψ) /
        ((Ideal.absNorm 𝔪.fin : ℂ) * (Ideal.absNorm b : ℂ) *
          (Real.sqrt ((NumberField.discr K).natAbs : ℝ) : ℂ)) := by
  rw [heckeThetaMellinScalar, FractionalIdeal.coeIdeal_absNorm, map_mul]
  simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero, Real.exp_zero,
    Complex.ofReal_one, one_mul, Nat.cast_mul, Rat.cast_mul, Rat.cast_natCast,
    Complex.ofReal_inv, Complex.ofReal_mul, Complex.ofReal_natCast,
    Nat.cast_natAbs, Int.cast_abs]
  ring

/-- Base character and norm cancel exactly in the reflected ordinary-class summand. -/
theorem heckeClassWeight_mul_reflectedDualFactor (ψ : HeckeCharacter 𝔪)
    (c : ClassGroup (𝓞 K)) (s : ℂ) :
    heckeClassWeight 𝔪 ψ c (1 - s) *
      heckeThetaMellinScalar 𝔪 ψ
        ((𝔪.fin * (heckeClassBaseIdeal 𝔪 c : Ideal (𝓞 K)) : Ideal (𝓞 K)) : FI) 0 *
      heckeDualMellinFactor 𝔪 (nonZeroDivisors.coe_ne_zero (heckeClassBaseIdeal 𝔪 c)) ψ s =
        heckeGaussConstant 𝔪 ψ * (-Complex.I) ^ parityDegree (heckeCoordinateParity 𝔪 ψ) *
          (heckeCompletionNorm 𝔪 : ℂ) ^ s /
          ((Ideal.absNorm 𝔪.fin : ℂ) * (Real.sqrt ((NumberField.discr K).natAbs : ℝ) : ℂ)) := by
  let B : ℂ := Ideal.absNorm (heckeClassBaseIdeal 𝔪 c : Ideal (𝓞 K))
  let v : ℂ := heckeValue 𝔪 ψ (heckeClassBaseIdeal 𝔪 c : Ideal (𝓞 K))
  have hB : B ≠ 0 := Nat.cast_ne_zero.mpr (Ideal.absNorm_ne_zero_of_nonZeroDivisors _)
  have hv : v ≠ 0 := heckeClassBaseIdeal_heckeValue_ne_zero 𝔪 ψ c
  have hp : B ^ (1 - s) * B ^ s = B := by
    rw [← Complex.cpow_add _ _ hB, sub_add_cancel, Complex.cpow_one]
  rw [heckeClassWeight, heckeThetaMellinScalar_zero_eq,
    heckeDualMellinFactor_eq_completionNorm]
  calc
    _ = (v⁻¹ * v) * ((B ^ (1 - s) * B ^ s) / B) *
        (heckeGaussConstant 𝔪 ψ * (-Complex.I) ^ parityDegree (heckeCoordinateParity 𝔪 ψ) *
          (heckeCompletionNorm 𝔪 : ℂ) ^ s /
          ((Ideal.absNorm 𝔪.fin : ℂ) * (Real.sqrt ((NumberField.discr K).natAbs : ℝ) : ℂ))) := by
      dsimp only [v, B]
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    _ = _ := by rw [inv_mul_cancel₀ hv, hp, div_self hB, one_mul, one_mul]

/-- The remaining discriminant/conductor scalar is exactly the unit root number after completion. -/
theorem heckeCompletionFactor_mul_reflectionScalar (ψ : HeckeCharacter 𝔪) (s : ℂ) :
    heckeCompletionFactor 𝔪 (1 - s) *
      (heckeGaussConstant 𝔪 ψ * (-Complex.I) ^ parityDegree (heckeCoordinateParity 𝔪 ψ) *
        (heckeCompletionNorm 𝔪 : ℂ) ^ s /
        ((Ideal.absNorm 𝔪.fin : ℂ) * (Real.sqrt ((NumberField.discr K).natAbs : ℝ) : ℂ))) =
      heckeRootNumber 𝔪 ψ * heckeCompletionFactor 𝔪 s := by
  let D : ℝ := (NumberField.discr K).natAbs
  let N : ℝ := Ideal.absNorm 𝔪.fin
  let δ : ℝ := heckeCompletionNorm 𝔪
  have hD : 0 < D := by
    dsimp only [D]
    exact_mod_cast Int.natAbs_pos.mpr (NumberField.discr_ne_zero K)
  have hN : 0 < N := by
    dsimp only [N]
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_ne_zero_of_nonZeroDivisors
      ⟨𝔪.fin, mem_nonZeroDivisors_of_ne_zero 𝔪.fin_ne_bot⟩)
  have hδ : δ = D * N := by simp only [δ, D, N, heckeCompletionNorm, Nat.cast_mul]
  have hδC : (δ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by rw [hδ]; exact (mul_pos hD hN).ne')
  have hsqrt : (δ : ℂ) ^ (1 / 2 : ℂ) = (Real.sqrt δ : ℂ) := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow (by rw [hδ]; positivity)]
    norm_num
  have hp : (δ : ℂ) ^ ((1 - s) / 2) * (δ : ℂ) ^ s =
      (Real.sqrt δ : ℂ) * (δ : ℂ) ^ (s / 2) := by
    rw [← hsqrt, ← Complex.cpow_add _ _ hδC, ← Complex.cpow_add _ _ hδC]
    congr 1
    ring
  have hroot : (Real.sqrt δ : ℂ) /
      ((N : ℂ) * (Real.sqrt D : ℂ)) = (Real.sqrt N : ℂ)⁻¹ := by
    have hsD : (Real.sqrt D : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hD).ne'
    have hsN : (Real.sqrt N : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hN).ne'
    have hnC : (N : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hN.ne'
    have hsquare : (Real.sqrt N : ℂ) ^ 2 = (N : ℂ) := by
      exact_mod_cast Real.sq_sqrt hN.le
    rw [hδ, Real.sqrt_mul hD.le, Complex.ofReal_mul, ← hsquare]
    field_simp
  change (δ : ℂ) ^ ((1 - s) / 2) *
      (heckeGaussConstant 𝔪 ψ * (-Complex.I) ^ parityDegree (heckeCoordinateParity 𝔪 ψ) *
        (δ : ℂ) ^ s / ((N : ℂ) * (Real.sqrt D : ℂ))) =
      (heckeGaussConstant 𝔪 ψ / (Real.sqrt N : ℂ) *
        (-Complex.I) ^ parityDegree (heckeCoordinateParity 𝔪 ψ)) * (δ : ℂ) ^ (s / 2)
  calc
    _ = (heckeGaussConstant 𝔪 ψ * (-Complex.I) ^ parityDegree (heckeCoordinateParity 𝔪 ψ)) *
        (((δ : ℂ) ^ ((1 - s) / 2) * (δ : ℂ) ^ s) /
          ((N : ℂ) * (Real.sqrt D : ℂ))) := by ring
    _ = (heckeGaussConstant 𝔪 ψ * (-Complex.I) ^ parityDegree (heckeCoordinateParity 𝔪 ψ)) *
        (((Real.sqrt δ : ℂ) / ((N : ℂ) * (Real.sqrt D : ℂ))) * (δ : ℂ) ^ (s / 2)) := by
      rw [hp]
      ring
    _ = _ := by rw [hroot]; ring

end GaloisForLFunctions.HeckeLFunctions

#print axioms GaloisForLFunctions.HeckeLFunctions.norm_heckeRootNumber
#print axioms GaloisForLFunctions.HeckeLFunctions.heckeClassWeight_mul_reflectedDualFactor
#print axioms GaloisForLFunctions.HeckeLFunctions.heckeCompletionFactor_mul_reflectionScalar
