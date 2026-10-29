import GaloisForLFunctions.HeckeLFunctions.HeckeLFunctionsHaveGlobalContinuation

/-!
# Cancellation of the completed Hecke theta residues

The physical zero-mode sum at zero is an ordinary-class character sum.
Actual descent identifies every inverse-class base weight, so orthogonality
cancels it for nontrivial characters. The dual zero-mode sum at one vanishes
because the ordinary L-function has zero residue and its Gamma factor is
nonzero there. Both arguments apply before reciprocal Gamma removal.
-/

noncomputable section
open NumberField
open scoped Classical nonZeroDivisors
namespace GaloisForLFunctions.HeckeLFunctions
open HTGeometry HTGeometry.IntegerLatticePoisson
variable {K : Type*} [Field K] [NumberField K] (𝔪 : Modulus K)
local instance : Fintype (ClassGroup (𝓞 K)) := Fintype.ofFinite _

/-- The physical zero-mode numerator before reciprocal Gamma factors are introduced. -/
def heckeCompletedPhysicalNumerator (ψ : HeckeCharacter 𝔪) (s : ℂ) : ℂ :=
  heckeMellinNormalization (K := K) * ∑ c : ClassGroup (𝓞 K),
    heckeClassWeight 𝔪 ψ c s * ((Units.regulator K : ℂ) * heckeThetaConstant 𝔪 ψ)

/-- The dual zero-mode numerator before reciprocal Gamma factors are introduced. -/
def heckeCompletedDualNumerator (ψ : HeckeCharacter 𝔪) (s : ℂ) : ℂ :=
  heckeMellinNormalization (K := K) * ∑ c : ClassGroup (𝓞 K),
    heckeClassWeight 𝔪 ψ c s *
      (heckeThetaMellinScalar 𝔪 ψ
        ((𝔪.fin * (heckeClassBaseIdeal 𝔪 c : Ideal (𝓞 K)) : Ideal (𝓞 K)) :
          FractionalIdeal (nonZeroDivisors (𝓞 K)) K) 0 *
        ((Units.regulator K : ℂ) * heckeDualThetaConstant 𝔪 ψ))

theorem differentiable_heckeCompletedPhysicalNumerator (ψ : HeckeCharacter 𝔪) :
    Differentiable ℂ (heckeCompletedPhysicalNumerator 𝔪 ψ) := by
  apply Differentiable.const_mul
  exact Differentiable.fun_sum fun c _ => (differentiable_heckeClassWeight 𝔪 ψ c).mul_const _

theorem differentiable_heckeCompletedDualNumerator (ψ : HeckeCharacter 𝔪) :
    Differentiable ℂ (heckeCompletedDualNumerator 𝔪 ψ) := by
  apply Differentiable.const_mul
  exact Differentiable.fun_sum fun c _ => (differentiable_heckeClassWeight 𝔪 ψ c).mul_const _

/-- Descended characters evaluate each chosen inverse-class base ideal in its actual ordinary class. -/
theorem heckeClassBaseIdeal_value_of_descent (ψ : HeckeCharacter 𝔪)
    (φ : ClassGroup (𝓞 K) →* ℂˣ) (hφ : φ.comp (toClassGroup 𝔪) = ψ)
    (c : ClassGroup (𝓞 K)) :
    heckeValue 𝔪 ψ (heckeClassBaseIdeal 𝔪 c : Ideal (𝓞 K)) = (φ (c⁻¹) : ℂ) := by
  rw [heckeValue_of_mem 𝔪 ψ (nonZeroDivisors.coe_ne_zero _)
    ((idealUnit_mem_idealGroup_iff 𝔪 _).mpr (heckeClassBaseIdeal_coprime 𝔪 c)),
    ← hφ, MonoidHom.comp_apply, toClassGroup_rayClass]
  have hu : idealUnit (nonZeroDivisors.coe_ne_zero (heckeClassBaseIdeal 𝔪 c)) =
      FractionalIdeal.mk0 K (heckeClassBaseIdeal 𝔪 c) := by
    apply Units.ext
    rfl
  change (φ (ClassGroup.mk K (idealUnit
    (nonZeroDivisors.coe_ne_zero (heckeClassBaseIdeal 𝔪 c)))) : ℂ) = _
  rw [hu, ClassGroup.mk_mk0, heckeClassBaseIdeal_class]

/-- At zero, each inverse base weight is the descended ordinary-class character itself. -/
theorem heckeClassWeight_zero_of_descent (ψ : HeckeCharacter 𝔪)
    (φ : ClassGroup (𝓞 K) →* ℂˣ) (hφ : φ.comp (toClassGroup 𝔪) = ψ)
    (c : ClassGroup (𝓞 K)) : heckeClassWeight 𝔪 ψ c 0 = (φ c : ℂ) := by
  rw [heckeClassWeight, Complex.cpow_zero, mul_one,
    heckeClassBaseIdeal_value_of_descent 𝔪 ψ φ hφ c, map_inv,
    Units.val_inv_eq_inv_val, inv_inv]

/-- Ordinary-class orthogonality cancels the physical completed residue for every nontrivial character. -/
theorem heckeCompletedPhysicalNumerator_zero {ψ : HeckeCharacter 𝔪} (hψ : ψ ≠ 1) :
    heckeCompletedPhysicalNumerator 𝔪 ψ 0 = 0 := by
  by_cases hp : parityDegree (heckeCoordinateParity 𝔪 ψ) = 0
  · by_cases hf : finiteHeckeWeight 𝔪 ψ = 1
    · obtain ⟨φ, hφ⟩ := exists_classCharacter_of_finiteParity_trivial 𝔪 ψ hf hp
      simp only [heckeCompletedPhysicalNumerator,
        heckeClassWeight_zero_of_descent 𝔪 ψ φ hφ, ← Finset.sum_mul,
        sum_classCharacter_eq_zero_of_comp 𝔪 ψ hψ φ hφ, zero_mul, mul_zero]
    · have hm : 𝔪.fin ≠ ⊤ := fun h => hf (finiteHeckeWeight_eq_one_of_fin_eq_top 𝔪 ψ h)
      simp only [heckeCompletedPhysicalNumerator, heckeThetaConstant, hm, false_and,
        if_false, mul_zero, Finset.sum_const_zero]
  · simp only [heckeCompletedPhysicalNumerator, heckeThetaConstant, hp, and_false,
      if_false, mul_zero, Finset.sum_const_zero]

/-- Reciprocal Gamma removal relates the ordinary and raw completed dual numerators exactly. -/
theorem heckeGlobalDualNumerator_eq_completed (ψ : HeckeCharacter 𝔪) (s : ℂ) :
    heckeGlobalDualNumerator 𝔪 ψ s =
      heckeCompletedDualNumerator 𝔪 ψ s * (heckeGammaFactor 𝔪 ψ s)⁻¹ := rfl

/-- Holomorphy of the ordinary Hecke L-function at one cancels the raw completed dual residue. -/
theorem heckeCompletedDualNumerator_one {ψ : HeckeCharacter 𝔪} (hψ : ψ ≠ 1) :
    heckeCompletedDualNumerator 𝔪 ψ 1 = 0 := by
  by_cases hp : parityDegree (heckeCoordinateParity 𝔪 ψ) = 0
  · have h := heckeThetaPoleCoefficient_eq_zero 𝔪 hψ
    rw [heckeThetaPoleCoefficient, if_pos hp] at h
    have hn : (Module.finrank ℚ K : ℂ) ≠ 0 := by
      exact_mod_cast (Module.finrank_pos (R := ℚ) (M := K)).ne'
    have hc : (2 / (Module.finrank ℚ K : ℂ)) ≠ 0 := div_ne_zero (by norm_num) hn
    have hglobal := (mul_eq_zero.mp h).resolve_left hc
    rw [heckeGlobalDualNumerator_eq_completed] at hglobal
    exact (mul_eq_zero.mp hglobal).resolve_right
      (inv_ne_zero (heckeGammaFactor_ne_zero 𝔪 ψ (by norm_num : 0 < (1 : ℂ).re)))
  · simp only [heckeCompletedDualNumerator, heckeDualThetaConstant, hp, false_and,
      if_false, mul_zero, Finset.sum_const_zero]

end GaloisForLFunctions.HeckeLFunctions

#print axioms GaloisForLFunctions.HeckeLFunctions.heckeCompletedPhysicalNumerator_zero
#print axioms GaloisForLFunctions.HeckeLFunctions.heckeCompletedDualNumerator_one
