import GaloisForLFunctions.HeckeLFunctions.HeckeDualAveragedMellinIsTheInverseClassSeries
import GaloisForLFunctions.HeckeLFunctions.HeckeCompletionFactorsHaveExactArithmeticNormalization
import GaloisForLFunctions.HeckeLFunctions.HeckeGammaCompletedFunctionsHaveRemovableValues

/-!
# The primitive completed Hecke functional equation

The conductor/codifferent permutation identifies all dual ideal classes
with the inverse-character series. Exact unit-averaged Mellin identities
and arithmetic scalar cancellation give reflection on the convergent
dual half-plane. Analytic uniqueness extends the pole-cleared equation
to the whole plane. Nontrivial characters have an entire completion,
so their equation includes both removable points.
-/

noncomputable section
open NumberField Filter Topology
open scoped Classical nonZeroDivisors
namespace GaloisForLFunctions.HeckeLFunctions
open HTGeometry
variable {K : Type*} [Field K] [NumberField K] (𝔪 : Modulus K)
local instance : Fintype (ClassGroup (𝓞 K)) := Fintype.ofFinite _

/-- The dual class series is the inverse-character class series at the exact different/conductor permutation. -/
theorem heckeDualClassL_eq_permuted_inverseClassL (ψ : HeckeCharacter 𝔪)
    (c : ClassGroup (𝓞 K)) (s : ℂ) :
    heckeDualClassL 𝔪 (nonZeroDivisors.coe_ne_zero (heckeClassBaseIdeal 𝔪 c)) ψ s =
      heckeInverseClassL 𝔪 ψ⁻¹ (heckeClassBaseIdeal 𝔪 (heckeDualClassPermutation 𝔪 c)) s := by
  let e : heckeDualClassIdeals 𝔪 (nonZeroDivisors.coe_ne_zero (heckeClassBaseIdeal 𝔪 c)) ≃
      inverseClassIntegralIdeals (heckeClassBaseIdeal 𝔪 (heckeDualClassPermutation 𝔪 c)) :=
    Equiv.subtypeEquivRight (fun I => by
      rw [heckeDualIdealUnit_class_inv, heckeClassBaseIdeal_class,
        heckeClassBaseIdeal_class, inv_inv, heckeDualClassPermutation_apply])
  exact e.tsum_eq
    (fun I : inverseClassIntegralIdeals
      (heckeClassBaseIdeal 𝔪 (heckeDualClassPermutation 𝔪 c)) => heckeIdealTerm 𝔪 ψ⁻¹ s I.1)

/-- All actual dual classes partition the inverse-character Hecke series, with no missing class. -/
theorem heckeL_inverse_eq_sum_dualClassL (ψ : HeckeCharacter 𝔪)
    {s : ℂ} (hs : 1 < s.re) :
    heckeL 𝔪 ψ⁻¹ s = ∑ c : ClassGroup (𝓞 K),
      heckeDualClassL 𝔪 (nonZeroDivisors.coe_ne_zero (heckeClassBaseIdeal 𝔪 c)) ψ s := by
  rw [heckeL_eq_sum_inverseClassL 𝔪 ψ⁻¹ hs]
  simp_rw [heckeDualClassL_eq_permuted_inverseClassL]
  exact (Fintype.sum_equiv (heckeDualClassPermutation 𝔪)
    (fun c => heckeInverseClassL 𝔪 ψ⁻¹
      (heckeClassBaseIdeal 𝔪 (heckeDualClassPermutation 𝔪 c)) s)
    (fun c => heckeInverseClassL 𝔪 ψ⁻¹ (heckeClassBaseIdeal 𝔪 c) s)
    (fun _ => rfl)).symm

/-- Finite class recombination gives the actual reflected completed theta on the initial dual half-plane. -/
theorem heckeCompletedThetaContinuation_one_sub (ψ : HeckeCharacter 𝔪)
    (hψ : heckeFiniteConductor 𝔪 ψ = 𝔪.fin) {s : ℂ} (hs : 1 < s.re) :
    heckeCompletedThetaContinuation 𝔪 ψ (1 - s) =
      (heckeGaussConstant 𝔪 ψ * (-Complex.I) ^
        HTGeometry.IntegerLatticePoisson.parityDegree (heckeCoordinateParity 𝔪 ψ) *
        (heckeCompletionNorm 𝔪 : ℂ) ^ s /
        ((Ideal.absNorm 𝔪.fin : ℂ) * (Real.sqrt ((NumberField.discr K).natAbs : ℝ) : ℂ))) *
      heckeGammaFactor 𝔪 ψ⁻¹ s * heckeL 𝔪 ψ⁻¹ s := by
  have hn : (Module.finrank ℚ K : ℂ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := ℚ) (M := K)).ne'
  have hw : (Units.torsionOrder K : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Units.torsionOrder_pos (K := K)).ne'
  rw [heckeCompletedThetaContinuation, heckeL_inverse_eq_sum_dualClassL 𝔪 ψ hs,
    Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c _
  rw [heckeUnitThetaMellinContinuation_reflection,
    heckeUnitThetaMellinPair_symm_eq_dualClassL 𝔪 (heckeClassBaseIdeal_coprime 𝔪 c)
      (nonZeroDivisors.coe_ne_zero _) ψ hψ hs]
  calc
    _ = (heckeClassWeight 𝔪 ψ c (1 - s) *
        heckeThetaMellinScalar 𝔪 ψ
          ((𝔪.fin * (heckeClassBaseIdeal 𝔪 c : Ideal (𝓞 K)) : Ideal (𝓞 K)) :
            FractionalIdeal (nonZeroDivisors (𝓞 K)) K) 0 *
        heckeDualMellinFactor 𝔪 (nonZeroDivisors.coe_ne_zero (heckeClassBaseIdeal 𝔪 c)) ψ s) *
        heckeGammaFactor 𝔪 ψ⁻¹ s *
        heckeDualClassL 𝔪 (nonZeroDivisors.coe_ne_zero (heckeClassBaseIdeal 𝔪 c)) ψ s := by
      rw [heckeMellinNormalization]
      field_simp
    _ = _ := by rw [heckeClassWeight_mul_reflectedDualFactor]

/-- The standard primitive discriminant/conductor completion, with all removable values filled. -/
def heckeCompletedLFunction (ψ : HeckeCharacter 𝔪) (s : ℂ) : ℂ :=
  heckeCompletionFactor 𝔪 s * heckeGammaCompletedLFunction 𝔪 ψ s

/-- The completion agrees with the conventional Gamma/discriminant/conductor product on `Re s > 1`. -/
theorem heckeCompletedLFunction_eq (ψ : HeckeCharacter 𝔪) {s : ℂ} (hs : 1 < s.re) :
    heckeCompletedLFunction 𝔪 ψ s =
      heckeCompletionFactor 𝔪 s * heckeGammaFactor 𝔪 ψ s * heckeL 𝔪 ψ s := by
  rw [heckeCompletedLFunction, heckeGammaCompletedLFunction_eq 𝔪 ψ hs, mul_assoc]

theorem meromorphic_heckeCompletedLFunction (ψ : HeckeCharacter 𝔪) :
    Meromorphic (heckeCompletedLFunction 𝔪 ψ) := fun s =>
  ((differentiable_heckeCompletionFactor 𝔪).analyticAt s).meromorphicAt.mul
    (meromorphic_heckeGammaCompletedLFunction 𝔪 ψ s)

/-- Every nontrivial finite-order character has an entire completed function. -/
theorem differentiable_heckeCompletedLFunction {ψ : HeckeCharacter 𝔪} (hψ : ψ ≠ 1) :
    Differentiable ℂ (heckeCompletedLFunction 𝔪 ψ) :=
  (differentiable_heckeCompletionFactor 𝔪).mul (differentiable_heckeGammaCompletedLFunction 𝔪 hψ)

/-- The actual arithmetic root number gives reflection on the convergent dual half-plane. -/
theorem heckeCompletedLFunction_reflection_right (ψ : HeckeCharacter 𝔪)
    (hψ : heckeFiniteConductor 𝔪 ψ = 𝔪.fin) {s : ℂ} (hs : 1 < s.re) :
    heckeCompletedLFunction 𝔪 ψ (1 - s) = heckeRootNumber 𝔪 ψ * heckeCompletedLFunction 𝔪 ψ⁻¹ s := by
  have hs0 : s ≠ 0 := by intro h; simp only [h, Complex.zero_re] at hs; linarith
  have hs1 : s ≠ 1 := by intro h; simp only [h, Complex.one_re, lt_self_iff_false] at hs
  have hl0 : 1 - s ≠ 0 := sub_ne_zero.mpr hs1.symm
  have hl1 : 1 - s ≠ 1 := by
    intro h
    apply hs0
    linear_combination -h
  rw [heckeCompletedLFunction, heckeGammaCompletedLFunction_eq_theta 𝔪 ψ hl0 hl1,
    heckeCompletedThetaContinuation_one_sub 𝔪 ψ hψ hs,
    heckeCompletedLFunction_eq 𝔪 ψ⁻¹ hs, ← mul_assoc, ← mul_assoc,
    heckeCompletionFactor_mul_reflectionScalar]
  ring

/-- Multiply the two explicit poles before totalization, retaining their analytic values at zero and one. -/
def heckePoleClearedCompletion (ψ : HeckeCharacter 𝔪) (s : ℂ) : ℂ :=
  heckeCompletionFactor 𝔪 s *
    (s * (s - 1) * heckeGammaCompletedRegularPart 𝔪 ψ s +
      (s - 1) * heckeGammaCompletedZeroCoefficient 𝔪 ψ +
      s * heckeGammaCompletedOneCoefficient 𝔪 ψ)

/-- The pole-cleared completed function is entire for every finite-order character. -/
theorem differentiable_heckePoleClearedCompletion (ψ : HeckeCharacter 𝔪) :
    Differentiable ℂ (heckePoleClearedCompletion 𝔪 ψ) := by
  apply (differentiable_heckeCompletionFactor 𝔪).mul
  exact (((differentiable_id.mul (differentiable_id.sub_const 1)).mul
    (differentiable_heckeGammaCompletedRegularPart 𝔪 ψ)).add
      ((differentiable_id.sub_const 1).mul_const _)).add (differentiable_id.mul_const _)

/-- Away from the poles, clearing the poles is ordinary multiplication by `s(s-1)`. -/
theorem heckePoleClearedCompletion_eq (ψ : HeckeCharacter 𝔪)
    {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    heckePoleClearedCompletion 𝔪 ψ s = s * (s - 1) * heckeCompletedLFunction 𝔪 ψ s := by
  rw [heckePoleClearedCompletion, heckeCompletedLFunction, heckeGammaCompletedLFunction]
  have hn : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  field_simp

private theorem entire_reflection_of_right_halfPlane {F G : ℂ → ℂ}
    (hF : Differentiable ℂ F) (hG : Differentiable ℂ G) (w : ℂ)
    (he : ∀ s : ℂ, 1 < s.re → F (1 - s) = w * G s) (s : ℂ) :
    F (1 - s) = w * G s := by
  have hf : AnalyticOnNhd ℂ (fun z => F (1 - z)) Set.univ := fun z _ =>
    (hF.comp ((differentiable_const (1 : ℂ)).sub differentiable_id)).analyticAt z
  have hg : AnalyticOnNhd ℂ (fun z => w * G z) Set.univ := fun z _ =>
    (hG.const_mul w).analyticAt z
  have hloc : (fun z => F (1 - z)) =ᶠ[𝓝 (2 : ℂ)] fun z => w * G z := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (show (2 : ℂ) ∈ {z : ℂ | 1 < z.re} by norm_num)] with z hz
    exact he z hz
  exact hf.eqOn_of_preconnected_of_eventuallyEq hg isPreconnected_univ (Set.mem_univ _) hloc
    (Set.mem_univ s)

/-- The primitive completed functional equation holds everywhere after clearing both actual poles. -/
theorem heckePoleClearedCompletion_reflection (ψ : HeckeCharacter 𝔪)
    (hψ : heckeFiniteConductor 𝔪 ψ = 𝔪.fin) (s : ℂ) :
    heckePoleClearedCompletion 𝔪 ψ (1 - s) =
      heckeRootNumber 𝔪 ψ * heckePoleClearedCompletion 𝔪 ψ⁻¹ s := by
  apply entire_reflection_of_right_halfPlane
    (differentiable_heckePoleClearedCompletion 𝔪 ψ)
    (differentiable_heckePoleClearedCompletion 𝔪 ψ⁻¹) (heckeRootNumber 𝔪 ψ) _ s
  intro z hz
  have hz0 : z ≠ 0 := by intro h; simp only [h, Complex.zero_re] at hz; linarith
  have hz1 : z ≠ 1 := by intro h; simp only [h, Complex.one_re, lt_self_iff_false] at hz
  have hl0 : 1 - z ≠ 0 := sub_ne_zero.mpr hz1.symm
  have hl1 : 1 - z ≠ 1 := by intro h; apply hz0; linear_combination -h
  rw [heckePoleClearedCompletion_eq 𝔪 ψ hl0 hl1,
    heckePoleClearedCompletion_eq 𝔪 ψ⁻¹ hz0 hz1,
    heckeCompletedLFunction_reflection_right 𝔪 ψ hψ hz]
  ring

/-- The primitive completed functional equation holds at every point away from its two possible poles. -/
theorem heckeCompletedLFunction_reflection (ψ : HeckeCharacter 𝔪)
    (hψ : heckeFiniteConductor 𝔪 ψ = 𝔪.fin) {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    heckeCompletedLFunction 𝔪 ψ (1 - s) = heckeRootNumber 𝔪 ψ * heckeCompletedLFunction 𝔪 ψ⁻¹ s := by
  have h := heckePoleClearedCompletion_reflection 𝔪 ψ hψ s
  have hl0 : 1 - s ≠ 0 := sub_ne_zero.mpr hs1.symm
  have hl1 : 1 - s ≠ 1 := by intro h; apply hs0; linear_combination -h
  rw [heckePoleClearedCompletion_eq 𝔪 ψ hl0 hl1,
    heckePoleClearedCompletion_eq 𝔪 ψ⁻¹ hs0 hs1] at h
  have hprod : (1 - s) * (1 - s - 1) = s * (s - 1) := by ring
  rw [hprod, mul_left_comm (heckeRootNumber 𝔪 ψ)] at h
  exact mul_left_cancel₀ (mul_ne_zero hs0 (sub_ne_zero.mpr hs1)) h

/-- For nontrivial primitive characters, the completed equation includes both removable points. -/
theorem heckeCompletedLFunction_reflection_entire {ψ : HeckeCharacter 𝔪}
    (hψ : heckeFiniteConductor 𝔪 ψ = 𝔪.fin) (hψ1 : ψ ≠ 1) (s : ℂ) :
    heckeCompletedLFunction 𝔪 ψ (1 - s) = heckeRootNumber 𝔪 ψ * heckeCompletedLFunction 𝔪 ψ⁻¹ s := by
  have hi : ψ⁻¹ ≠ 1 := by
    intro h
    apply hψ1
    apply MonoidHom.ext
    intro g
    have hg := DFunLike.congr_fun h g
    change (ψ g)⁻¹ = 1 at hg
    change ψ g = 1
    exact inv_eq_one.mp hg
  exact entire_reflection_of_right_halfPlane
    (differentiable_heckeCompletedLFunction 𝔪 hψ1)
    (differentiable_heckeCompletedLFunction 𝔪 hi) (heckeRootNumber 𝔪 ψ)
    (fun z hz => heckeCompletedLFunction_reflection_right 𝔪 ψ hψ hz) s

end GaloisForLFunctions.HeckeLFunctions

#print axioms GaloisForLFunctions.HeckeLFunctions.heckeCompletedThetaContinuation_one_sub
#print axioms GaloisForLFunctions.HeckeLFunctions.heckePoleClearedCompletion_reflection
#print axioms GaloisForLFunctions.HeckeLFunctions.heckeCompletedLFunction_reflection_entire
