import GaloisForLFunctions.HeckeLFunctions.HeckeCompletedThetaResiduesCancel

/-!
# Gamma-completed Hecke functions with their removable values

The actual class-theta expression splits into an entire term and two
zero-mode quotients. Divided differences replace their varying numerators
by entire functions and constant residues. This constructs a meromorphic
Gamma completion that is entire for every nontrivial character, including
the values at zero and one. Analytic uniqueness recovers the ordinary
L-function after multiplication by reciprocal Gamma.
-/

noncomputable section
open NumberField MeasureTheory Filter Topology
open scoped Classical nonZeroDivisors
namespace GaloisForLFunctions.HeckeLFunctions
open HTGeometry HTGeometry.IntegerLatticePoisson
variable {K : Type*} [Field K] [NumberField K] (𝔪 : Modulus K)
local instance : Fintype (ClassGroup (𝓞 K)) := Fintype.ofFinite _

/-- The finite sum of entire class-theta regular parts before removing Gamma factors. -/
def heckeCompletedThetaRegularPart (ψ : HeckeCharacter 𝔪) (s : ℂ) : ℂ :=
  heckeMellinNormalization (K := K) * ∑ c : ClassGroup (𝓞 K),
    heckeClassWeight 𝔪 ψ c s *
      heckeUnitThetaMellinRegularPart 𝔪 (heckeClassBaseIdeal_coprime 𝔪 c)
        (nonZeroDivisors.coe_ne_zero _) ψ (heckeThetaMellinArgument 𝔪 ψ s)

theorem differentiable_heckeCompletedThetaRegularPart (ψ : HeckeCharacter 𝔪) :
    Differentiable ℂ (heckeCompletedThetaRegularPart 𝔪 ψ) := by
  apply Differentiable.const_mul
  apply Differentiable.fun_sum
  intro c _
  exact (differentiable_heckeClassWeight 𝔪 ψ c).mul
    ((differentiable_heckeUnitThetaMellinRegularPart 𝔪 (heckeClassBaseIdeal_coprime 𝔪 c)
      (nonZeroDivisors.coe_ne_zero _) ψ).comp (differentiable_heckeThetaMellinArgument 𝔪 ψ))

/-- The raw Gamma-completed theta sum has precisely its two actual zero-mode quotients. -/
theorem heckeCompletedThetaContinuation_eq_regular_sub_poles (ψ : HeckeCharacter 𝔪) (s : ℂ) :
    heckeCompletedThetaContinuation 𝔪 ψ s = heckeCompletedThetaRegularPart 𝔪 ψ s -
      heckeCompletedPhysicalNumerator 𝔪 ψ s / heckeThetaMellinArgument 𝔪 ψ s -
      heckeCompletedDualNumerator 𝔪 ψ s /
        ((heckeThetaMellinWeight 𝔪 ψ : ℂ) - heckeThetaMellinArgument 𝔪 ψ s) := by
  have hc (c : ClassGroup (𝓞 K)) :
      heckeClassWeight 𝔪 ψ c s *
        heckeUnitThetaMellinContinuation 𝔪 (heckeClassBaseIdeal_coprime 𝔪 c)
          (nonZeroDivisors.coe_ne_zero _) ψ (heckeThetaMellinArgument 𝔪 ψ s) =
      heckeClassWeight 𝔪 ψ c s *
        heckeUnitThetaMellinRegularPart 𝔪 (heckeClassBaseIdeal_coprime 𝔪 c)
          (nonZeroDivisors.coe_ne_zero _) ψ (heckeThetaMellinArgument 𝔪 ψ s) -
      (heckeClassWeight 𝔪 ψ c s * ((Units.regulator K : ℂ) * heckeThetaConstant 𝔪 ψ)) /
        heckeThetaMellinArgument 𝔪 ψ s -
      (heckeClassWeight 𝔪 ψ c s * (heckeThetaMellinScalar 𝔪 ψ
        ((𝔪.fin * (heckeClassBaseIdeal 𝔪 c : Ideal (𝓞 K)) : Ideal (𝓞 K)) :
          FractionalIdeal (nonZeroDivisors (𝓞 K)) K) 0 *
          ((Units.regulator K : ℂ) * heckeDualThetaConstant 𝔪 ψ))) /
        ((heckeThetaMellinWeight 𝔪 ψ : ℂ) - heckeThetaMellinArgument 𝔪 ψ s) := by
    rw [heckeUnitThetaMellinContinuation, WeakFEPair.Λ]
    change _ * (heckeUnitThetaMellinRegularPart 𝔪 (heckeClassBaseIdeal_coprime 𝔪 c)
      (nonZeroDivisors.coe_ne_zero _) ψ (heckeThetaMellinArgument 𝔪 ψ s) -
      (1 / heckeThetaMellinArgument 𝔪 ψ s) •
        (Units.regulator K • heckeThetaConstant 𝔪 ψ) -
      (heckeThetaMellinScalar 𝔪 ψ
        ((𝔪.fin * (heckeClassBaseIdeal 𝔪 c : Ideal (𝓞 K)) : Ideal (𝓞 K)) :
          FractionalIdeal (nonZeroDivisors (𝓞 K)) K) 0 /
        ((heckeThetaMellinWeight 𝔪 ψ : ℂ) - heckeThetaMellinArgument 𝔪 ψ s)) •
          (Units.regulator K • heckeDualThetaConstant 𝔪 ψ)) = _
    simp only [Complex.real_smul, smul_eq_mul]
    ring
  simp only [heckeCompletedThetaContinuation, hc, Finset.sum_sub_distrib,
    ← Finset.sum_div, heckeCompletedThetaRegularPart,
    heckeCompletedPhysicalNumerator, heckeCompletedDualNumerator]
  ring

private theorem completed_dslope_differentiable {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (a : ℂ) : Differentiable ℂ (dslope f a) := fun z =>
  (RHTower.analyticAt_dslope_of_analyticAt (hf.analyticAt a) (hf.analyticAt z)).differentiableAt

/-- Entire regular part of the Gamma-completed function, including both divided-difference values. -/
def heckeGammaCompletedRegularPart (ψ : HeckeCharacter 𝔪) (s : ℂ) : ℂ :=
  if parityDegree (heckeCoordinateParity 𝔪 ψ) = 0 then
    heckeCompletedThetaRegularPart 𝔪 ψ s -
      (2 / (Module.finrank ℚ K : ℂ)) * dslope (heckeCompletedPhysicalNumerator 𝔪 ψ) 0 s +
      (2 / (Module.finrank ℚ K : ℂ)) * dslope (heckeCompletedDualNumerator 𝔪 ψ) 1 s
  else heckeCompletedThetaRegularPart 𝔪 ψ s

/-- The actual constant coefficient of the possible completed pole at zero. -/
def heckeGammaCompletedZeroCoefficient (ψ : HeckeCharacter 𝔪) : ℂ :=
  if parityDegree (heckeCoordinateParity 𝔪 ψ) = 0 then
    -(2 / (Module.finrank ℚ K : ℂ)) * heckeCompletedPhysicalNumerator 𝔪 ψ 0 else 0

/-- The actual constant coefficient of the possible completed pole at one. -/
def heckeGammaCompletedOneCoefficient (ψ : HeckeCharacter 𝔪) : ℂ :=
  if parityDegree (heckeCoordinateParity 𝔪 ψ) = 0 then
    (2 / (Module.finrank ℚ K : ℂ)) * heckeCompletedDualNumerator 𝔪 ψ 1 else 0

/-- Gamma-completed continuation with removable values supplied by entire divided differences. -/
def heckeGammaCompletedLFunction (ψ : HeckeCharacter 𝔪) (s : ℂ) : ℂ :=
  heckeGammaCompletedRegularPart 𝔪 ψ s +
    heckeGammaCompletedZeroCoefficient 𝔪 ψ / s +
    heckeGammaCompletedOneCoefficient 𝔪 ψ / (s - 1)

theorem differentiable_heckeGammaCompletedRegularPart (ψ : HeckeCharacter 𝔪) :
    Differentiable ℂ (heckeGammaCompletedRegularPart 𝔪 ψ) := by
  unfold heckeGammaCompletedRegularPart
  by_cases hp : parityDegree (heckeCoordinateParity 𝔪 ψ) = 0
  · simp only [if_pos hp]
    exact ((differentiable_heckeCompletedThetaRegularPart 𝔪 ψ).sub
      ((completed_dslope_differentiable
        (differentiable_heckeCompletedPhysicalNumerator 𝔪 ψ) 0).const_mul _)).add
      ((completed_dslope_differentiable
        (differentiable_heckeCompletedDualNumerator 𝔪 ψ) 1).const_mul _)
  · simp only [if_neg hp]
    exact differentiable_heckeCompletedThetaRegularPart 𝔪 ψ

/-- Away from zero and one, the corrected completion is exactly the actual class-theta expression. -/
theorem heckeGammaCompletedLFunction_eq_theta (ψ : HeckeCharacter 𝔪)
    {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    heckeGammaCompletedLFunction 𝔪 ψ s = heckeCompletedThetaContinuation 𝔪 ψ s := by
  rw [heckeCompletedThetaContinuation_eq_regular_sub_poles]
  by_cases hp : parityDegree (heckeCoordinateParity 𝔪 ψ) = 0
  · rw [heckeGammaCompletedLFunction, heckeGammaCompletedRegularPart,
      heckeGammaCompletedZeroCoefficient, heckeGammaCompletedOneCoefficient,
      if_pos hp, if_pos hp, if_pos hp,
      dslope_of_ne _ hs0, dslope_of_ne _ hs1, slope_def_field, slope_def_field, sub_zero]
    have hn : (Module.finrank ℚ K : ℂ) ≠ 0 := by
      exact_mod_cast (Module.finrank_pos (R := ℚ) (M := K)).ne'
    simp only [heckeThetaMellinArgument, heckeThetaMellinWeight, hp, Nat.cast_zero, add_zero,
      Complex.ofReal_div, Complex.ofReal_natCast, Complex.ofReal_ofNat]
    field_simp
    ring
  · have hz : heckeCompletedPhysicalNumerator 𝔪 ψ s = 0 := by
      simp only [heckeCompletedPhysicalNumerator, heckeThetaConstant, hp, and_false,
        if_false, mul_zero, Finset.sum_const_zero]
    have hk : heckeCompletedDualNumerator 𝔪 ψ s = 0 := by
      simp only [heckeCompletedDualNumerator, heckeDualThetaConstant, hp, false_and,
        if_false, mul_zero, Finset.sum_const_zero]
    simp only [heckeGammaCompletedLFunction, heckeGammaCompletedRegularPart,
      heckeGammaCompletedZeroCoefficient, heckeGammaCompletedOneCoefficient,
      hp, if_false, hz, hk, zero_div, sub_zero, add_zero]

/-- On the initial half-plane, the corrected function is the standard Gamma product times the ideal series. -/
theorem heckeGammaCompletedLFunction_eq (ψ : HeckeCharacter 𝔪)
    {s : ℂ} (hs : 1 < s.re) :
    heckeGammaCompletedLFunction 𝔪 ψ s = heckeGammaFactor 𝔪 ψ s * heckeL 𝔪 ψ s := by
  have hs0 : s ≠ 0 := by intro h; simp only [h, Complex.zero_re] at hs; linarith
  have hs1 : s ≠ 1 := by intro h; simp only [h, Complex.one_re, lt_self_iff_false] at hs
  rw [heckeGammaCompletedLFunction_eq_theta 𝔪 ψ hs0 hs1, heckeCompletedThetaContinuation_eq 𝔪 ψ hs]

/-- The Gamma-completed function is meromorphic on the whole plane with at most two simple poles. -/
theorem meromorphic_heckeGammaCompletedLFunction (ψ : HeckeCharacter 𝔪) :
    Meromorphic (heckeGammaCompletedLFunction 𝔪 ψ) := by
  intro s
  exact (((differentiable_heckeGammaCompletedRegularPart 𝔪 ψ).analyticAt s).meromorphicAt.add
    ((MeromorphicAt.const _ s).div (MeromorphicAt.id s))).add
      ((MeromorphicAt.const _ s).div ((MeromorphicAt.id s).sub (MeromorphicAt.const 1 s)))

/-- The completed physical residue vanishes for every nontrivial character. -/
theorem heckeGammaCompletedZeroCoefficient_eq_zero {ψ : HeckeCharacter 𝔪} (hψ : ψ ≠ 1) :
    heckeGammaCompletedZeroCoefficient 𝔪 ψ = 0 := by
  simp only [heckeGammaCompletedZeroCoefficient,
    heckeCompletedPhysicalNumerator_zero 𝔪 hψ, mul_zero, ite_self]

/-- The completed dual residue vanishes for every nontrivial character. -/
theorem heckeGammaCompletedOneCoefficient_eq_zero {ψ : HeckeCharacter 𝔪} (hψ : ψ ≠ 1) :
    heckeGammaCompletedOneCoefficient 𝔪 ψ = 0 := by
  simp only [heckeGammaCompletedOneCoefficient,
    heckeCompletedDualNumerator_one 𝔪 hψ, mul_zero, ite_self]

/-- Every nontrivial finite-order Hecke character has an entire Gamma-completed L-function. -/
theorem differentiable_heckeGammaCompletedLFunction {ψ : HeckeCharacter 𝔪} (hψ : ψ ≠ 1) :
    Differentiable ℂ (heckeGammaCompletedLFunction 𝔪 ψ) := by
  unfold heckeGammaCompletedLFunction
  simp only [heckeGammaCompletedZeroCoefficient_eq_zero 𝔪 hψ,
    heckeGammaCompletedOneCoefficient_eq_zero 𝔪 hψ, zero_div, add_zero]
  exact differentiable_heckeGammaCompletedRegularPart 𝔪 ψ

/-- The pole at one is the ordinary L-function residue multiplied by its nonvanishing Gamma factor. -/
theorem heckeGammaCompletedOneCoefficient_eq_pole_mul_gamma (ψ : HeckeCharacter 𝔪) :
    heckeGammaCompletedOneCoefficient 𝔪 ψ =
      heckeThetaPoleCoefficient 𝔪 ψ * heckeGammaFactor 𝔪 ψ 1 := by
  by_cases hp : parityDegree (heckeCoordinateParity 𝔪 ψ) = 0
  · rw [heckeGammaCompletedOneCoefficient, heckeThetaPoleCoefficient, if_pos hp, if_pos hp,
      heckeGlobalDualNumerator_eq_completed]
    rw [mul_assoc, mul_assoc,
      inv_mul_cancel₀ (heckeGammaFactor_ne_zero 𝔪 ψ (by norm_num : 0 < (1 : ℂ).re)), mul_one]
  · simp only [heckeGammaCompletedOneCoefficient, heckeThetaPoleCoefficient, hp, if_false, zero_mul]

/-- The completed trivial character retains the exact positive ordinary residue at one. -/
theorem heckeGammaCompletedOneCoefficient_one :
    heckeGammaCompletedOneCoefficient 𝔪 1 =
      (heckeDensity 𝔪 : ℂ) * heckeGammaFactor 𝔪 1 1 := by
  rw [heckeGammaCompletedOneCoefficient_eq_pole_mul_gamma, heckeThetaPoleCoefficient_one]

/-- Reciprocal Gamma recovers the entire ordinary function, including its removable values. -/
theorem heckeGammaCompletedLFunction_mul_gamma_inv {ψ : HeckeCharacter 𝔪}
    (hψ : ψ ≠ 1) (s : ℂ) :
    heckeGammaCompletedLFunction 𝔪 ψ s * (heckeGammaFactor 𝔪 ψ s)⁻¹ =
      heckeLFunction 𝔪 ψ s := by
  have hf : AnalyticOnNhd ℂ (fun z => heckeGammaCompletedLFunction 𝔪 ψ z *
      (heckeGammaFactor 𝔪 ψ z)⁻¹) Set.univ := fun z _ =>
    ((differentiable_heckeGammaCompletedLFunction 𝔪 hψ).mul
      (differentiable_heckeGammaFactor_inv 𝔪 ψ)).analyticAt z
  have hg : AnalyticOnNhd ℂ (heckeLFunction 𝔪 ψ) Set.univ := fun z _ =>
    (differentiable_heckeLFunction 𝔪 hψ).analyticAt z
  have he : (fun z => heckeGammaCompletedLFunction 𝔪 ψ z * (heckeGammaFactor 𝔪 ψ z)⁻¹)
      =ᶠ[𝓝 (2 : ℂ)] heckeLFunction 𝔪 ψ := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (show (2 : ℂ) ∈ {z : ℂ | 1 < z.re} by norm_num)] with z hz
    rw [heckeGammaCompletedLFunction_eq 𝔪 ψ hz, heckeLFunction_eq_heckeL 𝔪 ψ hz,
      mul_right_comm, mul_inv_cancel₀ (heckeGammaFactor_ne_zero 𝔪 ψ (zero_lt_one.trans hz)), one_mul]
  exact hf.eqOn_of_preconnected_of_eventuallyEq hg isPreconnected_univ (Set.mem_univ _) he
    (Set.mem_univ s)

end GaloisForLFunctions.HeckeLFunctions

#print axioms GaloisForLFunctions.HeckeLFunctions.differentiable_heckeGammaCompletedLFunction
#print axioms GaloisForLFunctions.HeckeLFunctions.heckeGammaCompletedLFunction_mul_gamma_inv
