import GaloisForLFunctions.HeckeLFunctions.HeckeLSeriesAreFiniteSumsOfClassThetaTransforms
import GaloisForLFunctions.RHTower.AnalyticDividedDifference
import GaloisForLFunctions.HeckeLFunctions.NonquadraticCharactersDoNotVanishOnTheLineReOne
import Mathlib.Analysis.Meromorphic.Order

/-!
# Global meromorphic continuation of finite-order Hecke L-functions

The actual finite sum of class theta transforms splits into an entire regular
part and two explicit zero-mode quotients. The reciprocal Gamma product removes
the pole at zero. Entire divided differences fill both removable quotients,
leaving one constant divided by `s - 1`.

Comparison with the proved ideal-counting continuation identifies that constant:
it vanishes for every nontrivial character and equals the positive Hecke density
for the trivial character. Thus the actual Hecke series extends meromorphically
to the plane, is entire for nontrivial characters, and has a genuine simple pole
at one for the trivial character. The identity theorem identifies this global
function with the older continuation on their common half-plane.
-/

noncomputable section
open NumberField NumberField.InfinitePlace MeasureTheory Filter Topology
open scoped Classical nonZeroDivisors
namespace GaloisForLFunctions.HeckeLFunctions
open HTGeometry HTGeometry.IntegerLatticePoisson
variable {K : Type*} [Field K] [NumberField K] (𝔪 : Modulus K)
local instance : Fintype (ClassGroup (𝓞 K)) := Fintype.ofFinite _

/-- The finite sum of actual entire theta regular parts, with the Hecke normalization removed. -/
def heckeGlobalThetaRegularPart (ψ : HeckeCharacter 𝔪) (s : ℂ) : ℂ :=
  (heckeMellinNormalization (K := K) * ∑ c : ClassGroup (𝓞 K),
    heckeClassWeight 𝔪 ψ c s *
      heckeUnitThetaMellinRegularPart 𝔪 (heckeClassBaseIdeal_coprime 𝔪 c)
        (nonZeroDivisors.coe_ne_zero _) ψ (heckeThetaMellinArgument 𝔪 ψ s)) *
          (heckeGammaFactor 𝔪 ψ s)⁻¹

/-- The entire numerator of the physical zero-mode pole after removing Gamma factors. -/
def heckeGlobalPhysicalNumerator (ψ : HeckeCharacter 𝔪) (s : ℂ) : ℂ :=
  (heckeMellinNormalization (K := K) * ∑ c : ClassGroup (𝓞 K),
    heckeClassWeight 𝔪 ψ c s * ((Units.regulator K : ℂ) * heckeThetaConstant 𝔪 ψ)) *
      (heckeGammaFactor 𝔪 ψ s)⁻¹

/-- The entire numerator of the dual zero-mode pole after removing Gamma factors. -/
def heckeGlobalDualNumerator (ψ : HeckeCharacter 𝔪) (s : ℂ) : ℂ :=
  (heckeMellinNormalization (K := K) * ∑ c : ClassGroup (𝓞 K),
    heckeClassWeight 𝔪 ψ c s *
      (heckeThetaMellinScalar 𝔪 ψ
        ((𝔪.fin * (heckeClassBaseIdeal 𝔪 c : Ideal (𝓞 K)) : Ideal (𝓞 K)) :
          FractionalIdeal (nonZeroDivisors (𝓞 K)) K) 0 *
        ((Units.regulator K : ℂ) * heckeDualThetaConstant 𝔪 ψ))) *
          (heckeGammaFactor 𝔪 ψ s)⁻¹

theorem differentiable_heckeGlobalThetaRegularPart (ψ : HeckeCharacter 𝔪) :
    Differentiable ℂ (heckeGlobalThetaRegularPart 𝔪 ψ) := by
  apply Differentiable.mul _ (differentiable_heckeGammaFactor_inv 𝔪 ψ)
  apply Differentiable.const_mul
  apply Differentiable.fun_sum
  intro c _
  exact (differentiable_heckeClassWeight 𝔪 ψ c).mul
    ((differentiable_heckeUnitThetaMellinRegularPart 𝔪 (heckeClassBaseIdeal_coprime 𝔪 c)
      (nonZeroDivisors.coe_ne_zero _) ψ).comp (differentiable_heckeThetaMellinArgument 𝔪 ψ))

theorem differentiable_heckeGlobalPhysicalNumerator (ψ : HeckeCharacter 𝔪) :
    Differentiable ℂ (heckeGlobalPhysicalNumerator 𝔪 ψ) := by
  apply Differentiable.mul _ (differentiable_heckeGammaFactor_inv 𝔪 ψ)
  apply Differentiable.const_mul
  exact Differentiable.fun_sum fun c _ => (differentiable_heckeClassWeight 𝔪 ψ c).mul_const _

theorem differentiable_heckeGlobalDualNumerator (ψ : HeckeCharacter 𝔪) :
    Differentiable ℂ (heckeGlobalDualNumerator 𝔪 ψ) := by
  apply Differentiable.mul _ (differentiable_heckeGammaFactor_inv 𝔪 ψ)
  apply Differentiable.const_mul
  exact Differentiable.fun_sum fun c _ => (differentiable_heckeClassWeight 𝔪 ψ c).mul_const _

/-- The exact global theta expression has only its two explicit zero-mode pole terms. -/
theorem heckeThetaLContinuation_eq_regular_sub_poles (ψ : HeckeCharacter 𝔪) (s : ℂ) :
    heckeThetaLContinuation 𝔪 ψ s = heckeGlobalThetaRegularPart 𝔪 ψ s -
      heckeGlobalPhysicalNumerator 𝔪 ψ s / heckeThetaMellinArgument 𝔪 ψ s -
      heckeGlobalDualNumerator 𝔪 ψ s /
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
  simp only [heckeThetaLContinuation, heckeCompletedThetaContinuation, hc,
    Finset.sum_sub_distrib, ← Finset.sum_div, heckeGlobalThetaRegularPart,
    heckeGlobalPhysicalNumerator, heckeGlobalDualNumerator]
  ring

/-- At zero parity degree the Gamma product vanishes at zero, so its reciprocal kills the physical pole. -/
theorem heckeGammaFactor_zero_of_degree_eq_zero (ψ : HeckeCharacter 𝔪)
    (hp : parityDegree (heckeCoordinateParity 𝔪 ψ) = 0) : heckeGammaFactor 𝔪 ψ 0 = 0 := by
  have hr : Complex.Gammaℝ 0 = 0 := Complex.Gammaℝ_eq_zero_iff.mpr ⟨0, by norm_num⟩
  have hc : Complex.Gammaℂ 0 = 0 := by
    rw [← Complex.Gammaℝ_mul_Gammaℝ_add_one, hr, zero_mul]
  have hcoords := (parityDegree_eq_zero_iff _).mp hp
  have hn : 0 < nrRealPlaces K + nrComplexPlaces K := by
    rw [← card_eq_nrRealPlaces_add_nrComplexPlaces]
    exact Fintype.card_pos
  simp only [heckeGammaFactor, hcoords, Bool.toNat_false, Nat.cast_zero, add_zero,
    hr, hc, Finset.prod_const, Finset.card_univ]
  change (0 : ℂ) ^ nrRealPlaces K * 0 ^ nrComplexPlaces K = 0
  rw [← pow_add, zero_pow hn.ne']

theorem heckeGlobalPhysicalNumerator_zero (ψ : HeckeCharacter 𝔪)
    (hp : parityDegree (heckeCoordinateParity 𝔪 ψ) = 0) :
    heckeGlobalPhysicalNumerator 𝔪 ψ 0 = 0 := by
  rw [heckeGlobalPhysicalNumerator, heckeGammaFactor_zero_of_degree_eq_zero 𝔪 ψ hp,
    inv_zero, mul_zero]

private theorem differentiable_dslope_entire {f : ℂ → ℂ} (hf : Differentiable ℂ f) (a : ℂ) :
    Differentiable ℂ (dslope f a) := fun z =>
  (RHTower.analyticAt_dslope_of_analyticAt (hf.analyticAt a) (hf.analyticAt z)).differentiableAt

/-- Entire regular part of the actual Hecke L-function, with both removable quotients filled. -/
def heckeEntireRegularPart (ψ : HeckeCharacter 𝔪) (s : ℂ) : ℂ :=
  if parityDegree (heckeCoordinateParity 𝔪 ψ) = 0 then
    heckeGlobalThetaRegularPart 𝔪 ψ s -
      (2 / (Module.finrank ℚ K : ℂ)) * dslope (heckeGlobalPhysicalNumerator 𝔪 ψ) 0 s +
      (2 / (Module.finrank ℚ K : ℂ)) * dslope (heckeGlobalDualNumerator 𝔪 ψ) 1 s
  else heckeGlobalThetaRegularPart 𝔪 ψ s

/-- The sole possible pole coefficient of the actual globally recombined L-function. -/
def heckeThetaPoleCoefficient (ψ : HeckeCharacter 𝔪) : ℂ :=
  if parityDegree (heckeCoordinateParity 𝔪 ψ) = 0 then
    (2 / (Module.finrank ℚ K : ℂ)) * heckeGlobalDualNumerator 𝔪 ψ 1 else 0

theorem differentiable_heckeEntireRegularPart (ψ : HeckeCharacter 𝔪) :
    Differentiable ℂ (heckeEntireRegularPart 𝔪 ψ) := by
  unfold heckeEntireRegularPart
  by_cases hp : parityDegree (heckeCoordinateParity 𝔪 ψ) = 0
  · simp only [if_pos hp]
    exact ((differentiable_heckeGlobalThetaRegularPart 𝔪 ψ).sub
      ((differentiable_dslope_entire (differentiable_heckeGlobalPhysicalNumerator 𝔪 ψ) 0).const_mul _)).add
        ((differentiable_dslope_entire (differentiable_heckeGlobalDualNumerator 𝔪 ψ) 1).const_mul _)
  · simp only [if_neg hp]
    exact differentiable_heckeGlobalThetaRegularPart 𝔪 ψ

/-- Filling the two removable quotients leaves only the explicit simple pole at one. -/
theorem heckeThetaLContinuation_eq_entireRegularPart_add_pole (ψ : HeckeCharacter 𝔪)
    {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    heckeThetaLContinuation 𝔪 ψ s =
      heckeEntireRegularPart 𝔪 ψ s + heckeThetaPoleCoefficient 𝔪 ψ / (s - 1) := by
  rw [heckeThetaLContinuation_eq_regular_sub_poles]
  by_cases hp : parityDegree (heckeCoordinateParity 𝔪 ψ) = 0
  · rw [heckeEntireRegularPart, heckeThetaPoleCoefficient, if_pos hp, if_pos hp,
      dslope_of_ne _ hs0, dslope_of_ne _ hs1, slope_def_field, slope_def_field,
      heckeGlobalPhysicalNumerator_zero 𝔪 ψ hp, sub_zero, sub_zero]
    have hn : (Module.finrank ℚ K : ℂ) ≠ 0 := by
      have hpos : 0 < (Module.finrank ℚ K : ℝ) := by
        rw [← numberFieldInfinitePlaceWeight_eq_finrank]
        exact numberFieldInfinitePlaceWeight_pos
      exact_mod_cast hpos.ne'
    simp only [heckeThetaMellinArgument, heckeThetaMellinWeight, hp, Nat.cast_zero, add_zero,
      Complex.ofReal_div, Complex.ofReal_natCast, Complex.ofReal_ofNat]
    field_simp
    ring
  · have hz : heckeGlobalPhysicalNumerator 𝔪 ψ s = 0 := by
      simp only [heckeGlobalPhysicalNumerator, heckeThetaConstant, hp, and_false,
        if_false, mul_zero, Finset.sum_const_zero, zero_mul]
    have hk : heckeGlobalDualNumerator 𝔪 ψ s = 0 := by
      simp only [heckeGlobalDualNumerator, heckeDualThetaConstant, hp, false_and,
        if_false, mul_zero, Finset.sum_const_zero, zero_mul]
    simp only [heckeEntireRegularPart, heckeThetaPoleCoefficient, hp, if_false,
      hz, hk, zero_div, sub_zero, add_zero]

/-- On its original half-plane the Hecke series is an entire function plus one simple pole. -/
theorem heckeL_eq_entireRegularPart_add_pole (ψ : HeckeCharacter 𝔪)
    {s : ℂ} (hs : 1 < s.re) :
    heckeL 𝔪 ψ s = heckeEntireRegularPart 𝔪 ψ s + heckeThetaPoleCoefficient 𝔪 ψ / (s - 1) := by
  have hs0 : s ≠ 0 := by intro h; simp only [h, Complex.zero_re] at hs; linarith
  have hs1 : s ≠ 1 := by intro h; simp only [h, Complex.one_re, lt_self_iff_false] at hs
  rw [← heckeThetaLContinuation_eq 𝔪 ψ hs]
  exact heckeThetaLContinuation_eq_entireRegularPart_add_pole 𝔪 ψ hs0 hs1

/-- The residue of the actual theta continuation is read on the original real half-line. -/
theorem tendsto_sub_one_mul_heckeL_thetaCoefficient (ψ : HeckeCharacter 𝔪) :
    Tendsto (fun σ : ℝ => ((σ : ℂ) - 1) * heckeL 𝔪 ψ σ)
      (𝓝[>] 1) (𝓝 (heckeThetaPoleCoefficient 𝔪 ψ)) := by
  have hc : Tendsto (fun σ : ℝ => (σ : ℂ)) (𝓝[>] (1 : ℝ)) (𝓝 (1 : ℂ)) := by
    simpa only [Complex.ofReal_one] using
      (Complex.continuous_ofReal.continuousAt (x := (1 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds
  have hreg := (differentiable_heckeEntireRegularPart 𝔪 ψ).continuous.continuousAt.tendsto.comp hc
  have hlim := ((hc.sub_const 1).mul hreg).add_const (heckeThetaPoleCoefficient 𝔪 ψ)
  simp only [sub_self, zero_mul, zero_add] at hlim
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with σ hσ
  have hσ1 : (σ : ℂ) - 1 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast (show 1 < σ from hσ).ne')
  simp only [Function.comp_apply]
  rw [heckeL_eq_entireRegularPart_add_pole 𝔪 ψ (by simpa using hσ)]
  field_simp

/-- Existing near-one holomorphy forces the global theta pole coefficient to vanish. -/
theorem heckeThetaPoleCoefficient_eq_zero {ψ : HeckeCharacter 𝔪} (hψ : ψ ≠ 1) :
    heckeThetaPoleCoefficient 𝔪 ψ = 0 := by
  have hc : Tendsto (fun σ : ℝ => (σ : ℂ)) (𝓝[>] (1 : ℝ)) (𝓝 (1 : ℂ)) := by
    simpa only [Complex.ofReal_one] using
      (Complex.continuous_ofReal.continuousAt (x := (1 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds
  have hcont := (differentiableAt_heckeLCont_one hψ).continuousAt.tendsto.comp hc
  have hlim := (hc.sub_const 1).mul hcont
  simp only [sub_self, zero_mul] at hlim
  have hzero : Tendsto (fun σ : ℝ => ((σ : ℂ) - 1) * heckeL 𝔪 ψ σ)
      (𝓝[>] 1) (𝓝 0) := by
    apply hlim.congr'
    filter_upwards [self_mem_nhdsWithin] with σ hσ
    simp only [Function.comp_apply]
    rw [heckeLCont_eq_heckeL hψ (by simpa using hσ)]
  exact tendsto_nhds_unique (tendsto_sub_one_mul_heckeL_thetaCoefficient 𝔪 ψ) hzero

/-- The trivial-character pole agrees exactly with the previously proved positive residue. -/
theorem heckeThetaPoleCoefficient_one : heckeThetaPoleCoefficient 𝔪 1 = heckeDensity 𝔪 :=
  tendsto_nhds_unique (tendsto_sub_one_mul_heckeL_thetaCoefficient 𝔪 1)
    (tendsto_sub_one_mul_heckeL_one (𝔪 := 𝔪))

/-- Every nontrivial finite-order ray class character has an entire Hecke L-function. -/
theorem heckeEntireRegularPart_eq_heckeL {ψ : HeckeCharacter 𝔪} (hψ : ψ ≠ 1)
    {s : ℂ} (hs : 1 < s.re) : heckeEntireRegularPart 𝔪 ψ s = heckeL 𝔪 ψ s := by
  rw [heckeL_eq_entireRegularPart_add_pole 𝔪 ψ hs,
    heckeThetaPoleCoefficient_eq_zero 𝔪 hψ, zero_div, add_zero]

/-- The trivial Hecke L-function has an entire regular part and its explicit simple pole. -/
theorem heckeL_one_eq_entireRegularPart_add_pole {s : ℂ} (hs : 1 < s.re) :
    heckeL 𝔪 1 s = heckeEntireRegularPart 𝔪 1 s + (heckeDensity 𝔪 : ℂ) / (s - 1) := by
  rw [heckeL_eq_entireRegularPart_add_pole 𝔪 1 hs, heckeThetaPoleCoefficient_one]

/-- The global Hecke L-function, with the entire regular part supplying removable values. -/
def heckeLFunction (ψ : HeckeCharacter 𝔪) (s : ℂ) : ℂ :=
  heckeEntireRegularPart 𝔪 ψ s + heckeThetaPoleCoefficient 𝔪 ψ / (s - 1)

/-- Global continuation agrees with the actual absolutely convergent ideal series. -/
theorem heckeLFunction_eq_heckeL (ψ : HeckeCharacter 𝔪) {s : ℂ} (hs : 1 < s.re) :
    heckeLFunction 𝔪 ψ s = heckeL 𝔪 ψ s :=
  (heckeL_eq_entireRegularPart_add_pole 𝔪 ψ hs).symm

/-- Every finite-order Hecke L-function is meromorphic on the whole complex plane. -/
theorem meromorphic_heckeLFunction (ψ : HeckeCharacter 𝔪) :
    Meromorphic (heckeLFunction 𝔪 ψ) := by
  intro s
  exact ((differentiable_heckeEntireRegularPart 𝔪 ψ).analyticAt s).meromorphicAt.add
    ((MeromorphicAt.const _ s).div ((MeromorphicAt.id s).sub (MeromorphicAt.const 1 s)))

/-- A nontrivial finite-order Hecke L-function is entire. -/
theorem differentiable_heckeLFunction {ψ : HeckeCharacter 𝔪} (hψ : ψ ≠ 1) :
    Differentiable ℂ (heckeLFunction 𝔪 ψ) := by
  unfold heckeLFunction
  simp only [heckeThetaPoleCoefficient_eq_zero 𝔪 hψ, zero_div, add_zero]
  exact differentiable_heckeEntireRegularPart 𝔪 ψ

/-- The only possible pole of a finite-order Hecke L-function is at one. -/
theorem differentiableAt_heckeLFunction (ψ : HeckeCharacter 𝔪) {s : ℂ} (hs : s ≠ 1) :
    DifferentiableAt ℂ (heckeLFunction 𝔪 ψ) s :=
  (differentiable_heckeEntireRegularPart 𝔪 ψ s).add
    ((differentiableAt_const (heckeThetaPoleCoefficient 𝔪 ψ)).div
      (differentiableAt_id.sub_const 1) (sub_ne_zero.mpr hs))

/-- The global trivial-character function has exactly the previously normalized polar term. -/
theorem heckeLFunction_one (s : ℂ) :
    heckeLFunction 𝔪 1 s = heckeEntireRegularPart 𝔪 1 s + (heckeDensity 𝔪 : ℂ) / (s - 1) := by
  rw [heckeLFunction, heckeThetaPoleCoefficient_one]

/-- The complex residue limit agrees with the explicit theta pole coefficient. -/
theorem tendsto_sub_one_mul_heckeLFunction (ψ : HeckeCharacter 𝔪) :
    Tendsto (fun s : ℂ => (s - 1) * heckeLFunction 𝔪 ψ s)
      (𝓝[≠] 1) (𝓝 (heckeThetaPoleCoefficient 𝔪 ψ)) := by
  have hreg := (differentiable_heckeEntireRegularPart 𝔪 ψ).continuous.continuousAt
    (x := (1 : ℂ))
  have ht := ((tendsto_id.sub_const (1 : ℂ)).mul hreg.tendsto).add_const
    (heckeThetaPoleCoefficient 𝔪 ψ)
  simp only [sub_self, zero_mul, zero_add] at ht
  apply (ht.mono_left nhdsWithin_le_nhds).congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hn : s - 1 ≠ 0 := sub_ne_zero.mpr hs
  simp only [id_eq]
  rw [heckeLFunction]
  field_simp

/-- The trivial character has a genuine simple pole at one. -/
theorem meromorphicOrderAt_heckeLFunction_one :
    meromorphicOrderAt (heckeLFunction 𝔪 1) 1 = (-1 : ℤ) := by
  apply (meromorphicOrderAt_eq_int_iff (meromorphic_heckeLFunction 𝔪 1 1)).mpr
  refine ⟨fun s : ℂ => (s - 1) * heckeEntireRegularPart 𝔪 1 s + (heckeDensity 𝔪 : ℂ),
    ?_, ?_, ?_⟩
  · exact ((analyticAt_id.sub analyticAt_const).mul
      ((differentiable_heckeEntireRegularPart 𝔪 1).analyticAt 1)).add analyticAt_const
  · simp only [sub_self, zero_mul, zero_add]
    exact_mod_cast (heckeDensity_pos 𝔪).ne'
  · filter_upwards [self_mem_nhdsWithin] with s hs
    have hn : s - 1 ≠ 0 := sub_ne_zero.mpr hs
    rw [heckeLFunction_one]
    simp only [smul_eq_mul, zpow_neg, zpow_one]
    field_simp

/-- The global continuation and the ideal-counting continuation agree on their shared half-plane. -/
theorem heckeLFunction_eq_heckeLCont {ψ : HeckeCharacter 𝔪} (hψ : ψ ≠ 1)
    {s : ℂ} (hs : 1 - (Module.finrank ℚ K : ℝ)⁻¹ < s.re) :
    heckeLFunction 𝔪 ψ s = heckeLCont 𝔪 ψ s := by
  let U : Set ℂ := {z | 1 - (Module.finrank ℚ K : ℝ)⁻¹ < z.re}
  have hu : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hcv : Convex ℝ U :=
    convex_halfSpace_gt ⟨fun _ _ => rfl, fun a z => by simp⟩ _
  have h2 : (2 : ℂ) ∈ U := by
    change 1 - (Module.finrank ℚ K : ℝ)⁻¹ < (2 : ℝ)
    linarith [errExp_lt_one (K := K)]
  have ha : AnalyticOnNhd ℂ (heckeLFunction 𝔪 ψ) U :=
    fun z _ => (differentiable_heckeLFunction 𝔪 hψ).analyticAt z
  have hb : AnalyticOnNhd ℂ (heckeLCont 𝔪 ψ) U :=
    (differentiableOn_heckeLCont hψ).analyticOnNhd hu
  have he : heckeLFunction 𝔪 ψ =ᶠ[𝓝 (2 : ℂ)] heckeLCont 𝔪 ψ := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (show (2 : ℂ) ∈ {z : ℂ | 1 < z.re} by norm_num)] with z hz
    exact (heckeLFunction_eq_heckeL 𝔪 ψ hz).trans (heckeLCont_eq_heckeL hψ hz).symm
  exact ha.eqOn_of_preconnected_of_eventuallyEq hb hcv.isPreconnected h2 he hs

/-- The global continuation inherits nonquadratic nonvanishing on the closed right half-plane. -/
theorem heckeLFunction_ne_zero_of_sq_ne_one {ψ : HeckeCharacter 𝔪}
    (hψ2 : ψ ^ 2 ≠ 1) {s : ℂ} (hs : 1 ≤ s.re) : heckeLFunction 𝔪 ψ s ≠ 0 := by
  have hψ : ψ ≠ 1 := fun h => hψ2 (by rw [h]; ext g; simp)
  rw [heckeLFunction_eq_heckeLCont 𝔪 hψ ((errExp_lt_one (K := K)).trans_le hs)]
  exact heckeLCont_ne_zero_of_sq_ne_one hψ2 hs

end GaloisForLFunctions.HeckeLFunctions
