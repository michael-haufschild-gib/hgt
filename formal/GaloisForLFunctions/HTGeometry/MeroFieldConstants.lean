import GaloisForLFunctions.HTGeometry.MeromorphicTranslationFixedField
import GaloisForLFunctions.HTGeometry.MeromorphicRealizationDerivative

/-!
# The constants of the meromorphic field of the plane

An element of the meromorphic function field of `ℂ` whose derivative vanishes is a complex constant.
Writing the element as a quotient of two entire germs and differentiating the cleared identity gives
a vanishing Wronskian for the two representatives, and a quotient of entire functions with vanishing
Wronskian is constant.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher Filter Topology
open scoped Differential

noncomputable section

attribute [local instance] relativeGaugeDomain relativeGaugeDifferential
  relativeGaugeRatFuncAlgebra relativeGaugeRatFuncDifferential relativeGaugeDifferentialAlgebra
  relativeGaugeCharZeroBase relativeGaugeCharZero relativeGaugeComplexAlgebra
  relativeGaugeComplexAlgebraAnalytic

/-- **The constants of the meromorphic field of the plane are the complex numbers.** -/
theorem exists_complex_of_deriv_eq_zero {x : meroField (Set.univ : Set ℂ)} (hx : x′ = 0) :
    ∃ c : ℂ, algebraMap ℂ (meroField (Set.univ : Set ℂ)) c = x := by
  classical
  obtain ⟨a, b, hbnz, hx'⟩ :=
    IsFractionRing.div_surjective (A := analyticSubring (Set.univ : Set ℂ))
      (K := meroField (Set.univ : Set ℂ)) x
  have hb : b ≠ 0 := nonZeroDivisors.ne_zero hbnz
  have hB : algebraMap (analyticSubring (Set.univ : Set ℂ)) (meroField (Set.univ : Set ℂ)) b ≠ 0 := by
    intro hzero
    exact hb (IsFractionRing.injective (analyticSubring (Set.univ : Set ℂ))
      (meroField (Set.univ : Set ℂ)) (by simpa using hzero))
  -- clear the denominator and differentiate
  have hxB : x * algebraMap (analyticSubring (Set.univ : Set ℂ)) (meroField (Set.univ : Set ℂ)) b
      = algebraMap (analyticSubring (Set.univ : Set ℂ)) (meroField (Set.univ : Set ℂ)) a := by
    rw [← hx']
    field_simp
  have hd := congrArg (fun t : meroField (Set.univ : Set ℂ) => t′) hxB
  simp only [differential_deriv_mul, hx, zero_mul, zero_add] at hd
  rw [meroFieldDifferential_algebraMap isOpen_univ isPreconnected_univ Set.univ_nonempty,
    meroFieldDifferential_algebraMap isOpen_univ isPreconnected_univ Set.univ_nonempty] at hd
  -- cross-multiply back to the germ ring
  have hcross : algebraMap (analyticSubring (Set.univ : Set ℂ)) (meroField (Set.univ : Set ℂ))
        (a * analyticSubringDeriv isOpen_univ b)
      = algebraMap (analyticSubring (Set.univ : Set ℂ)) (meroField (Set.univ : Set ℂ))
        (analyticSubringDeriv isOpen_univ a * b) := by
    rw [map_mul, map_mul, ← hxB]
    linear_combination (algebraMap (analyticSubring (Set.univ : Set ℂ))
      (meroField (Set.univ : Set ℂ)) b) * hd
  have hring : a * analyticSubringDeriv isOpen_univ b = analyticSubringDeriv isOpen_univ a * b :=
    IsFractionRing.injective (analyticSubring (Set.univ : Set ℂ))
      (meroField (Set.univ : Set ℂ)) hcross
  -- read the identity on representatives
  obtain ⟨f, hf, hfa⟩ := a.2
  obtain ⟨g, hg, hgb⟩ := b.2
  have hgerm : ((f : Germ (𝓟 (Set.univ : Set ℂ)) ℂ) * (deriv g : Germ (𝓟 (Set.univ : Set ℂ)) ℂ))
      = ((deriv f : Germ (𝓟 (Set.univ : Set ℂ)) ℂ) * (g : Germ (𝓟 (Set.univ : Set ℂ)) ℂ)) := by
    have hval := congrArg (Subtype.val) hring
    rw [MulMemClass.coe_mul, MulMemClass.coe_mul, analyticSubringDeriv_coe,
      analyticSubringDeriv_coe] at hval
    have hfa' : (a : Germ (𝓟 (Set.univ : Set ℂ)) ℂ) = (f : Germ (𝓟 (Set.univ : Set ℂ)) ℂ) :=
      hfa.symm
    have hgb' : (b : Germ (𝓟 (Set.univ : Set ℂ)) ℂ) = (g : Germ (𝓟 (Set.univ : Set ℂ)) ℂ) :=
      hgb.symm
    rw [hfa', hgb'] at hval
    rw [analyticGermDeriv_coe, analyticGermDeriv_coe] at hval
    exact hval
  have hN : Set.EqOn (fun z => deriv f z * g z - f z * deriv g z) 0 (Set.univ : Set ℂ) := by
    rw [← Germ.coe_mul, ← Germ.coe_mul, Germ.coe_eq] at hgerm
    intro z _
    have := eventually_principal.mp hgerm z (Set.mem_univ z)
    simp only [Pi.zero_apply]
    rw [sub_eq_zero]
    exact this.symm
  obtain ⟨c, hc⟩ := exists_constant_of_quotientWronskian_eq_zero a b hb hf hg hfa hgb hN
  exact ⟨c, by rw [show algebraMap ℂ (meroField (Set.univ : Set ℂ)) c
    = algebraMap (analyticSubring (Set.univ : Set ℂ)) (meroField (Set.univ : Set ℂ))
      (constToAnalytic Set.univ c) from rfl, hc, hx']⟩

end

end GaloisForLFunctions.HTGeometry
