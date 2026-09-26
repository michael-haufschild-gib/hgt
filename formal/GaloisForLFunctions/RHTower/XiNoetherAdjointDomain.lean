import GaloisForLFunctions.RHTower.XiEntireOnShellWronskianInternalization
import GaloisForLFunctions.RHTower.XiWeilCauchyCoreMultiplicity
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Entire obstruction and meromorphic realization of the Xi Noether adjoint

The canonical adjoint equation is `(XiC * F)' = 0`. In the entire source
algebra its only solution is zero: the product is constant, an actual Xi
zero annihilates that constant, and multiplication by Xi is injective.

The reciprocal Xi function supplies a meromorphic solution instead. Its
charge is one as a punctured germ, and its pole order at each Xi divisor
point is exactly the negative of that point's multiplicity. These poles
occur at every divisor point, with no critical-line selection.
-/

noncomputable section

namespace RHTower

open Complex Filter Topology

/-- The entire canonical adjoint equation, before imposing conservation. -/
def xiNoetherEntireAdjointDefect (F : DeningerEntire) : DeningerEntire :=
  deningerEntireDeriv (deningerEntireXi * F)

theorem xiNoetherEntireAdjointDefect_apply (F : DeningerEntire) (z : ℂ) :
    xiNoetherEntireAdjointDefect F z =
      XiC z * deriv (F : ℂ → ℂ) z + deriv XiC z * F z := by
  rw [xiNoetherEntireAdjointDefect, deningerEntireDeriv_mul]
  simp only [deningerEntire_add_apply, deningerEntire_mul_apply,
    deningerEntireXi_apply, deningerEntireDeriv_apply]
  change XiC z * deriv (F : ℂ → ℂ) z + F z * deriv XiC z = _
  ring

/-- No entire partner of Xi can carry a nonzero constant canonical charge. -/
theorem xiNoetherEntireCharge_constant_iff (F : DeningerEntire) :
    (∃ c : ℂ, deningerEntireXi * F = algebraMap ℂ DeningerEntire c) ↔ F = 0 := by
  constructor
  · rintro ⟨c, hc⟩
    obtain ⟨r, hr⟩ := xiDivisorSupport_infinite.nonempty
    let rho : XiDivisorSupport := ⟨r, hr⟩
    have hz := congrArg (fun G : DeningerEntire => G (xiSpectralPointSupport rho)) hc
    have hc0 : c = 0 := by
      simpa only [deningerEntire_mul_apply, deningerEntireXi_apply,
        XiC_xiSpectralPointSupport_eq_zero_source, zero_mul,
        deningerEntire_algebraMap_apply] using hz.symm
    apply deningerEntireXi_mul_injective
    simpa only [hc0, map_zero, mul_zero] using hc
  · rintro rfl
    exact ⟨0, by simp⟩

/-- The entire canonical adjoint has zero kernel, despite the nontrivial Xi source. -/
theorem xiNoetherEntireAdjointDefect_eq_zero_iff (F : DeningerEntire) :
    xiNoetherEntireAdjointDefect F = 0 ↔ F = 0 := by
  constructor
  · intro h
    have hd (z : ℂ) : deriv ((deningerEntireXi * F : DeningerEntire) : ℂ → ℂ) z = 0 :=
      congrArg (fun G : DeningerEntire => G z) h
    apply (xiNoetherEntireCharge_constant_iff F).mp
    refine ⟨(deningerEntireXi * F) 0, DeningerEntire.ext fun z => ?_⟩
    exact is_const_of_deriv_eq_zero (deningerEntireXi * F).2 hd z 0
  · rintro rfl
    simp [xiNoetherEntireAdjointDefect]

/-- The meromorphic canonical adjoint. At a pole Lean's total inverse has value zero;
conservation is therefore stated on punctured germs. -/
def xiNoetherMeromorphicAdjoint (z : ℂ) : ℂ := (XiC z)⁻¹

theorem meromorphicAt_xiNoetherMeromorphicAdjoint (z : ℂ) :
    MeromorphicAt xiNoetherMeromorphicAdjoint z :=
  (XiC_analytic z (Set.mem_univ z)).meromorphicAt.inv

/-- The reciprocal has exactly the pole multiplicity of its actual Xi source zero. -/
theorem xiNoetherMeromorphicAdjoint_order (rho : XiDivisorSupport) :
    meromorphicOrderAt xiNoetherMeromorphicAdjoint (xiSpectralPointSupport rho) =
      -((xiSupportMultiplicity rho : ℤ) : WithTop ℤ) := by
  change meromorphicOrderAt (XiC⁻¹) (xiSpectralPointSupport rho) = _
  rw [meromorphicOrderAt_inv,
    (XiC_analytic _ (Set.mem_univ _)).meromorphicOrderAt_eq,
    XiC_analyticOrderAt_support]
  simp only [ENat.map_coe, xiSupportMultiplicity]

/-- Every punctured germ carries unit Noether charge, including germs around actual zeros. -/
theorem eventually_xiNoetherMeromorphicAdjoint_charge (z : ℂ) :
    ∀ᶠ w in 𝓝[≠] z, XiC w * xiNoetherMeromorphicAdjoint w = 1 := by
  filter_upwards [eventually_XiC_ne_zero_punctured z] with w hw
  exact mul_inv_cancel₀ hw

/-- The reciprocal satisfies the source/adjoint conservation equation as a meromorphic germ. -/
theorem eventually_xiNoetherMeromorphicAdjoint_equation (z : ℂ) :
    ∀ᶠ w in 𝓝[≠] z,
      XiC w * deriv xiNoetherMeromorphicAdjoint w +
        deriv XiC w * xiNoetherMeromorphicAdjoint w = 0 := by
  filter_upwards [eventually_XiC_ne_zero_punctured z] with w hw
  have hd : deriv xiNoetherMeromorphicAdjoint w = -deriv XiC w / XiC w ^ 2 :=
    ((XiC_differentiable w).hasDerivAt.inv hw).deriv
  rw [hd, xiNoetherMeromorphicAdjoint]
  field_simp
  ring

/-- The meromorphic adjoint cannot be made continuous at any actual Xi zero by its point value. -/
theorem xiNoetherMeromorphicAdjoint_not_continuousAt (rho : XiDivisorSupport) :
    ¬ ContinuousAt xiNoetherMeromorphicAdjoint (xiSpectralPointSupport rho) := by
  intro h
  have hprod := (XiC_differentiable (xiSpectralPointSupport rho)).continuousAt.mul h
  have hlim := hprod.tendsto.mono_left
    (show 𝓝[≠] (xiSpectralPointSupport rho) ≤ 𝓝 (xiSpectralPointSupport rho) from
      nhdsWithin_le_nhds)
  have hone : Tendsto (fun w => XiC w * xiNoetherMeromorphicAdjoint w)
      (𝓝[≠] (xiSpectralPointSupport rho)) (𝓝 (1 : ℂ)) := by
    have hcharge : (fun w => XiC w * xiNoetherMeromorphicAdjoint w) =ᶠ[
        𝓝[≠] (xiSpectralPointSupport rho)] (fun _ => (1 : ℂ)) :=
      eventually_xiNoetherMeromorphicAdjoint_charge _
    exact tendsto_const_nhds.congr' hcharge.symm
  have he := tendsto_nhds_unique hlim hone
  apply zero_ne_one (α := ℂ)
  simpa only [Pi.mul_apply, XiC_xiSpectralPointSupport_eq_zero_source, zero_mul] using he

end RHTower
