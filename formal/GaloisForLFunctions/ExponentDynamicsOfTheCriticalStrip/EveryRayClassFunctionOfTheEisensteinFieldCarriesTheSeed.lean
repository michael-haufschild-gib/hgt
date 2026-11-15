import GaloisForLFunctions.ExponentDynamicsOfTheCriticalStrip.TheArtinFunctionOfTheCubeRootsOfTwoCarriesTheSeed
import GaloisForLFunctions.FamilyContinuationTheory.HarmonicGaussianPoissonGivesGrossencharacterContinuation

/-!
# Every ray class function of the Eisenstein field carries the seed

The seed of MMD (`hecke_nonzero`) is a theorem about the theta-lattice continuation of the Hecke
`L`-functions of finite order of `K = ℚ(ω)`. The completed ray class `L`-functions `Ξ_ψ` of
`HeckeLFunctions` carry the explicit formula and the index law of AGZ. This module transports the
seed to all of them.

* **The MMD character of `ψ`** (`heckeFamilyOfRay`): the residue character of `ψ` on
  `(O/𝔪)^×` (`finiteHeckeWeight`) is trivial on the global units, because `ψ((u)) = ψ(1) = 1`, and
  its ideal coefficients are the values of `ψ` (`idealCoeff_heckeFamilyOfRay`, through FCT
  `integralHeckeWeight_eq_heckeValue`). It is principal only for `ψ = 1`: every ray class of `K` is
  the class of a residue, `K` having trivial class group and no real place.
* **The bridge** (`LFunction_heckeFamilyOfRay_eq`): `Ξ_ψ(s)Γ(s)⁻¹N^{−s/2}` is entire and is the MMD
  `L`-function of `ψ` everywhere (identity theorem from `Re s > 1`).
* **The seed** (`heckeXi_ne_zero_of_seven_eighths_lt_re`, `re_le_seven_eighths_of_mem_heckeZeros`):
  for every nontrivial ray class character `ψ` of `ℚ(ω)`, `Ξ_ψ` has no zero on `Re s > 7/8`.
-/

noncomputable section

open NumberField Complex Set

namespace GaloisForLFunctions.ExponentDynamicsOfTheCriticalStrip

open GaloisForLFunctions.AbsoluteGeometryOfSpecZ
open MetaplecticMobiusDescent.Eisenstein MetaplecticMobiusDescent.CubicEisenstein HeckeLFunctions

local instance : IsCyclotomicExtension {3} ℚ K := CyclotomicField.isCyclotomicExtension 3 ℚ
local instance : IsPrincipalIdealRing O := IsCyclotomicExtension.Rat.three_pid K

variable (𝔪 : Modulus K) (ψ : HeckeCharacter 𝔪)

theorem finiteHeckeWeight_globalUnit (u : Oˣ) :
    finiteHeckeWeight 𝔪 ψ (Ideal.Quotient.mk 𝔪.fin (u : O)) = 1 := by
  have h := FamilyContinuationTheory.integralHeckeWeight_eq_heckeValue 𝔪 ψ u.ne_zero
  rw [Ideal.span_singleton_eq_top.mpr u.isUnit, ← Ideal.one_eq_top, heckeValue_one] at h
  exact h

/-- The MMD character of a ray class character of `ℚ(ω)`. -/
def heckeFamilyOfRay : HeckeFamily.Character :=
  HeckeFamily.Character.ofResidue 𝔪.fin 𝔪.fin_ne_bot (finiteHeckeWeight 𝔪 ψ)
    (finiteHeckeWeight_globalUnit 𝔪 ψ)

/-- The MMD coefficients of `ψ` are its values on ideals. -/
theorem idealCoeff_heckeFamilyOfRay (I : Ideal O) :
    HeckeFamily.idealCoeff (heckeFamilyOfRay 𝔪 ψ) I = heckeValue 𝔪 ψ I := by
  by_cases hI : I = ⊥
  · subst hI
    rw [heckeValue_bot]
    exact HeckeFamily.idealCoeff_zero _
  · obtain ⟨a, ha⟩ := (IsPrincipalIdealRing.principal I).principal
    have ha' : Ideal.span ({a} : Set O) = I := ha.symm
    have ha0 : a ≠ 0 := by
      rintro rfl
      exact hI (by rw [← ha', Ideal.span_singleton_eq_bot])
    rw [← ha', HeckeFamily.idealCoeff_span _ ha0]
    exact FamilyContinuationTheory.integralHeckeWeight_eq_heckeValue 𝔪 ψ ha0

/-- A nontrivial ray class character has a nontrivial residue character. -/
theorem heckeFamilyOfRay_residue_ne_one (hψ : ψ ≠ 1) : (heckeFamilyOfRay 𝔪 ψ).residue ≠ 1 := by
  intro h1
  have h1' : finiteHeckeWeight 𝔪 ψ = 1 := h1
  apply hψ
  ext c
  obtain ⟨x, rfl⟩ := rayResidueClass_surjective 𝔪 c
  have hemp : IsEmpty 𝔪.inf := ⟨fun w => isEmpty_isReal_infinitePlace.false w.1⟩
  have hx : rayResidueClass 𝔪 x = fullRayResidueClass 𝔪 x.1 := congrArg (rayResidueClass 𝔪) rfl
  have hfin : finiteResidueCharacter 𝔪 ψ x.1.1 = 1 := by
    apply Units.ext
    rw [← finiteHeckeWeight_unit, h1', MulChar.one_apply_coe, Units.val_one]
  have hinf : infiniteSignCharacter 𝔪 ψ x.1.2 = 1 := by
    rw [Subsingleton.elim x.1.2 1, map_one]
  rw [hx]
  change (rayResidueCharacter 𝔪 ψ x.1 : ℂ) = ((1 : HeckeCharacter 𝔪) _ : ℂ)
  rw [rayResidueCharacter_eq_mul, hfin, hinf, mul_one]
  rfl

/-- On `Re s > 1` the MMD `L`-function of `ψ` is `L(s, ψ)`. -/
theorem LFunction_heckeFamilyOfRay_eq_heckeL {s : ℂ} (hs : 1 < s.re) :
    HeckeFamily.LFunction (heckeFamilyOfRay 𝔪 ψ) s = heckeL 𝔪 ψ s := by
  rw [HeckeFamily.LFunction_eq_ideal_tsum _ hs, heckeL_eq_tsum_ideals 𝔪 ψ hs]
  have hsupp : Function.support (HeckeFamily.idealTerm (heckeFamilyOfRay 𝔪 ψ) s) ⊆
      (nonZeroDivisors (Ideal O) : Set (Ideal O)) := by
    intro I hI
    apply mem_nonZeroDivisors_of_ne_zero
    rintro rfl
    exact hI (by rw [HeckeFamily.idealTerm, HeckeFamily.idealCoeff_zero, zero_div])
  rw [← tsum_subtype_eq_of_support_subset hsupp]
  refine tsum_congr fun I => ?_
  simp only [HeckeFamily.idealTerm, heckeIdealTerm, MonoidHom.coe_mk, OneHom.coe_mk]
  rw [idealCoeff_heckeFamilyOfRay, cpow_neg, div_eq_mul_inv]

/-- The entire continuation of `L(s, ψ)` from its completion. -/
def rayCont (s : ℂ) : ℂ :=
  (heckeGammaFactor 𝔪 ψ s)⁻¹ * (heckeCompletionFactor 𝔪 s)⁻¹ * heckeXi 𝔪 ψ s

theorem differentiable_rayCont : Differentiable ℂ (rayCont 𝔪 ψ) :=
  ((differentiable_heckeGammaFactor_inv 𝔪 ψ).mul
    ((differentiable_heckeCompletionFactor 𝔪).inv (heckeCompletionFactor_ne_zero 𝔪))).mul
      (differentiable_heckeXi 𝔪 ψ)

theorem rayCont_eq_heckeL (hψ : ψ ≠ 1) {s : ℂ} (hs : 1 < s.re) : rayCont 𝔪 ψ s = heckeL 𝔪 ψ s := by
  have hΓ := heckeGammaFactor_ne_zero 𝔪 ψ (show 0 < s.re by linarith)
  have hN := heckeCompletionFactor_ne_zero 𝔪 s
  rw [rayCont, heckeXi_of_ne_one hψ, heckeCompletedLFunction_eq _ _ hs]
  field_simp

/-- **The bridge**: the MMD `L`-function of `ψ` is the continuation of `L(s, ψ)` everywhere. -/
theorem LFunction_heckeFamilyOfRay_eq (hψ : ψ ≠ 1) (s : ℂ) :
    HeckeFamily.LFunction (heckeFamilyOfRay 𝔪 ψ) s = rayCont 𝔪 ψ s := by
  have hL : Differentiable ℂ (HeckeFamily.LFunction (heckeFamilyOfRay 𝔪 ψ)) := by
    have h := HeckeCharacterAnalytic.continuedLattice_entire_nonprincipal (heckeFamilyOfRay 𝔪 ψ)
      (heckeFamilyOfRay_residue_ne_one 𝔪 ψ hψ)
    exact fun z => (h z).div_const 6
  have hA : AnalyticOnNhd ℂ (HeckeFamily.LFunction (heckeFamilyOfRay 𝔪 ψ)) univ :=
    fun z _ => hL.analyticAt z
  have hB : AnalyticOnNhd ℂ (rayCont 𝔪 ψ) univ := fun z _ => (differentiable_rayCont 𝔪 ψ).analyticAt z
  have hev : HeckeFamily.LFunction (heckeFamilyOfRay 𝔪 ψ) =ᶠ[nhds (2 : ℂ)] rayCont 𝔪 ψ := by
    have hopen : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const continuous_re
    filter_upwards [hopen.mem_nhds (by simp : (1 : ℝ) < (2 : ℂ).re)] with z hz
    rw [LFunction_heckeFamilyOfRay_eq_heckeL 𝔪 ψ hz, rayCont_eq_heckeL 𝔪 ψ hψ hz]
  exact hA.eqOn_of_preconnected_of_eventuallyEq hB isPreconnected_univ (mem_univ 2) hev (mem_univ s)

/-- **The seed for every ray class function of `ℚ(ω)`**: for `ψ ≠ 1` the completed `L(s, ψ)` has no
zero on `Re s > 7/8`. -/
theorem heckeXi_ne_zero_of_seven_eighths_lt_re (hψ : ψ ≠ 1) {s : ℂ} (hs : (7 / 8 : ℝ) < s.re) :
    heckeXi 𝔪 ψ s ≠ 0 := by
  intro h0
  have hG : rayCont 𝔪 ψ s = 0 := by rw [rayCont, h0, mul_zero]
  rw [← LFunction_heckeFamilyOfRay_eq 𝔪 ψ hψ] at hG
  exact ProbeFinalAssemblyUnconditional.hecke_nonzero (heckeFamilyOfRay 𝔪 ψ) s hs
    (Or.inr (heckeFamilyOfRay_residue_ne_one 𝔪 ψ hψ)) hG

/-- Every zero of a nontrivial primitive ray class `L`-function of `ℚ(ω)` lies in `Re s ≤ 7/8`. -/
theorem re_le_seven_eighths_of_mem_heckeZeros (hψ : ψ ≠ 1)
    (hc : heckeFiniteConductor 𝔪 ψ = 𝔪.fin) {ρ : ℂ} (hρ : ρ ∈ (heckeZeros 𝔪 ψ hc).carrier) :
    ρ.re ≤ 7 / 8 := by
  have h0 : heckeXi 𝔪 ψ ρ = 0 := hρ
  by_contra h
  exact heckeXi_ne_zero_of_seven_eighths_lt_re 𝔪 ψ hψ (lt_of_not_ge h) h0

end GaloisForLFunctions.ExponentDynamicsOfTheCriticalStrip
