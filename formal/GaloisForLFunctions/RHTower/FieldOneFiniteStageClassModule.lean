import GaloisForLFunctions.RHTower.FieldOneFiniteStageHaarScaling

/-!
# Module and idele locus of the finite-stage adelic class space

For `A_S = ℝ × ∏_{v ∈ S} ℚ_v`, the product of all local norms extends from
ideles to every additive adele, with value zero when a coordinate vanishes.
This file proves that the extended module is invariant under diagonal rational
`S`-units and therefore descends continuously to

`X_S = ℤ_Sˣ \ A_S`.

It also constructs the orbit-of-one map

`C_S = ℤ_Sˣ \ A_Sˣ → X_S`,

proves it continuous and injective, and proves compatibility of the modules
and scaling laws on both sides.  These are the algebraic and topological
parts of the primary-source idele-locus comparison.  No quotient measure,
Radon--Nikodym derivative, or `L²(X_S) ≃ L²(C_S)` is asserted here.
-/

namespace GaloisForLFunctions.RHTower

noncomputable section

open IsDedekindDomain
open scoped NNReal

/-! ### Module on additive adeles and their orbit quotient -/

/-- Product of all selected local norms, defined on every finite-stage
additive adele. -/
def fieldOneFiniteStageAdeleModule
    (S : Finset (HeightOneSpectrum ℤ)) :
    FieldOneFiniteStageAdele S → ℝ≥0 :=
  fun x =>
    ‖x.1‖₊ *
      ∏ v : ↥S, ‖x.2 v‖₊

theorem fieldOneFiniteStageAdeleModule_continuous
    (S : Finset (HeightOneSpectrum ℤ)) :
    Continuous (fieldOneFiniteStageAdeleModule S) := by
  apply Continuous.mul
  · exact continuous_nnnorm.comp continuous_fst
  · exact continuous_finsetProd _ fun v _ =>
      continuous_nnnorm.comp
        ((continuous_apply v).comp continuous_snd)

/-- Scaling an additive adele multiplies its extended module by the idele
module. -/
theorem fieldOneFiniteStageAdeleModule_smul
    (S : Finset (HeightOneSpectrum ℤ))
    (u : FieldOneFiniteStageIdele S)
    (x : FieldOneFiniteStageAdele S) :
    fieldOneFiniteStageAdeleModule S (u • x) =
      fieldOneFiniteStageModule S u *
        fieldOneFiniteStageAdeleModule S x := by
  change
    ‖(u.1 : ℝ) * x.1‖₊ *
        ∏ v : ↥S,
          ‖(u.2 v : v.1.adicCompletion ℚ) * x.2 v‖₊ =
      (‖(u.1 : ℝ)‖₊ *
          ∏ v : ↥S, ‖(u.2 v : v.1.adicCompletion ℚ)‖₊) *
        (‖x.1‖₊ * ∏ v : ↥S, ‖x.2 v‖₊)
  simp only [nnnorm_mul]
  rw [Finset.prod_mul_distrib]
  ac_rfl

/-- Every diagonal rational `S`-unit preserves the extended module. -/
theorem fieldOneFiniteStageAdeleModule_sUnit
    (S : Finset (HeightOneSpectrum ℤ))
    (h : fieldOneFiniteStageSUnitImage S)
    (x : FieldOneFiniteStageAdele S) :
    fieldOneFiniteStageAdeleModule S
        ((h : FieldOneFiniteStageIdele S) • x) =
      fieldOneFiniteStageAdeleModule S x := by
  rw [fieldOneFiniteStageAdeleModule_smul]
  have hh :=
    fieldOneFiniteStageSUnitImage_le_moduleKernel S h.property
  change fieldOneFiniteStageModule S
      (h : FieldOneFiniteStageIdele S) = 1 at hh
  rw [hh, one_mul]

/-- Continuous product module on the finite-stage orbit class space. -/
def fieldOneFiniteStageClassModule
    (S : Finset (HeightOneSpectrum ℤ)) :
    FieldOneFiniteStageClassSpace S → ℝ≥0 :=
  Quotient.lift
    (fieldOneFiniteStageAdeleModule S)
    (by
      intro x y hxy
      change
        MulAction.orbitRel
          (fieldOneFiniteStageSUnitImage S)
          (FieldOneFiniteStageAdele S) x y at hxy
      rw [MulAction.orbitRel_apply] at hxy
      change
        ∃ h : fieldOneFiniteStageSUnitImage S,
          (h : FieldOneFiniteStageIdele S) • y = x at hxy
      obtain ⟨h, rfl⟩ := hxy
      exact fieldOneFiniteStageAdeleModule_sUnit S h y)

@[simp]
theorem fieldOneFiniteStageClassModule_mk
    (S : Finset (HeightOneSpectrum ℤ))
    (x : FieldOneFiniteStageAdele S) :
    fieldOneFiniteStageClassModule S (Quotient.mk _ x) =
      fieldOneFiniteStageAdeleModule S x :=
  rfl

theorem fieldOneFiniteStageClassModule_continuous
    (S : Finset (HeightOneSpectrum ℤ)) :
    Continuous (fieldOneFiniteStageClassModule S) := by
  rw [(fieldOneFiniteStageClassQuotient_isOpenQuotientMap S).isQuotientMap.continuous_iff]
  exact fieldOneFiniteStageAdeleModule_continuous S

/-! ### The idele locus inside the orbit class space -/

/-- Forget that every idele coordinate is invertible. -/
def fieldOneFiniteStageIdeleVal
    (S : Finset (HeightOneSpectrum ℤ)) :
    FieldOneFiniteStageIdele S →
      FieldOneFiniteStageAdele S :=
  fun u => ((u.1 : ℝ), fun v => (u.2 v : v.1.adicCompletion ℚ))

theorem fieldOneFiniteStageIdeleVal_injective
    (S : Finset (HeightOneSpectrum ℤ)) :
    Function.Injective (fieldOneFiniteStageIdeleVal S) := by
  intro u w huw
  apply Prod.ext
  · apply Units.ext
    exact congrArg Prod.fst huw
  · funext v
    apply Units.ext
    exact congrArg (fun x => x.2 v) huw

theorem fieldOneFiniteStageIdeleVal_mul
    (S : Finset (HeightOneSpectrum ℤ))
    (u w : FieldOneFiniteStageIdele S) :
    fieldOneFiniteStageIdeleVal S (u * w) =
      u • fieldOneFiniteStageIdeleVal S w := by
  rfl

theorem fieldOneFiniteStageIdeleVal_continuous
    (S : Finset (HeightOneSpectrum ℤ)) :
    Continuous (fieldOneFiniteStageIdeleVal S) := by
  apply Continuous.prodMk
  · exact Units.continuous_val.comp continuous_fst
  · exact continuous_pi fun v => by
      have hunit :
          Continuous fun u : FieldOneFiniteStageIdele S => u.2 v :=
        (continuous_apply v).comp continuous_snd
      exact Units.continuous_val.comp hunit

/-- Orbit of `1`: the canonical map from finite-stage idele classes into
the additive orbit class space. -/
def fieldOneFiniteStageIdeleClassToClassSpace
    (S : Finset (HeightOneSpectrum ℤ)) :
    FieldOneFiniteStageIdeleClassGroup S →
      FieldOneFiniteStageClassSpace S :=
  fun c =>
    Quotient.liftOn' c
      (fun u => Quotient.mk _
        (fieldOneFiniteStageIdeleVal S u))
      (by
        intro u w huw
        apply Quotient.sound
        rw [QuotientGroup.leftRel_apply] at huw
        change
          MulAction.orbitRel
            (fieldOneFiniteStageSUnitImage S)
            (FieldOneFiniteStageAdele S)
            (fieldOneFiniteStageIdeleVal S u)
            (fieldOneFiniteStageIdeleVal S w)
        rw [MulAction.orbitRel_apply]
        change
          ∃ h : fieldOneFiniteStageSUnitImage S,
            (h : FieldOneFiniteStageIdele S) •
                fieldOneFiniteStageIdeleVal S w =
              fieldOneFiniteStageIdeleVal S u
        let h : fieldOneFiniteStageSUnitImage S :=
          ⟨u⁻¹ * w, huw⟩
        refine ⟨h⁻¹, ?_⟩
        change
          (u⁻¹ * w)⁻¹ • fieldOneFiniteStageIdeleVal S w =
            fieldOneFiniteStageIdeleVal S u
        rw [← fieldOneFiniteStageIdeleVal_mul]
        congr 1
        simp [mul_comm])

@[simp]
theorem fieldOneFiniteStageIdeleClassToClassSpace_mk
    (S : Finset (HeightOneSpectrum ℤ))
    (u : FieldOneFiniteStageIdele S) :
    fieldOneFiniteStageIdeleClassToClassSpace S
        (QuotientGroup.mk u) =
      Quotient.mk _
        (fieldOneFiniteStageIdeleVal S u) :=
  rfl

/-- The orbit-of-one map `C_S → X_S` is injective. -/
theorem fieldOneFiniteStageIdeleClassToClassSpace_injective
    (S : Finset (HeightOneSpectrum ℤ)) :
    Function.Injective
      (fieldOneFiniteStageIdeleClassToClassSpace S) := by
  intro c d hcd
  revert hcd
  refine Quotient.inductionOn₂' c d ?_
  intro u w huw
  rw [fieldOneFiniteStageIdeleClassToClassSpace_mk] at huw
  rw [fieldOneFiniteStageIdeleClassToClassSpace_mk] at huw
  rw [Quotient.eq] at huw
  change
    MulAction.orbitRel
      (fieldOneFiniteStageSUnitImage S)
      (FieldOneFiniteStageAdele S)
      (fieldOneFiniteStageIdeleVal S u)
      (fieldOneFiniteStageIdeleVal S w) at huw
  rw [MulAction.orbitRel_apply] at huw
  change
    ∃ h : fieldOneFiniteStageSUnitImage S,
      (h : FieldOneFiniteStageIdele S) •
          fieldOneFiniteStageIdeleVal S w =
        fieldOneFiniteStageIdeleVal S u at huw
  obtain ⟨h, hh⟩ := huw
  rw [QuotientGroup.eq_iff_div_mem]
  have hgroup :
      (h : FieldOneFiniteStageIdele S) * w = u := by
    apply fieldOneFiniteStageIdeleVal_injective S
    rw [fieldOneFiniteStageIdeleVal_mul]
    exact hh
  have hdiv :
      u / w = (h : FieldOneFiniteStageIdele S) := by
    rw [← hgroup]
    simp
  rw [hdiv]
  exact h.property

/-- The orbit-of-one map `C_S → X_S` is continuous. -/
theorem fieldOneFiniteStageIdeleClassToClassSpace_continuous
    (S : Finset (HeightOneSpectrum ℤ)) :
    Continuous (fieldOneFiniteStageIdeleClassToClassSpace S) := by
  rw [(QuotientGroup.isQuotientMap_mk
    (fieldOneFiniteStageSUnitImage S)).continuous_iff]
  simpa [Function.comp_def] using
    continuous_quotient_mk'.comp
      (fieldOneFiniteStageIdeleVal_continuous S)

/-- On the idele locus, the class-space module is the descended idele-class
module. -/
theorem fieldOneFiniteStageClassModule_ideleClass
    (S : Finset (HeightOneSpectrum ℤ))
    (c : FieldOneFiniteStageIdeleClassGroup S) :
    fieldOneFiniteStageClassModule S
        (fieldOneFiniteStageIdeleClassToClassSpace S c) =
      fieldOneFiniteStageIdeleClassModule S c := by
  refine Quotient.inductionOn' c ?_
  intro u
  rfl

/-- The class-space module is equivariant for idele-class scaling. -/
theorem fieldOneFiniteStageClassModule_smul
    (S : Finset (HeightOneSpectrum ℤ))
    (c : FieldOneFiniteStageIdeleClassGroup S)
    (x : FieldOneFiniteStageClassSpace S) :
    fieldOneFiniteStageClassModule S (c • x) =
      fieldOneFiniteStageIdeleClassModule S c *
        fieldOneFiniteStageClassModule S x := by
  refine Quotient.inductionOn' c ?_
  intro u
  refine Quotient.inductionOn x ?_
  intro a
  change
    fieldOneFiniteStageAdeleModule S (u • a) =
      fieldOneFiniteStageModule S u *
        fieldOneFiniteStageAdeleModule S a
  exact fieldOneFiniteStageAdeleModule_smul S u a

end

end GaloisForLFunctions.RHTower
