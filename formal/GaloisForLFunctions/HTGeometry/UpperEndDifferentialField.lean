import GaloisForLFunctions.HTGeometry.UpperEndMeromorphicField
import GaloisForLFunctions.HTGeometry.FractionRingDerivation
import Mathlib.RingTheory.Derivation.DifferentialRing
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Differential structure at the complex upper end

Differentiation descends to upper-end germs because eventual equality holds on an open upper
half-plane, where equal analytic representatives have equal derivatives.  It preserves the
eventual-analytic subring and extends by the quotient rule to the upper-end meromorphic field.

Every complex translation commutes with this derivation.  Hence the upper end is a genuine
translation--differential carrier for an arbitrary countable palette of complex shifts.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Set Topology Function
open scoped Differential

noncomputable section

/-- Differentiation is well-defined on germs at the upper end. -/
def upperEndGermDeriv : Germ upperEndFilter ℂ → Germ upperEndFilter ℂ :=
  Germ.map' deriv (by
    intro f g hfg
    change ∀ᶠ z in upperEndFilter, f z = g z at hfg
    rw [upperEndFilter_basis.eventually_iff] at hfg
    obtain ⟨H, -, hH⟩ := hfg
    change ∀ᶠ z in upperEndFilter, deriv f z = deriv g z
    rw [upperEndFilter_basis.eventually_iff]
    exact ⟨H, trivial, Set.EqOn.deriv hH (upperTail_isOpen H)⟩)

@[simp]
theorem upperEndGermDeriv_coe (f : ℂ → ℂ) :
    upperEndGermDeriv (f : Germ upperEndFilter ℂ) =
      (deriv f : Germ upperEndFilter ℂ) :=
  rfl

/-- The derivative of an eventual analytic germ is again eventual analytic. -/
def upperEndAnalyticDeriv (a : upperEndAnalyticSubring) :
    upperEndAnalyticSubring := by
  refine ⟨upperEndGermDeriv a.1, ?_⟩
  obtain ⟨f, H, hf, hfa⟩ := a.2
  refine ⟨deriv f, H, hf.deriv, ?_⟩
  rw [← hfa]
  rfl

@[simp]
theorem upperEndAnalyticDeriv_coe (a : upperEndAnalyticSubring) :
    (upperEndAnalyticDeriv a : Germ upperEndFilter ℂ) =
      upperEndGermDeriv (a : Germ upperEndFilter ℂ) :=
  rfl

theorem upperEndAnalyticDeriv_zero :
    upperEndAnalyticDeriv (0 : upperEndAnalyticSubring) = 0 := by
  apply Subtype.ext
  rw [upperEndAnalyticDeriv_coe]
  change (deriv (0 : ℂ → ℂ) : Germ upperEndFilter ℂ) = 0
  simp

theorem upperEndAnalyticDeriv_add (a b : upperEndAnalyticSubring) :
    upperEndAnalyticDeriv (a + b) =
      upperEndAnalyticDeriv a + upperEndAnalyticDeriv b := by
  obtain ⟨f, H, hf, hfa⟩ := a.2
  obtain ⟨g, K, hg, hgb⟩ := b.2
  apply Subtype.ext
  change upperEndGermDeriv ((a : Germ upperEndFilter ℂ) + b) =
    upperEndGermDeriv a + upperEndGermDeriv b
  rw [← hfa, ← hgb]
  change upperEndGermDeriv (↑(f + g) : Germ upperEndFilter ℂ) =
    upperEndGermDeriv (↑f : Germ upperEndFilter ℂ) +
      upperEndGermDeriv (↑g : Germ upperEndFilter ℂ)
  rw [upperEndGermDeriv_coe, upperEndGermDeriv_coe,
    upperEndGermDeriv_coe, ← Germ.coe_add, Germ.coe_eq]
  change ∀ᶠ z in upperEndFilter, deriv (f + g) z = deriv f z + deriv g z
  rw [upperEndFilter_basis.eventually_iff]
  refine ⟨max H K, trivial, fun z hz ↦ ?_⟩
  rw [deriv_add
    (hf z (upperTail_mono (le_max_left H K) hz)).differentiableAt
    (hg z (upperTail_mono (le_max_right H K) hz)).differentiableAt]

theorem upperEndAnalyticDeriv_mul (a b : upperEndAnalyticSubring) :
    upperEndAnalyticDeriv (a * b) =
      a * upperEndAnalyticDeriv b + b * upperEndAnalyticDeriv a := by
  obtain ⟨f, H, hf, hfa⟩ := a.2
  obtain ⟨g, K, hg, hgb⟩ := b.2
  apply Subtype.ext
  change upperEndGermDeriv ((a : Germ upperEndFilter ℂ) * b) =
    (a : Germ upperEndFilter ℂ) * upperEndGermDeriv b +
      (b : Germ upperEndFilter ℂ) * upperEndGermDeriv a
  rw [← hfa, ← hgb]
  change upperEndGermDeriv (↑(f * g) : Germ upperEndFilter ℂ) =
    (↑f : Germ upperEndFilter ℂ) * upperEndGermDeriv (↑g : Germ upperEndFilter ℂ) +
      (↑g : Germ upperEndFilter ℂ) * upperEndGermDeriv (↑f : Germ upperEndFilter ℂ)
  rw [upperEndGermDeriv_coe, upperEndGermDeriv_coe,
    upperEndGermDeriv_coe, ← Germ.coe_mul, ← Germ.coe_mul,
    ← Germ.coe_add, Germ.coe_eq]
  change ∀ᶠ z in upperEndFilter,
    deriv (f * g) z = f z * deriv g z + g z * deriv f z
  rw [upperEndFilter_basis.eventually_iff]
  refine ⟨max H K, trivial, fun z hz ↦ ?_⟩
  rw [deriv_mul
    (hf z (upperTail_mono (le_max_left H K) hz)).differentiableAt
    (hg z (upperTail_mono (le_max_right H K) hz)).differentiableAt]
  ring

/-- Ordinary complex differentiation on the eventual-analytic domain. -/
def upperEndAnalyticDerivation :
    Derivation ℤ upperEndAnalyticSubring upperEndAnalyticSubring := by
  let D : upperEndAnalyticSubring →+ upperEndAnalyticSubring :=
    { toFun := upperEndAnalyticDeriv
      map_zero' := upperEndAnalyticDeriv_zero
      map_add' := upperEndAnalyticDeriv_add }
  exact Derivation.mk' D.toIntLinearMap upperEndAnalyticDeriv_mul

/-- Quotient-rule differential structure on the upper-end meromorphic field. -/
@[reducible]
def upperEndMeroFieldDifferential : Differential upperEndMeroField := by
  letI := isDomain_upperEndAnalyticSubring
  letI : Algebra ℤ upperEndAnalyticSubring := Ring.toIntAlgebra _
  letI : Algebra ℤ upperEndMeroField := Ring.toIntAlgebra _
  exact ⟨fractionRingDerivation (K := ℤ)
    ((Algebra.linearMap upperEndAnalyticSubring upperEndMeroField).compDer
      upperEndAnalyticDerivation)⟩

/-- The fraction-field derivation restricts to ordinary differentiation on analytic germs. -/
theorem upperEndMeroFieldDifferential_algebraMap
    (a : upperEndAnalyticSubring) :
    letI := isDomain_upperEndAnalyticSubring
    letI := upperEndMeroFieldDifferential
    (algebraMap upperEndAnalyticSubring upperEndMeroField a)′ =
      algebraMap upperEndAnalyticSubring upperEndMeroField
        (upperEndAnalyticDeriv a) := by
  letI := isDomain_upperEndAnalyticSubring
  letI : Algebra ℤ upperEndAnalyticSubring := Ring.toIntAlgebra _
  letI : Algebra ℤ upperEndMeroField := Ring.toIntAlgebra _
  letI := upperEndMeroFieldDifferential
  change fractionRingDerivation _
    (algebraMap upperEndAnalyticSubring upperEndMeroField a) = _
  rw [fractionRingDerivation_algebraMap]
  rfl

/-- Translation commutes with differentiation on eventual-analytic germs. -/
theorem upperEndTranslationAnalyticEquiv_deriv (h : ℂ)
    (a : upperEndAnalyticSubring) :
    upperEndTranslationAnalyticEquiv h (upperEndAnalyticDeriv a) =
      upperEndAnalyticDeriv (upperEndTranslationAnalyticEquiv h a) := by
  obtain ⟨f, H, hf, hfa⟩ := a.2
  apply Subtype.ext
  change upperEndTranslateGerm h (upperEndGermDeriv (a : Germ upperEndFilter ℂ)) =
    upperEndGermDeriv (upperEndTranslateGerm h (a : Germ upperEndFilter ℂ))
  rw [← hfa]
  change (↑(fun z ↦ deriv f (z + h)) : Germ upperEndFilter ℂ) =
    (↑(deriv (fun z : ℂ ↦ f (z + h))) : Germ upperEndFilter ℂ)
  rw [Germ.coe_eq]
  change ∀ᶠ z in upperEndFilter, deriv f (z + h) = deriv (fun z : ℂ ↦ f (z + h)) z
  rw [upperEndFilter_basis.eventually_iff]
  refine ⟨H - h.im, trivial, fun z hz ↦ ?_⟩
  rw [deriv_comp_add_const]

/-- **Upper-end translation--derivation law.** Every complex translation is a differential-field
automorphism of the upper-end meromorphic carrier. -/
theorem upperEndTranslationMeroEquiv_deriv (h : ℂ)
    (z : upperEndMeroField) :
    letI := isDomain_upperEndAnalyticSubring
    letI := upperEndMeroFieldDifferential
    upperEndTranslationMeroEquiv h z′ =
      (upperEndTranslationMeroEquiv h z)′ := by
  let A := upperEndAnalyticSubring
  let F := upperEndMeroField
  letI hdom := isDomain_upperEndAnalyticSubring
  letI : Algebra ℤ A := Ring.toIntAlgebra _
  letI : Algebra ℤ F := Ring.toIntAlgebra _
  letI hdiff := upperEndMeroFieldDifferential
  let sigmaA : A ≃+* A := upperEndTranslationAnalyticEquiv h
  let sigmaF : F ≃+* F := upperEndTranslationMeroEquiv h
  let Dc : Derivation ℤ F F :=
    (Differential.equiv sigmaF : Differential F).deriv
  have hDc : Dc = Differential.deriv := by
    apply fractionRing_derivation_ext (A := A) (F := F)
    intro a
    change sigmaF.symm (Differential.deriv (sigmaF (algebraMap A F a))) = _
    have hsigma : sigmaF (algebraMap A F a) =
        algebraMap A F (sigmaA a) := by
      exact upperEndTranslationMeroEquiv_algebraMap h a
    rw [hsigma, upperEndMeroFieldDifferential_algebraMap]
    rw [upperEndMeroFieldDifferential_algebraMap]
    rw [← upperEndTranslationAnalyticEquiv_deriv]
    have hmap : sigmaF
        (algebraMap A F (upperEndAnalyticDeriv a)) =
          algebraMap A F (sigmaA (upperEndAnalyticDeriv a)) := by
      exact upperEndTranslationMeroEquiv_algebraMap h _
    have := congrArg sigmaF.symm hmap
    simpa [sigmaF] using this.symm
  have hzconj := Derivation.congr_fun hDc z
  change sigmaF.symm (Differential.deriv (sigmaF z)) = Differential.deriv z at hzconj
  have := congrArg sigmaF hzconj
  simpa [sigmaF] using this.symm

end

end GaloisForLFunctions.HTGeometry
