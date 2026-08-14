import GaloisForLFunctions.HTGeometry.EntireFunctionField
import GaloisForLFunctions.HTGeometry.FractionRingDerivation
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.RingTheory.Derivation.DifferentialRing

/-!
# Directional derivations of the entire fraction field

Differentiating an entire function along a fixed vector produces an entire function, and the
operation obeys the Leibniz rule.  Each direction therefore gives a derivation of the entire
functions, which extends by the quotient rule to their fraction field.

A basis of directions gives the commuting partial derivations of a complex space, the data a
complex torus `ℂ^n / Λ` needs.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

/-- Differentiation along a fixed vector. -/
noncomputable def entireDirectionalDerivative (v : V) (f : V → ℂ) : V → ℂ :=
  fun z => fderiv ℂ f z v

theorem differentiable_of_analyticOnNhd {f : V → ℂ} (hf : AnalyticOnNhd ℂ f Set.univ) :
    Differentiable ℂ f := fun z => (hf z (Set.mem_univ z)).differentiableAt

/-- The directional derivative of an entire function is entire. -/
theorem analyticOnNhd_entireDirectionalDerivative {f : V → ℂ}
    (hf : AnalyticOnNhd ℂ f Set.univ) (v : V) :
    AnalyticOnNhd ℂ (entireDirectionalDerivative v f) Set.univ := by
  have hfd : AnalyticOnNhd ℂ (fderiv ℂ f) Set.univ := hf.fderiv
  have hL : AnalyticOnNhd ℂ (fun L : V →L[ℂ] ℂ => L v) Set.univ :=
    (ContinuousLinearMap.apply ℂ ℂ v).analyticOnNhd Set.univ
  have hcomp := hL.comp hfd (Set.mapsTo_univ _ _)
  exact hcomp

theorem entireDirectionalDerivative_add (v : V) {f g : V → ℂ}
    (hf : Differentiable ℂ f) (hg : Differentiable ℂ g) :
    entireDirectionalDerivative v (f + g) =
      entireDirectionalDerivative v f + entireDirectionalDerivative v g := by
  funext z
  simp only [entireDirectionalDerivative, Pi.add_apply]
  rw [fderiv_add (hf z) (hg z)]
  rfl

theorem entireDirectionalDerivative_mul (v : V) {f g : V → ℂ}
    (hf : Differentiable ℂ f) (hg : Differentiable ℂ g) :
    entireDirectionalDerivative v (f * g) =
      f * entireDirectionalDerivative v g + g * entireDirectionalDerivative v f := by
  funext z
  simp only [entireDirectionalDerivative, Pi.add_apply, Pi.mul_apply]
  rw [fderiv_mul (hf z) (hg z)]
  simp

/-- Differentiation along a vector, on the entire functions. -/
noncomputable def entireDirDeriv (v : V) (a : entireSubring V) : entireSubring V :=
  ⟨entireDirectionalDerivative v (a : V → ℂ),
    analyticOnNhd_entireDirectionalDerivative a.2 v⟩

@[simp] theorem entireDirDeriv_coe (v : V) (a : entireSubring V) :
    ((entireDirDeriv v a : entireSubring V) : V → ℂ) =
      entireDirectionalDerivative v (a : V → ℂ) := rfl

theorem entireDirDeriv_zero (v : V) : entireDirDeriv v (0 : entireSubring V) = 0 := by
  apply Subtype.ext
  funext z
  simp [entireDirDeriv, entireDirectionalDerivative]

theorem entireDirDeriv_add (v : V) (a b : entireSubring V) :
    entireDirDeriv v (a + b) = entireDirDeriv v a + entireDirDeriv v b := by
  apply Subtype.ext
  show entireDirectionalDerivative v ((a : V → ℂ) + (b : V → ℂ)) = _
  rw [entireDirectionalDerivative_add v (differentiable_of_analyticOnNhd a.2)
    (differentiable_of_analyticOnNhd b.2)]
  rfl

theorem entireDirDeriv_mul (v : V) (a b : entireSubring V) :
    entireDirDeriv v (a * b) = a * entireDirDeriv v b + b * entireDirDeriv v a := by
  apply Subtype.ext
  show entireDirectionalDerivative v ((a : V → ℂ) * (b : V → ℂ)) = _
  rw [entireDirectionalDerivative_mul v (differentiable_of_analyticOnNhd a.2)
    (differentiable_of_analyticOnNhd b.2)]
  rfl

/-- **The directional derivation of the entire functions.** -/
noncomputable def entireDirDerivation (v : V) :
    Derivation ℤ (entireSubring V) (entireSubring V) := by
  let D : entireSubring V →+ entireSubring V :=
    { toFun := entireDirDeriv v
      map_zero' := entireDirDeriv_zero v
      map_add' := entireDirDeriv_add v }
  exact Derivation.mk' D.toIntLinearMap (entireDirDeriv_mul v)

@[simp] theorem entireDirDerivation_apply (v : V) (a : entireSubring V) :
    entireDirDerivation v a = entireDirDeriv v a := rfl

/-- The directional derivation valued in the fraction field. -/
noncomputable def entireDirDerivationField (v : V) :
    Derivation ℤ (entireSubring V) (EntireField V) :=
  (Algebra.linearMap (entireSubring V) (EntireField V)).compDer (entireDirDerivation v)

/-- **The directional derivation of the entire fraction field.** -/
noncomputable def fieldDirDerivation (v : V) :
    Derivation ℤ (EntireField V) (EntireField V) :=
  GaloisForLFunctions.fractionRingDerivation (entireDirDerivationField v)

theorem fieldDirDerivation_ofEntire (v : V) {f : V → ℂ} (hf : AnalyticOnNhd ℂ f Set.univ) :
    fieldDirDerivation v (ofEntire f hf) =
      ofEntire (entireDirectionalDerivative v f)
        (analyticOnNhd_entireDirectionalDerivative hf v) :=
  GaloisForLFunctions.fractionRingDerivation_algebraMap (entireDirDerivationField v) ⟨f, hf⟩

theorem fieldDirDerivation_constEntire (v : V) (c : ℂ) :
    fieldDirDerivation v (constEntire V c) = 0 := by
  rw [constEntire_apply, fieldDirDerivation_ofEntire]
  have hzero : entireDirectionalDerivative v (fun _ : V => c) = 0 := by
    funext z
    simp [entireDirectionalDerivative]
  have hcoe : ofEntire (entireDirectionalDerivative v (fun _ : V => c))
      (analyticOnNhd_entireDirectionalDerivative (analyticOnNhd_const (v := c) (𝕜 := ℂ)) v)
      = ofEntire (0 : V → ℂ) analyticOnNhd_const := by
    congr 1
  rw [hcoe, ofEntire]
  have hz : (⟨(0 : V → ℂ), analyticOnNhd_const⟩ : entireSubring V) = 0 := rfl
  rw [hz, map_zero]

end GaloisForLFunctions.HTGeometry
