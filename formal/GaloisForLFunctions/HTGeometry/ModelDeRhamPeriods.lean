import GaloisForLFunctions.HTGeometry.ManifoldDeRhamCohomology
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Analysis.Calculus.ContDiff.Basic
import GaloisForLFunctions.HTGeometry.NomologicalHomotopyGeometry.HigherPeriodSpencer
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Model-space forms and a concrete area-period geometry

Smooth model-space forms become actual manifold differential forms. The constant
determinant form on the real plane is closed and integrates to `ab` on an oriented
rectangle with sides `a,b`. These cell integrals supply every field of the local
period-geometry interface: their generated subgroup and its identity component are
the full coefficient line, and small squares have normalized limit one.

These are integrals over cells with boundary; no nonzero de Rham class on the
contractible plane is asserted.
-/

noncomputable section
open Bundle Manifold
open scoped Manifold ContDiff
namespace HTGeometry.SmoothDeRham
open DifferentialGeometry
attribute [local instance] normedSpaceTangentSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def ofModel {k : ℕ} (α : E → E [⋀^Fin k]→L[ℝ] ℝ) (hα : ContDiff ℝ ∞ α) :
    DifferentialForm 𝓘(ℝ, E) E k :=
  ⟨α, by
    intro x₀
    let e := trivializationAt (E [⋀^Fin k]→L[ℝ] ℝ)
      (Bundle.continuousAlternatingMap ℝ (Fin k) E (TangentSpace 𝓘(ℝ, E)) ℝ
        (Bundle.Trivial E ℝ)) x₀
    rw [Bundle.Trivialization.contMDiffAt_section_iff e
      (mem_baseSet_trivializationAt (E [⋀^Fin k]→L[ℝ] ℝ)
        (Bundle.continuousAlternatingMap ℝ (Fin k) E (TangentSpace 𝓘(ℝ, E)) ℝ
          (Bundle.Trivial E ℝ)) x₀)]
    have he (x : E) : (e ⟨x, α x⟩).2 = α x := by
      rw [continuousAlternatingMap_trivializationAt_apply]
      simp
      rfl
    simpa only [he] using hα.contMDiff.contMDiffAt⟩

def planeAreaAlternating : (Fin 2 → ℝ) [⋀^Fin 2]→L[ℝ] ℝ where
  toAlternatingMap := (Pi.basisFun ℝ (Fin 2)).det
  cont := by
    change Continuous (fun v : Fin 2 → Fin 2 → ℝ =>
      (Pi.basisFun ℝ (Fin 2)).det v)
    simp only [Module.Basis.det_apply, Module.Basis.toMatrix_apply, Pi.basisFun_repr, Matrix.det_fin_two]
    fun_prop

def planeAreaForm : DifferentialForm 𝓘(ℝ, Fin 2 → ℝ) (Fin 2 → ℝ) 2 :=
  ofModel (fun _ => planeAreaAlternating) contDiff_const

theorem planeAreaForm_apply (x : Fin 2 → ℝ) (v : Fin 2 → Fin 2 → ℝ) :
    planeAreaForm x v = v 0 0 * v 1 1 - v 1 0 * v 0 1 := by
  change (Pi.basisFun ℝ (Fin 2)).det v = _
  simp only [Module.Basis.det_apply, Module.Basis.toMatrix_apply, Pi.basisFun_repr, Matrix.det_fin_two]

theorem planeAreaForm_closed : DifferentialForm.exteriorDerivative planeAreaForm = 0 := by
  exact differentialForm_eq_zero_of_finrank_lt (by simp) _

open MeasureTheory Filter Set Topology
open NomologicalHomotopyGeometry.HigherPeriodSpencer

def rectangleAreaIntegral (s : ℝ × ℝ) : ℝ :=
  ∫ u in 0..s.1, ∫ v in 0..s.2,
    planeAreaForm ![u, v] ![![1, 0], ![0, 1]]

theorem rectangleAreaIntegral_eq (s : ℝ × ℝ) : rectangleAreaIntegral s = s.1 * s.2 := by
  simp [rectangleAreaIntegral, planeAreaForm_apply, intervalIntegral.integral_const]

theorem range_rectangleAreaIntegral : Set.range rectangleAreaIntegral = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  exact ⟨(x, 1), by simp [rectangleAreaIntegral_eq]⟩

def planeAreaPeriodGeometry : PeriodGeometry (V := ℝ) Unit (ℝ × ℝ) where
  arity := 2
  arity_ge_two := le_rfl
  curvatureValue _ := 1
  simplexIntegral := rectangleAreaIntegral
  simplexIntegral_mem_span s := by
    have h : (1 : ℝ) ∈ Submodule.span ℝ (Set.range (fun _ : Unit => (1 : ℝ))) :=
      Submodule.subset_span ⟨(), rfl⟩
    simpa using (Submodule.span ℝ (Set.range (fun _ : Unit => (1 : ℝ)))).smul_mem
      (rectangleAreaIntegral s) h
  restrictedAlgebra := ⊤
  restricted_carrier := by
    rw [range_rectangleAreaIntegral]
    simp
    rw [connectedComponentIn_univ, PreconnectedSpace.connectedComponent_eq_univ]
  smallSimplex _ t := (t, t)
  smallCell_zero _ := by simp [rectangleAreaIntegral_eq]
  smallCell_continuous _ := by
    simp only [rectangleAreaIntegral_eq]
    fun_prop
  smallCell_limit _ := by
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht' : t ≠ (0 : ℝ) := ht
    simp only [rectangleAreaIntegral_eq, pow_two, smul_eq_mul]
    field_simp

theorem planeAreaPeriods_span : planeAreaPeriodGeometry.curvatureSpan = ⊤ :=
  planeAreaPeriodGeometry.restrictedAlgebra_eq_curvatureSpan.symm

end HTGeometry.SmoothDeRham
