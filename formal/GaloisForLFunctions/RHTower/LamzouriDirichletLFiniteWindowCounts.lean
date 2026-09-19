import GaloisForLFunctions.HilbertMetric.LamzouriSimpleOrSelectedMultiplicity
import GaloisForLFunctions.RHTower.DirichletLZeroDensityWindowSupport

/-!
# Lamzouri bounds on finite Dirichlet-L zero windows

The centered vertical-window support for a completed nonprincipal Dirichlet
L-function is already finite and carries its exact positive divisor
multiplicity.  This module applies the finite collision inequalities to it.
-/

open Finset Complex
open scoped BigOperators

namespace RHTower

open GaloisForLFunctions.HilbertMetric

noncomputable section

/-- Natural-valued analytic multiplicity on a centered completed-L window. -/
def cglZeroDensityVerticalWindowNatMultiplicity
    (n : ℕ) (χ : NonprincipalDirichletCharacter n) (σ τ : ℝ) (H : NNReal)
    (z : ℂ) : ℕ :=
  Int.toNat (cglZeroDensityVerticalWindowMultiplicity n χ σ τ H z)

/-- Total natural multiplicity of the finite completed-L window. -/
def cglWindowMultiplicityMass
    (n : ℕ) (χ : NonprincipalDirichletCharacter n) (σ τ : ℝ) (H : NNReal) : ℝ :=
  finiteMultiplicityMass
    (cglZeroDensityVerticalWindowZeroSupport n χ σ τ H)
    (cglZeroDensityVerticalWindowNatMultiplicity n χ σ τ H)

/-- Diagonal collision energy of the finite completed-L divisor. -/
def cglWindowCollisionMass
    (n : ℕ) (χ : NonprincipalDirichletCharacter n) (σ τ : ℝ) (H : NNReal) : ℝ :=
  finiteMultiplicityCollisionMass
    (cglZeroDensityVerticalWindowZeroSupport n χ σ τ H)
    (cglZeroDensityVerticalWindowNatMultiplicity n χ σ τ H)

/-- Simple support of the finite completed-L divisor. -/
def cglWindowSimpleSupport
    (n : ℕ) (χ : NonprincipalDirichletCharacter n) (σ τ : ℝ) (H : NNReal) :
    Finset ℂ :=
  finiteSimpleMultiplicitySupport
    (cglZeroDensityVerticalWindowZeroSupport n χ σ τ H)
    (cglZeroDensityVerticalWindowNatMultiplicity n χ σ τ H)

/-- Multiplicity mass of completed-L zeros that are simple or lie on the
critical line. -/
def cglWindowSimpleOrCriticalMass
    (n : ℕ) (χ : NonprincipalDirichletCharacter n) (σ τ : ℝ) (H : NNReal) : ℝ :=
  finiteSimpleOrSelectedMultiplicityMass
    (cglZeroDensityVerticalWindowZeroSupport n χ σ τ H)
    (cglZeroDensityVerticalWindowNatMultiplicity n χ σ τ H)
    (fun z => z.re = 1 / 2)

/-- Critical-line mass in the window carried by non-simple zeros. -/
def cglWindowCriticalNonsimpleMass
    (n : ℕ) (χ : NonprincipalDirichletCharacter n) (σ τ : ℝ) (H : NNReal) : ℝ :=
  finiteSelectedNonsimpleMultiplicityMass
    (cglZeroDensityVerticalWindowZeroSupport n χ σ τ H)
    (cglZeroDensityVerticalWindowNatMultiplicity n χ σ τ H)
    (fun z => z.re = 1 / 2)

/-- The natural multiplicity mass is the corpus's literal divisor count. -/
theorem cglWindowMultiplicityMass_eq_count
    (n : ℕ) (χ : NonprincipalDirichletCharacter n) (σ τ : ℝ) (H : NNReal) :
    cglWindowMultiplicityMass n χ σ τ H =
      completedLFunctionZeroDensityVerticalWindowCount n χ σ τ H := by
  rw [completedLFunction_zeroDensityVerticalWindowCount_eq_sum_multiplicity]
  unfold cglWindowMultiplicityMass finiteMultiplicityMass
    cglZeroDensityVerticalWindowNatMultiplicity
  apply Finset.sum_congr rfl
  intro z hz
  have hnonneg :
      0 ≤ cglZeroDensityVerticalWindowMultiplicity n χ σ τ H z :=
    le_of_lt (cglZeroDensityVerticalWindowMultiplicity_pos n χ σ τ H z hz)
  exact_mod_cast Int.toNat_of_nonneg hnonneg

/-- Montgomery's simple-zero inequality for every completed nonprincipal
Dirichlet-L finite window. -/
theorem cglWindowSimpleSupport_lower
    (n : ℕ) (χ : NonprincipalDirichletCharacter n) (σ τ : ℝ) (H : NNReal) :
    2 * cglWindowMultiplicityMass n χ σ τ H -
        cglWindowCollisionMass n χ σ τ H ≤
      (cglWindowSimpleSupport n χ σ τ H).card := by
  exact finiteSimpleMultiplicitySupport_lower
    (cglZeroDensityVerticalWindowZeroSupport n χ σ τ H)
    (cglZeroDensityVerticalWindowNatMultiplicity n χ σ τ H)

/-- Lamzouri's distinct-support inequality for every completed-L window. -/
theorem cglWindowDistinctSupport_lower
    (n : ℕ) (χ : NonprincipalDirichletCharacter n) (σ τ : ℝ) (H : NNReal) :
    (3 / 2 : ℝ) * cglWindowMultiplicityMass n χ σ τ H -
        (1 / 2 : ℝ) * cglWindowCollisionMass n χ σ τ H ≤
      (cglZeroDensityVerticalWindowZeroSupport n χ σ τ H).card := by
  have h := finitePositiveMultiplicitySupport_lower
    (cglZeroDensityVerticalWindowZeroSupport n χ σ τ H)
    (cglZeroDensityVerticalWindowNatMultiplicity n χ σ τ H)
  have hs : finitePositiveMultiplicitySupport
      (cglZeroDensityVerticalWindowZeroSupport n χ σ τ H)
      (cglZeroDensityVerticalWindowNatMultiplicity n χ σ τ H) =
      cglZeroDensityVerticalWindowZeroSupport n χ σ τ H := by
    unfold finitePositiveMultiplicitySupport
    rw [Finset.filter_eq_self]
    intro z hz
    unfold cglZeroDensityVerticalWindowNatMultiplicity
    have hpos := cglZeroDensityVerticalWindowMultiplicity_pos n χ σ τ H z hz
    have hnz : Int.toNat
        (cglZeroDensityVerticalWindowMultiplicity n χ σ τ H z) ≠ 0 := by
      intro hzero
      have hnonpos := Int.toNat_eq_zero.mp hzero
      omega
    exact Nat.pos_of_ne_zero hnz
  simpa only [cglWindowMultiplicityMass, cglWindowCollisionMass, hs] using h

/-- The diagonal collision mass dominates total completed-L multiplicity. -/
theorem cglWindowMultiplicityMass_le_collisionMass
    (n : ℕ) (χ : NonprincipalDirichletCharacter n) (σ τ : ℝ) (H : NNReal) :
    cglWindowMultiplicityMass n χ σ τ H ≤
      cglWindowCollisionMass n χ σ τ H := by
  exact finiteMultiplicityMass_le_collisionMass
    (cglZeroDensityVerticalWindowZeroSupport n χ σ τ H)
    (cglZeroDensityVerticalWindowNatMultiplicity n χ σ τ H)

/-- Simple-or-critical completed-L mass gains every repeated critical-line
copy over the baseline simple-zero collision bound. -/
theorem cglWindowSimpleOrCriticalMass_lower
    (n : ℕ) (χ : NonprincipalDirichletCharacter n) (σ τ : ℝ) (H : NNReal) :
    2 * cglWindowMultiplicityMass n χ σ τ H -
        cglWindowCollisionMass n χ σ τ H +
        cglWindowCriticalNonsimpleMass n χ σ τ H ≤
      cglWindowSimpleOrCriticalMass n χ σ τ H := by
  exact finiteSimpleOrSelectedMultiplicityMass_lower
    (cglZeroDensityVerticalWindowZeroSupport n χ σ τ H)
    (cglZeroDensityVerticalWindowNatMultiplicity n χ σ τ H)
    (fun z => z.re = 1 / 2)

end

end RHTower
