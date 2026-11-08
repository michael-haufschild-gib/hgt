import GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.NarainMirrorSymmetry
import GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.NarainModularity

/-!
# Independent modularity of the three Narain moduli

Target mirror symmetry and Poisson triality exchange the three upper-half-plane variables. Worldsheet modularity therefore acts independently in every variable.
-/

open Complex RHTower UpperHalfPlane
open scoped MatrixGroups
open GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap
set_option autoImplicit false
noncomputable section
namespace GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap

/-- The partition viewed symmetrically on three copies of the upper half-plane. -/
def narainThreeModuli (ρ σ τ : UpperHalfPlane) : ℂ :=
  narainPartitionOnUpperHalfPlane ⟨ρ.re, ρ.im, ρ.im_pos⟩ ⟨σ.re, σ.im, σ.im_pos⟩ τ

theorem narainThreeModuli_swap_targets (ρ σ τ : UpperHalfPlane) :
    narainThreeModuli ρ σ τ = narainThreeModuli σ ρ τ :=
  narainPartition_mirror _ _ _ _

theorem narainThreeModuli_swap_area_worldsheet (ρ σ τ : UpperHalfPlane) :
    narainThreeModuli ρ σ τ = narainThreeModuli τ σ ρ :=
  narainPartition_triality ⟨ρ.re, ρ.im, ρ.im_pos⟩
    ⟨σ.re, σ.im, σ.im_pos⟩ ⟨τ.re, τ.im, τ.im_pos⟩

/-- Mirror exchange and Poisson triality also exchange shape and worldsheet moduli. -/
theorem narainThreeModuli_swap_shape_worldsheet (ρ σ τ : UpperHalfPlane) :
    narainThreeModuli ρ σ τ = narainThreeModuli ρ τ σ := by
  calc
    _ = narainThreeModuli σ ρ τ := narainThreeModuli_swap_targets ρ σ τ
    _ = narainThreeModuli τ ρ σ := narainThreeModuli_swap_area_worldsheet σ ρ τ
    _ = _ := narainThreeModuli_swap_targets τ ρ σ

theorem narainThreeModuli_modular_worldsheet (ρ σ τ : UpperHalfPlane) (γ : SL(2, ℤ)) :
    narainThreeModuli ρ σ (γ • τ) = narainThreeModuli ρ σ τ :=
  narainPartitionOnUpperHalfPlane_modular _ _ γ τ

theorem narainThreeModuli_modular_area (ρ σ τ : UpperHalfPlane) (γ : SL(2, ℤ)) :
    narainThreeModuli (γ • ρ) σ τ = narainThreeModuli ρ σ τ := by
  rw [narainThreeModuli_swap_area_worldsheet, narainThreeModuli_modular_worldsheet,
    narainThreeModuli_swap_area_worldsheet]

theorem narainThreeModuli_modular_shape (ρ σ τ : UpperHalfPlane) (γ : SL(2, ℤ)) :
    narainThreeModuli ρ (γ • σ) τ = narainThreeModuli ρ σ τ := by
  rw [narainThreeModuli_swap_targets, narainThreeModuli_modular_area,
    narainThreeModuli_swap_targets]

/-- Each of the three modular transformations acts independently on the actual partition. -/
theorem narainThreeModuli_modular (ρ σ τ : UpperHalfPlane) (γρ γσ γτ : SL(2, ℤ)) :
    narainThreeModuli (γρ • ρ) (γσ • σ) (γτ • τ) = narainThreeModuli ρ σ τ := by
  rw [narainThreeModuli_modular_area, narainThreeModuli_modular_shape,
    narainThreeModuli_modular_worldsheet]

#print axioms narainThreeModuli_swap_targets
#print axioms narainThreeModuli_swap_shape_worldsheet
#print axioms narainThreeModuli_modular
end GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap
