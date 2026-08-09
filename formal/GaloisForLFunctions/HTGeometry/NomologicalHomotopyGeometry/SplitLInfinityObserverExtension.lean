import GaloisForLFunctions.HTGeometry.NomologicalHomotopyGeometry.CyclicAInfinityLaw
import Mathlib.Tactic.Module

/-!
# Split `L∞` observer extensions and nonlinear Gauss--Codazzi

Relative coderivations are represented as a bracket-closed submodule of the actual completed-law
endomorphism algebra developed in `CyclicAInfinityLaw`.  The square of `Q₀ + τ` is expanded
without assumptions on the conclusion, giving the Maurer--Cartan extension equation, its
bidegree-resolved hierarchy, gauge covariance, exact split-product criterion, cyclic extension
action, Euler--Lagrange equation, and Bianchi identity.  A concrete affine Lie bracket proves that
pure-horizontal components can vanish while mixed vertical transport remains nonzero.
-/

namespace HTGeometry.NomologicalHomotopyGeometry.SplitLInfinityObserverExtension

open CyclicAInfinityLaw.QGeometry

variable {C : Type*} [AddCommGroup C] [Module ℝ C]

abbrev End := Module.End ℝ C

/-- Square expansion for a split background law plus a relative extension field. -/
theorem square_add (Q₀ τ : End (C := C)) :
    square (Q₀ + τ) = square Q₀ + dOdd Q₀ τ + square τ := by
  apply LinearMap.ext
  intro x
  simp [square, dOdd, LinearMap.comp_apply]
  module

/-- Relative coderivation sector of a split observer extension. -/
structure RelativeExtensionField where
  Q₀ : End (C := C)
  τ : End (C := C)
  relative : Submodule ℝ (End (C := C))
  q₀_square_zero : square Q₀ = 0
  τ_relative : τ ∈ relative
  differential_closed : ∀ D ∈ relative, dOdd Q₀ D ∈ relative
  odd_bracket_closed : ∀ D ∈ relative, ∀ E ∈ relative, oddBracket D E ∈ relative

namespace RelativeExtensionField

variable (F : RelativeExtensionField (C := C))

/-- Total split extension coderivation. -/
def totalLaw : End (C := C) := F.Q₀ + F.τ

/-- Maurer--Cartan residual of the relative extension field. -/
noncomputable def mcResidual : End (C := C) :=
  dOdd F.Q₀ F.τ + (2 : ℝ)⁻¹ • oddBracket F.τ F.τ

/-- The extension Maurer--Cartan residual remains a relative coderivation. -/
theorem mcResidual_relative : F.mcResidual ∈ F.relative := by
  apply F.relative.add_mem (F.differential_closed F.τ F.τ_relative)
  apply F.relative.smul_mem
  exact F.odd_bracket_closed F.τ F.τ_relative F.τ F.τ_relative

/-- Split nonlinear observer theorem: total square-zero is equivalent to the relative
Maurer--Cartan equation. -/
theorem total_square_zero_iff_mc :
    square F.totalLaw = 0 ↔ F.mcResidual = 0 := by
  rw [totalLaw, square_add, F.q₀_square_zero, zero_add, mcResidual,
    half_oddBracket_self]

/-- Exact declared-splitting product criterion. -/
theorem extension_eq_background_iff : F.totalLaw = F.Q₀ ↔ F.τ = 0 := by
  rw [totalLaw, add_eq_left]

/-- Both parity pieces of the background deformation differential square to zero. -/
theorem background_deformation_complex :
    (dOdd F.Q₀).comp (dEven F.Q₀) = 0 ∧
      (dEven F.Q₀).comp (dOdd F.Q₀) = 0 :=
  ⟨dOdd_comp_dEven F.Q₀ F.q₀_square_zero,
    dEven_comp_dOdd F.Q₀ F.q₀_square_zero⟩

/-- Bidegree projections of the relative coderivation algebra. -/
structure Bigrading where
  component : ℕ × ℕ → End (C := C) →ₗ[ℝ] End (C := C)
  detects_zero : ∀ D, (∀ degree, component degree D = 0) → D = 0

/-- Maurer--Cartan is exactly the complete nonlinear Gauss--Codazzi--Ricci hierarchy resolved in
every input bidegree. -/
theorem mc_iff_bidegree_hierarchy (B : Bigrading (C := C)) :
    F.mcResidual = 0 ↔ ∀ degree, B.component degree F.mcResidual = 0 := by
  constructor
  · intro h degree
    rw [h, map_zero]
  · exact B.detects_zero F.mcResidual

/-- Pure-horizontal projections alone are complete only when they detect every relative
coderivation, including mixed components. -/
theorem horizontal_complete_of_detects
    (horizontal : ℕ → End (C := C) →ₗ[ℝ] End (C := C))
    (hdetect : ∀ D ∈ F.relative, (∀ b, horizontal b D = 0) → D = 0)
    (hzero : ∀ b, horizontal b F.τ = 0) :
    F.τ = 0 :=
  hdetect F.τ F.τ_relative hzero

end RelativeExtensionField

section Gauge

/-- A filtration-unipotent change of split presentation, expressed by its linear automorphism on
the completed carrier and the two exact relative-preservation properties. -/
structure RelativeGauge (F : RelativeExtensionField (C := C)) where
  carrierEquiv : C ≃ₗ[ℝ] C
  backgroundDefect_relative :
    (carrierEquiv.toLinearMap.comp F.Q₀).comp carrierEquiv.symm.toLinearMap - F.Q₀ ∈ F.relative
  conjugate_relative : ∀ D ∈ F.relative,
    (carrierEquiv.toLinearMap.comp D).comp carrierEquiv.symm.toLinearMap ∈ F.relative

namespace RelativeGauge

variable {F : RelativeExtensionField (C := C)} (G : RelativeGauge F)

/-- Conjugation of a completed law operator. -/
def conjugate (D : End (C := C)) : End (C := C) :=
  (G.carrierEquiv.toLinearMap.comp D).comp G.carrierEquiv.symm.toLinearMap

/-- Relative field in the changed split presentation. -/
def transformedField : End (C := C) :=
  G.conjugate F.totalLaw - F.Q₀

/-- Change of splitting preserves the relative coderivation sector. -/
theorem transformedField_relative : G.transformedField ∈ F.relative := by
  rw [transformedField, RelativeExtensionField.totalLaw]
  have hconjAdd : G.conjugate (F.Q₀ + F.τ) = G.conjugate F.Q₀ + G.conjugate F.τ := by
    apply LinearMap.ext
    intro x
    simp [conjugate, LinearMap.comp_apply]
  rw [hconjAdd]
  have hrelative := F.relative.add_mem G.backgroundDefect_relative
    (G.conjugate_relative F.τ F.τ_relative)
  change (G.conjugate F.Q₀ - F.Q₀) + G.conjugate F.τ ∈ F.relative at hrelative
  rw [show G.conjugate F.Q₀ + G.conjugate F.τ - F.Q₀ =
    (G.conjugate F.Q₀ - F.Q₀) + G.conjugate F.τ by abel]
  exact hrelative

/-- Conjugation transports composition squares. -/
theorem conjugate_square (D : End (C := C)) :
    square (G.conjugate D) = G.conjugate (square D) := by
  apply LinearMap.ext
  intro x
  simp [square, conjugate, LinearMap.comp_apply]

/-- Gauge changes preserve and reflect the square-zero extension equation. -/
theorem transformed_square_zero_iff :
    square (G.conjugate F.totalLaw) = 0 ↔ square F.totalLaw = 0 := by
  rw [G.conjugate_square]
  constructor
  · intro h
    apply LinearMap.ext
    intro x
    have hx := LinearMap.congr_fun h (G.carrierEquiv x)
    simpa [conjugate, LinearMap.comp_apply] using hx
  · intro h
    rw [h]
    apply LinearMap.ext
    intro x
    simp [conjugate]

end RelativeGauge

end Gauge

section CyclicAction

/-- Cyclic DGLA identities needed by the extension Chern--Simons action. -/
structure CyclicExtensionLaw extends RelativeExtensionField (C := C) where
  pairing : End (C := C) →ₗ[ℝ] End (C := C) →ₗ[ℝ] ℝ
  pairing_nondegenerate : ∀ D, (∀ E, pairing E D = 0) → D = 0
  differential_cyclic : ∀ τ η, pairing τ (dOdd Q₀ η) = pairing η (dOdd Q₀ τ)
  bracket_cyclic_left : ∀ τ η, pairing τ (oddBracket η τ) = pairing η (oddBracket τ τ)
  bracket_cyclic_right : ∀ τ η, pairing τ (oddBracket τ η) = pairing η (oddBracket τ τ)

namespace CyclicExtensionLaw

variable (A : CyclicExtensionLaw (C := C))

/-- Cubic cyclic extension action. -/
noncomputable def action (τ : End (C := C)) : ℝ :=
  (2 : ℝ)⁻¹ * A.pairing τ (dOdd A.Q₀ τ) +
    (6 : ℝ)⁻¹ * A.pairing τ (oddBracket τ τ)

/-- Algebraic first variation of the cubic extension action. -/
noncomputable def firstVariation (τ η : End (C := C)) : ℝ :=
  (2 : ℝ)⁻¹ *
      (A.pairing η (dOdd A.Q₀ τ) + A.pairing τ (dOdd A.Q₀ η)) +
    (6 : ℝ)⁻¹ *
      (A.pairing η (oddBracket τ τ) + A.pairing τ (oddBracket η τ) +
        A.pairing τ (oddBracket τ η))

/-- Variation of the cyclic extension action pairs with the Maurer--Cartan residual. -/
theorem firstVariation_eq_pair_mc (τ η : End (C := C)) :
    A.firstVariation τ η =
      A.pairing η (dOdd A.Q₀ τ + (2 : ℝ)⁻¹ • oddBracket τ τ) := by
  rw [firstVariation, A.differential_cyclic τ η, A.bracket_cyclic_left τ η,
    A.bracket_cyclic_right τ η, map_add, LinearMap.map_smul]
  ring

/-- Nondegeneracy identifies the critical locus with the extension Maurer--Cartan locus. -/
theorem critical_iff_mc (τ : End (C := C)) :
    (∀ η, A.firstVariation τ η = 0) ↔
      dOdd A.Q₀ τ + (2 : ℝ)⁻¹ • oddBracket τ τ = 0 := by
  rw [show (∀ η, A.firstVariation τ η = 0) ↔
      ∀ η, A.pairing η (dOdd A.Q₀ τ + (2 : ℝ)⁻¹ • oddBracket τ τ) = 0 by
    simp_rw [A.firstVariation_eq_pair_mc]]
  exact ⟨A.pairing_nondegenerate _, fun h η => by rw [h, map_zero]⟩

/-- Twisted Bianchi identity for the total extension square. -/
theorem total_square_bianchi :
    (A.totalLaw.comp (square A.totalLaw)) -
      ((square A.totalLaw).comp A.totalLaw) = 0 := by
  apply LinearMap.ext
  intro x
  simp [RelativeExtensionField.totalLaw, square, LinearMap.comp_apply]

end CyclicExtensionLaw

end CyclicAction

section Countermodel

/-- Affine semidirect Lie bracket on a split two-dimensional carrier `(vertical, horizontal)`. -/
def affineBracket (x y : ℝ × ℝ) : ℝ × ℝ :=
  (x.2 * y.1 - y.2 * x.1, 0)

/-- Every pure-horizontal bracket vanishes in the affine countermodel. -/
theorem affine_pureHorizontal_zero (x y : ℝ) :
    affineBracket (0, x) (0, y) = 0 := by
  simp [affineBracket]

/-- A mixed vertical-horizontal component remains nonzero. -/
theorem affine_mixed_nonzero :
    affineBracket (0, 1) (1, 0) ≠ 0 := by
  intro h
  have := congrArg Prod.fst h
  norm_num [affineBracket] at this

/-- Vanishing horizontal curvature does not imply a direct-product observer extension. -/
theorem horizontal_curvature_incomplete :
    (∀ x y : ℝ, affineBracket (0, x) (0, y) = 0) ∧
      affineBracket (0, 1) (1, 0) ≠ 0 :=
  ⟨affine_pureHorizontal_zero, affine_mixed_nonzero⟩

end Countermodel

end HTGeometry.NomologicalHomotopyGeometry.SplitLInfinityObserverExtension
