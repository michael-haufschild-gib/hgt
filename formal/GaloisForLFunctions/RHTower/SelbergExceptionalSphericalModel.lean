import GaloisForLFunctions.RHTower.SphericalExponentPacketUnitarity
import GaloisForLFunctions.RHTower.RealSphericalIrreducibility

/-!
# Exceptional Selberg eigenvalues and spherical complementary models

This file closes the scalar-to-local portion of the symmetric-power route.  An eigenvalue
`0 < λ < 1/4` canonically determines `ν = sqrt(1/4-λ) ∈ (0,1/2)`.  The corresponding spherical
model is irreducible and unitarizable, and its shifted Casimir is exactly `λ`.

Because `ν` is nonzero, the exact packet theorems imply that some positive symmetric-power degree,
and already some positive even degree, fails the explicit spherical packet unitarity test.  An
automorphic proof would exclude the exceptional eigenvalue by supplying compatible unitary lifts
in every such degree; existence of those lifts for arbitrary Maass forms is the open input.
-/

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- A real scalar strictly inside the exceptional Selberg eigenvalue interval. -/
def SelbergExceptionalEigenvalue := {eigenvalue : ℝ //
  0 < eigenvalue ∧ eigenvalue < 1 / 4}

/-- Complementary exponent `sqrt(1/4-λ)` attached to an exceptional eigenvalue. -/
def SelbergExceptionalEigenvalue.complementaryExponent
    (eigenvalue : SelbergExceptionalEigenvalue) : ℝ :=
  Real.sqrt (1 / 4 - eigenvalue.1)

theorem SelbergExceptionalEigenvalue.complementaryExponent_mem_Ioo
    (eigenvalue : SelbergExceptionalEigenvalue) :
    eigenvalue.complementaryExponent ∈ Set.Ioo 0 (1 / 2) := by
  constructor
  · exact Real.sqrt_pos.mpr (by linarith [eigenvalue.2.2])
  · have hsqrt : Real.sqrt (1 / 4 - eigenvalue.1) < Real.sqrt (1 / 4) :=
      Real.sqrt_lt_sqrt (by linarith [eigenvalue.2.2]) (by linarith [eigenvalue.2.1])
    norm_num at hsqrt
    exact hsqrt

/-- The complementary exponent recovers the original exceptional eigenvalue exactly. -/
theorem SelbergExceptionalEigenvalue.eigenvalueOfComplementaryExponent_eq
    (eigenvalue : SelbergExceptionalEigenvalue) :
    eigenvalueOfComplementaryExponent eigenvalue.complementaryExponent = eigenvalue.1 := by
  rw [eigenvalueOfComplementaryExponent,
    SelbergExceptionalEigenvalue.complementaryExponent]
  rw [Real.sq_sqrt (by linarith [eigenvalue.2.2])]
  ring

/-- The associated spherical rank-one model lies in the complementary-series unitarity interval. -/
theorem SelbergExceptionalEigenvalue.localParameter_unitarizable
    (eigenvalue : SelbergExceptionalEigenvalue) :
    2 * eigenvalue.complementaryExponent ∈
      UnitarizableSphericalPrincipalParameter := by
  have hν := eigenvalue.complementaryExponent_mem_Ioo
  rw [unitarizableSphericalPrincipalParameter_eq_Ioo]
  rcases hν with ⟨hpos, hhalf⟩
  constructor <;> linarith

/-- Its shifted Casimir acts by the original exceptional Laplace eigenvalue. -/
theorem SelbergExceptionalEigenvalue.sphericalPrincipalLaplacian_eq
    (eigenvalue : SelbergExceptionalEigenvalue) :
    sphericalPrincipalLaplacian
        ((2 * eigenvalue.complementaryExponent : ℝ) : ℂ) =
      (eigenvalue.1 : ℂ) • LinearMap.id := by
  rw [sphericalPrincipalLaplacian_two_mul_eq_eigenvalue,
    eigenvalue.eigenvalueOfComplementaryExponent_eq]

/-- The associated spherical complementary-series Harish-Chandra module is irreducible. -/
theorem SelbergExceptionalEigenvalue.sphericalPrincipal_irreducible
    (eigenvalue : SelbergExceptionalEigenvalue) :
    ∀ W : Submodule ℂ SphericalKFiniteModel,
      IsSphericalHarishChandraSubmodule
          (2 * eigenvalue.complementaryExponent) W →
        W = ⊥ ∨ W = ⊤ := by
  apply sphericalPrincipal_irreducible_of_abs_lt_one
  have hν := eigenvalue.complementaryExponent_mem_Ioo
  rcases hν with ⟨hpos, hhalf⟩
  rw [abs_lt]
  constructor <;> linarith

/-- Every exceptional eigenvalue fails the explicit local unitarity test in some positive
symmetric-power degree. -/
theorem SelbergExceptionalEigenvalue.exists_nonunitarizable_symmetricPower_degree
    (eigenvalue : SelbergExceptionalEigenvalue) :
    ∃ d : ℕ, ¬SymmetricPowerSphericalPacketUnitarizable
      eigenvalue.complementaryExponent (d + 1) := by
  by_contra h
  have h' : ∀ d : ℕ, SymmetricPowerSphericalPacketUnitarizable
      eigenvalue.complementaryExponent (d + 1) :=
    fun d ↦ Classical.not_not.mp (not_exists.mp h d)
  have hmem : eigenvalue.complementaryExponent ∈
      {ν : ℝ | ∀ d : ℕ, SymmetricPowerSphericalPacketUnitarizable ν (d + 1)} := h'
  rw [all_degree_symmetricPowerSphericalPacketUnitarizable] at hmem
  have hzero : eigenvalue.complementaryExponent = 0 := by simpa using hmem
  linarith [eigenvalue.complementaryExponent_mem_Ioo.1]

/-- Some positive even symmetric-power degree already fails the explicit local unitarity test. -/
theorem SelbergExceptionalEigenvalue.exists_nonunitarizable_even_symmetricPower_degree
    (eigenvalue : SelbergExceptionalEigenvalue) :
    ∃ d : ℕ, ¬SymmetricPowerSphericalPacketUnitarizable
      eigenvalue.complementaryExponent (2 * (d + 1)) := by
  by_contra h
  have h' : ∀ d : ℕ, SymmetricPowerSphericalPacketUnitarizable
      eigenvalue.complementaryExponent (2 * (d + 1)) :=
    fun d ↦ Classical.not_not.mp (not_exists.mp h d)
  have hmem : eigenvalue.complementaryExponent ∈
      {ν : ℝ | ∀ d : ℕ,
        SymmetricPowerSphericalPacketUnitarizable ν (2 * (d + 1))} := h'
  rw [all_even_degree_symmetricPowerSphericalPacketUnitarizable] at hmem
  have hzero : eigenvalue.complementaryExponent = 0 := by simpa using hmem
  linarith [eigenvalue.complementaryExponent_mem_Ioo.1]

end
end GaloisForLFunctions.RHTower
