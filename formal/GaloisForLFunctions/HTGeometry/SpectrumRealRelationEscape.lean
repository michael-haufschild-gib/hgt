import GaloisForLFunctions.HTGeometry.RealRelationRootPacketBridge
import GaloisForLFunctions.HTGeometry.RealAffineHermitianFamilyProjectiveGenericity

/-!
# Families whose spectra escape every real relation

A single Hamiltonian can never certify that no real linear relation holds among its energies: at a
fixed spectrum the coefficient vectors annihilating it form a hyperplane.  What *can* be certified
by one Hamiltonian is that a **given** relation fails, in every relabelling.  Quantifying that over
all nonzero balanced coefficient vectors is the right hypothesis on a family, and it is exactly what
the labelling-orbit obstruction converts into a global statement about the parameters.

## Main results

* `SpectrumEscapesRealRelations` — the escape property of a set of Hamiltonians.
* `SpectrumEscapesRealRelations.mono` — it only improves when the set grows.
* `not_relation_on_open_of_spectrumEscapes` — **(L2) for a real-affine Hermitian family**: no
  nonzero balanced real relation among the energies can hold identically on a nonempty open set of
  parameters.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- A set of matrices **escapes real relations** when for every nonzero balanced real coefficient
vector some member has a simple real characteristic-root packet on which *every* relabelling of the
relation is nonzero. -/
def SpectrumEscapesRealRelations {I : Type*} [Fintype I] [DecidableEq I]
    (S : Set (Matrix I I ℂ)) : Prop :=
  ∀ c : I → ℝ, ∑ i, c i = 0 → c ≠ 0 →
    ∃ H ∈ S, ∃ E : I → ℝ,
      Function.Injective E ∧
      (∀ i, matrixCharpolyRelation (H, ((E i : ℝ) : ℂ)) = 0) ∧
      ∀ σ : Equiv.Perm I, ∑ i, c i * E (σ i) ≠ 0

theorem SpectrumEscapesRealRelations.mono {I : Type*} [Fintype I] [DecidableEq I]
    {S T : Set (Matrix I I ℂ)} (hS : SpectrumEscapesRealRelations S) (hST : S ⊆ T) :
    SpectrumEscapesRealRelations T := by
  intro c hbalanced hc
  obtain ⟨H, hHS, E, hinj, hroot, hesc⟩ := hS c hbalanced hc
  exact ⟨H, hST hHS, E, hinj, hroot, hesc⟩

/-- **(L2) for a real-affine Hermitian family.**  If the family realizes, for every nonzero balanced
real coefficient vector, one Hamiltonian whose simple spectrum escapes every relabelling of that
relation, then no such relation can annihilate the spectrum throughout a nonempty open set of
parameters.

Only one escaping Hamiltonian is needed per coefficient vector: the labelling-orbit obstruction is a
polynomial in the parameters, so vanishing on a nonempty open set would force it to vanish
identically. -/
theorem not_relation_on_open_of_spectrumEscapes
    {m : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (base : Matrix I I ℂ) (generator : Fin m → Matrix I I ℂ)
    (hS : SpectrumEscapesRealRelations (Set.range (realAffineMatrix base generator)))
    {c : I → ℝ} (hbalanced : ∑ i, c i = 0) (hc : c ≠ 0)
    {U : Set (Fin m → ℝ)} (hU : IsOpen U) (hUne : U.Nonempty)
    (spec : (Fin m → ℝ) → I → ℝ)
    (hinj : ∀ q ∈ U, Function.Injective (spec q))
    (hroot : ∀ q ∈ U, ∀ i,
      matrixCharpolyRelation (realAffineMatrix base generator q, ((spec q i : ℝ) : ℂ)) = 0)
    (hrel : ∀ q ∈ U, ∑ i, c i * spec q i = 0) : False := by
  obtain ⟨H, ⟨p₀, hp₀⟩, E, hEinj, hEroot, hEesc⟩ := hS c hbalanced hc
  refine not_relation_on_open_of_rootPacket_escape
    (realAffineMatrixPolynomial base generator) p₀ E hEinj ?_ hEesc hU hUne spec hinj ?_ hrel
  · intro i
    rw [eval_realAffineMatrixPolynomial, hp₀]
    exact hEroot i
  · intro q hq i
    rw [eval_realAffineMatrixPolynomial]
    exact hroot q hq i

end

end GaloisForLFunctions.HTGeometry
