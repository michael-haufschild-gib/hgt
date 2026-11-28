import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.LocalLanglands.SmoothIrreducibleCentralCharacter
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.LinearAlgebra.Countable
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.Topology.Instances.Matrix

/-! Scalar matrices act through a unique smooth character on a
smooth irreducible general linear representation over a finite
completion. The number field is countable and dense. -/

noncomputable section

open NumberField IsDedekindDomain Matrix TopologicalSpace

namespace GlobalTheory.GLp

variable {F : Type} [Field F] [NumberField F] {n : ℕ}
  {V : Type} [AddCommGroup V] [Module ℂ V]

theorem exists_unique_smoothGLCentralCharacter (v : HeightOneSpectrum (𝓞 F))
    (ρ : Representation ℂ (GL (Fin n) (v.adicCompletion F)) V) [ρ.IsIrreducible]
    (hρ : ∀ x : V, IsOpen {g : GL (Fin n) (v.adicCompletion F) | ρ g x = x}) :
    ∃ ω : (v.adicCompletion F)ˣ →* ℂˣ, IsOpen (ω.ker : Set (v.adicCompletion F)ˣ) ∧
      (∀ z x, ρ (GeneralLinearGroup.scalar (Fin n) z) x = (ω z : ℂ) • x) ∧
      ∀ ω' : (v.adicCompletion F)ˣ →* ℂˣ,
        (∀ z x, ρ (GeneralLinearGroup.scalar (Fin n) z) x = (ω' z : ℂ) • x) → ω' = ω := by
  let L := v.adicCompletion F
  let M := Matrix (Fin n) (Fin n) L
  letI : Countable F := Finsupp.Countable.of_moduleFinite (R := ℚ)
  letI : SeparableSpace L := .of_denseRange (algebraMap F L) (HeightOneSpectrum.denseRange_algebraMap F v)
  letI : SecondCountableTopology L := inferInstance
  letI : SecondCountableTopology M := inferInstanceAs (SecondCountableTopology (Fin n → Fin n → L))
  letI : SecondCountableTopology Mᵐᵒᵖ :=
    (MulOpposite.opHomeomorph (M := M)).symm.isEmbedding.secondCountableTopology
  letI : SecondCountableTopology (GL (Fin n) L) :=
    (Units.isEmbedding_embedProduct (M := M)).secondCountableTopology
  have hc : Continuous (Matrix.scalar (Fin n) : L →+* M) := by
    apply continuous_matrix
    intro i j
    by_cases h : i = j
    · subst j
      simp only [Matrix.scalar_apply, Matrix.diagonal_apply_eq]
      exact continuous_id
    · simp only [Matrix.scalar_apply, Matrix.diagonal_apply_ne _ h]
      exact continuous_const
  have hcomm (z : Lˣ) (g : GL (Fin n) L) : Commute (GeneralLinearGroup.scalar (Fin n) z) g := by
    apply Units.ext
    apply Matrix.ext
    intro i j
    change (Matrix.diagonal (fun _ : Fin n => (z : L)) * g.val) i j =
      (g.val * Matrix.diagonal (fun _ : Fin n => (z : L))) i j
    rw [Matrix.diagonal_mul, Matrix.mul_diagonal, mul_comm]
  obtain ⟨ω, ho, ha⟩ := Representation.exists_smooth_centralCharacter ρ hρ
    (GeneralLinearGroup.scalar (Fin n)) (Units.continuous_map hc) hcomm
  refine ⟨ω, ho, ha, fun ω' hw => ?_⟩
  letI : Nontrivial V := IsSimpleModule.nontrivial (MonoidAlgebra ℂ (GL (Fin n) L)) ρ.asModule
  obtain ⟨x, hx⟩ := exists_ne (0 : V)
  exact MonoidHom.ext fun z => Units.ext (smul_left_injective ℂ hx ((hw z x).symm.trans (ha z x)))

end GlobalTheory.GLp

#print axioms GlobalTheory.GLp.exists_unique_smoothGLCentralCharacter
