import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalGLCentralCharacter
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.LocalLanglands.SmoothRepresentationScalarTwist
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.LocalLanglands.BlockUnipotentRadicals
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.LocalLanglands.SmoothIrreducibleClass
import Mathlib.Topology.Algebra.Group.Matrix

/-! In rank one every matrix is scalar. A smooth irreducible
representation therefore comes from its smooth central character. -/

noncomputable section

open Matrix NumberField IsDedekindDomain Representation
open GlobalTheory.PRep

namespace GlobalTheory.GLp

variable {k : Type} [Field k]

theorem scalar_det_fin_one (g : GL (Fin 1) k) : GeneralLinearGroup.scalar (Fin 1) g.det = g := by
  apply Units.ext
  apply Matrix.ext
  intro i j
  have hi : i = 0 := Subsingleton.elim _ _
  have hj : j = 0 := Subsingleton.elim _ _
  subst i j
  simp [Matrix.scalar_apply, Matrix.det_fin_one]

/-- The scalar action of a character pulled back along determinant. -/
def rankOneCharacter (χ : kˣ →* ℂˣ) : Representation ℂ (GL (Fin 1) k) ℂ :=
  (Representation.trivial ℂ (GL (Fin 1) k) ℂ).scalarTwist (χ.comp GeneralLinearGroup.det)

@[simp] theorem rankOneCharacter_apply (χ : kˣ →* ℂˣ) (g : GL (Fin 1) k) (x : ℂ) :
    rankOneCharacter χ g x = (χ g.det : ℂ) * x := rfl

theorem rankOneCharacter_irreducible (χ : kˣ →* ℂˣ) : (rankOneCharacter χ).IsIrreducible := by
  letI : Nontrivial (Subrepresentation (rankOneCharacter χ)) :=
    ⟨⊥, ⊤, fun he => bot_ne_top (congrArg Subrepresentation.toSubmodule he)⟩
  refine ⟨fun U => ?_⟩
  by_cases hU : U = ⊥
  · exact Or.inl hU
  right
  apply Subrepresentation.toSubmodule_injective
  change U.toSubmodule = ⊤
  have hn : U.toSubmodule ≠ ⊥ := fun he => hU (Subrepresentation.toSubmodule_injective he)
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hn
  apply eq_top_iff.mpr
  intro x _
  have hx := U.toSubmodule.smul_mem (x / a) ha
  rwa [smul_eq_mul, div_mul_cancel₀ _ ha0] at hx

/-- The smooth irreducible rank-one representation associated to a character. -/
def rankOneIrrRep [TopologicalSpace k] [IsTopologicalRing k] (χ : kˣ →* ℂˣ)
    (hχ : IsOpen (χ.ker : Set kˣ)) : IrrRep (GL (Fin 1) k) where
  V := ℂ
  ρ := rankOneCharacter χ
  smooth := scalarTwist_smooth _ (fun x => by simpa only [trivial_apply, Set.setOf_true] using isOpen_univ) _
    (hχ.preimage GeneralLinearGroup.continuous_det)
  irr := rankOneCharacter_irreducible χ

theorem rankOneIrrRep_cuspidal [TopologicalSpace k] [IsTopologicalRing k] (χ : kˣ →* ℂˣ)
    (hχ : IsOpen (χ.ker : Set kˣ)) : IsSmoothCuspidal (rankOneIrrRep χ hχ).ρ := by
  refine ⟨(rankOneIrrRep χ hχ).smooth, fun b hb => ?_⟩
  obtain ⟨x, y, hxy⟩ := hb
  exact (((Subsingleton.elim x y) ▸ hxy).false).elim

theorem exists_rankOneIrrRep_equiv {F : Type} [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (σ : IrrRep (GL (Fin 1) (v.adicCompletion F))) :
    ∃ (χ : (v.adicCompletion F)ˣ →* ℂˣ) (hχ : IsOpen (χ.ker : Set (v.adicCompletion F)ˣ)),
      Nonempty (σ.ρ.Equiv (rankOneIrrRep χ hχ).ρ) := by
  let L := v.adicCompletion F
  let G := GL (Fin 1) L
  letI := σ.irr
  obtain ⟨χ, hχ, hsc, -⟩ := exists_unique_smoothGLCentralCharacter v σ.ρ σ.smooth
  letI : Nontrivial σ.V := IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) σ.ρ.asModule
  obtain ⟨x, hx⟩ := exists_ne (0 : σ.V)
  let j : ℂ →ₗ[ℂ] σ.V := LinearMap.id.smulRight x
  have hj (g : G) (c : ℂ) : j (rankOneCharacter χ g c) = σ.ρ g (j c) := by
    change ((χ g.det : ℂ) * c) • x = σ.ρ g (c • x)
    have h := hsc g.det x
    rw [scalar_det_fin_one] at h
    rw [map_smul, h, smul_smul, mul_comm]
  let U : Subrepresentation σ.ρ :=
    ⟨LinearMap.range j, fun g {w} hw => by obtain ⟨c, rfl⟩ := hw; exact ⟨_, hj g c⟩⟩
  have hU : U ≠ ⊥ := fun h => hx (by
    have hm : x ∈ U := ⟨1, one_smul ℂ x⟩
    rwa [h] at hm)
  have hs : Function.Surjective j := LinearMap.range_eq_top.mp
    (congrArg (fun T : Subrepresentation σ.ρ => T.toSubmodule) ((eq_bot_or_eq_top U).resolve_left hU))
  have hi : Function.Injective j := smul_left_injective ℂ hx
  let t : (rankOneIrrRep χ hχ).ρ.IntertwiningMap σ.ρ :=
    ⟨j, fun g => LinearMap.ext (hj g)⟩
  exact ⟨χ, hχ, ⟨(Representation.IntertwiningMap.ofBijective t ⟨hi, hs⟩).symm⟩⟩

end GlobalTheory.GLp

#print axioms GlobalTheory.GLp.rankOneIrrRep_cuspidal
#print axioms GlobalTheory.GLp.exists_rankOneIrrRep_equiv
