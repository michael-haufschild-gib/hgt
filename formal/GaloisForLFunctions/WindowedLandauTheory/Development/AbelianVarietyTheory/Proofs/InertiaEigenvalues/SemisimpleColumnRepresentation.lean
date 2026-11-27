import GaloisForLFunctions.WindowedLandauTheory.SharpRestriction.LevelLetterCocycles.DataN
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.RepresentationTheory.Semisimple

/-! The column action of a general linear representation agrees with
Mathlib's representation and semisimplicity predicates. -/

open WindowedLandauTheory.MainNotions.N

namespace GlobalTheory.SemisimpleMatrix

variable {Γ k : Type} [Group Γ] [Field k] {a : ℕ}

def colRep (ρ : Γ →* GL (Fin a) k) : Representation k Γ (Fin a → k) where
  toFun g := Matrix.toLin' ((ρ g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k)
  map_one' := by
    rw [map_one, Units.val_one, Matrix.toLin'_one]
    rfl
  map_mul' g h := by
    rw [map_mul, Units.val_mul, Matrix.toLin'_mul]
    rfl

theorem colRep_apply (ρ : Γ →* GL (Fin a) k) (g : Γ) :
    colRep ρ g = Matrix.toLin' ((ρ g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k) := rfl

theorem colRep_semisimple (ρ : Γ →* GL (Fin a) k) (h : IsSSRep ρ) :
    (colRep ρ).IsSemisimpleRepresentation := by
  refine ⟨fun P => ?_⟩
  obtain ⟨W', h1, h2⟩ := h P.toSubmodule fun g v hv => P.apply_mem_toSubmodule g hv
  refine ⟨⟨W', fun g v hv => h1 g v hv⟩, ?_⟩
  rw [isCompl_iff, disjoint_iff, codisjoint_iff,
    ← Subrepresentation.toSubmodule_injective.eq_iff, ← Subrepresentation.toSubmodule_injective.eq_iff]
  rw [isCompl_iff, disjoint_iff, codisjoint_iff] at h2
  exact h2

end GlobalTheory.SemisimpleMatrix
