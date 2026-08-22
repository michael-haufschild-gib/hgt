import GaloisForLFunctions.HTGeometry.DennisSteinFieldSymbolGeneration

/-!
# The rank-four torus-kernel test

This is the diagonal endpoint of Milnor's proof of Theorem 9.11.  After the Weyl-to-torus
reduction, a kernel element has the form

```text
h₀₁(u₁) h₀₂(u₂) h₀₃(u₃)
```

modulo Steinberg symbols.  The three off-base diagonal entries recover the three units separately.
Thus a spine in `K₂` has trivial parameters and is itself in the Steinberg-symbol subgroup.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open Matrix

variable {F : Type*} [Field F]

/-- The rank-four diagonal normal-form spine based at coordinate `0`. -/
def fin4TorusSpine (u₁ u₂ u₃ : Fˣ) : SteinbergGroup F (Fin 4) :=
  steinbergTorus (by decide : (0 : Fin 4) ≠ 1) u₁
    * steinbergTorus (by decide : (0 : Fin 4) ≠ 2) u₂
    * steinbergTorus (by decide : (0 : Fin 4) ≠ 3) u₃

/-- **Milnor §9.11, diagonal kernel step.** A rank-four torus spine belongs to `K₂` exactly when
all three displayed units are one. -/
theorem fin4TorusSpine_mem_KTwo_iff (u₁ u₂ u₃ : Fˣ) :
    fin4TorusSpine u₁ u₂ u₃ ∈ KTwo F (Fin 4) ↔ u₁ = 1 ∧ u₂ = 1 ∧ u₃ = 1 := by
  constructor
  · intro h
    rw [fin4TorusSpine, mem_KTwo_iff, map_mul, map_mul, steinbergToGL_torus,
      steinbergToGL_torus, steinbergToGL_torus] at h
    have h₁ := congrFun (congrFun (congrArg (fun M : (Matrix (Fin 4) (Fin 4) F)ˣ =>
        (M : Matrix (Fin 4) (Fin 4) F)) h) 1) 1
    have h₂ := congrFun (congrFun (congrArg (fun M : (Matrix (Fin 4) (Fin 4) F)ˣ =>
        (M : Matrix (Fin 4) (Fin 4) F)) h) 2) 2
    have h₃ := congrFun (congrFun (congrArg (fun M : (Matrix (Fin 4) (Fin 4) F)ˣ =>
        (M : Matrix (Fin 4) (Fin 4) F)) h) 3) 3
    refine ⟨?_, ?_, ?_⟩
    · apply Units.ext
      simpa [diagUnit, diagMatrix, Matrix.mul_apply, Fin.sum_univ_four] using h₁
    · apply Units.ext
      simpa [diagUnit, diagMatrix, Matrix.mul_apply, Fin.sum_univ_four] using h₂
    · apply Units.ext
      simpa [diagUnit, diagMatrix, Matrix.mul_apply, Fin.sum_univ_four] using h₃
  · rintro ⟨rfl, rfl, rfl⟩
    rw [fin4TorusSpine, steinbergTorus_one, steinbergTorus_one, steinbergTorus_one, one_mul]
    exact Subgroup.one_mem _

/-- The rank-four torus normal-form spine contributes no residue beyond Steinberg symbols. -/
theorem fin4TorusSpine_mem_symbolSubgroup_of_mem_KTwo (u₁ u₂ u₃ : Fˣ)
    (h : fin4TorusSpine u₁ u₂ u₃ ∈ KTwo F (Fin 4)) :
    fin4TorusSpine u₁ u₂ u₃ ∈ steinbergSymbolSubgroup F (Fin 4) := by
  obtain ⟨rfl, rfl, rfl⟩ := (fin4TorusSpine_mem_KTwo_iff u₁ u₂ u₃).1 h
  rw [fin4TorusSpine, steinbergTorus_one, steinbergTorus_one, steinbergTorus_one, one_mul]
  exact Subgroup.one_mem _

end GaloisForLFunctions.HTGeometry
